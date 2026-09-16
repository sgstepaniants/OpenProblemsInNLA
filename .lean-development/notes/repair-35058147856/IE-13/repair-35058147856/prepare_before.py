#!/usr/bin/env python3
"""Retain exact observed development inputs before editing; never execute Lean."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess

P = Path(__file__).resolve().parent
A = P.parent.parent
B = A.parent.parent
R = B / 'development-runs/35058147856'
G = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
COMMIT = 'd36c8b357347a78781e854328a95fd5e4adce852'
sha = lambda b: hashlib.sha256(b).hexdigest()
assert not (P / 'BEFORE-MANIFEST.json').exists()
receipt = json.loads((R / 'artifacts/lean-development-statements/receipt.json').read_text())
assert receipt['repository_commit'] == COMMIT
prior = json.loads((A / 'proof-handoffs/repair-35055219493/BEFORE-BINDINGS.json').read_text())
freeze = json.loads((A / 'STATEMENT-FREEZE.json').read_text())
assert sha((A / 'STATEMENT-FREEZE.json').read_bytes()) == '85916aae89eb2111ff914b8767e8918548c132a6ff6c7ed92e52286bec1998fe'

def save(rel, contents):
    dst = P / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    assert not dst.exists()
    dst.write_bytes(contents)

rows = []
paths = sorted([str(f.relative_to(A)) for f in (A / 'NLA/IE13').glob('*.lean')] + ['Solution.lean'])
assert len(paths) == 27
for rel in paths + ['Challenge.lean']:
    key = 'NLA/IE13/Complete.lean' if rel == 'Solution.lean' else 'Challenges/IE13.lean' if rel == 'Challenge.lean' else rel
    gitpath = '.lean-development/' + key
    blob = subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(G), 'rev-parse', COMMIT + ':' + gitpath]).decode().strip()
    raw = subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(G), 'cat-file', 'blob', blob])
    assert (A / rel).read_bytes() == raw, rel
    assert sha(raw) == receipt['source_sha256'][key], rel
    save('before/' + rel, raw)
    save('actual-git/' + key, raw)
    rows.append({'author_path': rel, 'receipt_key': key, 'git_path': gitpath,
                 'git_blob': blob, 'sha256': sha(raw), 'exact_bytes_match': True})
for rel, digest in freeze['frozen_files_sha256'].items():
    raw = (A / rel).read_bytes()
    assert sha(raw) == digest, rel
    save('frozen/' + rel, raw)
for name, row in prior['all28_public_headers'].items():
    text = (A / row['source']).read_text()
    m = re.search(r'(?m)^theorem\s+' + re.escape(name) + r'\b([\s\S]*?)\s*:=', text)
    assert m and ' '.join(m.group(0).removesuffix(':=').split()) == row['normalized_header'], name
save('before/IMPLEMENTATION-MAP.json', (A / 'IMPLEMENTATION-MAP.json').read_bytes())
save('frozen/STATEMENT-FREEZE.json', (A / 'STATEMENT-FREEZE.json').read_bytes())
shutil.copytree(R, P / 'actual-run')
for name in ['repair-35055219493', 'witness-attainment-complete']:
    save('prior-packets/' + name + '--MANIFEST.json', (A / 'proof-handoffs' / name / 'MANIFEST.json').read_bytes())
bindings = {'run': 35058147856, 'actual_commit': COMMIT,
    'root_audit_sha256': sha((R / 'ROOT-AUDIT.json').read_bytes()),
    'independent_runtime_manifest_sha256': sha((R / 'ie13-independent/MANIFEST.json').read_bytes()),
    'frozen_manifest_sha256': sha((A / 'STATEMENT-FREEZE.json').read_bytes()),
    'all27_active_plus_frozen_challenge_exact_source_matches': rows,
    'frozen_files_sha256': freeze['frozen_files_sha256'],
    'all28_public_headers': prior['all28_public_headers']}
save('BEFORE-BINDINGS.json', (json.dumps(bindings, indent=2) + '\n').encode())
manifest = {str(f.relative_to(P)): sha(f.read_bytes()) for f in sorted(P.rglob('*')) if f.is_file()}
save('BEFORE-MANIFEST.json', (json.dumps(manifest, indent=2) + '\n').encode())
print(json.dumps({'before_exact_input_matches': len(rows), 'frozen': len(freeze['frozen_files_sha256']),
    'contracts': len(prior['all28_public_headers']), 'BEFORE_MANIFEST_sha256': sha((P / 'BEFORE-MANIFEST.json').read_bytes())}, indent=2))
