#!/usr/bin/env python3
"""Snapshot the candidate and refresh its source index; no Lean execution."""
from pathlib import Path
import hashlib
import json
import re

P = Path(__file__).resolve().parent
A = P.parent.parent
sha = lambda b: hashlib.sha256(b).hexdigest()
before = json.loads((P / 'BEFORE-BINDINGS.json').read_text())
paths = [r['author_path'] for r in before['all27_active_plus_frozen_challenge_exact_source_matches']
         if r['author_path'] != 'Challenge.lean']
source_map = json.loads((P / 'before/IMPLEMENTATION-MAP.json').read_text())
assert source_map['actual_compilation_of_complete_closure'] is False
assert source_map['whole_problem_verified'] is False
for rel in sorted(set(paths) | set(before['frozen_files_sha256'])):
    raw = (A / rel).read_bytes()
    dest = P / 'after' / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    assert not dest.exists()
    dest.write_bytes(raw)
source_map['source_sha256'] = {rel: sha((A / rel).read_bytes()) for rel in paths}
for name, row in source_map['public_exports'].items():
    contents = (A / row['file']).read_bytes()
    text = contents.decode()
    match = re.search(r'(?m)^theorem\s+' + re.escape(name) + r'\b', text)
    assert match, name
    row['line'] = text[:match.start()].count('\n') + 1
    row['sha256'] = sha(contents)
contents = (json.dumps(source_map, indent=2) + '\n').encode()
(A / 'IMPLEMENTATION-MAP.json').write_bytes(contents)
(P / 'after/IMPLEMENTATION-MAP.json').write_bytes(contents)
print(json.dumps({'snapshotted_active': len(paths), 'frozen': len(before['frozen_files_sha256']),
                  'refreshed_implementation_map_sha256': sha(contents)}, indent=2))
