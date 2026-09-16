#!/usr/bin/env python3
"""Authenticate completed development evidence; no Lean or Lake is executed."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

P = Path(__file__).resolve().parent
R = P.parent
G = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
HEAD = 'd36c8b357347a78781e854328a95fd5e4adce852'
RUN = 35058147856
sha = lambda b: hashlib.sha256(b).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(G), *args])

meta = json.loads((R / 'run.json').read_text())
assert meta['id'] == RUN and meta['head_sha'] == HEAD and meta['status'] == 'completed'
assert meta['repository']['full_name'] == 'sgstepaniants/OpenProblemsInNLA'
A = R / 'artifacts/lean-development-statements'
receipt = json.loads((A / 'receipt.json').read_text())
assert receipt['repository_commit'] == HEAD and receipt['run_id'] == str(RUN)
assert receipt['uid'] == 1001 and receipt['platform'].startswith('Linux-')
assert receipt['mathematical_verification'] is False and receipt['comparator_run'] is False
expected = {}
for entry in git('ls-tree', '-r', '-z', HEAD, '--', '.lean-development').split(b'\0'):
    if not entry:
        continue
    desc, path = entry.split(b'\t', 1)
    mode, kind, blob = desc.split()
    assert kind == b'blob'
    expected[path.decode()[len('.lean-development/'):]] = blob.decode()
assert len(expected) == len(receipt['source_sha256']) == 1633
assert set(expected) == set(receipt['source_sha256'])
bindings = []
for rel, blob in sorted(expected.items()):
    contents = git('cat-file', 'blob', blob)
    assert sha(contents) == receipt['source_sha256'][rel], rel
    bindings.append({'path': rel, 'Git_blob': blob, 'sha256': sha(contents), 'receipt_match': True})

commands = receipt['commands']
assert len(commands) == 7
expected_argv = [
    ['lean', '--version'], ['lake', 'env', 'true'], ['lake', 'exe', 'cache', 'get'],
    ['lake', 'build', 'NLA.MI04.Complete'], ['lake', 'env', 'lean', 'Challenges/MI04.lean'],
    ['lake', 'build', 'NLA.IE13.Complete'], ['lake', 'env', 'lean', 'Challenges/IE13.lean']]
assert [c['argv'] for c in commands] == expected_argv
for c in commands:
    assert c['source_sha256_after'] == receipt['source_sha256'], c['log']
    assert sha((A / c['log']).read_bytes()) == c['sha256'], c['log']
assert all(c['exit_code'] == 0 for c in commands[:3])
pins = json.loads(git('show', HEAD + ':.lean-development/lake-manifest.json'))
for pin in pins['packages']: assert receipt['dependency_commits'][pin['name']] == pin['rev']

jobs = json.loads((R / 'jobs.json').read_text())['jobs']
job = next(j for j in jobs if j['name'] == 'statements')
assert job['head_sha'] == HEAD and job['conclusion'] == meta['conclusion']
raw_file = R / f"job-{job['id']}.log"
raw = raw_file.read_text()
raw_lines = [re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '', s) for s in raw.splitlines()]
assert HEAD in raw_lines
payload_matches = []
for c in commands:
    lines = [s for s in (A / c['log']).read_text().splitlines() if s]
    pos = 0
    for line in lines:
        while pos < len(raw_lines) and raw_lines[pos] != line:
            pos += 1
        assert pos < len(raw_lines), (c['log'], 'line absent from authenticated job log', line)
        pos += 1
    payload_matches.append({'log': c['log'], 'nonempty_payload_lines_matched_in_order': len(lines)})

artifact = next(a for a in json.loads((R / 'artifacts.json').read_text())['artifacts']
                if a['name'] == 'lean-development-statements')
archive_hash = sha((R / 'lean-development-statements.zip').read_bytes())
assert artifact['workflow_run']['head_sha'] == HEAD and artifact['digest'] == 'sha256:' + archive_hash
assert not artifact['expired']
outcomes = {}
for pid, namespace, expected_contracts in [('MI-04', 'MI04', 21), ('IE-13', 'IE13', 28)]:
    source = git('show', HEAD + ':.lean-development/Challenges/' + namespace + '.lean').decode()
    names = re.findall(r'(?m)^theorem\s+(\S+)', source)
    assert len(names) == expected_contracts
    names = ['NLA.' + namespace + '.' + n for n in names]
    module = (A / (pid + '-modules.log')).read_text()
    challenge = (A / (pid + '-challenge.log')).read_text()
    passed = re.findall(r'(?:Built|Replayed) (NLA\.' + namespace + r'\.\w+)', module)
    failed = re.findall(r'✖ \[[^\]]*\] Building (NLA\.' + namespace + r'\.\w+)', module)
    public_axioms = {}
    for name in names:
        found = re.findall(re.escape("'" + name + "' depends on axioms: ") + r'\[([^\]]*)\]', module)
        if found:
            public_axioms[name] = [x.split(', ') if x else [] for x in found]
    module_command = next(c for c in commands if c['log'] == pid + '-modules.log')
    challenge_command = next(c for c in commands if c['log'] == pid + '-challenge.log')
    outcomes[pid] = {
        'module_build_exit_code': module_command['exit_code'],
        'modules_reported_built': sorted(set(passed)), 'modules_reported_failed': sorted(set(failed)),
        'all_error_lines': [s for s in module.splitlines() if s.startswith('error:')],
        'public_expected_names': names, 'public_axiom_reports_actually_printed': public_axioms,
        'challenge_exit_code': challenge_command['exit_code'],
        'challenge_deliberate_holes': challenge.count('declaration uses `sorry`'),
        'challenge_errors': [s for s in challenge.splitlines() if s.startswith('error:')],
        'strict_whole_problem_verification': False,
        'Comparator_executed': False}
    assert outcomes[pid]['challenge_deliberate_holes'] == expected_contracts

shared = json.loads((R / 'ROOT-AUDIT.json').read_text())
assert shared['actual_checkout'] == HEAD and shared['bound_git_inputs'] == 1633
for rel in ['.lean-development/check.py', '.lean-development/projects.json', '.github/workflows/lean-development.yml']:
    dst = P / 'exact-executed-source' / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_bytes(git('show', HEAD + ':' + rel))
(P / 'ALL-1633-INPUT-BINDINGS.json').write_text(json.dumps(bindings, indent=2) + '\n')
report = {
    'reviewer': '/root/ie13_continuation', 'run': RUN, 'actual_commit': HEAD,
    'actual_run_conclusion': meta['conclusion'], 'actual_job': job['id'],
    'all1633_tracked_inputs_exactly_Git_and_receipt_bound': True,
    'all7_command_pre_post_source_maps_identical': True,
    'all7_command_logs_sha256_and_raw_job_stream_bound': True,
    'log_payload_matches': payload_matches,
    'dependencies_exactly_match_pinned_manifest': True,
    'platform': receipt['platform'], 'uid': receipt['uid'],
    'artifact_id': artifact['id'], 'artifact_sha256': archive_hash,
    'receipt_sha256': sha((A / 'receipt.json').read_bytes()),
    'shared_audit_sha256': sha((R / 'ROOT-AUDIT.json').read_bytes()),
    'shared_auditor_label_note': 'The reused auditor emits a fixed /root reviewer label. It was run by this child agent and is not a separate claim of root manual review.',
    'outcomes': outcomes,
    'local_Lean_or_Lake': False, 'source_changes': False,
    'new_dispatch_Git_count_or_publication': False,
    'scope': 'Authenticated development compilation and statement elaboration only. It does not execute strict default-kernel replay or Comparator. Deliberate Challenge holes are specifications; printed partial helper results do not establish complete problem acceptance.'
}
(P / 'OPERATIONAL-CHECKS.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'run': RUN, 'conclusion': meta['conclusion'], 'inputs': 1633,
    'commands': 7, 'outcomes': {k:{x:v[x] for x in ['module_build_exit_code','modules_reported_built','modules_reported_failed','challenge_exit_code','challenge_deliberate_holes']} for k,v in outcomes.items()},
    'CHECKS_sha256': sha((P / 'OPERATIONAL-CHECKS.json').read_bytes())}, indent=2))
