"""Read-only Git/log audit. Does not invoke Lean or Lake."""
from pathlib import Path, PurePosixPath
import hashlib, json, re, subprocess, zipfile

HERE = Path(__file__).resolve().parent
RUN = Path('/tmp/nla-lean-next-20260915/development-runs/35040116376')
REPO = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
PACKAGE = Path('/tmp/nla-lean-next-20260915/inequalities/MI-04')
COMMIT = '32f2bd6520df49e45a782cd8813b377e8234d5cf'
ARTIFACT = RUN / 'artifacts/lean-development-statements'
sha = lambda b: hashlib.sha256(b).hexdigest()

def save(rel, data):
    p = HERE / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    if p.exists():
        assert p.read_bytes() == data, p
    else:
        p.write_bytes(data)

def git_file(rel):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(REPO),
                                    'show', COMMIT + ':' + rel])

run = json.loads((RUN / 'run.json').read_text())
jobs = json.loads((RUN / 'jobs.json').read_text())['jobs']
arts = json.loads((RUN / 'artifacts.json').read_text())['artifacts']
r = json.loads((ARTIFACT / 'receipt.json').read_text())
assert run['id'] == 35040116376 and run['head_sha'] == COMMIT
assert run['status'] == 'completed' and run['conclusion'] == 'failure'
assert run['run_attempt'] == 1 and r['run_attempt'] == '1'
assert r['run_id'] == str(run['id']) and r['repository_commit'] == COMMIT
assert r['uid'] == 1001 and r['platform'].startswith('Linux-')
assert r['status'] == 'failed'
assert r['mathematical_verification'] is False and r['comparator_run'] is False
assert len(jobs) == 1 and jobs[0]['id'] == 104617877093
assert jobs[0]['conclusion'] == 'failure'
assert len(arts) == 1 and arts[0]['id'] == 10424728704
assert arts[0]['workflow_run']['head_sha'] == COMMIT and not arts[0]['expired']
zip_bytes = (RUN / 'lean-development-statements.zip').read_bytes()
assert arts[0]['digest'] == 'sha256:' + sha(zip_bytes)
assert sha(zip_bytes) == 'da7ae17b630893d046643cfaed8c278a3dd941770218977cccf4cd43fe33f3ee'
with zipfile.ZipFile(RUN / 'lean-development-statements.zip') as z:
    members = []
    for item in z.infolist():
        p = PurePosixPath(item.filename)
        assert not p.is_absolute() and '..' not in p.parts
        assert ((item.external_attr >> 16) & 0o170000) != 0o120000
        if not item.is_dir():
            data = z.read(item)
            assert data == (ARTIFACT / p).read_bytes()
            members.append(str(p))
            save(Path('runtime/artifact') / p, data)
    assert len(members) == 8

files = subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(REPO),
          'ls-tree', '-r', '--name-only', COMMIT, '.lean-development'], text=True).splitlines()
assert len(files) == 216
assert {f.removeprefix('.lean-development/') for f in files} == set(r['source_sha256'])
for f in files:
    b = git_file(f)
    assert sha(b) == r['source_sha256'][f.removeprefix('.lean-development/')], f
    save(Path('git-inputs') / f, b)
save('git-inputs/.github/workflows/lean-development.yml',
     git_file('.github/workflows/lean-development.yml'))

job_bytes = (RUN / 'job-104617877093.log').read_bytes()
normalized = '\n'.join(re.sub(r'^\ufeff?\d{4}-\d\d-\d\dT[0-9:.]+Z ?', '', line)
                       for line in job_bytes.decode().splitlines())
assert COMMIT in normalized and sha(zip_bytes) in normalized
assert "RUN ['lake', 'build', 'NLA.MI04.Definitions']" in normalized
assert "RUN ['lake', 'env', 'lean', 'Challenges/MI04.lean']" in normalized
assert 'Elaborate independent statements' in json.dumps(jobs)
assert len(r['commands']) == 7
expected = [
    (['lean', '--version'], 0), (['lake', 'env', 'true'], 0),
    (['lake', 'exe', 'cache', 'get'], 0),
    (['lake', 'build', 'NLA.MI04.Definitions'], 1),
    (['lake', 'env', 'lean', 'Challenges/MI04.lean'], 1),
    (['lake', 'build', 'NLA.MF22.Norms', 'NLA.MF22.ScalarCertificates'], 1),
    (['lake', 'env', 'lean', 'Challenges/MF22.lean'], 0),
]
for c, (argv, code) in zip(r['commands'], expected):
    b = (ARTIFACT / c['log']).read_bytes()
    assert c['argv'] == argv and c['exit_code'] == code
    assert sha(b) == c['sha256']
    assert c['source_sha256_after'] == r['source_sha256']
    assert b.decode().rstrip('\n') in normalized, c['log']

manifest = json.loads(git_file('.lean-development/lake-manifest.json'))
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert len(pins) == 10 and pins == r['dependency_commits']
held_pins = {p['name']: p['rev'] for p in json.loads((PACKAGE/'lake-manifest.json').read_text())['packages']}
assert pins == held_pins
assert git_file('.lean-development/lean-toolchain') == (PACKAGE/'lean-toolchain').read_bytes()
assert 'Lean (version 4.33.1, x86_64-unknown-linux-gnu' in (ARTIFACT/'lean-version.log').read_text()

binding = {
    'NLA/MI04/Definitions.lean': 'NLA/MI04/Definitions.lean',
    'Challenges/MI04.lean': 'Challenge.lean',
    'notes/MI04-statement-review/NUMERICAL_TARGETS.md': 'NUMERICAL_TARGETS.md',
}
for git_rel, held_rel in binding.items():
    assert git_file('.lean-development/'+git_rel) == (PACKAGE/held_rel).read_bytes()
draft = json.loads((PACKAGE/'DRAFT-CHECKS.json').read_text())
for rel, h in draft['source_sha256'].items():
    assert sha((PACKAGE/rel).read_bytes()) == h
challenge = (PACKAGE/'Challenge.lean').read_text()
names = re.findall(r'^theorem\s+(\w+)', challenge, re.M)
assert names == draft['proposed_exports'] and len(names) == 21
assert challenge.count('by sorry') == 21
assert not (PACKAGE/'Solution.lean').exists()
assert not (PACKAGE/'NLA/MI04/Solution.lean').exists()
assert not re.search(r'\b(sorry|axiom)\b', (PACKAGE/'NLA/MI04/Definitions.lean').read_text())
mi_log = (ARTIFACT/'MI-04-modules.log').read_text()
assert 'Definitions.lean:32:14: Function expected at' in mi_log
assert 'Definitions.lean:85:46: Function expected at' in mi_log
assert mi_log.count('Function expected at') == 2
assert 'object file' in (ARTIFACT/'MI-04-challenge.log').read_text()
assert (ARTIFACT/'MI-04-challenge.log').read_text().count('declaration uses `sorry`') == 0
assert (ARTIFACT/'MF-22-challenge.log').read_text().count('declaration uses `sorry`') == 22

for rel in ['run.json','jobs.json','artifacts.json','FETCH-IDENTITY.json',
            'job-104617877093.log','lean-development-statements.zip','ROOT-AUDIT.json']:
    save(Path('runtime')/rel, (RUN/rel).read_bytes())
for rel in ['fetch_repository_run.py','audit_development_run.py']:
    save(Path('audit-tools')/rel, (RUN.parent.parent/rel).read_bytes())

out = {
    'reviewer': '/root/next_inequalities',
    'role_disclosure': 'Authored the MI04 statement package; this is a runtime/source-identity audit, not an independent mathematical referee approval.',
    'run': run['id'], 'commit': COMMIT, 'conclusion': 'failure',
    'job': jobs[0]['id'], 'artifact': arts[0]['id'], 'archive_sha256': sha(zip_bytes),
    'bound_tracked_inputs': len(files), 'exact_source_set': True,
    'all_seven_command_prepost_source_hashes_unchanged': True,
    'all_seven_raw_logs_contiguously_present_in_actual_job_log': True,
    'commands': [{k:v for k,v in c.items() if k!='source_sha256_after'} for c in r['commands']],
    'dependency_commits': pins,
    'held_MI04_package_files_unchanged': len(draft['source_sha256']),
    'MI04_source_bindings': {k:sha(git_file('.lean-development/'+k)) for k in binding},
    'MI04_intended_obligations': names,
    'MI04_definition_elaboration_passed': False,
    'MI04_challenge_elaboration_passed': False,
    'MI04_reached_declaration_placeholders': 0,
    'MI04_failure': 'Definitions lines32/85 unannotated Matrix.toEuclideanCLM application; Challenge dependency missing.',
    'MF22_norm_module_built': True,
    'MF22_scalar_module_passed': False,
    'MF22_challenge_types_passed': 22,
    'mathematical_verification': False, 'comparator_run': False,
    'freeze_authorized_by_this_audit': False,
    'local_lean_or_lake_executed': False,
}
save('AUDIT.json', (json.dumps(out, indent=2)+'\n').encode())
inputs = {str(p.relative_to(HERE)):sha(p.read_bytes()) for p in sorted(HERE.rglob('*'))
          if p.is_file() and p.name not in {'INPUTS.json','REVIEW.md'}}
save('INPUTS.json', (json.dumps(inputs, indent=2)+'\n').encode())
print(json.dumps({'report':str(HERE), 'audit_sha256':sha((HERE/'AUDIT.json').read_bytes()),
                  'inputs_sha256':sha((HERE/'INPUTS.json').read_bytes()),
                  'MI04_statement_acceptance':False}, indent=2))
