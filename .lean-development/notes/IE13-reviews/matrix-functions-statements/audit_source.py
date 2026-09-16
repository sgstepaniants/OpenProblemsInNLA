"""Read-only, source-bound checks for the independent IE13 statement review."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).parent
PKG = Path('/tmp/nla-lean-next-20260915/elimination/IE-13')
REPO = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
MATHLIB = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages/mathlib/Mathlib')


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    manifest = json.loads((PKG/'DRAFT-MANIFEST.json').read_text())
    assert sha(PKG/'DRAFT-MANIFEST.json') == '7df9990e5e5f944f4c90890a6e12cd0cc6b9838cbbde2ee33a9f5061d7516c38'
    for rel, record in manifest['files'].items():
        assert sha(PKG/rel) == record['sha256']
        assert (PKG/rel).stat().st_size == record['bytes']
        assert (PKG/rel).read_bytes() == (ROOT/'snapshot'/rel).read_bytes()
    provenance = json.loads((PKG/'SOURCE-PROVENANCE.json').read_text())
    for source in provenance['sources']:
        actual = subprocess.check_output(['git', 'show', source['commit']+':'+source['git_path']], cwd=REPO)
        assert actual == (PKG/source['retained_path']).read_bytes()
        blob = subprocess.check_output(['git', 'rev-parse', source['commit']+':'+source['git_path']], cwd=REPO, text=True).strip()
        assert blob == source['git_blob']
    reuse = json.loads((PKG/'REUSE-AUDIT.json').read_text())
    prior = {}
    for rel in reuse['source_paths']:
        actual = subprocess.check_output(['git', 'show', reuse['source_commit']+':'+rel], cwd=REPO)
        assert hashlib.sha256(actual).hexdigest() == reuse['source_sha256'][Path(rel).name]
        prior[Path(rel).name] = actual.decode()
    definitions = (PKG/'NLA/IE13/Definitions.lean').read_text()
    for name in reuse['declarations_with_identical_semantic_bodies']:
        pattern = rf'(?ms)^(?:abbrev|def) {re.escape(name)}\b.*?(?=\n/--|\n(?:abbrev|def|theorem|lemma) |\n(?:namespace|end) |\Z)'
        new = re.search(pattern, definitions).group(0).strip()
        old = next(match.group(0).strip() for text in prior.values()
                   if (match := re.search(pattern, text)) is not None)
        assert new == old, name
    challenge = (PKG/'Challenge.lean').read_text()
    names = re.findall(r'^theorem\s+(\w+)', challenge, re.M)
    assert len(names) == 28 and len(set(names)) == 28
    assert len(re.findall(r'\bsorry\b', challenge)) == 28
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', definitions)
    assert not (PKG/'Solution.lean').exists()
    assert len(list((PKG/'NLA').rglob('*.lean'))) == 1
    comparator = json.loads((PKG/'comparator.json').read_text())
    assert comparator['theorem_names'] == ['NLA.IE13.'+name for name in names]
    assert comparator['definition_names'] == []
    assert comparator['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
    deps = {x['name']: x['rev'] for x in json.loads((PKG/'lake-manifest.json').read_text())['packages']}
    assert deps['mathlib'] == '0df444a360eaa60ab8c11dca51a86af692955474'
    assert deps['leancert'] == '621a43d7cf21f87872392a01e874f2f1dbddc926'
    assert (PKG/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'
    api_hashes = {}
    for rel in ['Data/Finset/Lattice/Fold.lean', 'Order/Bounds/Defs.lean',
                'Order/ConditionallyCompleteLattice/Basic.lean']:
        dest = ROOT/'api-source'/rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes((MATHLIB/rel).read_bytes())
        api_hashes[rel] = sha(dest)
    inputs = {'author_manifest_sha256': sha(PKG/'DRAFT-MANIFEST.json'),
              'snapshot_files': {str(p.relative_to(ROOT/'snapshot')): sha(p)
                                 for p in sorted((ROOT/'snapshot').rglob('*')) if p.is_file()},
              'canonical_git_source_comparisons': True,
              'reused_semantic_blocks_exactly_equal': reuse['declarations_with_identical_semantic_bodies'],
              'challenge_declarations': names,
              'read_pinned_api_hashes': api_hashes}
    (ROOT/'INPUTS.json').write_text(json.dumps(inputs, indent=2)+'\n')
    diagnostics = json.loads((ROOT/'EXACT-DIAGNOSTICS.json').read_text())
    checks = {'problem_id': 'IE-13', 'reviewer': 'OpenAI Codex agent /root/next_matrix_functions',
              'phase': 'independent full pre-proof statement review',
              'independent_nonimplementer': True,
              'verdict': 'APPROVE exact full statement boundary; no mathematical correction requested',
              'all21_manifest_files_match': True,
              'all3_canonical_sources_match_immutable_git': True,
              'all13_reused_definition_bodies_identical': True,
              'all28_contracts_independently_read': True,
              'comparator_28_to_28_no_definition_holes': True,
              'schema_validation': json.loads((ROOT/'SCHEMA-CHECK.json').read_text()),
              'pins_match': True, 'author_source_mutated': False,
              'exact_diagnostics_sha256': sha(ROOT/'EXACT-DIAGNOSTICS.json'),
              'bounded_diagnostic_summary': {k: v for k, v in diagnostics.items() if not isinstance(v, list)},
              'bounded_witness_cases': len(diagnostics['rational_witnesses']),
              'local_Lean_or_Lake_execution': False,
              'actual_statement_elaboration_accepted': False,
              'freeze_or_proof_implementation_authorized_by_this_report': False,
              'kernel_axiom_or_comparator_acceptance_claimed': False,
              'whole_problem_Lean_verified': False}
    (ROOT/'CHECKS.json').write_text(json.dumps(checks, indent=2)+'\n')
    print('Exact draft/source/reuse/pin/metadata checks passed; 28 statements approved at source level only.')


if __name__ == '__main__':
    main()
