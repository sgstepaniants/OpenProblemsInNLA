#!/usr/bin/env python3
"""Read-only source binding for an independent, non-executed Lean source review."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

OUT = Path(__file__).resolve().parent
BASE = Path('/tmp/nla-lean-next-20260915')
PKG = BASE / 'inequalities/MI-04'
REPO = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
MATH = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages/mathlib')
COMMIT = 'ce47b5630bf3680d9211131c3a43825b022c139a'
MATH_COMMIT = '0df444a360eaa60ab8c11dca51a86af692955474'
HANDOFF = 'proof-handoffs/block-extrema/MANIFEST.json'
EXPECTED_HANDOFF = '99b196f373f86bc43b7e2bfd6a239d5dd1ec9c0be8cd6f94fdb896ad3710ea62'
PROOFS = [
    'NLA/MI04/BlockSymmetry.lean', 'NLA/MI04/ScaledSymmetry.lean',
    'NLA/MI04/Unitary.lean', 'NLA/MI04/Coordinates.lean',
    'NLA/MI04/Rayleigh.lean', 'NLA/MI04/Quadratic.lean',
]
API = [
    'Mathlib/Data/Matrix/Block.lean',
    'Mathlib/Algebra/Star/Unitary.lean',
    'Mathlib/LinearAlgebra/UnitaryGroup.lean',
    'Mathlib/LinearAlgebra/Matrix/Hermitian.lean',
    'Mathlib/Analysis/InnerProductSpace/Adjoint.lean',
    'Mathlib/Analysis/InnerProductSpace/Rayleigh.lean',
    'Mathlib/Analysis/CStarAlgebra/Matrix.lean',
]
FILES = {}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def read_json(path):
    return json.loads(path.read_text())

def retain(path, rel, role, expected=None):
    data = path.read_bytes()
    h = digest(data)
    if expected is not None:
        assert h == expected, (path, h, expected)
    target = OUT / 'snapshots' / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        assert target.read_bytes() == data, ('immutable snapshot changed', target)
    else:
        target.write_bytes(data)
    FILES[str(rel)] = {'sha256':h, 'bytes':len(data), 'role':role}
    return data

def header(text, name):
    match = re.search(r'(?m)^theorem\s+' + re.escape(name) + r'\b', text)
    assert match, name
    decl = text[match.start():].split(':=', 1)[0]
    return ' '.join(decl.split())

handoff_data = retain(PKG/HANDOFF, 'package/'+HANDOFF, 'author source handoff', EXPECTED_HANDOFF)
handoff = json.loads(handoff_data)
freeze = read_json(PKG/'STATEMENT-FREEZE.json')
for rel, h in freeze['frozen_files_sha256'].items():
    retain(PKG/rel, 'package/'+rel, 'unchanged frozen boundary/config', h)
retain(PKG/'STATEMENT-FREEZE.json', 'package/STATEMENT-FREEZE.json', 'statement freeze and its historical phase labels')
old = read_json(PKG/'proof-handoffs/second-order-limit/MANIFEST.json')
for rel in PROOFS:
    expected = handoff['new_files'].get(rel)
    retain(PKG/rel, 'package/'+rel, 'complete mathematical source read', expected)
source_prov = read_json(PKG/'SOURCE-PROVENANCE.json')
assert source_prov['immutable_commit'] == COMMIT
for rel, h in source_prov['files_sha256'].items():
    data = retain(PKG/'source'/rel, 'source/'+rel, 'immutable original source/policy', h)
    git_data = subprocess.check_output(['git','show',f'{COMMIT}:{rel}'], cwd=REPO)
    assert data == git_data, ('original source mismatch', rel)
for rel in API:
    data = retain(MATH/rel, 'mathlib/'+rel, 'pinned primary API source')
    git_data = subprocess.check_output(['git','show',f'{MATH_COMMIT}:{rel}'], cwd=MATH)
    assert data == git_data, ('pinned Mathlib source mismatch', rel)
prior = BASE/'reviews/MI04-elimination-second-order-limit'
for rel in ['REVIEW.md','CHECKS.json','INPUTS.json']:
    retain(prior/rel, 'prior-limit-review/'+rel, 'separate prior incremental review, unchanged')
challenge = (PKG/'Challenge.lean').read_text()
header_matches = {}
for name, mod in [('universal_to_extreme_symmetry','BlockSymmetry'),('extreme_symmetry_scaled_unitary','ScaledSymmetry')]:
    text = (PKG/f'NLA/MI04/{mod}.lean').read_text()
    header_matches[name] = header(challenge,name) == header(text,name)
    assert header_matches[name], name
    assert f'#print axioms {name}' in text
    assert f'#assert_trust kernel {name}' in text
    assert 'set_option leancert.trust "kernel"' in text
for rel in PROOFS:
    text = (PKG/rel).read_text()
    assert not re.search(r'\b(sorry|admit|unsafe|native_decide|axiom)\b', text), rel
    assert not re.search(r'^import .*Challenge', text, re.M), rel
checks = {
    'reviewer':'OpenAI Codex AI agent /root/next_elimination',
    'reviewer_is_implementation_author':False,
    'phase':'independent incremental mathematical source review',
    'verdict':'APPROVE source only; actual compilation and complete-project gates pending',
    'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
    'handoff_sha256':EXPECTED_HANDOFF,
    'new_sources_sha256':handoff['new_files'],
    'all_ten_frozen_files_unchanged':True,
    'exact_header_matches':header_matches,
    'all_original_sources_match_immutable_Git':True,
    'all_retained_primary_API_files_match_pinned_Git':True,
    'complete_sources_read':PROOFS,
    'finding_count':0,
    'method_checks':{
        'actual_Euclidean_operator_norm_and_Rayleigh_supremum':True,
        'genuine_PSD_boundary_completion_including_singular_zero_case':True,
        'nonnegative_boundary_value_from_two_actual_coordinate_vectors':True,
        'universal_original_completion_premise_used_without_replacement':True,
        'reverse_inequality_from_literal_sign_unitary_and_negated_T':True,
        'unitary_conjugation_inverts_each_arbitrary_Hermitian_test_T':True,
        'positive_scaling_uses_actual_T_div_r_and_positive_homogeneity':True,
        'all_complex_X_and_all_n_at_least_one':True,
        'no_rank_invertibility_or_distinctness_requirement':True,
        'no_proof_holes_new_axioms_unsafe_native_or_Challenge_imports_in_reviewed_sources':True,
        'kernel_trust_assertions_and_axiom_prints_present':True,
    },
    'mechanical_scope':{
        'local_Lean_or_Lake':False,
        'new_module_actual_compilation':'pending; no execution inspected or asserted',
        'Comparator':'not run in this review',
        'default_kernel':'not run in this review',
        'transitive_axiom_acceptance':'not measured in this review',
    },
    'scope_limit':'Two intermediate frozen exports and their source dependencies only; not complete MI04 acceptance.',
    'author_source_mutations':False,
}
(OUT/'INPUTS.json').write_text(json.dumps({'files':FILES,'count':len(FILES)},indent=2)+'\n')
(OUT/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({'input_count':len(FILES),'checks_sha256':digest((OUT/'CHECKS.json').read_bytes()),'inputs_sha256':digest((OUT/'INPUTS.json').read_bytes()),'headers':header_matches},indent=2))
