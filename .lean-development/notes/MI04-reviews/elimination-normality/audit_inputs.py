#!/usr/bin/env python3
"""Bind a source-only independent MI-04 review; never execute Lean or Lake."""
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
NEW = {
    'WeightedProbes': '8fb7c11c6c36371a3a3cee2e3ed6869be8b325ea063a8abe35bd5cd79510f693',
    'Probes': '659176443980b438e7f55bd8df45ee5174ac87117fc37a73bd6c4900f349df01',
    'BasisTransport': 'a3bd7f091903150bcf01c981a5a1ae8aae7bc8c31ea00f4b601aa53636c9341e',
    'Normality': 'd8abea3f3a78a9381890e637e022553ba0b9b0317d184b33d799123391831d6f',
}
DEPENDENCIES = ['Limit', 'Unitary', 'ScaledSymmetry', 'BlockSymmetry', 'Coordinates',
    'Correction', 'Punctured', 'UpperBound', 'Quadratic', 'Rayleigh', 'ScalarGeometry']
PACKETS = {
    'basis-normality': '0fd7594f1975e044862f4c47bd242633284b3ba0e1ec8aac89401175cf577350',
    'repair-35046126916': '9182bf25928f2f11ed6e1fa15bd929aa4e7839ce86f6c9a54859ab27579ea65c',
    'proactive-Ne-symm': '93f53996092456e3a2eb66a8db397080ff1124030c0ccdf536543102e0b67f34',
    'proactive-basis-Ne-symm': '1f7e419c3496239aacbc31d5037e6cdc67aa3fd429fd6cb84727f0a3e14ae3b5',
}
API = [
    'Mathlib/Analysis/InnerProductSpace/PiL2.lean',
    'Mathlib/Analysis/InnerProductSpace/Orthonormal.lean',
    'Mathlib/Analysis/InnerProductSpace/Adjoint.lean',
    'Mathlib/Analysis/CStarAlgebra/Matrix.lean',
    'Mathlib/Order/Filter/Tendsto.lean',
    'Mathlib/Topology/Separation/Hausdorff.lean',
    'Mathlib/Topology/Order/DenselyOrdered.lean',
]
FILES = {}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def retain(path, rel, role, expected=None):
    data = path.read_bytes()
    h = digest(data)
    if expected is not None:
        assert h == expected, (str(path), h, expected)
    target = OUT / 'snapshots' / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        assert target.read_bytes() == data, ('immutable snapshot differs', str(target))
    else:
        target.write_bytes(data)
    FILES[rel] = {'sha256': h, 'bytes': len(data), 'role': role}
    return data

def header(text, name):
    start = re.search(r'(?m)^theorem\s+' + re.escape(name) + r'\b', text)
    assert start, name
    return ' '.join(text[start.start():].split(':=', 1)[0].split())

freeze = json.loads((PKG / 'STATEMENT-FREEZE.json').read_text())
for rel, h in freeze['frozen_files_sha256'].items():
    retain(PKG/rel, 'package/'+rel, 'unchanged frozen boundary/configuration', h)
retain(PKG/'STATEMENT-FREEZE.json', 'package/STATEMENT-FREEZE.json', 'historical statement freeze')
for name in list(NEW) + DEPENDENCIES:
    rel = f'NLA/MI04/{name}.lean'
    retain(PKG/rel, 'package/'+rel,
           'complete new source reviewed' if name in NEW else 'prior-reviewed dependency source reconciled',
           NEW.get(name))
for name, expected in PACKETS.items():
    directory = PKG/'proof-handoffs'/name
    manifest_data = retain(directory/'MANIFEST.json', f'handoffs/{name}/MANIFEST.json',
        'author source handoff or explicitly separated repair', expected)
    manifest = json.loads(manifest_data)
    for rel, h in manifest.get('files', {}).items():
        retain(directory/rel, f'handoffs/{name}/{rel}', 'retained before/after/diff/actual diagnostic', h)
for name in ['weighted-probes']:
    retain(PKG/'proof-handoffs'/name/'MANIFEST.json', f'handoffs/{name}/MANIFEST.json',
        'historical original weighted-probes handoff; later Probes repair explicitly retained')
source = json.loads((PKG/'SOURCE-PROVENANCE.json').read_text())
assert source['immutable_commit'] == COMMIT
for rel, h in source['files_sha256'].items():
    data = retain(PKG/'source'/rel, 'source/'+rel, 'original canonical target/manuscript/policy', h)
    assert data == subprocess.check_output(['git','show',f'{COMMIT}:{rel}'], cwd=REPO), rel
for rel in API:
    data = retain(MATH/rel, 'mathlib/'+rel, 'pinned primary API inspected')
    assert data == subprocess.check_output(['git','show',f'{MATH_COMMIT}:{rel}'], cwd=MATH), rel
for prior in ['MI04-elimination-second-order-limit', 'MI04-elimination-block-extrema']:
    for rel in ['REVIEW.md','CHECKS.json','INPUTS.json','MANIFEST.json']:
        retain(BASE/'reviews'/prior/rel, f'prior-reviews/{prior}/{rel}', 'immutable prior incremental review')

for name in list(NEW) + DEPENDENCIES:
    text = (PKG/f'NLA/MI04/{name}.lean').read_text()
    assert not re.search(r'\b(sorry|admit|unsafe|native_decide|axiom)\b', text), name
    assert not re.search(r'(?m)^import .*Challenge', text), name
challenge = (PKG/'Challenge.lean').read_text()
targets = {
    'weighted_magnitude_identity':'WeightedProbes',
    'offDiagonal_magnitude_symmetry':'Probes',
    'orthonormal_pair_symmetry':'BasisTransport',
    'pair_symmetry_normal':'Normality',
}
headers = {}
for theorem, module in targets.items():
    text = (PKG/f'NLA/MI04/{module}.lean').read_text()
    headers[theorem] = header(challenge,theorem) == header(text,theorem)
    assert headers[theorem], theorem
    assert f'#print axioms {theorem}' in text
    assert f'#assert_trust kernel {theorem}' in text
    assert 'set_option leancert.trust "kernel"' in text
before_basis = (PKG/'proof-handoffs/proactive-basis-Ne-symm/before/BasisTransport.lean').read_bytes()
after_basis = (PKG/'NLA/MI04/BasisTransport.lean').read_bytes()
assert before_basis.replace(b'hne.symm', b'Ne.symm hne') == after_basis
before_probes = (PKG/'proof-handoffs/proactive-Ne-symm/before/Probes.lean').read_bytes()
after_probes = (PKG/'NLA/MI04/Probes.lean').read_bytes()
assert before_probes.replace(b'hij.symm', b'(Ne.symm hij)') == after_probes
repair = PKG/'proof-handoffs/repair-35046126916'
for name in ['Coordinates','Rayleigh']:
    assert (repair/f'after/{name}.lean').read_bytes() == (PKG/f'NLA/MI04/{name}.lean').read_bytes()
    assert (repair/f'before/{name}.lean').read_bytes() == subprocess.check_output([
        'git','show',f'64a04495cb03fa7496cbdc3dc72f94779ab4c340:.lean-development/NLA/MI04/{name}.lean'],cwd=REPO)

checks = {
    'reviewer':'OpenAI Codex AI agent /root/next_elimination',
    'reviewer_is_MI04_implementation_author':False,
    'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
    'verdict':'APPROVE incremental mathematical source; author corrected one prospective API defect; actual compilation pending',
    'new_sources_sha256':NEW,
    'all_ten_frozen_files_unchanged':True,
    'four_exact_frozen_header_matches':headers,
    'original_source_commit':COMMIT,
    'all_original_sources_match_immutable_Git':True,
    'pinned_Mathlib_commit':MATH_COMMIT,
    'all_retained_API_files_match_pinned_Git':True,
    'complete_new_modules_read':list(NEW),
    'prior_reviewed_dependencies_reconciled':DEPENDENCIES,
    'method_checks':{
        'actual_positive_side_limits_and_nontrivial_filter':True,
        'opposite_block_peak_coefficients_are_row_and_column_magnitudes':True,
        'two_exact_probes_isolate_each_entry_with_no_dimension_enumeration':True,
        'basis_extension_retains_given_vectors_and_actual_unitary_coordinates':True,
        'all_complex_orthonormal_pairs_no_dimension_at_least_two_assumption':True,
        'singleton_extension_and_all_Parseval_terms_including_diagonal':True,
        'arbitrary_vector_normalization_cancels_only_proved_nonzero_scalar':True,
        'actual_CLM_adjoint_normality_equivalence_and_injective_matrix_star_map':True,
        'dimension_one_retained_and_no_X_invertibility_or_genericity':True,
        'no_new_proof_holes_axioms_unsafe_native_or_Challenge_imports':True,
        'kernel_assertions_and_axiom_prints_present_not_yet_executed':True,
    },
    'findings':[{
        'id':'MI04-normality-source-01',
        'kind':'prospective Lean API defect, no mathematical defect',
        'location':'original BasisTransport.lean:48',
        'description':'hne.symm on a disequality repeated the invalid field lookup actually observed in Coordinates.',
        'author_resolution':'One explicit Ne.symm hne replacement; exact before/after/diff retained.',
        'status':'resolved in reviewed source; actual compiler acceptance pending',
    }],
    'repair_reconciliation':{
        'actual_run':35046126916,
        'actual_commit':'64a04495cb03fa7496cbdc3dc72f94779ab4c340',
        'Rayleigh_Coordinates_before_match_Git':True,
        'Rayleigh_Coordinates_proof_only_API_repairs_reviewed':True,
        'Probes_two_proactive_Ne_symm_replacements_only':True,
        'BasisTransport_one_proactive_Ne_symm_replacement_only':True,
        'no_claim_new_four_modules_ran_in_that_failed_run':True,
    },
    'mechanical_scope':{
        'local_Lean_or_Lake':False,
        'new_module_actual_compilation':'pending; source-only review',
        'Comparator':'not run in this review',
        'default_kernel':'not run in this review',
        'transitive_axiom_acceptance':'not measured in this review',
    },
    'scope_limit':'Four intermediate frozen exports and their prerequisites only. Diagonalization, collinearity, affine reconstruction, full solution, and publication gates remain outside this acceptance.',
    'author_source_mutations_by_reviewer':False,
}
(OUT/'INPUTS.json').write_text(json.dumps({'files':FILES,'count':len(FILES)},indent=2)+'\n')
(OUT/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({'input_count':len(FILES),'checks_sha256':digest((OUT/'CHECKS.json').read_bytes()),
    'inputs_sha256':digest((OUT/'INPUTS.json').read_bytes()),'four_headers':headers},indent=2))
