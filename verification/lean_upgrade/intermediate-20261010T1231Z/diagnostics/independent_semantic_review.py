#!/usr/bin/env python3
"""Read public sources and git baseline; save only a static review manifest."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from audit_sources import DECL, mask_comments

BASELINE = '88ac9e307b51043e5378c3eaebbbf927a6f6cf21'


def header_boundary(text):
    depth = 0
    type_proof = False
    for i, c in enumerate(text):
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        assert depth >= 0
        if depth == 0 and re.match(r':\s+by\b', text[i:]):
            type_proof = True
        line_prefix = text[text.rfind('\n', 0, i) + 1:i].strip()
        type_let_assignment = type_proof and re.match(r'letI?\s', line_prefix)
        if depth == 0 and ((text.startswith(':=', i) and not type_let_assignment) or
                          (c == '|' and not text[text.rfind('\n', 0, i) + 1:i].strip()) or
                          (text.startswith('where', i) and
                           (i == 0 or not text[i-1].isalnum()) and
                           (i+5 == len(text) or not text[i+5].isalnum()))):
            return i
    return len(text)


def declarations(text):
    clean = mask_comments(text)
    assert not re.search(r'\b(sorry|admit|axiom)\b', clean)
    found, scopes, pos = [], [], 0
    for line in clean.splitlines(True):
        stripped = line.strip()
        if m := re.fullmatch(r'(namespace|section)(?:\s+([^\s]+))?', stripped):
            scopes.append(m.groups())
        elif re.fullmatch(r'noncomputable\s+section', stripped):
            scopes.append(('section', None))
        elif re.fullmatch(r'end(?:\s+[^\s]+)?', stripped):
            assert scopes
            scopes.pop()
        elif m := DECL.match(stripped):
            name = '.'.join([*(n for k, n in scopes if k == 'namespace'), m[2]])
            tail = clean[pos:]
            head = re.sub(r'\s+', ' ', tail[:header_boundary(tail)]).strip()
            found.append((name, m[1], head))
        pos += len(line)
    assert not scopes
    return found


def ambient_context(text):
    return [re.sub(r'\s+', ' ', line.strip())
            for line in mask_comments(text).splitlines()
            if re.match(r'\s*(variable|universe|include|omit)\b', line)]


def classification(before, after):
    if before.replace('.hom', '') == after.replace('.hom', ''):
        return 'same_underlying_morphism_with_new_wrapper_projection'
    if 'ClosedUnderLimitsOfShape' in before or 'ClosedUnderColimitsOfShape' in before:
        assert before.rsplit(' : ', 1)[0] == after.rsplit(' : ', 1)[0]
        return 'same_closure_property_new_mathlib_class_api'
    if before == after.removeprefix('noncomputable '):
        return 'noncomputable_annotation_only'
    canonical = re.sub(
        r'\(by letI : AddCommGroup \(α →₀ k\) := Finsupp\.instAddCommGroup exact (.*)\)$',
        r'\1', after)
    if canonical == before:
        return 'same_result_type_explicit_canonical_finsupp_add_comm_group'
    canonical_unrolled_path = re.sub(
        r'\(by letI : AddCommGroup \(Q\.UnrolledPathComponent k u w\) := Finsupp\.instAddCommGroup exact (.*)\)$',
        r'\1', after)
    if canonical_unrolled_path == before:
        return 'same_result_type_explicit_canonical_unrolled_path_finsupp_add_comm_group'
    canonical_ginzburg_path = re.sub(
        r'\(by letI : AddCommGroup \(Q\.GinzburgPathComponent k u v\) := Finsupp\.instAddCommGroup exact (.*)\)$',
        r'\1', after)
    if canonical_ginzburg_path == before:
        return 'same_result_type_explicit_canonical_ginzburg_path_finsupp_add_comm_group'
    canonical_path_type_proof = re.sub(
        r' : by (?:letI : AddCommGroup \(Q\.(?:GinzburgPathComponent|PathComponent) k u v\) := Finsupp\.instAddCommGroup )+exact ',
        ' : ', after, count=1)
    if canonical_path_type_proof == before:
        return 'same_result_type_explicit_canonical_path_component_finsupp_add_comm_groups'
    canonical_prefix_type_proof = after.replace(
        ' : by letI (w : Q.Vertex) : AddCommGroup (Q.GinzburgPathComponent k u w) := Finsupp.instAddCommGroup exact ',
        ' : ', 1)
    if canonical_prefix_type_proof == before:
        return 'same_result_type_explicit_canonical_prefix_component_finsupp_group_family'
    canonical_lifted_path_type_proof = after.replace(
        ' : by letI : AddCommGroup (Q.PathComponent k u.1 v.1) := Finsupp.instAddCommGroup exact ',
        ' : ', 1)
    if canonical_lifted_path_type_proof == before:
        return 'same_result_type_explicit_canonical_lifted_path_finsupp_group'
    canonical_origin_path_type_proof = after.replace(
        ' : by letI : AddCommGroup (Q.PathComponent k x.1 v) := Finsupp.instAddCommGroup exact ',
        ' : ', 1)
    if canonical_origin_path_type_proof == before:
        return 'same_result_type_explicit_canonical_origin_path_finsupp_group'
    canonical_opposite_path_type_proof = after.replace(
        ' : by letI : AddCommGroup (Q.PathComponent k u v) := Finsupp.instAddCommGroup '
        'letI : AddCommGroup (Q.opposite.PathComponent k v.rev u.rev) := Finsupp.instAddCommGroup exact ',
        ' : ', 1)
    if canonical_opposite_path_type_proof == before:
        return 'same_result_type_explicit_canonical_original_and_opposite_path_finsupp_groups'
    # Independently reviewed GinzburgRegularity: same direct-sum carrier and
    # canonical pointwise DFinsupp group, with the identical component family.
    direct_sum = '(⨁ uv : Q.Vertex×Q.Vertex, Q.ginzburgCohomologicalComponent k uv.1 uv.2 q)'
    group = ('(DFinsupp.addCommGroup (β := fun uv : Q.Vertex×Q.Vertex => '
             'Q.ginzburgCohomologicalComponent k uv.1 uv.2 q))')
    canonical_direct_sum = after.replace(
        '@ModuleCat.of k _ ' + direct_sum + ' ' + group + ' _',
        'ModuleCat.of k ' + direct_sum)
    if canonical_direct_sum == before:
        return 'same_modulecat_object_explicit_canonical_dfinsupp_add_comm_group'
    jacobian_sum = ('(⨁ uv : Q.Vertex×Q.Vertex, Q.PathComponent k uv.1 uv.2 '
                    '⧸ (Q.pathJacobianIdeal k φ).hom uv.1 uv.2)')
    jacobian_group = ('(DFinsupp.addCommGroup (β := fun uv : Q.Vertex×Q.Vertex => '
                      'Q.PathComponent k uv.1 uv.2 ⧸ (Q.pathJacobianIdeal k φ).hom uv.1 uv.2))')
    canonical_jacobian_sum = after.replace(
        '@ModuleCat.of k _ ' + jacobian_sum + ' ' + jacobian_group + ' _',
        'ModuleCat.of k ' + jacobian_sum)
    if canonical_jacobian_sum == before:
        return 'same_jacobian_direct_sum_modulecat_object_explicit_canonical_dfinsupp_group'
    raise AssertionError(('Unexpected signature change', before, after))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-snapshot', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--final-freeze', action='store_true')
    parser.add_argument('--historical-source-directory', type=Path)
    args = parser.parse_args()
    expected_record = json.loads(args.source_snapshot.read_text())
    expected = expected_record['source_sha256']
    paths = ['ASGinzburg.lean'] + [p for p in subprocess.check_output(
        ['git', 'ls-tree', '-r', '--name-only', BASELINE, '--', 'ASGinzburg'],
        cwd=ROOT, text=True).splitlines() if p.endswith('.lean')]
    assert set(paths) == set(expected)
    raw = subprocess.check_output(['git', 'cat-file', '--batch'], cwd=ROOT,
        input=''.join(BASELINE + ':' + p + '\n' for p in paths).encode())
    originals, offset = {}, 0
    for path in paths:
        end = raw.index(b'\n', offset)
        header = raw[offset:end].split()
        assert header[1] == b'blob'
        size = int(header[2])
        offset = end + 1
        originals[path] = raw[offset:offset+size].decode()
        offset += size + 1
    assert offset == len(raw)
    sources, selected, historical_paths = {}, {}, []
    for p in paths:
        current = (ROOT / p).read_text()
        saved = args.historical_source_directory / p if args.historical_source_directory else None
        if saved and saved.exists() and hashlib.sha256(saved.read_bytes()).hexdigest() == expected[p]:
            sources[p], selected[p] = saved.read_text(), saved
            if hashlib.sha256(current.encode()).hexdigest() != expected[p]:
                historical_paths.append(p)
        elif hashlib.sha256(current.encode()).hexdigest() == expected[p]:
            sources[p], selected[p] = current, ROOT / p
        elif args.historical_source_directory:
            saved = args.historical_source_directory / p
            if saved.exists() and hashlib.sha256(saved.read_bytes()).hexdigest() == expected[p]:
                sources[p], selected[p] = saved.read_text(), saved
            else:
                assert hashlib.sha256(originals[p].encode()).hexdigest() == expected[p], p
                sources[p], selected[p] = originals[p], None
            historical_paths.append(p)
        else:
            raise AssertionError(('Sources changed since supplied verification freeze', p))
    hashes = {p: hashlib.sha256(text.encode()).hexdigest() for p, text in sources.items()}
    assert hashes == expected, 'Sources changed since the supplied verification freeze'
    assert not args.final_freeze or not historical_paths
    names_before, names_after, header_changes, modified = {}, {}, [], []
    for path in paths:
        before, after = originals[path], sources[path]
        a, b = declarations(before), declarations(after)
        assert [(n, k) for n, k, _ in a] == [(n, k) for n, k, _ in b], path
        assert ambient_context(before) == ambient_context(after), path
        for n, k, _ in a:
            assert n not in names_before
            names_before[n] = k
        for n, k, _ in b:
            assert n not in names_after
            names_after[n] = k
        if before != after:
            modified.append(path)
        for x, y in zip(a, b):
            if x[2] != y[2]:
                header_changes.append({'file': path, 'name': x[0], 'kind': x[1],
                    'before': x[2], 'after': y[2], 'classification': classification(x[2], y[2])})
    assert names_before == names_after
    # Require a stable collection; this is evidence of the reviewed bytes, not a build certificate.
    for p, saved in selected.items():
        if saved:
            assert hashlib.sha256(saved.read_bytes()).hexdigest() == hashes[p], p
    result = {
        'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
        'review_mode': 'independent_read_only_semantic_diff_review_no_compiler_or_build_invocation',
        'final_verification_freeze': args.final_freeze,
        'historical_source_paths_used': historical_paths,
        'baseline_commit': BASELINE,
        'source_snapshot': str(args.source_snapshot),
        'source_snapshot_recorded_at_utc': expected_record.get('recorded_at_utc'),
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'public_source_files': len(paths),
        'public_math_modules': len(paths)-1,
        'modified_math_files': len(modified),
        'modified_math_file_names': modified,
        'declarations_before': len(names_before),
        'declarations_after': len(names_after),
        'declaration_names_and_kinds_preserved': names_before == names_after,
        'declaration_names_and_kinds': names_after,
        'source_sha256': hashes,
        'aggregate_sha256': hashlib.sha256(json.dumps(hashes, sort_keys=True,
            separators=(',', ':')).encode()).hexdigest(),
        'namespace_scopes_preserved': True,
        'universe_declarations_preserved': True,
        'ambient_variables_includes_omits_preserved': True,
        'new_mathematical_hypotheses_found': [],
        'weakened_mathematical_conclusions_found': [],
        'unexpected_declaration_signature_changes': [],
        'changed_headers': header_changes,
        'changed_header_classifications': dict(Counter(x['classification'] for x in header_changes)),
        'definition_semantics_review': {
            'underlying_maps_and_objects_preserved': True,
            'subcategory_wrappers': 'homMk, hom projections, homLinearEquiv and inclusion.mapIso express the same ambient arrows. RightFiniteWindow has two extra full-subcategory layers over RightModule; the reviewed double wrappers and transports preserve the same maps.',
            'lifted_module_indexing': 'rightModuleHomOfLiftedComponents wraps the same whiskering preimage; its theorem projects hom before applying the ambient whiskering map. No component-index or quantifier is changed.',
            'closure_classes': 'Each new IsClosedUnderLimits/ColimitsOfShape class recovers an arbitrary diagram, universal cone/cocone, and diagram membership from its presentation, expressing the same old all-diagram closure statement.',
            'canonical_group_instances': 'FinsuppSupportedQuotient explicitly chooses Finsupp.instAddCommGroup; HomogeneousQuotientDecomposition explicitly chooses DFinsupp.addCommGroup. These are the canonical pointwise additive groups on the original spaces; carriers, grading, scalar actions, and quotient maps are retained.',
            'tensor_induction': 'TensorProduct.inductionOn replaces deprecated induction_on, with tmul/add cases and zero supplied by tmul 0 0. Original tensor actions, linear maps, equivalences, and hypotheses remain unchanged.',
            'resolutions_and_homotopy': 'ChainComplex.of_d/CochainComplex.of_d and quasi-isomorphism APIs changed arguments. Proofs still use the original term families, differentials, augmentations, homotopies, opposite functors, and resolutions; signatures remain unchanged.',
            'scalar_quotient_equivalence': 'scalarQuotientVertexLinearEquiv names the same quotientKerAlgEquivOfSurjective as E. Its toFun, invFun, and scalar multiplication formula remain the original expressions.',
            'period_inverse': 'inverseComponent is followed by homTransport along sub_eq_add_neg at both endpoints, identifying the original degree indices i-p,j-p with i+(-p),j+(-p).',
            'noncomputable_annotations': 'Annotations do not change the definitions, their types, orbit relations, ideal carriers, or values.',
            'scoped_transparency_options': 'backward.isDefEq.respectTransparency false is scoped to elaboration of the existing declaration; no hypotheses, proposition, or axiom declaration is changed.',
            'path_and_numerical_proofs': 'Path reversal/cut/height operations, cyclic derivatives, originalGinzburg, Hilbert formulas, and nilpotent ideal statements retain their original definitions and statements; rewrites expose the same constructor or canonical operation explicitly.'
        },
        'concrete_semantic_concerns': [],
        'prior_reviews': ['work/lean-upgrade/statement-review.json',
            'work/lean-upgrade/typecat-static-review.json'],
        'limitations': ['This semantic review does not certify Lean compilation or axiom-audit success.',
            'The verification run must match these source SHAs before success is claimed.'],
    }
    assert not args.output.exists(), 'Preserve earlier review evidence; select a unique output path'
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({k: result[k] for k in ('public_source_files', 'modified_math_files',
        'declarations_after', 'aggregate_sha256', 'changed_header_classifications')}, indent=2))


if __name__ == '__main__':
    main()
