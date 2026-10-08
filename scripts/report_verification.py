#!/usr/bin/env python3
"""Certify this run's exit codes, exact coverage, source hashes and allowed axioms."""
import argparse
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
from audit_sources import ROOT, inventory, project_sources, require_unique

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TOOLCHAIN = 'leanprover/lean4:v4.24.0'
MATHLIB = 'f897ebcf72cd16f89ab4577d0c826cd14afaafc7'
RECORD = re.compile(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", re.M)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def check_coverage(entries, text):
    expected = [e['name'] for e in entries]
    require_unique(expected, 'inventory names')
    names, axioms = [], set()
    # Lean pretty-printing wraps long declarations' axiom lists across lines.
    # Parse complete records, but reject all intervening non-whitespace output.
    cursor = 0
    for match in RECORD.finditer(text):
        if text[cursor:match.start()].strip():
            raise ValueError(f'Unexpected axiom audit output: {text[cursor:match.start()]}')
        names.append(match[1])
        axioms.update(n.strip() for n in (match[2] or '').split(',') if n.strip())
        cursor = match.end()
    if text[cursor:].strip():
        raise ValueError(f'Unexpected axiom audit output: {text[cursor:]}')
    require_unique(names, 'axiom log names')
    if Counter(names) != Counter(expected):
        raise ValueError(f'Audit coverage mismatch; missing={sorted(set(expected)-set(names))}; '
                         f'extra={sorted(set(names)-set(expected))}')
    if axioms - ALLOWED:
        raise ValueError(f'Unaccepted axiom dependencies: {sorted(axioms - ALLOWED)}')
    return names, axioms


def certify(run_dir, root=ROOT):
    run = json.loads((run_dir / 'run.json').read_text())
    if run['run_id'] != run_dir.name or run['status'] != 'running':
        raise ValueError('Report requires the active run, not a previous certificate')
    for stage in ('regression_tests', 'source_audit', 'environment', 'build', 'axioms'):
        step = next(s for s in run['steps'] if s['stage'] == stage)
        if step['exit_code'] != 0 or not step.get('ended_at_utc'):
            raise ValueError(f'Current run stage failed/incomplete: {stage}')
        if digest(run_dir / step['log']) != step['log_sha256']:
            raise ValueError(f'Current run log changed: {stage}')
    entries = json.loads((run_dir / 'declarations.json').read_text())
    if entries != inventory(root):
        raise ValueError('Inventory differs from current source declarations')
    commands = re.findall(r'^#print axioms (\S+)$', (root / 'AxiomAudit.lean').read_text(), re.M)
    require_unique(commands, 'audit command names')
    if Counter(commands) != Counter(e['name'] for e in entries):
        raise ValueError('AxiomAudit commands differ from current inventory')
    hashes = {str(p.relative_to(root)): digest(p) for p in [*project_sources(root), root / 'AxiomAudit.lean']}
    if hashes != run['lean_source_sha256']:
        raise ValueError('Sources changed during verification')
    environment = json.loads((run_dir / 'environment.json').read_text())
    if environment['lean_toolchain'] != TOOLCHAIN or environment['mathlib_revision'] != MATHLIB:
        raise ValueError('Pinned environment mismatch')
    names, axioms = check_coverage(entries, (run_dir / 'axioms.log').read_text())
    return {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'run_id': run['run_id'],
            'lean_toolchain': TOOLCHAIN, 'mathlib_revision': MATHLIB,
            'module_count': len(hashes) - 2, 'declaration_count': len(entries),
            'unique_declaration_count': len(names), 'declaration_kinds': dict(Counter(e['kind'] for e in entries)),
            'definitions_theorems_and_types': sum(e['kind'] != 'instance' for e in entries),
            'theorem_count': sum(e['kind'] in ('theorem', 'lemma') for e in entries),
            'missing_theorems': [], 'kernel_axiom_dependencies': sorted(axioms),
            'build_success': True, 'unchecked_proof_dependencies': [], 'source_placeholders': [],
            'main_theorem_proved': False, 'main_theorem_formal_statement_implemented': False,
            'source_paper_sha256': digest(root / 'docs/source.pdf'), 'lean_source_sha256': hashes}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run-dir', type=Path, required=True)
    args = parser.parse_args()
    result = certify(args.run_dir.resolve())
    (args.run_dir / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f"Kernel axiom audit passed for {result['declaration_count']} distinct declarations "
          f"including all {result['theorem_count']} theorems; main results remain incomplete.")


if __name__ == '__main__':
    main()
