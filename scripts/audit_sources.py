#!/usr/bin/env python3
"""Inventory explicit declarations; reject duplicate or unsupported declarations."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
IDENT = r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*"
DECL = re.compile(rf"(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?"
                  rf"(def|abbrev|theorem|lemma|structure|inductive|instance)\s+({IDENT})(?=\s|[:(\[{{]|$)")


def mask_comments(text):
    """Mask nested Lean comments and strings, preserving lines and columns."""
    result = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                result[i:i+2] = '  '
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                result[i:i+2] = '  '
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    result[i] = ' '
                i += 1
        elif string:
            result[i] = '\n' if text[i] == '\n' else ' '
            if text[i] == '\\' and i + 1 < len(text):
                result[i+1] = ' '
                i += 2
            else:
                string = text[i] != '"'
                i += 1
        elif text.startswith('/-', i):
            result[i:i+2] = '  '
            depth, i = 1, i + 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end == -1 else end
            result[i:end] = ' ' * (end - i)
            i = end
        elif text[i] == '"':
            result[i] = ' '
            string, i = True, i + 1
        else:
            i += 1
    if depth or string:
        raise ValueError('Unterminated comment or string')
    return ''.join(result)


def project_sources(root):
    return [root / 'ASGinzburg.lean', *sorted((root / 'ASGinzburg').rglob('*.lean'))]


def require_unique(names, label):
    duplicates = {n: c for n, c in Counter(names).items() if c > 1}
    if duplicates:
        raise ValueError(f'Duplicate {label}: {duplicates}')


def inventory(root=ROOT):
    entries = []
    for source in project_sources(root):
        clean = mask_comments(source.read_text())
        if re.search(r'\b(sorry|admit|axiom)\b', clean):
            raise ValueError(f'Unchecked proof placeholder/declaration in {source}')
        scopes = []
        for number, raw_line in enumerate(clean.splitlines(), 1):
            line = raw_line.strip()
            if match := re.fullmatch(rf'(namespace|section)(?:\s+({IDENT}))?', line):
                scopes.append(match.groups())
            elif re.fullmatch(r'noncomputable\s+section', line):
                scopes.append(('section', None))
            elif re.fullmatch(rf'end(?:\s+{IDENT})?', line):
                if not scopes:
                    raise ValueError(f'Unbalanced end at {source}:{number}')
                scopes.pop()
            elif match := DECL.match(line):
                kind, name = match.groups()
                entries.append({'name': '.'.join([*(n for k, n in scopes if k == 'namespace'), name]),
                                'kind': kind, 'file': str(source.relative_to(root)), 'line': number})
            elif not line.startswith('attribute ') and re.search(r'\b(def|abbrev|theorem|lemma|structure|inductive|instance|opaque)\b', line):
                raise ValueError(f'Unsupported declaration syntax at {source}:{number}: {line}')
        if scopes:
            raise ValueError(f'Unclosed namespace/section in {source}')
    require_unique([e['name'] for e in entries], 'source declaration names')
    if not entries:
        raise ValueError('No project declarations inventoried')
    return entries


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'verification')
    args = parser.parse_args()
    entries = inventory()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / 'declarations.json').write_text(json.dumps(entries, indent=2) + '\n')
    (ROOT / 'AxiomAudit.lean').write_text('import ASGinzburg\n\n' +
        '\n'.join('#print axioms ' + e['name'] for e in entries) + '\n')
    print(json.dumps({'declarations': len(entries), 'unique_names': len(set(e['name'] for e in entries)),
                      'definitions_theorems_and_types': sum(e['kind'] != 'instance' for e in entries),
                      'by_kind': dict(Counter(e['kind'] for e in entries))}, indent=2))


if __name__ == '__main__':
    main()
