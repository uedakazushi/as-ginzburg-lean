#!/usr/bin/env python3
"""Inventory project declarations and generate an exhaustive public-declaration audit."""
import collections
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
entries = []
for source in sorted((root / "ASGinzburg").glob("*.lean")):
    scopes = []
    raw = source.read_text()
    uncommented = re.sub(r"/\-.*?\-/", "", raw, flags=re.S)
    uncommented = re.sub(r"--[^\n]*", "", uncommented)
    if re.search(r"\b(sorry|admit|axiom)\b", uncommented):
        raise SystemExit(f"Unchecked proof placeholder/declaration in {source}")
    for number, line in enumerate(raw.splitlines(), 1):
        line = line.strip()
        if match := re.match(r"(namespace|section)\s+([\w.]+)$", line):
            scopes.append((match.group(1), match.group(2)))
        elif re.match(r"end(?:\s+[\w.]+)?$", line):
            scopes.pop()
        elif match := re.match(
            r"(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
            r"(def|abbrev|theorem|lemma|structure|inductive)\s+([\w]+)", line
        ):
            kind, name = match.groups()
            entries.append({
                "name": ".".join([*(name for kind, name in scopes if kind == "namespace"), name]),
                "kind": kind,
                "file": str(source.relative_to(root)),
                "line": number,
            })
output = root / "verification"
output.mkdir(exist_ok=True)
(output / "declarations.json").write_text(json.dumps(entries, indent=2) + "\n")
(root / "AxiomAudit.lean").write_text(
    "import ASGinzburg\n\n" +
    "\n".join("#print axioms " + entry["name"] for entry in entries) + "\n"
)
print(json.dumps({"declarations": len(entries), "by_kind": dict(collections.Counter(
    entry["kind"] for entry in entries))}, indent=2))
