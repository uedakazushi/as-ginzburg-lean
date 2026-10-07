#!/usr/bin/env python3
"""Check every recorded axiom dependency and write a scoped verification certificate."""
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
entries = json.loads((root / "verification/declarations.json").read_text())
audit = (root / "verification/axioms.log").read_text()
names = re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", audit)
expected = [entry["name"] for entry in entries]
if set(names) != set(expected) or len(names) != len(expected):
    raise SystemExit("Axiom audit did not cover every inventoried declaration exactly once")
axioms = set()
for line in audit.splitlines():
    if match := re.search(r"depends on axioms: \[([^]]*)\]", line):
        axioms.update(filter(None, (name.strip() for name in match.group(1).split(","))))
allowed = {"propext", "Classical.choice", "Quot.sound"}
if axioms - allowed:
    raise SystemExit(f"Unaccepted axiom dependencies: {sorted(axioms - allowed)}")
build = (root / "verification/build.log").read_text()
if "Build completed successfully" not in build:
    raise SystemExit("No successful build recorded")
manifest = json.loads((root / "lake-manifest.json").read_text())
mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
sources = [root / "ASGinzburg.lean", root / "AxiomAudit.lean",
           *sorted((root / "ASGinzburg").glob("*.lean"))]
result = {
    "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
    "mathlib_revision": mathlib["rev"],
    "module_count": len(list((root / "ASGinzburg").glob("*.lean"))),
    "declaration_count": len(entries),
    "declaration_kinds": dict(Counter(entry["kind"] for entry in entries)),
    "kernel_axiom_dependencies": sorted(axioms),
    "build_success": True,
    "unchecked_proof_dependencies": [],
    "main_theorem_proved": False,
    "main_theorem_formal_statement_implemented": False,
    "source_paper_sha256": sha256((root / "docs/source.pdf").read_bytes()).hexdigest(),
    "lean_source_sha256": {str(path.relative_to(root)): sha256(path.read_bytes()).hexdigest()
                           for path in sources},
}
(root / "verification/results.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"Kernel axiom audit passed for {len(names)} declarations; main theorem remains incomplete.")
