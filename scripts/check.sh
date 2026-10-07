#!/usr/bin/env bash
set -euo pipefail
project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$project_dir"
python3 scripts/audit_sources.py
scripts/with_lean.sh lake build 2>&1 | tee verification/build.log
scripts/with_lean.sh lake env lean AxiomAudit.lean > verification/axioms.log
python3 scripts/report_verification.py
