#!/usr/bin/env bash
set -euo pipefail
project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if [ -n "${AS_GINZBURG_LEAN_ROOT:-}" ]; then
  export PATH="$AS_GINZBURG_LEAN_ROOT/bin:$PATH"
fi
if [ "${AS_GINZBURG_PROC_SELF_FIX:-0}" = 1 ]; then
  shim="$project_dir/.lake/proc_self.so"
  if [ ! -f "$shim" ]; then
    mkdir -p "$project_dir/.lake"
    cc -shared -fPIC -o "$shim" "$project_dir/scripts/proc_self.c" -ldl
  fi
  export LD_PRELOAD="$shim${LD_PRELOAD:+:$LD_PRELOAD}"
  export TAR_OPTIONS="--no-same-owner${TAR_OPTIONS:+ $TAR_OPTIONS}"
fi
exec "$@"
