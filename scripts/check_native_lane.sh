#!/usr/bin/env bash
# Check the core-only invariant of the `FastFieldNative` precompiled lane.
#
# `precompileModules` runs native codegen over the lane's entire import closure. As long as every
# module in the lane imports nothing outside Lean core, that closure is a handful of files. The
# moment one of them imports something mathlib-side, codegen tries to natively compile a mathlib
# closure -- which does not fail loudly, it just makes the build enormous (and can OOM the
# machine). This script turns that silent failure into a loud one.
#
# Run from the repository root. Exits non-zero on violation.
set -euo pipefail

cd "$(dirname "$0")/.."

# The lane, mirroring the `FastFieldNative` globs in lakefile.lean.
LANE=(
  "FastFieldNative.lean"
  "CompElliptic/Vendor/CompPoly/Montgomery/Native64x8Defs.lean"
  "CompElliptic/Curves/Pasta/Fast/NatKernel.lean"
  "CompElliptic/Curves/Pasta/Fast/ProjectiveMontDefs.lean"
)

# `FastFieldNative.lean` is the root module; it may import the rest of the lane and nothing else.
status=0
for f in "${LANE[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "MISSING: $f is listed in the lane but does not exist" >&2
    status=1
    continue
  fi
  while read -r _ mod _; do
    [[ -z "${mod:-}" ]] && continue
    path="${mod//.//}.lean"
    for allowed in "${LANE[@]}"; do
      if [[ "$path" == "$allowed" ]]; then
        continue 2
      fi
    done
    echo "VIOLATION: $f imports $mod, which is outside the core-only lane" >&2
    status=1
  done < <(grep -E '^import ' "$f" || true)
done

if [[ $status -eq 0 ]]; then
  echo "FastFieldNative lane is core-only (${#LANE[@]} modules)."
fi
exit $status
