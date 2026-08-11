#!/usr/bin/env bash
# Re-check the built library with nanoda, an independent reimplementation of the Lean
# kernel in Rust (https://github.com/ammkrn/nanoda_lib). The point is kernel-level
# defence in depth: a proof of False exploiting a kernel soundness bug would also have
# to get past a second, independently implemented checker (cf. the postmortem of
# lean4#14576, which recommends exactly this).
#
# Usage: scripts/check_nanoda.sh <lean4export-binary> <nanoda-binary>
# The library must already be built (`lake build`). Set LAKE to choose the lake that
# provides the export environment (default: `lake` from PATH).
#
# scripts/nanoda-config.json is the machine-checked axiom census: nanoda's strict mode
# fails on any axiom declared outside its `permitted_axioms`, and `pp_declars` fails if
# an expected native_decide axiom disappears from the export. In between,
# scripts/check_export_axioms.py closes the remaining gap: axioms that must be
# permitted because Lean core declares them unconditionally, but must remain unused
# (`sorryAx` in particular) are checked to be cited by nothing.
set -euo pipefail

LEAN4EXPORT=${1:?usage: check_nanoda.sh <lean4export-binary> <nanoda-binary>}
NANODA=${2:?usage: check_nanoda.sh <lean4export-binary> <nanoda-binary>}
LAKE=${LAKE:-lake}

# The export roots. Every module of the package must be reachable from these (checked
# below), so a module cannot silently drop out of the re-check. MetaCheck is
# deliberately absent: it is not part of the production library, and its forged axioms
# exist to be rejected.
ROOTS=(CompElliptic CompElliptic.Fields.Jubjub FastFieldNative)

python3 - "${ROOTS[@]}" <<'EOF'
import re, sys
from pathlib import Path
roots = sys.argv[1:]
files = [Path("CompElliptic.lean"), Path("FastFieldNative.lean")]
files += sorted(Path("CompElliptic").rglob("*.lean"))
mod = lambda p: ".".join(p.with_suffix("").parts)
imports = {mod(f): set(re.findall(r"^import\s+([A-Za-z0-9_.]+)", f.read_text(), re.M))
           for f in files}
reachable, todo = set(), list(roots)
while todo:
    m = todo.pop()
    if m in reachable or m not in imports:
        continue
    reachable.add(m)
    todo.extend(imports[m])
missing = sorted(set(imports) - reachable)
if missing:
    print("VIOLATION: module(s) outside the export roots' import closure:",
          file=sys.stderr)
    for m in missing:
        print(f"  {m}", file=sys.stderr)
    sys.exit(1)
print(f"export coverage: all {len(imports)} project modules reachable from the roots")
EOF

mkdir -p work
"$LAKE" env "$LEAN4EXPORT" "${ROOTS[@]}" > work/compelliptic-export.ndjson
python3 scripts/check_export_axioms.py scripts/nanoda-config.json
"$NANODA" scripts/nanoda-config.json
