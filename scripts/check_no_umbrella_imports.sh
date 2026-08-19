#!/usr/bin/env bash
# Check that no Lean file imports the Mathlib umbrella modules.
#
# `import Mathlib` pulls in all of Mathlib, and `import Mathlib.Tactic` is the same
# failure mode at smaller scale: each transitively loads a large slice of Mathlib's
# theory into every Lean process that elaborates the file (measured in zcash/ironwood
# at roughly 6.5 GB RSS for the full umbrella and +1.3 GB RSS / +1.6 s import-load
# time for `Mathlib.Tactic`, against the narrow modules a file actually needs).
# During a parallel Lake build several such processes create severe memory and GC
# pressure. Nothing fails when an umbrella import creeps in — builds just quietly
# get slow — so the absence has to be enforced mechanically.
#
# The rule: no tracked `.lean` file may contain a bare `import Mathlib` or a bare
# `import Mathlib.Tactic` (with or without a trailing comment). Specific submodule
# imports such as `import Mathlib.Tactic.Ring` are fine. If an umbrella import is
# ever legitimately needed, extend this script with an explicit allowlist rather
# than deleting the check.
#
# Run from the repository root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

# One-or-more whitespace after `import` (not exactly one space), and optional
# `public`/`meta` modifiers, so spacing variants and module-system prefixes
# cannot slip a banned umbrella past the anchor.
violations=$(git ls-files '*.lean' | xargs grep -nE '^(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+Mathlib(\.Tactic)?([[:space:]]|$)' || true)

if [ -n "$violations" ]; then
  echo "::error::bare 'import Mathlib' / 'import Mathlib.Tactic' umbrella imports are not allowed; import the specific Mathlib modules instead (see scripts/check_no_umbrella_imports.sh):"
  echo "$violations"
  exit 1
fi
echo "umbrella imports: none."
