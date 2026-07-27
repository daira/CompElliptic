#!/usr/bin/env bash
# Check that every `@[csimp]` declaration in the library is covered by an
# `assert_axioms` entry in CompElliptic/TrustBoundary.lean. The compiler applies a
# csimp substitution in all downstream compiled code, but the axioms of the lemma's
# own proof are not propagated into downstream `native_decide` axiom tracking (open
# lean4#7463), so a csimp lemma whose axioms go unchecked would be an
# axiom-smuggling channel.
#
# Robustness: every line containing "csimp" is scanned; backtick-quoted spans are
# stripped first, so documentation must quote mentions as `@[csimp]` — an unquoted
# occurrence of attribute syntax (`@[..., csimp, ...]` or `attribute [csimp] name`)
# is treated as real, and must name its declaration on the same line. Matching
# against the census is by the declaration's final name component.
#
# Scope: this guards against accidental omissions, NOT adversarial code. The
# backtick pairing is line-local and heuristic — one can imagine crafted input
# where a span the line-local pairing takes as quoted actually contains live
# attribute syntax. Robustness against that would need a real parser (or a
# Lean-side enumeration of the attribute extension), which is not attempted here;
# code in this repository is reviewed, not adversarial. Run from the repository
# root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

status=0
count=0
while IFS=: read -r file lineno line; do
  stripped=$(printf '%s' "$line" | sed 's/`[^`]*`//g')
  if ! printf '%s' "$stripped" | grep -qE '@\[[^]]*\bcsimp\b|attribute[[:space:]]*\[[^]]*\bcsimp\b'; then
    continue  # only backtick-quoted documentation mentions on this line
  fi
  name=$(printf '%s' "$stripped" | sed -nE "s/.*(theorem|def)[[:space:]]+([A-Za-z0-9_'.]+).*/\2/p")
  if [[ -z "$name" ]]; then
    name=$(printf '%s' "$stripped" | sed -nE "s/.*attribute[[:space:]]*\[[^]]*csimp[^]]*\][[:space:]]+([A-Za-z0-9_'.]+).*/\1/p")
  fi
  if [[ -z "$name" ]]; then
    echo "VIOLATION: $file:$lineno: csimp attribute syntax must name its declaration on the same line (write \`@[csimp] theorem <name>\`), and documentation mentions must be backtick-quoted" >&2
    status=1
    continue
  fi
  count=$((count + 1))
  if ! grep -qE "^assert_axioms .*\.${name}( |\$)|^assert_axioms ${name}( |\$)" CompElliptic/TrustBoundary.lean; then
    echo "VIOLATION: csimp declaration ${name} ($file:$lineno) has no assert_axioms entry in CompElliptic/TrustBoundary.lean" >&2
    status=1
  fi
done < <(grep -rn "csimp" CompElliptic/ --include="*.lean" | grep -v "^CompElliptic/TrustBoundary.lean")

if [[ $status -eq 0 ]]; then
  echo "csimp census: ${count} csimp declaration(s), all covered."
fi
exit $status
