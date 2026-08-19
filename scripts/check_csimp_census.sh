#!/usr/bin/env bash
# Check that every `@[csimp]` declaration in the library is covered by an
# `assert_axioms` entry in some census file. The compiler applies a
# csimp substitution in all downstream compiled code, but the axioms of the lemma's
# own proof are not propagated into downstream `native_decide` axiom tracking (
# lean4#7463), so a csimp lemma whose axioms go unchecked would be an
# axiom-smuggling channel.
#
# Robustness: every line containing "csimp" is scanned. Documentation must quote
# mentions as exactly `@[csimp]` (backtick-quoted); that exact string is removed
# before testing, so any remaining attribute syntax (`@[..., csimp, ...]` or
# `attribute [csimp] name`) is treated as real and must name its declaration on
# the same line. An `attribute` command may list several targets; every one is
# checked, and an unparsable target fails rather than being skipped. The same-line
# rule is load-bearing: a target continued onto the next line is invisible to a
# line scanner. Matching against the census is by the declaration's final name
# component.
#
# Scope: this guards against accidental omissions, NOT adversarial code. Run from
# the repository root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

# Every "csimp" line in the library (the census file itself included: a csimp
# declared there is enforced like any other, and its comments follow the same
# quoting rule). `MetaCheck/` is excluded: it holds forged declarations that
# exercise the rejection paths of the census macros themselves; censusing those
# would assert the very axiom set a fixture exists to be rejected for.
matches=$(find CompElliptic CompElliptic.lean FastFieldNative.lean -name '*.lean' -print0 \
  | xargs -0 grep -n "csimp" /dev/null || true)

# Census entries that actually run, by final name component. Any census file
# counts, not just CompElliptic/TrustBoundary.lean: a lemma is pinned wherever
# its entry sits.
#
# Widening the search to those files means excluding `#guard_msgs`-wrapped
# entries, which assert that a census entry *fails* and so are the opposite of
# coverage. They sit at column 0 like real entries -- the wrapper is the
# preceding line -- and the rejection fixtures are full of them, so an
# expected-to-fail entry would otherwise satisfy this check.
censused=$(find CompElliptic MetaCheck -name "*.lean" -print0 | xargs -0 awk '
  FNR == 1 { prev = "" }
  /^assert_axioms / && prev !~ /^#guard_msgs/ { sub(/.*\./, "", $2); print $2 }
  { prev = $0 }
')

status=0
count=0
while IFS=: read -r file lineno line; do
  [[ -z "$file" ]] && continue
  stripped=${line//'`@[csimp]`'/}
  if ! printf '%s' "$stripped" | grep -qE '@\[[^]]*\bcsimp\b|attribute[[:space:]]*\[[^]]*\bcsimp\b'; then
    continue  # only quoted documentation mentions on this line
  fi
  names=$(printf '%s' "$stripped" | sed -nE "s/.*(theorem|def)[[:space:]]+([A-Za-z0-9_'.]+).*/\2/p")
  if [[ -z "$names" ]]; then
    # `attribute [csimp] a b …` applies the attribute to every listed target: collect the whole
    # target list, and fail on any token the identifier grammar does not cover rather than
    # silently checking a prefix of the command.
    targets=$(printf '%s' "$stripped" \
      | sed -nE "s/.*attribute[[:space:]]*\[[^]]*csimp[^]]*\][[:space:]]+(.*)$/\1/p" \
      | sed -E 's/--.*$//')
    ident_re="^[A-Za-z0-9_'.]+$"
    for target in $targets; do
      if [[ "$target" =~ $ident_re ]]; then
        names="$names $target"
      else
        echo "VIOLATION: $file:$lineno: unparsable csimp attribute target '$target'" >&2
        status=1
      fi
    done
  fi
  if [[ -z "${names// /}" ]]; then
    echo "VIOLATION: $file:$lineno: csimp attribute syntax must name its declaration on the same line (write \`@[csimp] theorem <name>\`), and documentation mentions must be quoted as exactly \`@[csimp]\`" >&2
    status=1
    continue
  fi
  for name in $names; do
    count=$((count + 1))
    # Herestring rather than a pipe: `grep -q` exits at the first match, which under `pipefail`
    # would make a *successful* lookup fail the pipeline on the writer's SIGPIPE.
    if ! grep -qxF "${name##*.}" <<< "$censused"; then
      echo "VIOLATION: csimp declaration ${name} ($file:$lineno) has no assert_axioms entry in any census file" >&2
      status=1
    fi
  done
done <<< "$matches"

if [[ $status -eq 0 ]]; then
  echo "csimp census: ${count} csimp declaration(s), all covered."
fi
exit $status
