#!/usr/bin/env bash
# Check that every Lean module in the package is reachable from the build surface.
#
# `lake build` compiles exactly the modules reachable from the default targets: each
# `lean_lib`'s glob roots plus everything they transitively import. A module outside that
# set is not elaborated at all — its `sorry`s, its axiom drift, even a failure to compile
# are invisible to CI while the build stays green. CI runs a plain `lake build`
# (leanprover/lean-action), so `defaultTargets` in `lakefile.toml` is the single spelling
# of the build surface and there is no CI-side target list to drift from it. This script
# asserts the end-to-end property: EVERY module file in the package is covered by some
# counted target, however the import graph shifts under future trims.
#
# The check mirrors Lake's own semantics (Lake.Glob, v4.30.0):
#   * `"A.B"`   selects exactly the module A.B;
#   * `"A.B.+"` selects all submodules of A.B (the files under A/B/), not A.B itself;
#   * `"A.B.*"` selects A.B and all submodules;
#   * a `lean_lib` with no `globs` field defaults to its root module (`Glob.one name`).
# The counted targets are `defaultTargets` plus the `FastFieldNative` lane: the lane is
# deliberately outside `defaultTargets` (precompilation over its import closure is
# expensive, so building it is opt-in), and its own invariants are enforced by
# `scripts/check_native_lane.sh` and `scripts/check_native_optin.py`.
#
# `find` rather than `git ls-files`: a not-yet-staged module is still checked. Run from
# the repository root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

# Top-level module files (the package roots, and any stray module someone adds
# beside them) are part of the universe too — hardcoding the known roots would
# leave a stray top-level module invisible to the check.
{ find CompElliptic MetaCheck -name '*.lean' -print
  find . -maxdepth 1 -name '*.lean' -print | sed 's|^\./||'; } | sort | awk '
  # The found files arrive on stdin as a LIST; they become awk input files via ARGV,
  # so FILENAME-based dispatch below sees each one. Lean module paths contain no
  # whitespace, so line-based reading is exact.
  BEGIN {
    nuniv = 0
    ARGV[ARGC++] = "lakefile.toml"
    while ((getline f < "/dev/stdin") > 0) ARGV[ARGC++] = f
    # The opt-in precompiled lane counts as a covered target; see the header.
    targets["FastFieldNative"] = 1
  }

  # ── lakefile.toml: defaultTargets and each [[lean_lib]] name/globs ──────────
  FILENAME == "lakefile.toml" {
    if ($0 ~ /^defaultTargets[ \t]*=/) {
      line = $0
      while (match(line, /"[^"]+"/)) {
        targets[substr(line, RSTART + 1, RLENGTH - 2)] = 1
        line = substr(line, RSTART + RLENGTH)
      }
    }
    if ($0 ~ /^\[\[lean_lib\]\]/) { inlib = 1; libname = ""; next }
    if ($0 ~ /^\[/) { inlib = 0; inglobs = 0; next }
    if (inlib && match($0, /^name[ \t]*=[ \t]*"[^"]+"/)) {
      line = $0; match(line, /"[^"]+"/)
      libname = substr(line, RSTART + 1, RLENGTH - 2)
      next
    }
    if (inlib && $0 ~ /^globs[ \t]*=/) inglobs = 1
    if (inlib && inglobs) {
      line = $0
      while (match(line, /"[^"]+"/)) {
        libglobs[libname] = libglobs[libname] " " substr(line, RSTART + 1, RLENGTH - 2)
        line = substr(line, RSTART + RLENGTH)
      }
      if ($0 ~ /\]/) inglobs = 0
    }
    next
  }

  # ── *.lean files: the module universe and its internal import edges ─────────
  # Imports are recorded only from the file HEADER (Lean permits them nowhere
  # else): edge scanning stops at the first line that is not blank, a comment,
  # `module`/`prelude`, or an import. Without this, an import-shaped line inside
  # a block comment or docstring would create a phantom edge — and a phantom
  # edge lets the guard pass for a module `lake build` never elaborates.
  {
    if (!(FILENAME in seen)) {
      seen[FILENAME] = 1
      mod = FILENAME
      sub(/\.lean$/, "", mod)
      gsub(/\//, ".", mod)
      univ[mod] = 1
      order[nuniv++] = mod
      filemod[mod] = FILENAME
      curmod = mod
      hdrdone = 0
      cdepth = 0
    }
    if (hdrdone) next
    line = $0
    if (cdepth > 0) {                     # inside a (possibly nested) block comment
      cdepth += gsub(/\/-/, "/-", line) - gsub(/-\//, "-/", line)
      next
    }
    if (line ~ /^[ \t]*$/) next           # blank
    if (line ~ /^[ \t]*--/) next          # line comment
    if (line ~ /^[ \t]*\/-/) {            # block comment or docstring opens
      cdepth += gsub(/\/-/, "/-", line) - gsub(/-\//, "-/", line)
      next
    }
    sub(/^public[ \t]+/, "", line)
    sub(/^meta[ \t]+/, "", line)
    if (line ~ /^import[ \t]+/) {
      split(line, parts, /[ \t]+/)
      adj[curmod] = adj[curmod] " " parts[2]
      next
    }
    if (line ~ /^(module|prelude)[ \t]*$/) next
    hdrdone = 1                           # first real command: the header is over
  }

  END {
    status = 0
    # Expand the counted targets globs into the BFS root set.
    for (lib in targets) {
      globs = (lib in libglobs) ? libglobs[lib] : lib
      n = split(globs, g, / +/)
      for (i = 1; i <= n; i++) {
        if (g[i] == "") continue
        hit = 0
        if (g[i] ~ /\.\+$/ || g[i] ~ /\.\*$/) {
          pre = substr(g[i], 1, length(g[i]) - 2)      # strip ".+" / ".*"
          withroot = (g[i] ~ /\.\*$/)
          for (j = 0; j < nuniv; j++) {
            m = order[j]
            if (index(m, pre ".") == 1 || (withroot && m == pre)) {
              queue[nq++] = m; hit = 1
            }
          }
        } else if (g[i] in univ) {
          queue[nq++] = g[i]; hit = 1
        }
        if (!hit) {
          printf "VIOLATION: target %s glob %s matches no module file\n", lib, g[i] > "/dev/stderr"
          status = 1
        }
      }
    }
    # BFS over the in-package import edges.
    for (q = 0; q < nq; q++) {
      m = queue[q]
      if (m in covered) continue
      covered[m] = 1
      n = split(adj[m], deps, / +/)
      for (i = 1; i <= n; i++)
        if (deps[i] in univ && !(deps[i] in covered))
          queue[nq++] = deps[i]
    }
    ncov = 0
    for (j = 0; j < nuniv; j++) {
      m = order[j]
      if (m in covered) { ncov++; continue }
      printf "VIOLATION: %s (%s) is not built by any counted target — add it to a lakefile glob or import it from a covered module\n", m, filemod[m] > "/dev/stderr"
      status = 1
    }
    if (status == 0)
      printf "build coverage: %d module(s), all covered by the counted targets.\n", ncov
    exit status
  }
'
