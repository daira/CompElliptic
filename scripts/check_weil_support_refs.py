#!/usr/bin/env python3
"""Check the design doc's references to the formalized facts, in three
directions: every declaration of CompElliptic/Hashing/WeilSupport.lean
must be referenced (backticked) somewhere in
design/weil-constant-derivation.md; every backticked identifier in the
doc (dot-qualified ones included) must be a dot-path suffix of the
fully qualified name of a declaration somewhere in CompElliptic, or be
a known non-Lean term; and every referenced declaration must be named
directly in an `assert_axioms` or `assert_computable` entry of
CompElliptic/TrustBoundary.lean. The doc is a pencil-and-paper proof
whose reader relies on everything it cites, so an unpinned citation
would be a gap in axiom-checking. Run from the repository root; exits
non-zero on violation."""
import pathlib
import re
import sys

# Backticked identifiers that are not Lean declarations (RFC and spec
# names, Sage identifiers, and similar).
ALLOWED_NON_LEAN = {
    'map_to_curve_simple_swu', 'hash_to_field',
}

DECL_RE = re.compile(
    r'^(private +|protected +)?(?:noncomputable +|partial +|unsafe +)?'
    r'(?:theorem|lemma|def|abbrev|instance|axiom|opaque|inductive'
    r'|structure|class) '
    r"(_root_\.)?([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)")
NS_RE = re.compile(r"^namespace +([A-Za-z_][A-Za-z0-9_.']*)")
END_RE = re.compile(r"^end +([A-Za-z_][A-Za-z0-9_.']*)")


def declared_names(path: pathlib.Path) -> set:
    """The fully qualified names declared in a Lean file. The enclosing
    namespace is reconstructed from the `namespace`/`end` pairs above each
    declaration — `end <id>` pops only a matching innermost `namespace`, so
    a named `section ... end` cannot corrupt the stack — the same
    reconstruction as ironwood's `scripts/check_endpoint_census.sh`. A
    `_root_.` prefix ignores the enclosing namespace; a `private`
    declaration is not citable, so it is not collected."""
    names = set()
    stack = []
    for line in path.read_text().splitlines():
        m = NS_RE.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = END_RE.match(line)
        if m:
            if stack and stack[-1] == m.group(1):
                stack.pop()
            continue
        m = DECL_RE.match(line)
        if m and not (m.group(1) or '').startswith('private'):
            names.add(m.group(3) if m.group(2) or not stack
                      else '.'.join(stack) + '.' + m.group(3))
    return names


def is_path_suffix(name: str, full: str) -> bool:
    """Whether `name` is a dot-path suffix of `full`, on segment
    boundaries."""
    return full == name or full.endswith('.' + name)


root = pathlib.Path(__file__).resolve().parent.parent
support = declared_names(root / 'CompElliptic/Hashing/WeilSupport.lean')
everywhere = set()
for f in (root / 'CompElliptic').rglob('*.lean'):
    everywhere |= declared_names(f)

doc = (root / 'design/weil-constant-derivation.md').read_text()
listed = set(re.findall(
    r'`([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)`', doc))
# Backticked filenames (`BranchCovers.lean`, `weilbound.sage`) are file
# references, not declarations.
listed = {name for name in listed
          if not re.search(r'\.(lean|sage|py|md|toml|yml|sh)$', name)}

# A citation resolves when it is a dot-path suffix of some declaration's
# fully qualified name. Final-segment matching alone would let a bogus
# `junk.last` resolve against any declaration ending in `last`.
missing = sorted(full for full in support
                 if not any(is_path_suffix(name, full) for name in listed))
unknown = sorted(name for name in listed
                 if name not in ALLOWED_NON_LEAN
                 and not any(is_path_suffix(name, full) for full in everywhere))

# Census entries are written fully qualified, so a reference is pinned when
# some entry's name ends with it at a segment boundary. An ambiguous short
# reference (`mapToCurve`) is satisfied by any of its instantiations; the
# census pins all of them.
pins = set(re.findall(
    r'^assert_(?:axioms|computable) +(?:_root_\.)?'
    r'([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)',
    (root / 'CompElliptic/TrustBoundary.lean').read_text(), re.M))
unpinned = sorted(name for name in listed
                  if name not in ALLOWED_NON_LEAN and name not in unknown
                  and not any(is_path_suffix(name, p) for p in pins))
if missing:
    print("declared in WeilSupport.lean but not referenced in the doc:",
          *missing, sep='\n  ')
if unknown:
    print("backticked in the doc but not a CompElliptic declaration"
          " (add to ALLOWED_NON_LEAN if intentional):",
          *unknown, sep='\n  ')
if unpinned:
    print("referenced in the doc but not pinned in the axiom census"
          " (CompElliptic/TrustBoundary.lean):",
          *unpinned, sep='\n  ')
sys.exit(1 if (missing or unknown or unpinned) else 0)
