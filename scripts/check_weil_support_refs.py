#!/usr/bin/env python3
"""Check the design doc's references to the formalized facts: every
declaration of CompElliptic/Hashing/WeilSupport.lean must be referenced
(backticked) somewhere in design/weil-constant-derivation.md, and every
backticked identifier in the doc (dot-qualified ones included) must
resolve to a declaration — its exact fully qualified name anywhere in
CompElliptic, or a dot-path suffix of one under the relevant modules
(CompElliptic.{Hashing,Curves}). A citation that also matches a name
outside the relevant modules must qualify itself. Every declaration a
citation can refer to must be named directly in an `assert_axioms` or
`assert_computable` entry of CompElliptic/TrustBoundary.lean: the doc
is a pencil-and-paper proof whose reader relies on everything it cites,
so an unpinned citation would be a gap in axiom-checking. Declared Lean
names that could be mistaken for a filename or an allowlisted non-Lean
term are rejected outright, so the citation filters cannot silently
mask a real declaration. Run from the repository root; exits non-zero
on violation."""
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
FILENAME_RE = re.compile(r"\.(lean|sage|py|md|toml|yml|sh)$")


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
relevant = {full for full in everywhere
            if full.startswith('CompElliptic.Hashing.')
            or full.startswith('CompElliptic.Curves.')}
confusable = {full for full in everywhere
              if any(is_path_suffix(name, full) for name in ALLOWED_NON_LEAN)
              or FILENAME_RE.search(full)}

doc = (root / 'design/weil-constant-derivation.md').read_text()
listed = set(re.findall(
    r'`([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)`', doc))
# Backticked filenames (`BranchCovers.lean`, `weilbound.sage`) are file
# references, not declarations.
listed = {name for name in listed
          if name not in ALLOWED_NON_LEAN
          and not FILENAME_RE.search(name)}

# A citation resolves when it either matches the fully qualified name
# exactly, or it is a dot-path suffix of the fully qualified name of
# some declaration under a "relevant" module (see above). Final-segment
# matching alone would let a bogus `junk.last` resolve against any
# declaration ending in `last`. Allowing matches in any module would
# incur a greater risk of typos accidentally matching unrelated names.
missing = {full for full in support
           if not any(is_path_suffix(name, full) for name in listed)}
unknown = {name for name in listed
           if name not in everywhere    # exact match
           and not any(is_path_suffix(name, full) for full in relevant)}

# There should not be any non-fully-qualified references that match names
# outside the relevant modules. An unknown citation selects no referents:
# its remedy is fixing the citation, so it must not also demand
# qualification or pins here and below.
irrelevant = {full for full in everywhere
              if full not in relevant
              and any(name not in unknown
                      and name != full and is_path_suffix(name, full)
                      for name in listed)}

# Census entries are written fully qualified, so a reference is pinned when
# *every* declaration of which it is a dot-path suffix is included in the
# census. So an ambiguous short reference (e.g. `mapToCurve`) requires all
# of its potential referents to be pinned. Cases already reported as
# "irrelevant" matches are excluded.
pins = set(re.findall(
    r'^assert_(?:axioms|computable) +(?:_root_\.)?'
    r'([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)',
    (root / 'CompElliptic/TrustBoundary.lean').read_text(), re.M))
unpinned = {full for full in everywhere
            if full not in pins and full not in irrelevant
            and any(name not in unknown and is_path_suffix(name, full)
                    for name in listed)}

if missing:
    print("declared in WeilSupport.lean but not referenced in the doc:",
          *sorted(missing), sep='\n  ')
if unknown:
    print("backticked in the doc but not found as a relevant or fully qualified"
          " declaration (add to ALLOWED_NON_LEAN if intentional):",
          *sorted(unknown), sep='\n  ')
if irrelevant:
    print("referenced in the doc but matches a name outside the relevant modules"
          " (qualify to avoid ambiguity):",
          *sorted(irrelevant), sep='\n  ')
if unpinned:
    print("referenced in the doc but not pinned in the axiom census"
          " (CompElliptic/TrustBoundary.lean):",
          *sorted(unpinned), sep='\n  ')
if confusable:
    print("declared Lean name that looks like a filename or a name in"
          " the ALLOWED_NON_LEAN list:",
          *sorted(confusable), sep='\n  ')

sys.exit(1 if (missing or unknown or irrelevant or unpinned or confusable) else 0)
