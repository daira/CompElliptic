#!/usr/bin/env python3
"""Check the design doc's references to the formalized supporting facts:
every declaration of CompElliptic/Hashing/WeilSupport.lean must be
referenced (backticked) somewhere in design/weil-constant-derivation.md,
and every backticked identifier in the doc (dot-qualified ones included)
must resolve to a declaration somewhere in CompElliptic or be a known
non-Lean term. Run from the repository root; exits non-zero on
violation."""
import pathlib
import re
import sys

# Backticked identifiers that are not Lean declarations (RFC and spec
# names, Sage identifiers, and similar).
ALLOWED_NON_LEAN = {
    'map_to_curve_simple_swu', 'hash_to_field',
}

DECL_RE = re.compile(
    r'^(?:noncomputable )?(?:def|theorem|abbrev|structure) '
    r'(?:_root_\.)?([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)',
    re.M)

root = pathlib.Path(__file__).resolve().parent.parent
support = set(DECL_RE.findall(
    (root / 'CompElliptic/Hashing/WeilSupport.lean').read_text()))
everywhere = set()
for f in (root / 'CompElliptic').rglob('*.lean'):
    everywhere |= set(DECL_RE.findall(f.read_text()))

doc = (root / 'design/weil-constant-derivation.md').read_text()
listed = set(re.findall(
    r'`([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)`', doc))
# Backticked filenames (`BranchCovers.lean`, `weilbound.sage`) are file
# references, not declarations.
listed = {name for name in listed
          if not re.search(r'\.(lean|sage|py|md|toml|yml|sh)$', name)}


def last(name: str) -> str:
    """The final dot-separated segment of a (possibly qualified) name."""
    return name.rsplit('.', 1)[-1]


# Declarations are spelled bare inside namespace blocks or dot-qualified at
# top level; references may use either form. Compare by final segment.
declared_last = {last(name) for name in everywhere}
missing = sorted({last(name) for name in support}
                 - {last(name) for name in listed})
unknown = sorted(name for name in listed
                 if last(name) not in declared_last
                 and name not in ALLOWED_NON_LEAN)
if missing:
    print("declared in WeilSupport.lean but not referenced in the doc:",
          *missing, sep='\n  ')
if unknown:
    print("backticked in the doc but not a CompElliptic declaration"
          " (add to ALLOWED_NON_LEAN if intentional):",
          *unknown, sep='\n  ')
sys.exit(1 if (missing or unknown) else 0)
