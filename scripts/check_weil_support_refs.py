#!/usr/bin/env python3
"""Check the design doc's references to the formalized supporting facts:
every declaration of CompElliptic/Hashing/WeilSupport.lean must be
referenced (backticked) somewhere in design/weil-constant-derivation.md,
and every backticked identifier in the doc must resolve to a declaration
somewhere in CompElliptic or be a known non-Lean term. Run from the
repository root; exits non-zero on violation."""
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
    r'(?:_root_\.(?:[A-Za-z_][A-Za-z0-9_]*\.)*)?([A-Za-z_][A-Za-z0-9_]*)',
    re.M)

root = pathlib.Path(__file__).resolve().parent.parent
support = set(DECL_RE.findall(
    (root / 'CompElliptic/Hashing/WeilSupport.lean').read_text()))
everywhere = set()
for f in (root / 'CompElliptic').rglob('*.lean'):
    everywhere |= set(DECL_RE.findall(f.read_text()))

doc = (root / 'design/weil-constant-derivation.md').read_text()
listed = set(re.findall(r'`([A-Za-z_][A-Za-z0-9_]*)`', doc))

missing = sorted(support - listed)
unknown = sorted(listed - everywhere - ALLOWED_NON_LEAN)
if missing:
    print("declared in WeilSupport.lean but not referenced in the doc:",
          *missing, sep='\n  ')
if unknown:
    print("backticked in the doc but not a CompElliptic declaration"
          " (add to ALLOWED_NON_LEAN if intentional):",
          *unknown, sep='\n  ')
sys.exit(1 if (missing or unknown) else 0)
