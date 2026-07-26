# Vendored material (temporary)

This directory holds code that belongs to an **upstream dependency** and lives here only until
CompElliptic's pin of that dependency can provide it. Nothing else should be added to it, and
nothing in here may import anything from the rest of CompElliptic *except* what is explicitly
noted below.

Each subdirectory carries its own deletion criterion. When that criterion is met the
subdirectory is deleted and the import paths are rewritten — the code itself does not change.

## `CompPoly/Montgomery/` — eight-limb Montgomery field

A **temporary vendoring** of the [CompPoly](https://github.com/Verified-zkEVM/CompPoly) branch
`fast_multilimb_fields` (commit `b3850f0`), which adds eight-limb (8 × 32-bit packed in
`UInt64`) Montgomery arithmetic for 255-bit prime moduli next to the existing single-word
`Montgomery/Native32*`. It is what makes `CompElliptic/Curves/Pasta/Fast/ProjectiveMontDefs.lean`
fast enough to be worth precompiling.

**Delete this directory** when CompElliptic's CompPoly pin moves past
[CompPoly#258](https://github.com/Verified-zkEVM/CompPoly/pull/258) (the eight-limb Montgomery
field) and [CompPoly#274](https://github.com/Verified-zkEVM/CompPoly/pull/274). On landing, the
import paths become `CompElliptic.Vendor.CompPoly.Montgomery.X` →
`CompPoly.Fields.Montgomery.X`, and `Pasta.lean` is dropped (see below).

| File | Upstream original | Change |
|---|---|---|
| `Basic.lean` | `CompPoly/Fields/Montgomery/Basic.lean` | none |
| `Native64x8Defs.lean` | `CompPoly/Fields/Montgomery/Native64x8.lean` (definitions) | split out, `ℕ` → `Nat`, plus the Pasta constants and monomorphic entry points |
| `Native64x8.lean` | `CompPoly/Fields/Montgomery/Native64x8.lean` (theorems) | imports the split-out definitions; two `norm_num` calls dropped (Lean 4.30 vs 4.31 `simp` drift) |
| `Native64x8Mul.lean` | same name | import path; one `norm_num` dropped |
| `Native64x8Field.lean` | same name | import path |
| `Pasta.lean` | `CompPoly/Fields/Pasta/{Basic,Fast}.lean` | **rewritten**: reuses `CompElliptic.Fields.Pasta`'s primes and Pratt certificates instead of vendoring a second copy, so the repo keeps exactly one `Field (ZMod PALLAS_SCALAR_CARD)` instance and the Montgomery carrier bridges directly into `CompElliptic.Curves.Pasta.Fast.Projective.Fq` |

`Pasta.lean` is the one file here that imports CompElliptic (`CompElliptic.Fields.Pasta`); it is
also the one file that is dropped rather than re-pointed when the vendoring ends, precisely
because upstream carries its own copy of that data.

The definition/proof split exists for the precompiled lane: `Native64x8Defs.lean` imports
nothing beyond Lean core, so it can be native-compiled (the `FastFieldNative` library, see the
lakefile) without dragging a mathlib import closure through codegen. Keep it that way.
Upstream has since **also** adopted the same definitions/proofs split, so the vendored copy and
upstream have converged on the same shape; the eventual migration is an import-path rewrite
rather than a restructuring.

Namespaces are deliberately **unchanged** from upstream (`Montgomery.Native64x8`) — that is the
whole point of vendoring these files unmodified, and it is what makes the migration a pure
import-path rewrite. The pinned CompPoly predates the `Montgomery` directory, so nothing
clashes.
