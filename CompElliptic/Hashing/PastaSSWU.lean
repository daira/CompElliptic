/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.IsoPasta
import CompElliptic.Hashing.SimplifiedSWU
import CompElliptic.Hashing.SignedLift
import Mathlib.Tactic.ReduceModChar

/-!
# The deployed simplified-SWU parameters for the Pasta curves

The concrete `SSWUParams` instances for hashing to Pallas and Vesta, as deployed
(`hashtocurve.sage`, `pasta_curves`). Simplified SWU runs on the iso-curves
(which have `A ≠ 0`), with `Z = -13` for both curves, the parity sign function
`sgn0`, and the square-root split over the nonsquare `lam := rootOfUnity` — the
primitive `2^{32}`-nd root of unity `5ᵀ` that drives Tonelli–Shanks, which
`pasta_curves` reuses as `ROOT_OF_UNITY` — with `θ = √(Z/lam)` precomputed.
`lam` needs no per-field non-residue check: a full-order root of unity is a
nonsquare (`TonelliShanks.rootOfUnity_not_isSquare`).

The `θ` values are the `THETA` constants of `pasta_curves`
(<https://github.com/zcash/pasta_curves/blob/24c71faa6f19a54ec79f0828d50277c532b88e34/src/curves.rs#L1099>
for Pallas, `…#L1199` for Vesta); the `example`s below tie the hex literals to
the reference's `from_raw` limbs. Either square root of `Z/lam` would work: `θ`
enters only the nonsquare branch's candidate ordinate, whose sign the final
parity-matching step overrides. We use the same root as `pasta_curves` and
`zcash-test-vectors` so that intermediate values can be compared directly.
`hashtocurve.sage`
(<https://github.com/zcash/pasta/blob/f0f7068552a3565786cb338448cb58bc36a8314a/hashtocurve.sage>)
computes the same parameters at lines 211–217 (`h = F.g` is `5ᵀ`, from
`SqrtField`'s `g = Mod(z, p)^m` with `z = 5`).

The criterion-4 witnesses were computed with

```
F = GF(p)                                    # resp. GF(q)
x = F(B) / (F(-13) * F(A))
w = sqrt(x^3 + F(A)*x + F(B))
```

for the iso-curve coefficients `A`, `B`.
-/

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Fields.Pasta
open CompElliptic.Hashing

namespace CompElliptic.Curves.Pasta

namespace Pallas

/-- `-13` is a quadratic non-residue in the Pallas base field: Euler's criterion,
with the power evaluated by fast modular exponentiation. -/
theorem neg_thirteen_not_isSquare : ¬ IsSquare (-13 : PallasBaseField) := by
  rw [ZMod.euler_criterion PALLAS_BASE_CARD (by decide : (-13 : PallasBaseField) ≠ 0)]
  reduce_mod_char
  decide

/-- The deployed simplified-SWU parameters targeting iso-Pallas. -/
def sswu : SSWUParams PallasBaseField where
  E := isoCurve
  A_nonzero := by decide
  Z := -13
  Z_nonsquare := neg_thirteen_not_isSquare
  d := pallasBase
  lam := pallasBase.rootOfUnity
  lam_nonsquare := pallasBase.rootOfUnity_not_isSquare
  θ := 0x0f7bdb65814179b44647aef782d5cdc851f64fc4dc888857ca330bcc09ac318e
  θ_spec := by decide
  sgn := sgn0
  crit4 := ⟨0x0333fa3f8cb3bbd6e18f2fba2717db760fa5b179f0e2993f73395bb94a9eabe4, by
    -- Clear the divisions first: modular inversion under `decide`'s kernel
    -- evaluation is infeasible, while the division-free identity is fast.
    -- `field_simp` needs the *atomic* nonzero facts — it rewrites the
    -- denominator to `13^3 * A^3`, which a combined `-13 * A ≠ 0` fails to
    -- discharge, leaving a division behind.
    have h13 : (13 : PallasBaseField) ≠ 0 := by decide
    have hA : isoCurve.A ≠ 0 := by decide
    field_simp [h13, hA]
    decide⟩

/-- `θ` is byte-for-byte `pasta_curves`' `THETA` for `Fp` (`from_raw`
little-endian `u64` limbs, least significant first). -/
example : sswu.θ = 0xca330bcc09ac318e
    + 0x51f64fc4dc888857 * 2^64
    + 0x4647aef782d5cdc8 * 2^128
    + 0x0f7bdb65814179b4 * 2^192 := by decide

end Pallas

namespace Vesta

/-- `-13` is a quadratic non-residue in the Vesta base field: Euler's criterion,
with the power evaluated by fast modular exponentiation. -/
theorem neg_thirteen_not_isSquare : ¬ IsSquare (-13 : VestaBaseField) := by
  rw [ZMod.euler_criterion PALLAS_SCALAR_CARD (by decide : (-13 : VestaBaseField) ≠ 0)]
  reduce_mod_char
  decide

/-- The deployed simplified-SWU parameters targeting iso-Vesta. -/
def sswu : SSWUParams VestaBaseField where
  E := isoCurve
  A_nonzero := by decide
  Z := -13
  Z_nonsquare := neg_thirteen_not_isSquare
  d := vestaBase
  lam := vestaBase.rootOfUnity
  lam_nonsquare := vestaBase.rootOfUnity_not_isSquare
  θ := 0x2b3483a1ee9a382f53c3808d9e2f235738578ccadf03ac27632cae9872df1b5d
  θ_spec := by decide
  sgn := sgn0
  crit4 := ⟨0x1e004d52293581bcab805716bdb5ebcd8c1742ca68528997460503c7a51dd3e5, by
    -- Clear the divisions first, as for Pallas.
    have h13 : (13 : VestaBaseField) ≠ 0 := by decide
    have hA : isoCurve.A ≠ 0 := by decide
    field_simp [h13, hA]
    decide⟩

/-- `θ` is byte-for-byte `pasta_curves`' `THETA` for `Fq` (`from_raw`
little-endian `u64` limbs, least significant first). -/
example : sswu.θ = 0x632cae9872df1b5d
    + 0x38578ccadf03ac27 * 2^64
    + 0x53c3808d9e2f2357 * 2^128
    + 0x2b3483a1ee9a382f * 2^192 := by decide

end Vesta

end CompElliptic.Curves.Pasta
