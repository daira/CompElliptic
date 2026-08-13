/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.IsoPasta
import CompElliptic.Isogenies.Homomorphism
import CompElliptic.Curves.PastaOrder
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

## Checking against references

The fixtures below pin `mapXY` against `hashtocurve.sage`'s vectors, and
`mapHashOutputsToCurve` —the deployed construction after `hash_to_field`— against
the `zcash-test-vectors` group-hash vector for Pallas and the Halo 2
fixed-generator derivation for Vesta. The missing Vesta vectors in
`zcash-test-vectors` are tracked by
<https://github.com/zcash/zcash-test-vectors/issues/132>, and direct
comparison against the `pasta_curves` Rust implementation by
<https://github.com/daira/CompElliptic/issues/24>.
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

/-- The precomputed resolvent root for RFC 9380's criterion 3 on iso-Pallas is not a
cube: `not_exists_pow_eq_of_pow_ne_one`, with the power evaluated by fast modular
exponentiation as for `neg_five_not_isCube`. -/
theorem crit3_w_not_isCube : ¬ ∃ u : PallasBaseField,
    u ^ 3 = (0x27234601c28978a85e0960ed291d6536dbecfb7c12f0173667d69bce9a3d69bc
      : PallasBaseField) := by
  have hcard : Fintype.card PallasBaseField = PALLAS_BASE_CARD := ZMod.card _
  refine Fields.not_exists_pow_eq_of_pow_ne_one (n := 3) (by rw [hcard]; decide)
    (by decide) ?_
  rw [hcard]
  show (0x27234601c28978a85e0960ed291d6536dbecfb7c12f0173667d69bce9a3d69bc
    : ZMod PALLAS_BASE_CARD) ^ ((PALLAS_BASE_CARD - 1) / 3) ≠ 1
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
  crit2 := by decide
  crit3 := by
    -- `s` is a square root of the resolvent discriminant and `w` the resolvent
    -- root, precomputed in Sagemath for `q := B - Z`; `decide` checks both.
    have h := Fields.cubic_no_root_of_resolvent_noncube
      (h2 := (by decide : (2 : PallasBaseField) ≠ 0))
      (h3 := (by decide : (3 : PallasBaseField) ≠ 0))
      (A := isoCurve.A) (q := isoCurve.B + 13)
      (s := 0x0e468c038512f150bc12c1da523aca6d95935dfc1c933551368006b0347ad875)
      (w := 0x27234601c28978a85e0960ed291d6536dbecfb7c12f0173667d69bce9a3d69bc)
      (hs := by decide) (hw := by decide) (hnc := crit3_w_not_isCube)
    intro x hx
    exact h x (by linear_combination hx)
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

/-- `sgn0` is a sign function on the Pallas base field: the modulus is odd. -/
theorem isSignFunction_sgn0 : IsSignFunction (sgn0 (p := PALLAS_BASE_CARD)) :=
  haveI : NeZero PALLAS_BASE_CARD := ⟨by decide⟩
  CompElliptic.Hashing.isSignFunction_sgn0 (Nat.odd_iff.mpr (by decide))

/-- The deployed `map_to_curve` for Pallas: simplified SWU onto iso-Pallas,
then the 3-isogeny down to Pallas. -/
def mapToCurve (u : PallasBaseField) : SWPoint curve :=
  iso.map (sswu.map u)

/-- The deployed mapping is odd away from `0`: simplified SWU is
(`SSWUParams.map_neg`), and the isogeny commutes with negation
(`ThreeIsogeny.map_neg`). -/
theorem mapToCurve_neg {u : PallasBaseField} (hu : u ≠ 0) :
    mapToCurve (-u) = -(mapToCurve u) := by
  simp only [mapToCurve]
  rw [sswu.map_neg isSignFunction_sgn0 hu]
  exact iso.map_neg (sswu.map u)

/-- The zero-repaired deployed mapping is literally odd — the form the
character-sum analysis consumes. -/
theorem isOdd_zeroRepaired_mapToCurve : IsOdd (zeroRepaired mapToCurve) :=
  isOdd_zeroRepaired fun _ hu => mapToCurve_neg hu

/-- The deployed hash-to-curve construction for Pallas after `hash_to_field`:
add on the iso-curve, apply the isogeny once. -/
def mapHashOutputsToCurve (u₀ u₁ : PallasBaseField) : SWPoint curve :=
  iso.mapHashOutputsToCurve sswu.map u₀ u₁

/-- The construction agrees with mapping each point down and adding on
Pallas — the order `zcash-test-vectors` and `pasta_curves` use — by the
homomorphism. -/
theorem mapHashOutputsToCurve_eq (u₀ u₁ : PallasBaseField) :
    mapHashOutputsToCurve u₀ u₁ = mapToCurve u₀ + mapToCurve u₁ :=
  iso_map_add (sswu.map u₀) (sswu.map u₁)

/-! ### Fixtures for `mapXY` against `hashtocurve.sage`

The first three `u` values are the script's self-test inputs (`u = 0` exercises
the exceptional `ta = 0` branch). The last two are the field elements its
`hash_to_field` produces for the `hash_to_pallas_jacobian` test vector
(`msg = "Trans rights now!"`, `DST = "z.cash:test-pallas_XMD:BLAKE2b_SSWU_RO_"`),
extracted by running the script with `VERBOSE = True`; they take opposite
`IsSquare` branches. Expected outputs are
`map_to_curve_simple_swu(...).to_affine(IsoEp)` from the same script. -/

example : sswu.mapXY 0 =
    (0x2c150731d26bf03de9585bf1a0c67160f6ca6e5ce0e2b674af333253bca63800,
     0x0333fa3f8cb3bbd6e18f2fba2717db760fa5b179f0e2993f73395bb94a9eabe4) := by
  native_decide

example : sswu.mapXY 1 =
    (0x0bb222fb72c9783337e0e9e1c4282c391407f5f9d9fcc94ace1d677dbf3ba120,
     0x36366437b8048026b50626f004b30dd99389b090d8a502d78f3fbd565fe86477) := by
  native_decide

example : sswu.mapXY
    0x123456789abcdef123456789abcdef123456789abcdef123456789abcdef0123 =
    (0x24f27f64d536dbc39c03c18fda8e65a9a12b7418818ed76c040b83ef97b25723,
     0x03e6c9c2288650534d76b391d26c8ee6e4e99fad1f41b411481fa968f8184a75) := by
  native_decide

example : sswu.mapXY
    0x1bdd4c3fc1169a6d8eb82d66652f44a1e4a73cc1b6da4bba1d95fa6111c85a6f =
    (0x05c3482fe40155e152fdc0be06c4766b67a2b3d8d9bb64ee6137382879dc2160,
     0x3825fb730c259375175ff31b94dc36dcf031b13f3116bda725f1c98717739f1f) := by
  native_decide

example : sswu.mapXY
    0x0dd7332b3108010636107798c0ea89f94c79fb0472cb7b8222c450142802e4af =
    (0x2c6e5aa1a88cd76c8a9d436438d2993244bf7704e4f322a86d0890bd6cee28ab,
     0x0b20c46efea44d15e4828808c86a72789d54328635ba4274d8e9b48d9654f65b) := by
  native_decide

/-! ### The `zcash-test-vectors` group-hash fixture

`zcash-test-vectors` pins `group_hash(b"z.cash:test", b"Trans rights now!")` — the
same `(msg, DST)` pair as the vector above, after `group_hash`'s DST expansion —
to an affine Pallas point:
<https://github.com/zcash/zcash-test-vectors/blob/78321beacb0e0477e33cd002b56585a107c2708c/zcash_test_vectors/orchard/group_hash.py#L143>.
The example pins `mapHashOutputsToCurve` at the vector's two `hash_to_field`
outputs (their `mapXY` coordinates are pinned above) to the reference point,
whose coordinates are quoted in decimal, verbatim from `group_hash.py`. -/

example :
    mapHashOutputsToCurve
        0x1bdd4c3fc1169a6d8eb82d66652f44a1e4a73cc1b6da4bba1d95fa6111c85a6f
        0x0dd7332b3108010636107798c0ea89f94c79fb0472cb7b8222c450142802e4af
      = ⟨10899331951394555178876036573383466686793225972744812919361819919497009261523,
         851679174277466283220362715537906858808436854303373129825287392516025427980,
         Or.inl (by native_decide)⟩ := by
  native_decide

end Pallas

namespace Vesta

/-- `-13` is a quadratic non-residue in the Vesta base field: Euler's criterion,
with the power evaluated by fast modular exponentiation. -/
theorem neg_thirteen_not_isSquare : ¬ IsSquare (-13 : VestaBaseField) := by
  rw [ZMod.euler_criterion PALLAS_SCALAR_CARD (by decide : (-13 : VestaBaseField) ≠ 0)]
  reduce_mod_char
  decide

/-- The precomputed resolvent root for RFC 9380's criterion 3 on iso-Vesta is not a
cube: `not_exists_pow_eq_of_pow_ne_one`, with the power evaluated by fast modular
exponentiation as for `neg_five_not_isCube`. -/
theorem crit3_w_not_isCube : ¬ ∃ u : VestaBaseField,
    u ^ 3 = (0x2236a351e7028c01c80f079ca37fd81fd024e547a51813136e8516e4eaf7d998
      : VestaBaseField) := by
  have hcard : Fintype.card VestaBaseField = PALLAS_SCALAR_CARD := ZMod.card _
  refine Fields.not_exists_pow_eq_of_pow_ne_one (n := 3) (by rw [hcard]; decide)
    (by decide) ?_
  rw [hcard]
  show (0x2236a351e7028c01c80f079ca37fd81fd024e547a51813136e8516e4eaf7d998
    : ZMod PALLAS_SCALAR_CARD) ^ ((PALLAS_SCALAR_CARD - 1) / 3) ≠ 1
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
  crit2 := by decide
  crit3 := by
    -- As for Pallas: precomputed Sagemath certificates, checked by `decide`.
    have h := Fields.cubic_no_root_of_resolvent_noncube
      (h2 := (by decide : (2 : VestaBaseField) ≠ 0))
      (h3 := (by decide : (3 : VestaBaseField) ≠ 0))
      (A := isoCurve.A) (q := isoCurve.B + 13)
      (s := 0x046d46a3ce051803901e0f3946ffb03f7e033193409b7d4950c342a8d5efb82d)
      (w := 0x2236a351e7028c01c80f079ca37fd81fd024e547a51813136e8516e4eaf7d998)
      (hs := by decide) (hw := by decide) (hnc := crit3_w_not_isCube)
    intro x hx
    exact h x (by linear_combination hx)
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

/-- `sgn0` is a sign function on the Vesta base field: the modulus is odd. -/
theorem isSignFunction_sgn0 : IsSignFunction (sgn0 (p := PALLAS_SCALAR_CARD)) :=
  haveI : NeZero PALLAS_SCALAR_CARD := ⟨by decide⟩
  CompElliptic.Hashing.isSignFunction_sgn0 (Nat.odd_iff.mpr (by decide))

/-- The deployed `map_to_curve` for Vesta: simplified SWU onto iso-Vesta,
then the 3-isogeny down to Vesta. -/
def mapToCurve (u : VestaBaseField) : SWPoint curve :=
  iso.map (sswu.map u)

/-- The deployed mapping is odd away from `0`: simplified SWU is
(`SSWUParams.map_neg`), and the isogeny commutes with negation
(`ThreeIsogeny.map_neg`). -/
theorem mapToCurve_neg {u : VestaBaseField} (hu : u ≠ 0) :
    mapToCurve (-u) = -(mapToCurve u) := by
  simp only [mapToCurve]
  rw [sswu.map_neg isSignFunction_sgn0 hu]
  exact iso.map_neg (sswu.map u)

/-- The zero-repaired deployed mapping is literally odd — the form the
character-sum analysis consumes. -/
theorem isOdd_zeroRepaired_mapToCurve : IsOdd (zeroRepaired mapToCurve) :=
  isOdd_zeroRepaired fun _ hu => mapToCurve_neg hu

/-- The deployed hash-to-curve construction for Vesta after `hash_to_field`:
add on the iso-curve, apply the isogeny once. -/
def mapHashOutputsToCurve (u₀ u₁ : VestaBaseField) : SWPoint curve :=
  iso.mapHashOutputsToCurve sswu.map u₀ u₁

/-- The construction agrees with mapping each point down and adding on
Vesta — the order `zcash-test-vectors` and `pasta_curves` use — by the
homomorphism. -/
theorem mapHashOutputsToCurve_eq (u₀ u₁ : VestaBaseField) :
    mapHashOutputsToCurve u₀ u₁ = mapToCurve u₀ + mapToCurve u₁ :=
  iso_map_add (sswu.map u₀) (sswu.map u₁)

/-! ### Fixtures for `mapXY` against `hashtocurve.sage`

As for Pallas: the script's three self-test inputs, then the two field
elements of its `hash_to_vesta_jacobian` test vector (`msg = "hello"`,
`DST = "z.cash:test-vesta_XMD:BLAKE2b_SSWU_RO_"`), which take opposite
`IsSquare` branches (in the opposite order to the Pallas vector). -/

example : sswu.mapXY 0 =
    (0x252ca74e8e7b7846cb59112c429e22166fa1dc53f442887ab66e73e89c4736c2,
     0x21ffb2add6ca7e43547fa8e9424a1432962f5631a1421f464641e7595ae22c1c) := by
  native_decide

example : sswu.mapXY 1 =
    (0x17ea828ed62281a1bb3dd72d681ada4ff18f20da82e1e7a022413d7d565a5eff,
     0x163cdc7b7bf3906fd03a189d0ba3a4d8af5ac6cb7a49db6257016680903bcff7) := by
  native_decide

example : sswu.mapXY
    0x123456789abcdef123456789abcdef123456789abcdef123456789abcdef0123 =
    (0x3b45aa24da5eead97e0e822c3a6cd21de7753d6bcb80e86b2a83d7965ae0fdcd,
     0x2c1f0a3607e56114240c198424efc075a8754031486a04daa7d167cbcb2e0f4f) := by
  native_decide

example : sswu.mapXY
    0x02ff3bc53fd8e95662b4614d32237aef43b36e53774401004eac13537507b1ac =
    (0x046a6cd3eb4941e556826c63ea8bd0d7c99d73c4a9bcbce66c8a69f39acb57d9,
     0x03bf12b7e097fc69f44204aaa1f2024573051cc0afdf6c9cc7e613d758eb17d6) := by
  native_decide

example : sswu.mapXY
    0x249ed75088f240d4c420e893e3b9cebfeb151a2a6e3e3f7dad559a98f139fcef =
    (0x3c59d550a420b986f9c65efd30753c1e31e732d8d572bd9805d82ee585e9ce80,
     0x328cde92a9c7c5ff3138cee2e342898ec171f46f6e1f6c40d364196a0eefafbf) := by
  native_decide

/-! ### The composed group-hash fixture

As for Pallas, but against `hashtocurve.sage`'s own `hash_to_vesta_jacobian`
vector. The script prints Jacobian coordinates; the first example below checks
the conversion to affine (`x/z²`, `y/z³`), with the printed `Eq { x, y, z }`
output quoted verbatim, so the pinned point can be compared directly against
the script's output. `zcash-test-vectors` carries no Vesta group-hash vector
yet, because Orchard's group hash targets Pallas — the gap is
<https://github.com/zcash/zcash-test-vectors/issues/132> — and this
`(msg, DST)` pair (`D = b"z.cash:test"`, `msg = b"hello"`, expanded over
`vesta`) is the shape such a vector is expected to take. -/

-- The script's printed Jacobian output, converted to the affine point pinned below.
example :
    ((0x12763505036e0e1a6684b7a7d8d5afb7378cc2b191a95e34f44824a06fcbd08e
        / 0x1b58d4aa4d68c3f4d9916b77c79ff9911597a27f2ee46244e98eb9615172d2ad ^ 2 :
        VestaBaseField),
     (0x0256eafc0188b79bfa7c4b2b393893ddc298e90da500fa4a9aee17c2ea4240e6
        / 0x1b58d4aa4d68c3f4d9916b77c79ff9911597a27f2ee46244e98eb9615172d2ad ^ 3 :
        VestaBaseField))
      = (0x2e983e009cf3b86bc95f91b3411bd6cbd0a87f8c3c3dae80f3f2637084849204,
         0x310fb8f3316d069a1fb9374bdbc0fb1391c864a5208b2a812341db7f50b2e106) := by
  native_decide

example :
    mapHashOutputsToCurve
        0x02ff3bc53fd8e95662b4614d32237aef43b36e53774401004eac13537507b1ac
        0x249ed75088f240d4c420e893e3b9cebfeb151a2a6e3e3f7dad559a98f139fcef
      = ⟨0x2e983e009cf3b86bc95f91b3411bd6cbd0a87f8c3c3dae80f3f2637084849204,
         0x310fb8f3316d069a1fb9374bdbc0fb1391c864a5208b2a812341db7f50b2e106,
         Or.inl (by native_decide)⟩ := by
  native_decide

/-! ### The Halo 2 fixed-generator spot-checks

Halo 2's `Params::new` derives the `2^k` polynomial-commitment generators
(`k = 11` for the Orchard Action circuit) plus `W` and `U` by hash-to-curve
over Vesta with domain prefix `"Halo2-Parameters"`: generator `i` hashes the
five bytes `[0] ++ u32_le(i)`, `W` hashes `[1]`, and `U` hashes `[2]`
(<https://github.com/zcash/halo2/blob/cafc26e269e4b1b123af8f2a0aa36bff6474448e/halo2_proofs/src/poly/commitment.rs#L35-L115>).
These spot-check the generators at indices `0` and `2^{11} - 1`, and `W` and
`U`; the `hash_to_field` outputs and expected points were computed with
`hashtocurve.sage` at `DST = "Halo2-Parameters-vesta_XMD:BLAKE2b_SSWU_RO_"`
and are recorded in the issue above. -/

-- The generator at index `0`.
example :
    mapHashOutputsToCurve
        0x0689c26b8485b6125b554ae564602872c4169750375c764f5f74741d8a6e7241
        0x089aae9d92dd9f5758bd8a7e3cb911a97e8aef5cc81e3c0767c18a5267954aa6
      = ⟨0x3decc7d8be779b2b8505a808c7e8109341ef95101391f5589738bf79d05e0645,
         0x30ac4ee40eb29dca411d3869f0bf452cb569bc56a0d674b998e794ce233f4531,
         Or.inl (by native_decide)⟩ := by
  native_decide

-- The generator at index `2^{11} - 1 = 2047`.
example :
    mapHashOutputsToCurve
        0x0a360980c8054088f9be339559eace1e7e985c3ac942bed952e7aef3103d178e
        0x0b0130d836325841f078cd1e94ba58d25311c47c6e31a6a1239424d36729d592
      = ⟨0x11743a31bb9d8d5259d8101be81cfd6662f8da73d9ccf609cf678a66841a49bd,
         0x3789a55b81d0b4779cb2869130f30043f124695da7b64b08934cc2401f51214c,
         Or.inl (by native_decide)⟩ := by
  native_decide

-- `W`.
example :
    mapHashOutputsToCurve
        0x3942ef4eff2efc40dbabf511bb9d2f4d2d564ae89a155959ee1deef5dbc1a25c
        0x239a4c1aeb9e98b3a5d0909d945babcbed9c34bcfe13501fa71e1968c5a8219d
      = ⟨0x2bbc94ef7b22aebef24f9a4b0cc1831882548b605171366017d45c3e6fd92075,
         0x082b801a6e176239943bfb759fb02138f47a5c8cc4aa7fa0af559fde4e3abd97,
         Or.inl (by native_decide)⟩ := by
  native_decide

-- `U`.
example :
    mapHashOutputsToCurve
        0x08786c60d346bd37392ad60bc4140e7c560ffad514418a9fc907cbfb481f6deb
        0x2da9e3ae3a7ebb742dcb78280b4c38a36819ede1c7ec3093615eb5b8729c2d8f
      = ⟨0x17a8b1830ad3ba49f240c0d0244f6911f6ac5997bba0d5c7cc61bffddcc49d37,
         0x2df4dd8b1be11f9db0176cf4cd0e52ff5528f693211cb7212bf6acd3327782cf,
         Or.inl (by native_decide)⟩ := by
  native_decide

end Vesta

end CompElliptic.Curves.Pasta
