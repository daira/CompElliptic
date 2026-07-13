/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.PastaOrder
import CompElliptic.Endomorphism

/-!
# The GLV endomorphism on the Pasta curves (Pallas and Vesta)

Instantiates `Endomorphism.lean` at the two Pasta curves. Both are `y² = x³ + 5`, so
`A = 0` and the endomorphism `φ (x, y) = (ζ x, y)` applies, where `ζ` is a primitive cube root of
unity in the *base* field (`p ≡ q ≡ 1 mod 3`, so both fields have them).

The payoff is `phi_eq_lambda_nsmul`: **`φ = [λ]` on the whole group**, where `λ` is a primitive cube
root of unity in the *scalar* field. Everything general was proved outright in
`Endomorphism.lean`; here only *closed numeric facts* remain, in the *Independently re-checkable
trust* style:

* the field-level facts (`ζ³ = 1`, `ζ ≠ 1`, `ζ² + ζ + 1 = 0`, and the `λ` analogues) are
  kernel-`decide`d, so the *definition* of `φ` carries no `native_decide`;
* the single point fact `φ G = [λ] G` is `native_decide`d. Kernel `decide` cannot do it — not
  merely slowly, but at all: `binNsmul` is defined by well-founded recursion, so its equations do
  not reduce definitionally and `decide` gets stuck at `instDecidableEqSWPoint`. This is the same
  reason `PastaOrder.lean`'s `[order] G = 𝒪` witness is `native_decide`.

**The (ζ, λ) pairing is not free.** Each field has *two* primitive cube roots of unity, and a given
`ζ` acts as `[λ]` for exactly one of the two candidate `λ`s (the other `ζ` pairs with the other
`λ`). Pairing them wrongly gives a `φ` that is still a perfectly good endomorphism, just equal to
`[λ²]` rather than `[λ]` — a silent, wrong-by-a-cube-root bug. `phi_Gpt` is precisely the check
that rules this out, which is why it is a machine-checked fact and not a comment.

Note the Pasta cycle shows up here too: Pallas's `ζ` lives in `𝔽ₚ` and its `λ` in `𝔽_q`, while
Vesta's `ζ` lives in `𝔽_q` and its `λ` in `𝔽ₚ` — so the two curves' constants are *crossed*.
-/

namespace CompElliptic.Curves.Pasta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder
  CompElliptic.Endomorphism CompElliptic.Fields.Pasta

namespace Pallas

/-- A primitive cube root of unity in the Pallas *base* field `𝔽ₚ`; `φ` scales `x` by it. -/
def ZETA : PallasBaseField :=
  0x2d33357cb532458ed3552a23a8554e5005270d29d19fc7d27b7fd22f0201b547

/-- The matching primitive cube root of unity in the Pallas *scalar* field `𝔽_q`, as a `ℕ` (so that
`LAMBDA • _` is the fast `binNsmul` action). `φ` acts as `[LAMBDA]` — pinned by `phi_Gpt`. -/
def LAMBDA : ℕ :=
  0x397e65a7d7c1ad71aee24b27e308f0a61259527ec1d4752e619d1840af55f1b1

/-- Pallas is `y² = x³ + 5`, so `A = 0` — the hypothesis the endomorphism needs. -/
theorem A_zero : curve.A = 0 := rfl

/-- `ζ` is a cube root of unity — the hypothesis `φ` is built on. Kernel-`decide`d, so the
*definition* of `φ` carries no `native_decide`. -/
theorem ZETA_cube : ZETA ^ 3 = 1 := by decide

/-- `ζ ≠ 1`, so `φ` is not the identity map (together with `ZETA_cube`, `ζ` is *primitive*). -/
theorem ZETA_ne_one : ZETA ≠ 1 := by decide

/-- Primitivity in the form actually used downstream: `ζ² + ζ + 1 = 0`. -/
theorem ZETA_quad : ZETA ^ 2 + ZETA + 1 = 0 := by decide

/-- `λ` is a canonical (reduced) representative of its scalar-field class. -/
theorem LAMBDA_lt : LAMBDA < PALLAS_SCALAR_CARD := by decide

/-- `λ` is a cube root of unity in the scalar field — the scalar-side counterpart of
`ZETA_cube`, and the reason `φ³ = id` is consistent with `φ = [λ]`. -/
theorem LAMBDA_cube : (LAMBDA : PallasScalarField) ^ 3 = 1 := by decide

/-- `λ² + λ + 1 = 0`: the relation `φ² + φ + 1 = 0` that GLV decomposition rests on. -/
theorem LAMBDA_quad : (LAMBDA : PallasScalarField) ^ 2 + LAMBDA + 1 = 0 := by decide

/-- **The GLV endomorphism on Pallas**: `φ (x, y) = (ζ x, y)`. -/
def phi (P : SWPoint curve) : SWPoint curve := phiPt A_zero ZETA_cube P

/-- The spot-check that pins the `(ζ, λ)` pairing: `φ G = [λ] G` on the test point `G = (-1, 2)`.

This is the *one* closed fact the whole `φ = [λ]` theorem rests on beyond the general proofs, and
it is exactly what would fail if `ζ` were paired with the wrong cube root of unity. -/
theorem phi_Gpt : phi Gpt = LAMBDA • Gpt := by native_decide

/-- **`φ = [λ]` on the whole Pallas group** (assuming Hasse's bound).

`φ` is an endomorphism (proved outright, `phiHom`); the group has prime order
`PALLAS_SCALAR_CARD` (`Pallas.card_eq`, the one place Hasse is assumed); and `φ G = [λ] G` for the
non-identity `G` (`phi_Gpt`). By `endo_eq_nsmul_of_prime_card`, `φ` is `[λ]` everywhere. -/
theorem phi_eq_lambda_nsmul (hHasse : HasseBound curve) (P : SWPoint curve) :
    phi P = LAMBDA • P :=
  phiPt_eq_nsmul A_zero ZETA_cube (card_eq hHasse) Gpt_ne_zero phi_Gpt P

-- `φ` fixes `𝒪`.
example : phi 0 = 0 := by native_decide

-- `φ` is nontrivial: it moves `G` (it is not the identity map, cf. `ZETA_ne_one`).
example : phi Gpt ≠ Gpt := by native_decide

-- `φ³ = id` on `G` (the computational shadow of `phi_phi_phi`).
example : phi (phi (phi Gpt)) = Gpt := by native_decide

-- `φ` is additive on a concrete pair (the computational shadow of `phi_add`).
example : phi (Gpt + (2 : ℕ) • Gpt) = phi Gpt + phi ((2 : ℕ) • Gpt) := by native_decide

-- **The `(ζ, λ)` pairing has teeth.** `λ²` is the *other* primitive cube root of unity in `𝔽_q`,
-- and `φ` is emphatically not `[λ²]`. Pairing `ζ` with it would give a well-typed, perfectly valid
-- endomorphism that is simply the wrong one — which is what `phi_Gpt` exists to rule out.
example : phi Gpt ≠ (LAMBDA ^ 2 % PALLAS_SCALAR_CARD) • Gpt := by native_decide

end Pallas

namespace Vesta

/-- A primitive cube root of unity in the Vesta *base* field `𝔽_q` (`= PallasScalarField`; the Pasta
cycle crosses the two curves' constants). -/
def ZETA : VestaBaseField :=
  0x06819a58283e528e511db4d81cf70f5a0fed467d47c033af2aa9d2e050aa0e4f

/-- The matching primitive cube root of unity in the Vesta *scalar* field `𝔽ₚ`, as a `ℕ`. -/
def LAMBDA : ℕ :=
  0x12ccca834acdba712caad5dc57aab1b01d1f8bd237ad31491dad5ebdfdfe4ab9

/-- Vesta is `y² = x³ + 5`, so `A = 0`. -/
theorem A_zero : curve.A = 0 := rfl

/-- `ζ` is a cube root of unity — the hypothesis `φ` is built on. -/
theorem ZETA_cube : ZETA ^ 3 = 1 := by decide

/-- `ζ ≠ 1`, so `φ` is not the identity map. -/
theorem ZETA_ne_one : ZETA ≠ 1 := by decide

/-- Primitivity: `ζ² + ζ + 1 = 0`. -/
theorem ZETA_quad : ZETA ^ 2 + ZETA + 1 = 0 := by decide

/-- `λ` is a canonical (reduced) representative of its scalar-field class. -/
theorem LAMBDA_lt : LAMBDA < PALLAS_BASE_CARD := by decide

/-- `λ` is a cube root of unity in the scalar field. -/
theorem LAMBDA_cube : (LAMBDA : VestaScalarField) ^ 3 = 1 := by decide

/-- `λ² + λ + 1 = 0`. -/
theorem LAMBDA_quad : (LAMBDA : VestaScalarField) ^ 2 + LAMBDA + 1 = 0 := by decide

/-- **The GLV endomorphism on Vesta**: `φ (x, y) = (ζ x, y)`. -/
def phi (P : SWPoint curve) : SWPoint curve := phiPt A_zero ZETA_cube P

/-- The spot-check pinning the `(ζ, λ)` pairing on Vesta: `φ G = [λ] G`. -/
theorem phi_Gpt : phi Gpt = LAMBDA • Gpt := by native_decide

/-- **`φ = [λ]` on the whole Vesta group** (assuming Hasse's bound). -/
theorem phi_eq_lambda_nsmul (hHasse : HasseBound curve) (P : SWPoint curve) :
    phi P = LAMBDA • P :=
  phiPt_eq_nsmul A_zero ZETA_cube (card_eq hHasse) Gpt_ne_zero phi_Gpt P

-- As for Pallas: `φ` fixes `𝒪`, is nontrivial, cubes to the identity, is additive, and is *not*
-- `[λ²]` (the other primitive cube root of unity in the scalar field).
example : phi 0 = 0 := by native_decide
example : phi Gpt ≠ Gpt := by native_decide
example : phi (phi (phi Gpt)) = Gpt := by native_decide
example : phi (Gpt + (2 : ℕ) • Gpt) = phi Gpt + phi ((2 : ℕ) • Gpt) := by native_decide
example : phi Gpt ≠ (LAMBDA ^ 2 % PALLAS_BASE_CARD) • Gpt := by native_decide

end Vesta

end CompElliptic.Curves.Pasta
