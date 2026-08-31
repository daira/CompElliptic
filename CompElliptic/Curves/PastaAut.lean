/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Curves.PastaOrder
import CompElliptic.CurveForms.Automorphisms

/-!
# The six automorphisms of Pallas and Vesta

Both Pasta curves are `y² = x³ + 5`, so `A = 0` and `j = 0`, and both base fields
contain a primitive cube root of unity. `CurveForms.Automorphisms` then supplies
six automorphisms `(x, y) ↦ (ζᵏ · x, ± y)`; this module pins the constant `ζ` for
each curve and checks that the six are genuinely distinct, so the automorphism
group really does contain a copy of `μ₆` rather than collapsing.

Distinctness is a concrete closed fact, so it is settled by kernel `decide` at
the test point `G = (-1, 2)`: the three `x`-coordinates `ζᵏ · (-1)` are distinct
because `ζ` has order `3`, and the two `y`-coordinates `± 2` are distinct because
the field has odd characteristic.

`ZETA_quad` records that `ζ` satisfies `ζ² + ζ + 1 = 0` — the same relation the
adjoined `ω` of `Rings.Eisenstein` satisfies. That is the arithmetic content of
the statement that the six automorphisms of a `j = 0` curve are the six units of
`ℤ[ω]` acting: the `x`-exponent is the power of `ω` and the `y`-sign is the sign
of the unit, and `Automorphisms.autPt_comp` is the resulting multiplication law.
-/

namespace CompElliptic.Curves.Pasta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveForms.Automorphisms

namespace Pallas

/-- A primitive cube root of unity in the Pallas base field `𝔽ₚ`. -/
def ZETA : Fields.Pasta.PallasBaseField :=
  0x2d33357cb532458ed3552a23a8554e5005270d29d19fc7d27b7fd22f0201b547

theorem A_zero : curve.A = 0 := rfl

theorem ZETA_cube : ZETA ^ 3 = 1 := by decide

theorem ZETA_ne_one : ZETA ≠ 1 := by decide

/-- `ζ² + ζ + 1 = 0`: the defining relation of the adjoined `ω` in
`Rings.Eisenstein`. This is what identifies the `x`-scalings with the cube roots
of unity in `ℤ[ω]`. -/
theorem ZETA_quad : ZETA ^ 2 + ZETA + 1 = 0 := by decide

/-- The six automorphisms of Pallas, as additive automorphisms of the point
group: `(x, y) ↦ (ζᵏ · x, ± y)` for `k ∈ {0, 1, 2}`. -/
def aut (k : ℕ) (s : Bool) : SWPoint curve ≃+ SWPoint curve :=
  autEquiv A_zero ZETA_cube k s

/-- The parameters of the six automorphisms. -/
def autParams : List (ℕ × Bool) :=
  [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)]

/-- **The six are genuinely six.** Their values at `G = (-1, 2)` are pairwise
distinct, so the six parameter pairs give six different automorphisms and the
automorphism group contains a copy of `μ₆`. -/
theorem aut_nodup_at_Gpt :
    (autParams.map fun ks =>
      ((autPt A_zero ZETA_cube ks.1 ks.2 Gpt).x,
       (autPt A_zero ZETA_cube ks.1 ks.2 Gpt).y)).Nodup := by
  simp only [autParams, List.map_cons, List.map_nil, autPt_x, autPt_y]
  decide

end Pallas

namespace Vesta

/-- A primitive cube root of unity in the Vesta base field `𝔽_q`. -/
def ZETA : Fields.Pasta.VestaBaseField :=
  0x06819a58283e528e511db4d81cf70f5a0fed467d47c033af2aa9d2e050aa0e4f

theorem A_zero : curve.A = 0 := rfl

theorem ZETA_cube : ZETA ^ 3 = 1 := by decide

theorem ZETA_ne_one : ZETA ≠ 1 := by decide

theorem ZETA_quad : ZETA ^ 2 + ZETA + 1 = 0 := by decide

/-- The six automorphisms of Vesta. -/
def aut (k : ℕ) (s : Bool) : SWPoint curve ≃+ SWPoint curve :=
  autEquiv A_zero ZETA_cube k s

theorem aut_nodup_at_Gpt :
    (Pallas.autParams.map fun ks =>
      ((autPt A_zero ZETA_cube ks.1 ks.2 Gpt).x,
       (autPt A_zero ZETA_cube ks.1 ks.2 Gpt).y)).Nodup := by
  simp only [Pallas.autParams, List.map_cons, List.map_nil, autPt_x, autPt_y]
  decide

end Vesta

end CompElliptic.Curves.Pasta
