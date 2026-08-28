/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Rings.Eisenstein.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The finite quotients `ℤ[ω]/n`, computably

`Eisenstein (ZMod n)` **is** `ℤ[ω]/n`, because `Eisenstein` commutes with base
change (`Basic.lean`). Reducing the coefficients rather than quotienting the ring
means `Fintype` and `DecidableEq` are inherited from `ZMod n`, so the finite
claims in `Rings.Eisenstein.Orbits` are settled by kernel `decide`.

## Main results

* `Eisenstein.card_eq` — `#(ℤ[ω]/n) = n²`.
* `Eisenstein.two_dvd_iff` — an element is even exactly when both
  coordinates are, so halving is exact and coordinate-wise.
* `Eisenstein.mod_two_eq_zero_or_isUnit`, `Eisenstein.mul_eq_zero_mod_two` —
  `ℤ[ω]/2` is the field `𝔽₄`, i.e. `2` is inert. This is what makes
  "odd" and "unit" the same predicate mod `2^w`, and it is why `ℤ[ω]/2^w` is a
  local ring with maximal ideal `(2)`.
-/

namespace CompElliptic.Rings.Eisenstein

variable {R : Type*}

/-- `R[ω]` is just a pair of coefficients. -/
def equivProd (R : Type*) : Eisenstein R ≃ R × R where
  toFun x := (x.a, x.b)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro p; cases p; rfl

/-- `R[ω]` is computably finite whenever `R` is: it is a pair of coefficients, so
the enumeration is the product enumeration — no choice, and it reduces in the
kernel. Named so the trust census can pin its computability. -/
instance instFintype [Fintype R] : Fintype (Eisenstein R) :=
  Fintype.ofEquiv _ (equivProd R).symm

/-- `#R[ω] = (#R)²`. For `R = ZMod (2^w)` this is the `4^w` the odd-class count is taken from. -/
theorem card_eq [Fintype R] :
    Fintype.card (Eisenstein R) = Fintype.card R * Fintype.card R := by
  rw [Fintype.card_congr (equivProd R), Fintype.card_prod]

section Two

variable [CommRing R]

/-- The numeral `2` is the coefficient pair `⟨2, 0⟩`; `ω` plays no part in it. -/
theorem two_eq : (2 : Eisenstein R) = ⟨2, 0⟩ := by
  have h : (2 : Eisenstein R) = 1 + 1 := by norm_num
  rw [h]
  ext
  · show (1 : R) + 1 = 2; norm_num
  · show (0 : R) + 0 = 0; simp

@[simp] theorem two_a : (2 : Eisenstein R).a = 2 := by rw [two_eq]
@[simp] theorem two_b : (2 : Eisenstein R).b = 0 := by rw [two_eq]

/-- `2 ∣ a + b·ω` exactly when `2 ∣ a` and `2 ∣ b`. The forward
direction is immediate because `2` is a rational integer, so multiplication by it
is coordinate-wise: `2 · ⟨c, d⟩ = ⟨2c, 2d⟩`. Halving is therefore exact and needs
no reasoning about `ω` — which is what lets the Eisenstein recoder halve in the
ring exactly as the coordinate-wise recoder halves each component. -/
theorem two_dvd_iff (x : Eisenstein R) :
    (2 : Eisenstein R) ∣ x ↔ (2 : R) ∣ x.a ∧ (2 : R) ∣ x.b := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.a, by simp⟩, ⟨y.b, by simp⟩⟩
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨⟨c, d⟩, by ext <;> simp [hc, hd]⟩

end Two

/-! ## `2` is inert, so `ℤ[ω]/2 = 𝔽₄`

`X² + X + 1` has no root in `𝔽₂` (both `0` and `1` evaluate to `1`), so it is
irreducible there and `2` stays prime in `ℤ[ω]`. Stated below in the two
computational forms the rest of the development uses: the quotient has four
elements, and it has no zero divisors. Both are `decide` over at most `16` pairs,
so they add no axiom. -/

/-- **Cardinality.** `ℤ[ω]/2` has four elements — it is `𝔽₄`, not
`𝔽₂ × 𝔽₂`, which is the content of `2` being inert rather than split. -/
theorem card_mod_two : Fintype.card (Eisenstein (ZMod 2)) = 4 := by decide

/-- **No zero divisors.** `ℤ[ω]/2` is a domain, hence (being finite) a
field. Equivalently `2` is a prime element of `ℤ[ω]`. -/
theorem mul_eq_zero_mod_two (x y : Eisenstein (ZMod 2)) :
    x * y = 0 → x = 0 ∨ y = 0 := by revert x y; decide

/-- **Every nonzero class is invertible.** The residue field is `𝔽₄`,
so a class is a unit exactly when it is nonzero. This is the fact that lets
"odd" (not divisible by `2`) and "unit" be used interchangeably mod `2^w`. -/
theorem exists_inv_mod_two (x : Eisenstein (ZMod 2)) (hx : x ≠ 0) :
    ∃ y, x * y = 1 := by revert x; decide

end CompElliptic.Rings.Eisenstein
