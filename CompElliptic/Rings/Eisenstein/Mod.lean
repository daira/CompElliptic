/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Rings.Eisenstein.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField

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
* `Eisenstein.instFieldModTwo`, `Eisenstein.algEquivGaloisField` — `ℤ[ω]/2` is
  not merely *a* four-element field with no zero divisors: it **is** `𝔽₄`, as an
  explicit isomorphism onto `GaloisField 2 2`. That is the precise content of
  `2` being INERT rather than split, and it is what makes "odd" and "unit" the
  same predicate mod `2^w`, hence why `ℤ[ω]/2^w` is a local ring with maximal
  ideal `(2)`.
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

/-! ## `ℤ[ω]/2` is `𝔽₄`

The three facts above say `ℤ[ω]/2` is a commutative ring with four elements in
which every nonzero element is invertible. That makes it a field of order `4`,
and finite fields of equal cardinality are isomorphic, so it is `𝔽₄` — which
`GaloisField 2 2` denotes. Below, that identification is made explicit.

The inverse is computable and needs no search: the multiplicative group of a
four-element field has order `3`, so `x³ = 1` for `x ≠ 0` and therefore
`x⁻¹ = x²`. -/

/-- Inversion in `ℤ[ω]/2`. The unit group has order `3`, so squaring inverts. -/
def invTwo (x : Eisenstein (ZMod 2)) : Eisenstein (ZMod 2) := x ^ 2

/-- Squaring really does invert: `x · x² = x³ = 1` for every nonzero `x`. -/
theorem mul_invTwo (x : Eisenstein (ZMod 2)) (hx : x ≠ 0) : x * invTwo x = 1 := by
  revert x; decide

/-- **`ℤ[ω]/2` is a field.** Computable: the inverse is squaring, not a search. -/
instance instFieldModTwo : Field (Eisenstein (ZMod 2)) :=
  { instCommRing with
    inv := invTwo
    exists_pair_ne := ⟨0, 1, by decide⟩
    mul_inv_cancel := mul_invTwo
    inv_zero := by decide
    nnqsmul := _
    qsmul := _ }

/-- Its cardinality is `2² = 4`, in the shape the classification wants. -/
theorem card_mod_two_eq_pow : Fintype.card (Eisenstein (ZMod 2)) = 2 ^ 2 := by
  rw [card_mod_two]; norm_num

/-- **`ℤ[ω]/2 ≅ 𝔽₄`.** A finite field is determined up to isomorphism by its
cardinality, so the four-element field `ℤ[ω]/2` is `GaloisField 2 2`, Mathlib's
`𝔽₄`. The isomorphism is one of `ZMod 2`-algebras, so it respects the coefficient
embedding as well as the ring structure.

This is the precise statement that `2` is INERT in `ℤ[ω]`: were `2` split, the
quotient would be `𝔽₂ × 𝔽₂`, which has four elements but zero divisors and is
not a field. The `𝔽₄`-ness is exactly what fails in that case, and it is what the
rest of the development uses when it treats "odd" and "unit" as the same
predicate.

Noncomputable because the classification produces the isomorphism by choice; the
field structure itself (`instFieldModTwo`) stays computable. -/
noncomputable def algEquivGaloisField :
    Eisenstein (ZMod 2) ≃ₐ[ZMod 2] GaloisField 2 2 :=
  GaloisField.algEquivGaloisFieldOfFintype 2 2 card_mod_two_eq_pow

/-- `ℤ[ω]/2` and `𝔽₄` are isomorphic as rings. -/
theorem nonempty_ringEquiv_galoisField :
    Nonempty (Eisenstein (ZMod 2) ≃+* GaloisField 2 2) :=
  ⟨algEquivGaloisField.toRingEquiv⟩

end CompElliptic.Rings.Eisenstein
