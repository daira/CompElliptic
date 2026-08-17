/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.FibreBound

/-!
# The branch covers of the simplified SWU mapping

Away from the exceptional input, the simplified SWU mapping offers two
candidate abscissae `x₁ u` and `x₂ u`, and outputs a point over whichever one
makes the curve equation `g x = x³ + A·x + B` a square. This file gives each
branch its hyperelliptic model: the curve equation at the branch abscissa,
cleared of denominators. Writing `ta = (Z·u²)² + Z·u²`, both branches share
the degree-12 core

`Φ(u) = B²·(ta + 1)³ + A³·ta²`   (`phiCore`),

and the two models are `W² = d_j·(Z·u²+1)·Φ(u)` (`model1`, `model2`) with
twist constants `d₁ = -A³·B·Z³` and `d₂ = -A³·B` (`twist1`, `twist2`). The
main identities `model1_eq` and `model2_eq` state that the model value is
the curve equation at the branch abscissa times the square of an explicit
scaling (`scale1`, `scale2`). `g_x2_eq` is the branch dichotomy in algebraic
form: `g (x₂ u) = (Z·u²)³ · g (x₁ u)`.

The notation follows `design/weil-constant-derivation.md` §2, which derives
the Weil character-sum bound for the deployed mappings from these models;
formal consumption of that bound is tracked at
<https://github.com/daira/CompElliptic/issues/28>.

On a field where `-1` is a square (both Pasta base fields), `Z·u² + 1` never
vanishes (`Zuu_add_one_ne_zero`), so the scalings vanish only at `u = 0` and
the models are nonzero wherever `Φ` is.

`modelPoints1`/`modelPoints2` collect each cover's rational points in model
coordinates, as a `Finset ((F × F) ⊕ Bool)`. `Sum.inl` carries an affine
model point `(u, W)`, so each set holds the affine solutions of
`W² = H_j(u)`. The models have even degree 14, so each smooth model also
has two points at infinity; they are rational —and included, as
`Sum.inr false` and `Sum.inr true`— exactly when the leading square class
`d_j·Z` is a square.

The `Bool` is a bare tag: the two points at infinity
are the conjugate pair of places over `u = ∞`, swapped by the hyperelliptic
involution, and the formalization fixes no correspondence between the tags
and the places. Only the pair's cardinality and its common image `𝒪` enter
any statement, so every result is invariant under swapping the tags, and
the cited input's faithfulness needs only some bijection — which either
labelling provides.

`cover1Map`/`cover2Map` send a model point to the curve:
* an affine point over `u ≠ 0` goes to the point with abscissa `x_j u` and
  ordinate `W / s_j u`;
* everything else goes to `𝒪`: the `u = 0` fibre, the points at infinity,
  and junk values off the model.

On the parameter range the derivation targets (`-A·B` a nonsquare, which
holds at the deployed instantiations) the points at infinity genuinely map
to `𝒪`. The correspondence theorems carry that hypothesis.
-/

namespace CompElliptic.Hashing

open Finset CompElliptic.CurveForms.ShortWeierstrass

namespace SSWUParams

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The first branch abscissa `x₁ u = B·(ta + 1) / (A·(-ta))`, the value
`(G.mapXYUpToSign u).1` takes when the square-root split chooses the first
branch (and `ta ≠ 0`). -/
def x1 (G : SSWUParams F) (u : F) : F :=
  G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1)
    / (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))

/-- The second branch abscissa `x₂ u = Z·u² · x₁ u`. -/
def x2 (G : SSWUParams F) (u : F) : F := G.Z * u^2 * G.x1 u

/-- The shared degree-12 core `Φ(u) = B²·(ta + 1)³ + A³·ta²` of the two
branch models, with `ta = (Z·u²)² + Z·u²`. -/
def phiCore (G : SSWUParams F) (u : F) : F :=
  G.E.B^2 * (((G.Z * u^2)^2 + G.Z * u^2) + 1)^3
    + G.E.A^3 * ((G.Z * u^2)^2 + G.Z * u^2)^2

/-- The twist constant `d₁ = -A³·B·Z³` of the first branch model. -/
def twist1 (G : SSWUParams F) : F := -(G.E.A^3 * G.E.B * G.Z^3)

/-- The twist constant `d₂ = -A³·B` of the second branch model. `twist1` and
`twist2` differ by `Z³`, which is `Z` times a square: the two models are
quadratic twists of one another by the nonsquare `Z`. -/
def twist2 (G : SSWUParams F) : F := -(G.E.A^3 * G.E.B)

/-- The first branch model `H₁(u) = d₁·(Z·u²+1)·Φ(u)`. -/
def model1 (G : SSWUParams F) (u : F) : F :=
  G.twist1 * (G.Z * u^2 + 1) * G.phiCore u

/-- The second branch model `H₂(u) = d₂·(Z·u²+1)·Φ(u)`. -/
def model2 (G : SSWUParams F) (u : F) : F :=
  G.twist2 * (G.Z * u^2 + 1) * G.phiCore u

/-- The scaling `s₁ u = A³·Z³·u³·(Z·u²+1)²` relating the first branch's
ordinate to the model coordinate: `W = y·s₁ u` on the first cover. -/
def scale1 (G : SSWUParams F) (u : F) : F :=
  G.E.A^3 * G.Z^3 * u^3 * (G.Z * u^2 + 1)^2

/-- The scaling `s₂ u = A³·(Z·u²+1)²` relating the second branch's ordinate
to the model coordinate: `W = y·s₂ u` on the second cover. -/
def scale2 (G : SSWUParams F) (u : F) : F :=
  G.E.A^3 * (G.Z * u^2 + 1)^2

/-- On a field where `-1` is a square, `Z·u² + 1` never vanishes: a root
would exhibit the nonsquare `Z` as `-1` times a square. This is the
exceptional-set lemma of the derivation: the `t = -1` fibre of the branch
covers has no rational points. -/
theorem Zuu_add_one_ne_zero (G : SSWUParams F) (hsq : IsSquare (-1 : F))
    (u : F) : G.Z * u^2 + 1 ≠ 0 := by
  intro h
  rcases eq_or_ne u 0 with rfl | hu
  · simp at h
  · obtain ⟨s, hs⟩ := hsq
    have hZu : G.Z * u^2 = -1 := by linear_combination h
    refine G.Z_nonsquare ⟨s/u, ?_⟩
    rw [div_mul_div_comm, show u*u = u^2 from (pow_two u).symm]
    exact (eq_div_iff (pow_ne_zero 2 hu)).mpr (hZu.trans hs)

/-- `Φ(0) = B²`: the core is nonzero at `u = 0`. -/
theorem phiCore_zero (G : SSWUParams F) : G.phiCore 0 = G.E.B^2 := by
  simp [phiCore]

/-- The first model at `u = 0` is `d₁·B²`, in the square class of `d₁`. -/
theorem model1_zero (G : SSWUParams F) : G.model1 0 = G.twist1 * G.E.B^2 := by
  simp [model1, phiCore_zero]

/-- The second model at `u = 0` is `d₂·B²`, in the square class of `d₂`. -/
theorem model2_zero (G : SSWUParams F) : G.model2 0 = G.twist2 * G.E.B^2 := by
  simp [model2, phiCore_zero]

/-- The first scaling vanishes exactly at `u = 0` (on a field where `-1` is
a square). -/
theorem scale1_ne_zero (G : SSWUParams F) (hsq : IsSquare (-1 : F)) {u : F}
    (hu : u ≠ 0) : G.scale1 u ≠ 0 := by
  unfold scale1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 G.A_nonzero)
    (pow_ne_zero 3 G.Z_nonzero)) (pow_ne_zero 3 hu))
    (pow_ne_zero 2 (G.Zuu_add_one_ne_zero hsq u))

/-- The second scaling never vanishes (on a field where `-1` is a square). -/
theorem scale2_ne_zero (G : SSWUParams F) (hsq : IsSquare (-1 : F)) (u : F) :
    G.scale2 u ≠ 0 := by
  unfold scale2
  exact mul_ne_zero (pow_ne_zero 3 G.A_nonzero)
    (pow_ne_zero 2 (G.Zuu_add_one_ne_zero hsq u))

section ClearedIdentities

variable (G : SSWUParams F)

/-- The defining equation of `x₁ u`, cleared of its denominator:
`x₁ u · (A·(-ta)) = B·(ta + 1)`. -/
theorem x1_mul_den (hsq : IsSquare (-1 : F)) {u : F} (hu : u ≠ 0) :
    G.x1 u * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))
      = G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1) := by
  have hden : G.E.A * -((G.Z * u^2)^2 + G.Z * u^2) ≠ 0 :=
    mul_ne_zero G.A_nonzero
      (neg_ne_zero.mpr (G.ta_ne_zero_of_u_ne_zero hsq hu))
  unfold x1
  exact div_mul_cancel₀ _ hden

/-- **The first branch model identity**: the curve equation at `x₁ u`, times
the square of the scaling `s₁ u`, is the model value `H₁(u)`. Away from
`u = 0` the scaling is nonzero, so `H₁(u)` and `g (x₁ u)` are in the same
square class. -/
theorem model1_eq (hsq : IsSquare (-1 : F)) {u : F} (hu : u ≠ 0) :
    ((G.x1 u)^3 + G.E.A * G.x1 u + G.E.B) * (G.scale1 u)^2 = G.model1 u := by
  have hden : G.E.A * -((G.Z * u^2)^2 + G.Z * u^2) ≠ 0 :=
    mul_ne_zero G.A_nonzero
      (neg_ne_zero.mpr (G.ta_ne_zero_of_u_ne_zero hsq hu))
  have hX := G.x1_mul_den hsq hu
  unfold scale1 model1 twist1 phiCore
  refine mul_left_cancel₀ (pow_ne_zero 3 hden) ?_
  linear_combination ((G.E.A^3 * G.Z^3 * u^3 * (G.Z * u^2 + 1)^2)^2 *
    ((G.x1 u * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2)))^2
      + G.x1 u * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))
          * (G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))
      + (G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))^2
      + G.E.A * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^2)) * hX

/-- **The second branch model identity**: the curve equation at `x₂ u`, times
the square of the scaling `s₂ u`, is the model value `H₂(u)`. The scaling is
nowhere zero, so `H₂(u)` and `g (x₂ u)` are in the same square class at every
`u ≠ 0`. -/
theorem model2_eq (hsq : IsSquare (-1 : F)) {u : F} (hu : u ≠ 0) :
    ((G.x2 u)^3 + G.E.A * G.x2 u + G.E.B) * (G.scale2 u)^2 = G.model2 u := by
  have hden : G.E.A * -((G.Z * u^2)^2 + G.Z * u^2) ≠ 0 :=
    mul_ne_zero G.A_nonzero
      (neg_ne_zero.mpr (G.ta_ne_zero_of_u_ne_zero hsq hu))
  have hX := G.x1_mul_den hsq hu
  unfold x2 scale2 model2 twist2 phiCore
  refine mul_left_cancel₀ (pow_ne_zero 3 hden) ?_
  linear_combination ((G.E.A^3 * (G.Z * u^2 + 1)^2)^2 *
    ((G.Z * u^2)^3
        * ((G.x1 u * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2)))^2
          + G.x1 u * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))
              * (G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))
          + (G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))^2)
      + G.E.A * (G.Z * u^2)
          * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^2)) * hX

/-- **The branch dichotomy, in algebraic form**: the curve equation at `x₂ u`
is `(Z·u²)³` times the curve equation at `x₁ u`. The factor
`(Z·u²)³ = Z·(Z·u³)²` is `Z` times a nonzero square for `u ≠ 0`, so exactly
one of the two curve-equation values is a square whenever both are nonzero. -/
theorem g_x2_eq (hsq : IsSquare (-1 : F)) {u : F} (hu : u ≠ 0) :
    (G.x2 u)^3 + G.E.A * G.x2 u + G.E.B
      = (G.Z * u^2)^3 * ((G.x1 u)^3 + G.E.A * G.x1 u + G.E.B) := by
  have hden : G.E.A * -((G.Z * u^2)^2 + G.Z * u^2) ≠ 0 :=
    mul_ne_zero G.A_nonzero
      (neg_ne_zero.mpr (G.ta_ne_zero_of_u_ne_zero hsq hu))
  have hX := G.x1_mul_den hsq hu
  unfold x2
  refine mul_left_cancel₀ (pow_ne_zero 3 hden) ?_
  linear_combination (G.E.A * (G.Z * u^2)
    * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^2 * (1 - (G.Z * u^2)^2)) * hX

end ClearedIdentities

section ModelPoints

variable (G : SSWUParams F)

include G in
/-- A nonsquare exists only in odd characteristic: in characteristic 2 every
element of a finite field is a square, against `Z_nonsquare`. -/
theorem ringChar_ne_two : ringChar F ≠ 2 := fun h =>
  G.Z_nonsquare (FiniteField.isSquare_of_char_two h G.Z)

/-- The first twist constant is nonzero. -/
theorem twist1_ne_zero : G.twist1 ≠ 0 := by
  unfold twist1
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 G.A_nonzero)
    G.E.B_nonzero) (pow_ne_zero 3 G.Z_nonzero))

/-- The second twist constant is nonzero. -/
theorem twist2_ne_zero : G.twist2 ≠ 0 := by
  unfold twist2
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 G.A_nonzero) G.E.B_nonzero)

/-- The first model never vanishes. At `u = 0` its value is `d₁·B² ≠ 0`. At
`u ≠ 0`, a zero would put the zero-ordinate point `(x₁ u, 0)` on the curve,
which the no-2-torsion hypothesis `hy0` excludes. So the model's rational
points never have `W = 0`: the merged boundary case of the derivation is
empty. -/
theorem model1_ne_zero (hsq : IsSquare (-1 : F))
    (hy0 : ∀ x : F, ¬ OnCurve G.E.A G.E.B (x, 0)) (u : F) :
    G.model1 u ≠ 0 := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [G.model1_zero]
    exact mul_ne_zero G.twist1_ne_zero (pow_ne_zero 2 G.E.B_nonzero)
  · intro h
    rcases mul_eq_zero.mp ((G.model1_eq hsq hu).trans h) with hg | hs
    · exact hy0 (G.x1 u) (by simpa [OnCurve] using hg.symm)
    · exact pow_ne_zero 2 (G.scale1_ne_zero hsq hu) hs

/-- The second model never vanishes; see `model1_ne_zero`. -/
theorem model2_ne_zero (hsq : IsSquare (-1 : F))
    (hy0 : ∀ x : F, ¬ OnCurve G.E.A G.E.B (x, 0)) (u : F) :
    G.model2 u ≠ 0 := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [G.model2_zero]
    exact mul_ne_zero G.twist2_ne_zero (pow_ne_zero 2 G.E.B_nonzero)
  · intro h
    rcases mul_eq_zero.mp ((G.model2_eq hsq hu).trans h) with hg | hs
    · exact hy0 (G.x2 u) (by simpa [OnCurve] using hg.symm)
    · exact pow_ne_zero 2 (G.scale2_ne_zero hsq u) hs

/-- The point set of the first cover, in model coordinates: the affine
solutions of `W² = H₁(u)`, plus the two points at infinity —tagged by a
bare `Bool`, since neither has a distinguished coordinate— exactly when
the leading square class `d₁·Z` is a square. -/
def modelPoints1 : Finset ((F × F) ⊕ Bool) :=
  ((univ.filter fun p : F × F => p.2^2 = G.model1 p.1).image Sum.inl)
    ∪ (if IsSquare (G.twist1 * G.Z) then {Sum.inr false, Sum.inr true} else ∅)

/-- The point set of the second cover, in model coordinates; see
`modelPoints1`. -/
def modelPoints2 : Finset ((F × F) ⊕ Bool) :=
  ((univ.filter fun p : F × F => p.2^2 = G.model2 p.1).image Sum.inl)
    ∪ (if IsSquare (G.twist2 * G.Z) then {Sum.inr false, Sum.inr true} else ∅)

/-- The affine members of the first cover's point set: `(u, W)` is in the
set exactly when it solves the model, `W² = H₁(u)`. -/
@[simp] theorem mem_modelPoints1_inl {p : F × F} :
    Sum.inl p ∈ G.modelPoints1 ↔ p.2^2 = G.model1 p.1 := by
  unfold modelPoints1
  simp only [mem_union, mem_image, mem_filter, mem_univ, true_and,
    Sum.inl.injEq]
  constructor
  · rintro (⟨q, hq, rfl⟩ | hbad)
    · exact hq
    · exfalso; revert hbad; split_ifs <;> simp
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

/-- The affine members of the second cover's point set: `(u, W)` is in the
set exactly when it solves the model, `W² = H₂(u)`. -/
@[simp] theorem mem_modelPoints2_inl {p : F × F} :
    Sum.inl p ∈ G.modelPoints2 ↔ p.2^2 = G.model2 p.1 := by
  unfold modelPoints2
  simp only [mem_union, mem_image, mem_filter, mem_univ, true_and,
    Sum.inl.injEq]
  constructor
  · rintro (⟨q, hq, rfl⟩ | hbad)
    · exact hq
    · exfalso; revert hbad; split_ifs <;> simp
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

/-- The infinite members of the first cover's point set: both points at
infinity are present exactly when the leading square class `d₁·Z` is a
square. -/
@[simp] theorem mem_modelPoints1_inr {b : Bool} :
    Sum.inr b ∈ G.modelPoints1 ↔ IsSquare (G.twist1 * G.Z) := by
  unfold modelPoints1
  simp only [mem_union, mem_image]
  constructor
  · rintro (⟨q, _, hq⟩ | h)
    · exact absurd hq (by simp)
    · revert h; split_ifs with hsq <;> intro h
      · exact hsq
      · simp at h
  · intro hsq
    refine Or.inr ?_
    rw [if_pos hsq]
    rcases b <;> simp

/-- The infinite members of the second cover's point set: both points at
infinity are present exactly when the leading square class `d₂·Z` is a
square. -/
@[simp] theorem mem_modelPoints2_inr {b : Bool} :
    Sum.inr b ∈ G.modelPoints2 ↔ IsSquare (G.twist2 * G.Z) := by
  unfold modelPoints2
  simp only [mem_union, mem_image]
  constructor
  · rintro (⟨q, _, hq⟩ | h)
    · exact absurd hq (by simp)
    · revert h; split_ifs with hsq <;> intro h
      · exact hsq
      · simp at h
  · intro hsq
    refine Or.inr ?_
    rw [if_pos hsq]
    rcases b <;> simp

/-- The covering map of the first cover, in model coordinates. An affine
model point over `u ≠ 0` goes to the curve point with abscissa `x₁ u` and
ordinate `W / s₁ u`. Everything else goes to `𝒪`: the `u = 0` fibre, the
points at infinity, and junk values off the model. The `𝒪` images are
genuine on the parameter range the correspondence theorems target (`-A·B`
a nonsquare). There this cover's rational boundary points sit over `u = 0`,
where the abscissa has a pole. -/
def cover1Map (hsq : IsSquare (-1 : F)) : (F × F) ⊕ Bool → SWPoint G.E
  | .inl p =>
    if h : p.1 ≠ 0 ∧ p.2^2 = G.model1 p.1 then
      ⟨G.x1 p.1, p.2 / G.scale1 p.1, Or.inl (by
        show (p.2 / G.scale1 p.1)^2 = (G.x1 p.1)^3 + G.E.A * G.x1 p.1 + G.E.B
        rw [div_pow, h.2, ← G.model1_eq hsq h.1,
          mul_div_cancel_right₀ _ (pow_ne_zero 2 (G.scale1_ne_zero hsq h.1))])⟩
    else 0
  | .inr _ => 0

/-- The covering map of the second cover; see `cover1Map`. On the targeted
parameter range this cover's rational boundary points are at infinity, where
the abscissa has a pole. -/
def cover2Map (hsq : IsSquare (-1 : F)) : (F × F) ⊕ Bool → SWPoint G.E
  | .inl p =>
    if h : p.1 ≠ 0 ∧ p.2^2 = G.model2 p.1 then
      ⟨G.x2 p.1, p.2 / G.scale2 p.1, Or.inl (by
        show (p.2 / G.scale2 p.1)^2 = (G.x2 p.1)^3 + G.E.A * G.x2 p.1 + G.E.B
        rw [div_pow, h.2, ← G.model2_eq hsq h.1,
          mul_div_cancel_right₀ _ (pow_ne_zero 2 (G.scale2_ne_zero hsq p.1))])⟩
    else 0
  | .inr _ => 0

end ModelPoints

end SSWUParams

/-! ## Counting square roots

The fibre of a model over `u₀` is the solution set of `W² = H(u₀)`; these
helpers count it. In odd characteristic, a nonzero square has exactly the
two roots `±r`, and a nonsquare has none. -/

/-- The solutions of `W² = a` for a nonzero `a` with a root `r`: exactly
`{r, -r}`. -/
theorem filter_sq_eq_pair {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {a r : F} (hr : r^2 = a) :
    (univ.filter fun W : F => W^2 = a) = {r, -r} := by
  ext W
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  rw [← hr, sq_eq_sq_iff_eq_or_eq_neg]

/-- In odd characteristic, a nonzero square has exactly two square roots. -/
theorem filter_sq_card_of_isSquare {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {a : F} (hchar : ringChar F ≠ 2) (ha : a ≠ 0)
    (hsq : IsSquare a) :
    (univ.filter fun W : F => W^2 = a).card = 2 := by
  obtain ⟨r, hr⟩ := hsq
  have hr2 : r^2 = a := by rw [sq]; exact hr.symm
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact ha (by rw [← hr2]; ring)
  rw [filter_sq_eq_pair hr2]
  refine card_pair_eq_two_iff.mpr fun h => hr0 ?_
  exact (Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp h.symm

/-- A nonsquare has no square roots. -/
theorem filter_sq_eq_empty {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {a : F} (hns : ¬ IsSquare a) :
    (univ.filter fun W : F => W^2 = a) = ∅ := by
  rw [filter_eq_empty_iff]
  intro W _
  exact fun hW => hns ⟨W, by rw [← hW]; ring⟩

/-- A nonsquare times a nonzero square is a nonsquare. -/
theorem not_isSquare_mul_sq {F : Type*} [Field F] {z c : F}
    (hz : ¬ IsSquare z) (hc : c ≠ 0) : ¬ IsSquare (z * c^2) := by
  rintro ⟨t, ht⟩
  refine hz ⟨t/c, ?_⟩
  field_simp
  linear_combination ht

namespace SSWUParams

/-! ## The fibre over a nonzero input

Fix `u ≠ 0`. Exactly one branch's curve-equation value `g (x_j u)` is a
nonzero square, and the mapping outputs a point over that branch's abscissa
(`map_x`). On the square branch the model fibre `W² = H_j(u)` has the two
roots `±(map u).y · s_j u`, whose covering-map images are `map u` and
`-(map u)`; on the other branch the fibre is empty. `fibre_sum` packages
this: summed over both covers, any function of the images contributes
exactly `φ (map u) + φ (-(map u))`. -/

section FibreSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (G : SSWUParams F)

/-- The candidate ordinate squares to the curve equation at the output
abscissa: the on-curve fact `onCurve_mapXY`, restated through `map`. -/
theorem map_y_sq (u : F) :
    ((G.map u).y)^2 = ((G.map u).x)^3 + G.E.A * (G.map u).x + G.E.B :=
  G.onCurve_mapXY u

/-- **The branch selection.** For `u ≠ 0`, the mapping outputs the branch
whose curve-equation value is a square: the abscissa is `x₁ u` when
`g (x₁ u)` is a square, else `x₂ u`. The square-root split tests exactly
`IsSquare (U / xdiv³)`, and `U / xdiv³ = g (x₁ u)`. -/
theorem map_x (hsq : IsSquare (-1 : F)) {u : F} (hu : u ≠ 0) :
    (G.map u).x
      = if IsSquare ((G.x1 u)^3 + G.E.A * G.x1 u + G.E.B) then G.x1 u
        else G.x2 u := by
  have hta : (G.Z * u^2)^2 + G.Z * u^2 ≠ 0 := G.ta_ne_zero_of_u_ne_zero hsq hu
  have hden : G.E.A * -((G.Z * u^2)^2 + G.Z * u^2) ≠ 0 :=
    mul_ne_zero G.A_nonzero (neg_ne_zero.mpr hta)
  have hX := G.x1_mul_den hsq hu
  -- The ratio the square-root split tests is the curve equation at `x₁ u`.
  have hUdiv : ((G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))^2
        + G.E.A * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^2)
          * (G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))
        + G.E.B * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^3
      = ((G.x1 u)^3 + G.E.A * G.x1 u + G.E.B)
          * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^3 := by
    linear_combination (-((G.x1 u * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2)))^2
      + G.x1 u * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))
          * (G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))
      + (G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))^2
      + G.E.A * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^2)) * hX
  have hbiff : (sqrtRatio G.d G.lam
        (((G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))^2
            + G.E.A * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^2)
              * (G.E.B * (((G.Z * u^2)^2 + G.Z * u^2) + 1))
            + G.E.B * (G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^3)
        ((G.E.A * -((G.Z * u^2)^2 + G.Z * u^2))^3)).2 = true
      ↔ IsSquare ((G.x1 u)^3 + G.E.A * G.x1 u + G.E.B) := by
    rw [sqrtRatio_true_iff, hUdiv,
      mul_div_cancel_right₀ _ (pow_ne_zero 3 hden)]
  show (G.mapXYUpToSign u).1 = _
  simp only [mapXYUpToSign]
  rw [if_neg hta]
  by_cases hgs : IsSquare ((G.x1 u)^3 + G.E.A * G.x1 u + G.E.B)
  · rw [if_pos hgs, hbiff.mpr hgs, if_pos rfl]
    rfl
  · rw [if_neg hgs, Bool.eq_false_iff.mpr fun h => hgs (hbiff.mp h),
      if_neg (by simp)]
    unfold x2 x1
    ring

/-- The first covering map's abscissa at a genuine affine model point. -/
theorem cover1Map_inl_x (hsq : IsSquare (-1 : F)) {u W : F} (hu : u ≠ 0)
    (hW : W^2 = G.model1 u) :
    (G.cover1Map hsq (Sum.inl (u, W))).x = G.x1 u := by
  simp [cover1Map, hu, hW]

/-- The first covering map's ordinate at a genuine affine model point. -/
theorem cover1Map_inl_y (hsq : IsSquare (-1 : F)) {u W : F} (hu : u ≠ 0)
    (hW : W^2 = G.model1 u) :
    (G.cover1Map hsq (Sum.inl (u, W))).y = W / G.scale1 u := by
  simp [cover1Map, hu, hW]

/-- The second covering map's abscissa at a genuine affine model point. -/
theorem cover2Map_inl_x (hsq : IsSquare (-1 : F)) {u W : F} (hu : u ≠ 0)
    (hW : W^2 = G.model2 u) :
    (G.cover2Map hsq (Sum.inl (u, W))).x = G.x2 u := by
  simp [cover2Map, hu, hW]

/-- The second covering map's ordinate at a genuine affine model point. -/
theorem cover2Map_inl_y (hsq : IsSquare (-1 : F)) {u W : F} (hu : u ≠ 0)
    (hW : W^2 = G.model2 u) :
    (G.cover2Map hsq (Sum.inl (u, W))).y = W / G.scale2 u := by
  simp [cover2Map, hu, hW]

/-- **The fibre over a nonzero input, summed.** Over `u ≠ 0`, the two
covers' affine model fibres together contribute the images `map u` and
`-(map u)`, each once: the square branch's two roots supply them, and the
other branch's fibre is empty. -/
theorem fibre_sum (hsq : IsSquare (-1 : F))
    (hy0 : ∀ x : F, ¬ OnCurve G.E.A G.E.B (x, 0))
    {M : Type*} [AddCommMonoid M] (φ : SWPoint G.E → M) {u : F} (hu : u ≠ 0) :
    (∑ W ∈ univ.filter fun W : F => W^2 = G.model1 u,
        φ (G.cover1Map hsq (Sum.inl (u, W))))
      + (∑ W ∈ univ.filter fun W : F => W^2 = G.model2 u,
        φ (G.cover2Map hsq (Sum.inl (u, W))))
      = φ (G.map u) + φ (-(G.map u)) := by
  have hchar := G.ringChar_ne_two
  have hH1 := G.model1_ne_zero hsq hy0 u
  have hH2 := G.model2_ne_zero hsq hy0 u
  have hg1 : (G.x1 u)^3 + G.E.A * G.x1 u + G.E.B ≠ 0 := fun h =>
    hH1 (by rw [← G.model1_eq hsq hu, h, zero_mul])
  have hg2 : (G.x2 u)^3 + G.E.A * G.x2 u + G.E.B ≠ 0 := fun h =>
    hH2 (by rw [← G.model2_eq hsq hu, h, zero_mul])
  have hu3 : G.Z * u^3 ≠ 0 := mul_ne_zero G.Z_nonzero (pow_ne_zero 3 hu)
  by_cases hgs : IsSquare ((G.x1 u)^3 + G.E.A * G.x1 u + G.E.B)
  · -- Branch 1 carries the square; branch 2's fibre is empty.
    have hx : (G.map u).x = G.x1 u := by rw [G.map_x hsq hu, if_pos hgs]
    have hy2 : ((G.map u).y)^2 = (G.x1 u)^3 + G.E.A * G.x1 u + G.E.B := by
      rw [← hx]; exact G.map_y_sq u
    have hyne : (G.map u).y ≠ 0 := fun h => hg1 (by rw [← hy2, h]; ring)
    have hr2 : ((G.map u).y * G.scale1 u)^2 = G.model1 u := by
      rw [mul_pow, hy2, G.model1_eq hsq hu]
    have hrne : (G.map u).y * G.scale1 u ≠ 0 :=
      mul_ne_zero hyne (G.scale1_ne_zero hsq hu)
    have hns2 : ¬ IsSquare (G.model2 u) := by
      obtain ⟨t, ht⟩ := hgs
      have ht0 : t ≠ 0 := fun h => hg1 (by rw [ht, h, mul_zero])
      have hM : G.model2 u = G.Z * (G.Z * u^3 * t * G.scale2 u)^2 := by
        rw [← G.model2_eq hsq hu, G.g_x2_eq hsq hu, ht]; ring
      rw [hM]
      exact not_isSquare_mul_sq G.Z_nonsquare
        (mul_ne_zero (mul_ne_zero hu3 ht0) (G.scale2_ne_zero hsq u))
    rw [filter_sq_eq_empty hns2, Finset.sum_empty, _root_.add_zero,
      filter_sq_eq_pair hr2, Finset.sum_pair fun h => hrne
        ((Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp h.symm)]
    have hP : G.cover1Map hsq (Sum.inl (u, (G.map u).y * G.scale1 u))
        = G.map u := by
      refine SWPoint.ext_pair ?_
      rw [G.cover1Map_inl_x hsq hu hr2, G.cover1Map_inl_y hsq hu hr2, hx,
        mul_div_cancel_right₀ _ (G.scale1_ne_zero hsq hu)]
    have hQ : G.cover1Map hsq (Sum.inl (u, -((G.map u).y * G.scale1 u)))
        = -(G.map u) := by
      have hr2' : (-((G.map u).y * G.scale1 u))^2 = G.model1 u := by
        rw [neg_sq, hr2]
      refine SWPoint.ext_pair ?_
      rw [G.cover1Map_inl_x hsq hu hr2', G.cover1Map_inl_y hsq hu hr2',
        SWPoint.neg_x, SWPoint.neg_y, hx, neg_div,
        mul_div_cancel_right₀ _ (G.scale1_ne_zero hsq hu)]
    rw [hP, hQ]
  · -- Branch 2 carries the square; branch 1's fibre is empty.
    have hZ3 : ¬ IsSquare ((G.Z * u^2)^3) := by
      have h : (G.Z * u^2)^3 = G.Z * (G.Z * u^3)^2 := by ring
      rw [h]
      exact not_isSquare_mul_sq G.Z_nonsquare hu3
    have hgs2 : IsSquare ((G.x2 u)^3 + G.E.A * G.x2 u + G.E.B) := by
      rw [G.g_x2_eq hsq hu]
      exact isSquare_mul_of_not_isSquare hZ3 hgs
    have hx : (G.map u).x = G.x2 u := by rw [G.map_x hsq hu, if_neg hgs]
    have hy2 : ((G.map u).y)^2 = (G.x2 u)^3 + G.E.A * G.x2 u + G.E.B := by
      rw [← hx]; exact G.map_y_sq u
    have hyne : (G.map u).y ≠ 0 := fun h => hg2 (by rw [← hy2, h]; ring)
    have hr2 : ((G.map u).y * G.scale2 u)^2 = G.model2 u := by
      rw [mul_pow, hy2, G.model2_eq hsq hu]
    have hrne : (G.map u).y * G.scale2 u ≠ 0 :=
      mul_ne_zero hyne (G.scale2_ne_zero hsq u)
    have hns1 : ¬ IsSquare (G.model1 u) := by
      rw [← G.model1_eq hsq hu]
      exact not_isSquare_mul_sq hgs (G.scale1_ne_zero hsq hu)
    rw [filter_sq_eq_empty hns1, Finset.sum_empty, _root_.zero_add,
      filter_sq_eq_pair hr2, Finset.sum_pair fun h => hrne
        ((Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp h.symm)]
    have hP : G.cover2Map hsq (Sum.inl (u, (G.map u).y * G.scale2 u))
        = G.map u := by
      refine SWPoint.ext_pair ?_
      rw [G.cover2Map_inl_x hsq hu hr2, G.cover2Map_inl_y hsq hu hr2, hx,
        mul_div_cancel_right₀ _ (G.scale2_ne_zero hsq u)]
    have hQ : G.cover2Map hsq (Sum.inl (u, -((G.map u).y * G.scale2 u)))
        = -(G.map u) := by
      have hr2' : (-((G.map u).y * G.scale2 u))^2 = G.model2 u := by
        rw [neg_sq, hr2]
      refine SWPoint.ext_pair ?_
      rw [G.cover2Map_inl_x hsq hu hr2', G.cover2Map_inl_y hsq hu hr2',
        SWPoint.neg_x, SWPoint.neg_y, hx, neg_div,
        mul_div_cancel_right₀ _ (G.scale2_ne_zero hsq u)]
    rw [hP, hQ]

end FibreSum

end SSWUParams

end CompElliptic.Hashing
