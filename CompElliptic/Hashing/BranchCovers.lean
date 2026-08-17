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
-/

namespace CompElliptic.Hashing

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

end SSWUParams

end CompElliptic.Hashing
