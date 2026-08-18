/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.BranchCovers
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Supporting facts for the Weil-constant derivation

The cited steps of `design/weil-constant-derivation.md` —the genus of the
branch covers (§2) and their total ramification (§3)— cannot be stated in
Lean without vocabulary Mathlib does not yet have. Their *inputs* can. This
file proves those inputs, so that the paper proof's checkable algebra is
machine-checked and only the two genuinely geometric steps remain cited
(<https://github.com/daira/CompElliptic/issues/28>; the vocabulary itself
is <https://github.com/daira/CompElliptic/issues/30>).

The genus computation (§2) consumes:
* `phiPoly_squarefree` — the core `Φ` is squarefree, by the design doc's
  own argument: `Φ = φ ∘ ta` for the cubic `φ` (`phiPoly_eq_comp`), `φ` is
  separable (`phiCubic_separable`, by a Bézout certificate whose constant
  is `A³·B²·(4·A³ + 27·B²)` —exactly the standing nonzero quantities—),
  and `Φ` is coprime to each factor of `ta′`;
* `phiPoly_natDegree` and the model degrees — `Φ` has degree 12, and the
  models `H_j` degree 14 with squarefreeness (`model1Poly_squarefree`,
  `model2Poly_squarefree`), which is what the hyperelliptic genus formula
  `g = ⌊(14 - 1)/2⌋ = 6` is applied to (Galbraith, *Mathematics of Public
  Key Cryptography*, ch. 10; Stichtenoth, *Algebraic Function Fields and
  Codes*, 2nd ed., ch. 6).

The ramification argument (§3) consumes:
* `p2Poly_isEisensteinAt` and `p1RecipPoly_isEisensteinAt` — the branch
  quartics over `F[w]` satisfy the classical Eisenstein irreducibility
  criterion (`Polynomial.IsEisensteinAt`) at the ideal `(w)`;
* `eval_g_neg_B_div_A` — `g(-B/A) = -(B/A)³ ≠ 0` (this is why `w` is a
  uniformizer at both points over `w = 0`).

The Eisenstein criterion is that the leading coefficient lies outside the
ideal, every lower coefficient lies inside it, and the constant coefficient
lies outside its square. The cited total-ramification argument relies on
this criterion's transplant to places of function fields (Stichtenoth,
*Algebraic Function Fields and Codes*, 2nd ed., ch. 3; design doc,
Background). The transplant is a statement about any discrete valuation on
the coefficient field — it instantiates the criterion rather than being a
new theorem. Its hypotheses force the polynomial's Newton polygon to be a
single segment from `(0, 1)` to `(n, 0)`, so every root has valuation `1/n`
(Milne, *Algebraic Number Theory*, course notes, ch. 7, Prop. 7.44 —
stated there for characteristic zero, but the argument is
characteristic-free). This yields irreducibility and ramification index
`n` —total ramification— at once. The classical form instantiates this at
`ℤ` localized at a prime; the function-field form instantiates it at the
local ring of a place of the base curve, a uniformizer standing in for
the prime — here `w` itself, by `g_neg_B_div_A_ne_zero`. Our statements
check the coefficient pattern at the polynomial ring `F[w]`; the passage
to the valuation at the two places is part of the cited step.

Everything here is stated over the polynomial rings `F[u]` and `(F[w])[u]`;
the connection from these inputs to genus 6 and to the no-unramified-subcover
condition is the cited part.
-/

namespace CompElliptic.Hashing

open Polynomial

/-- A Bézout identity with a nonzero constant right-hand side witnesses
coprimality: divide through by the constant. -/
theorem isCoprime_of_bezout {F : Type*} [Field F] {p q u v : Polynomial F}
    {c : F} (hc : c ≠ 0) (h : u*p + v*q = C c) : IsCoprime p q := by
  refine ⟨C c⁻¹ * u, C c⁻¹ * v, ?_⟩
  calc C c⁻¹ * u * p + C c⁻¹ * v * q = C c⁻¹ * (u*p + v*q) := by ring
    _ = 1 := by rw [h, ← C_mul, inv_mul_cancel₀ hc, C_1]

namespace SSWUParams

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (G : SSWUParams F)

/-! ## The core `Φ` as a polynomial, and its cubic factor through `ta` -/

/-- The cubic `φ(T) = B²·(T + 1)³ + A³·T²` through which the core factors:
`Φ = φ ∘ ta` (design doc §2, the squarefreeness lemma). -/
noncomputable def phiCubic : Polynomial F :=
  (C G.E.B)^2 * (X + 1)^3 + (C G.E.A)^3 * X^2

/-- The core `Φ(u) = B²·(ta + 1)³ + A³·ta²` as a polynomial in `u`
(`phiCore` is its evaluation). -/
noncomputable def phiPoly : Polynomial F :=
  (C G.E.B)^2 * (G.taPoly + 1)^3 + (C G.E.A)^3 * G.taPoly^2

/-- `Φ` factors through `ta`: `Φ = φ ∘ ta`. -/
theorem phiPoly_eq_comp : G.phiPoly = G.phiCubic.comp G.taPoly := by
  simp only [phiPoly, phiCubic, add_comp, mul_comp, pow_comp, C_comp, X_comp,
    one_comp]

/-- `phiPoly` evaluates to the pointwise core `phiCore`. -/
theorem eval_phiPoly (u : F) : G.phiPoly.eval u = G.phiCore u := by
  simp only [phiPoly, phiCore, taPoly, tPoly, eval_add, eval_mul, eval_pow,
    eval_C, eval_X, eval_one]

/-- `Φ` has degree exactly 12; its leading coefficient is `B²·Z⁶`. -/
theorem phiPoly_natDegree : G.phiPoly.natDegree = 12 := by
  rw [phiPoly, taPoly, tPoly]
  compute_degree!
  exact ⟨G.E.B_nonzero, G.Z_nonzero⟩

/-! ## Separability of the cubic, by Bézout certificate

The cofactors were computed by `xgcd` in `scripts/weil-derivation-checks.sage`;
the identity's constant is `A³·B²·(4·A³ + 27·B²)`, nonzero exactly from the
standing assumptions plus ellipticity. -/

/-- The derivative of the cubic `φ`. -/
theorem phiCubic_derivative :
    G.phiCubic.derivative = 3*(C G.E.B)^2 * (X + 1)^2 + 2*(C G.E.A)^3 * X := by
  simp only [phiCubic, derivative_add, derivative_mul, derivative_pow,
    derivative_C, derivative_X, derivative_one, Nat.cast_ofNat, map_ofNat]
  ring

/-- **The cubic `φ` is separable**, by the Bézout certificate
`s·φ + t·φ′ = A³·B²·(4·A³ + 27·B²)` computed in
`scripts/weil-derivation-checks.sage`: the identity's constant is a product
of exactly the standing nonzero quantities. -/
theorem phiCubic_separable (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    G.phiCubic.Separable := by
  refine isCoprime_of_bezout
    (u := (6*(C G.E.A)^3*(C G.E.B)^2 + 36*(C G.E.B)^4) * X
      + (4*(C G.E.A)^6 + 36*(C G.E.A)^3*(C G.E.B)^2 + 63*(C G.E.B)^4))
    (v := -((2*(C G.E.A)^3*(C G.E.B)^2 + 12*(C G.E.B)^4) * X^2)
      - (2*(C G.E.A)^6 + 18*(C G.E.A)^3*(C G.E.B)^2 + 33*(C G.E.B)^4) * X
      - (3*(C G.E.A)^3*(C G.E.B)^2 + 21*(C G.E.B)^4))
    (c := G.E.A^3 * G.E.B^2 * (4*G.E.A^3 + 27*G.E.B^2))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 G.A_nonzero)
      (pow_ne_zero 2 G.E.B_nonzero)) hdisc) ?_
  have hC : (C (G.E.A^3 * G.E.B^2 * (4*G.E.A^3 + 27*G.E.B^2)) : Polynomial F)
      = (C G.E.A)^3 * (C G.E.B)^2 * (4*(C G.E.A)^3 + 27*(C G.E.B)^2) := by
    simp only [map_mul, map_pow, map_add, map_ofNat]
  rw [phiCubic_derivative, phiCubic, hC]
  ring

/-! ## `Φ` is coprime to the factors of `ta′` -/

/-- The derivative of `ta` factors as `(2·Z·X)·(2·Z·X² + 1)` — the critical
points of `ta` are `u = 0` and the locus `Z·u² = -1/2`. -/
theorem taPoly_derivative :
    G.taPoly.derivative = (2 * C G.Z * X) * (2 * C G.Z * X^2 + 1) := by
  simp only [taPoly, tPoly, derivative_add, derivative_mul, derivative_pow,
    derivative_C, derivative_X, Nat.cast_ofNat, map_ofNat]
  ring

/-- A polynomial with nonzero constant coefficient is coprime to `X`. -/
theorem _root_.CompElliptic.Hashing.isCoprime_X_of_coeff_zero
    {F : Type*} [Field F] {p : Polynomial F} (h : p.coeff 0 ≠ 0) :
    IsCoprime p X := by
  refine isCoprime_of_bezout (u := 1) (v := -p.divX) (c := p.coeff 0) h ?_
  linear_combination -(X_mul_divX_add p)

/-- Nonzero constants are coprime to everything. -/
theorem _root_.CompElliptic.Hashing.isCoprime_C_of_ne_zero
    {F : Type*} [Field F] {p : Polynomial F} {c : F} (hc : c ≠ 0) :
    IsCoprime p (C c) :=
  ⟨0, C c⁻¹, by simp [← C_mul, inv_mul_cancel₀ hc]⟩

/-- `Φ` has constant coefficient `B²`: it is coprime to `X`. This is the
design doc's `φ(ta(0)) = B² ≠ 0` case of the squarefreeness lemma. -/
theorem phiPoly_coeff_zero : G.phiPoly.coeff 0 = G.E.B^2 := by
  rw [coeff_zero_eq_eval_zero, G.eval_phiPoly, G.phiCore_zero]

/-- The even-powers polynomial `Ψ` with `64·Φ = Ψ(2·Z·X² + 1)`: the core,
re-expanded around the second critical locus of `ta`. Its constant term is
the ellipticity `4·A³ + 27·B²` — the design doc's `64·φ(-1/4)`. -/
noncomputable def psiPoly : Polynomial F :=
  (C G.E.B)^2 * X^6 + (4*(C G.E.A)^3 + 9*(C G.E.B)^2) * X^4
    + (27*(C G.E.B)^2 - 8*(C G.E.A)^3) * X^2
    + (4*(C G.E.A)^3 + 27*(C G.E.B)^2)

/-- `Ψ`'s constant coefficient is the ellipticity. -/
theorem psiPoly_coeff_zero :
    G.psiPoly.coeff 0 = 4*G.E.A^3 + 27*G.E.B^2 := by
  rw [coeff_zero_eq_eval_zero]
  simp [psiPoly]

/-- The re-expansion `64·Φ = Ψ(2·Z·X² + 1)`, checked symbolically in
`scripts/weil-derivation-checks.sage`. -/
theorem phiPoly_64_eq :
    64 * G.phiPoly = G.psiPoly.comp (2 * C G.Z * X^2 + 1) := by
  simp only [psiPoly, phiPoly, taPoly, tPoly, add_comp, mul_comp, pow_comp,
    sub_comp, C_comp, X_comp, ofNat_comp, Nat.cast_ofNat]
  ring

/-- `Φ` is coprime to `2·Z·X² + 1`: modulo that factor, `64·Φ` is the
nonzero constant `4·A³ + 27·B²`. This is the design doc's `ta = -1/4` case
of the squarefreeness lemma. -/
theorem phiPoly_isCoprime_snd (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    IsCoprime G.phiPoly (2 * C G.Z * X^2 + 1) := by
  refine isCoprime_of_bezout (u := 64)
    (v := -(G.psiPoly.divX.comp (2 * C G.Z * X^2 + 1)))
    (c := 4*G.E.A^3 + 27*G.E.B^2) hdisc ?_
  have h := X_mul_divX_add G.psiPoly
  rw [G.psiPoly_coeff_zero] at h
  have hcomp : G.psiPoly.comp (2 * C G.Z * X^2 + 1)
      = (2 * C G.Z * X^2 + 1) * G.psiPoly.divX.comp (2 * C G.Z * X^2 + 1)
        + C (4*G.E.A^3 + 27*G.E.B^2) := by
    conv_lhs => rw [← h]
    simp only [add_comp, mul_comp, X_comp, C_comp]
  calc 64 * G.phiPoly + -(G.psiPoly.divX.comp (2 * C G.Z * X^2 + 1))
        * (2 * C G.Z * X^2 + 1)
      = G.psiPoly.comp (2 * C G.Z * X^2 + 1)
        - (2 * C G.Z * X^2 + 1) * G.psiPoly.divX.comp (2 * C G.Z * X^2 + 1)
        := by rw [G.phiPoly_64_eq]; ring
    _ = C (4*G.E.A^3 + 27*G.E.B^2) := by rw [hcomp]; ring

/-! ## `Φ` is squarefree -/

/-- **`Φ` is separable**: its derivative is `(φ′ ∘ ta)·ta′` by the chain
rule, `φ′ ∘ ta` is coprime to `Φ = φ ∘ ta` because the cubic's Bézout
certificate transports along composition, and each factor of `ta′` is
handled by the two critical-value cases. This is the design doc's
squarefreeness lemma (§2), step for step. -/
theorem phiPoly_separable (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    G.phiPoly.Separable := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero G.ringChar_ne_two
  rw [Polynomial.separable_def, G.phiPoly_eq_comp, derivative_comp,
    taPoly_derivative, ← G.phiPoly_eq_comp]
  refine IsCoprime.mul_right (IsCoprime.mul_right ?_ ?_) ?_
  · -- `2·Z·X`: a nonzero constant times `X`, and `Φ(0) = B² ≠ 0`.
    have hconst : (2 : Polynomial F) * C G.Z = C (2 * G.Z) := by
      rw [C_mul, map_ofNat]
    rw [hconst]
    exact IsCoprime.mul_right
      (isCoprime_C_of_ne_zero (mul_ne_zero h2 G.Z_nonzero))
      (isCoprime_X_of_coeff_zero (by
        rw [G.phiPoly_coeff_zero]
        exact pow_ne_zero 2 G.E.B_nonzero))
  · exact G.phiPoly_isCoprime_snd hdisc
  · -- `φ′ ∘ ta`, by transporting the cubic's certificate along `comp ta`.
    rw [G.phiPoly_eq_comp]
    exact IsCoprime.map (G.phiCubic_separable hdisc)
      (eval₂RingHom (C : F →+* Polynomial F) G.taPoly)

/-- **`Φ` is squarefree** — the input the cited hyperelliptic genus formula
consumes (design doc §2). -/
theorem phiPoly_squarefree (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    Squarefree G.phiPoly :=
  (G.phiPoly_separable hdisc).squarefree

/-! ## The models: squarefree of degree 14

`H_j = d_j·(Z·u²+1)·Φ` — the objects the cited hyperelliptic genus formula
is applied to. -/

/-- The first model `H₁ = d₁·(Z·u²+1)·Φ` as a polynomial in `u`. -/
noncomputable def model1Poly : Polynomial F :=
  C G.twist1 * ((G.tPoly + 1) * G.phiPoly)

/-- The second model `H₂ = d₂·(Z·u²+1)·Φ` as a polynomial in `u`. -/
noncomputable def model2Poly : Polynomial F :=
  C G.twist2 * ((G.tPoly + 1) * G.phiPoly)

/-- `model1Poly` evaluates to the pointwise model `model1`. -/
theorem eval_model1Poly (u : F) : G.model1Poly.eval u = G.model1 u := by
  simp only [model1Poly, model1, tPoly, eval_mul, eval_add, eval_C, eval_X,
    eval_pow, eval_one, G.eval_phiPoly]
  ring

/-- `model2Poly` evaluates to the pointwise model `model2`. -/
theorem eval_model2Poly (u : F) : G.model2Poly.eval u = G.model2 u := by
  simp only [model2Poly, model2, tPoly, eval_mul, eval_add, eval_C, eval_X,
    eval_pow, eval_one, G.eval_phiPoly]
  ring

/-- `Z·X² + 1` is separable: its Bézout certificate against its derivative
`2·Z·X` has the constant `2`. -/
theorem tPoly_add_one_separable : (G.tPoly + 1).Separable := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero G.ringChar_ne_two
  have hd : (G.tPoly + 1).derivative = 2 * C G.Z * X := by
    simp only [tPoly, derivative_add, derivative_mul, derivative_pow,
      derivative_C, derivative_X, derivative_one, Nat.cast_ofNat, map_ofNat]
    ring
  rw [Polynomial.separable_def, hd]
  refine isCoprime_of_bezout (u := 2) (v := -X) (c := 2) h2 ?_
  have hC2 : (C (2 : F) : Polynomial F) = 2 := map_ofNat _ 2
  rw [tPoly, hC2]
  ring

/-- `Φ` is coprime to `Z·X² + 1`: modulo that factor, `ta = 0` and
`Φ = B²`. This is the design doc's coprimality of `Φ` with the models'
quadratic factor. -/
theorem phiPoly_isCoprime_tPoly_add_one :
    IsCoprime G.phiPoly (G.tPoly + 1) := by
  refine isCoprime_of_bezout (u := 1)
    (v := -(G.tPoly * ((C G.E.B)^2 * G.taPoly^2
      + (3*(C G.E.B)^2 + (C G.E.A)^3) * G.taPoly + 3*(C G.E.B)^2)))
    (c := G.E.B^2) (pow_ne_zero 2 G.E.B_nonzero) ?_
  have hC : (C (G.E.B^2) : Polynomial F) = (C G.E.B)^2 := map_pow _ _ _
  rw [hC, phiPoly, taPoly, tPoly]
  ring

/-- **The first model is squarefree**: a unit times the product of the two
coprime separable factors `Z·X² + 1` and `Φ`. -/
theorem model1Poly_squarefree (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    Squarefree G.model1Poly := by
  refine Polynomial.Separable.squarefree ?_
  rw [model1Poly]
  have hunit : IsUnit (C G.twist1) := isUnit_C.mpr G.twist1_ne_zero.isUnit
  refine Polynomial.Separable.mul ((separable_C _).mpr G.twist1_ne_zero.isUnit)
    (Polynomial.Separable.mul G.tPoly_add_one_separable
      (G.phiPoly_separable hdisc)
      ((G.phiPoly_isCoprime_tPoly_add_one).symm)) ?_
  exact (isCoprime_C_of_ne_zero G.twist1_ne_zero).symm

/-- **The second model is squarefree**; see `model1Poly_squarefree`. -/
theorem model2Poly_squarefree (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    Squarefree G.model2Poly := by
  refine Polynomial.Separable.squarefree ?_
  rw [model2Poly]
  refine Polynomial.Separable.mul ((separable_C _).mpr G.twist2_ne_zero.isUnit)
    (Polynomial.Separable.mul G.tPoly_add_one_separable
      (G.phiPoly_separable hdisc)
      ((G.phiPoly_isCoprime_tPoly_add_one).symm)) ?_
  exact (isCoprime_C_of_ne_zero G.twist2_ne_zero).symm

/-- **The first model has degree 14** — with squarefreeness, the input to
the cited genus formula `g = ⌊(14 - 1)/2⌋ = 6` (Galbraith ch. 10;
Stichtenoth ch. 6). -/
theorem model1Poly_natDegree : G.model1Poly.natDegree = 14 := by
  rw [model1Poly, phiPoly, taPoly, tPoly]
  compute_degree!
  repeat' constructor
  all_goals first
    | exact G.E.B_nonzero
    | exact G.Z_nonzero
    | exact G.twist1_ne_zero

/-- **The second model has degree 14**; see `model1Poly_natDegree`. -/
theorem model2Poly_natDegree : G.model2Poly.natDegree = 14 := by
  rw [model2Poly, phiPoly, taPoly, tPoly]
  compute_degree!
  repeat' constructor
  all_goals first
    | exact G.E.B_nonzero
    | exact G.Z_nonzero
    | exact G.twist2_ne_zero

/-! ## The branch quartics are Eisenstein at `w = 0`

The design doc's §3 works over the function field of the curve, where `w`
vanishes simply at the two points over `w = 0` (because
`g(-B/A) = -(B/A)³ ≠ 0`). The checkable input is the Eisenstein coefficient
pattern of the quartics over `F[w]`, at the ideal `(w)`; the step from the
pattern to total ramification —and from there to the absence of unramified
subcovers— is the cited part. -/

/-- The second branch quartic `P₂ = B·Z²·u⁴ + Z·w·u² + w`, over `F[w]`
(the inner variable is `w`, the outer `u`). -/
noncomputable def p2Poly : Polynomial (Polynomial F) :=
  C (C (G.E.B * G.Z^2)) * X^4 + C (C G.Z * X) * X^2 + C (X : Polynomial F)

/-- The reciprocal of the first branch quartic:
`B·u⁴ + Z·w·u² + Z²·w`. -/
noncomputable def p1RecipPoly : Polynomial (Polynomial F) :=
  C (C G.E.B) * X^4 + C (C G.Z * X) * X^2 + C (C (G.Z^2) * X)

/-- `P₂` has degree 4. -/
theorem p2Poly_natDegree : G.p2Poly.natDegree = 4 := by
  rw [p2Poly]
  compute_degree!
  exact ⟨G.E.B_nonzero, G.Z_nonzero⟩

/-- The reciprocal quartic has degree 4. -/
theorem p1RecipPoly_natDegree : G.p1RecipPoly.natDegree = 4 := by
  rw [p1RecipPoly]
  compute_degree!
  exact G.E.B_nonzero

/-- Coefficients of `P₂`, by direct computation. -/
theorem p2Poly_coeff :
    G.p2Poly.coeff 0 = (X : Polynomial F) ∧ G.p2Poly.coeff 1 = 0
      ∧ G.p2Poly.coeff 2 = C G.Z * X ∧ G.p2Poly.coeff 3 = 0
      ∧ G.p2Poly.coeff 4 = C (G.E.B * G.Z^2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [p2Poly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C]
      norm_num

/-- Coefficients of the reciprocal quartic, by direct computation. -/
theorem p1RecipPoly_coeff :
    G.p1RecipPoly.coeff 0 = C (G.Z^2) * X ∧ G.p1RecipPoly.coeff 1 = 0
      ∧ G.p1RecipPoly.coeff 2 = C G.Z * X ∧ G.p1RecipPoly.coeff 3 = 0
      ∧ G.p1RecipPoly.coeff 4 = C G.E.B := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [p1RecipPoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C]
      norm_num

/-- `X² ∤ c·X` in `F[w]` for a nonzero constant `c`: degree comparison. -/
theorem _root_.CompElliptic.Hashing.not_X_sq_dvd {F : Type*} [Field F]
    {c : Polynomial F} (hc : c ≠ 0)
    (hdeg : c.natDegree = 0) : ¬ (X:Polynomial F)^2 ∣ c * X := by
  intro hdvd
  have hne : c * (X:Polynomial F) ≠ 0 :=
    mul_ne_zero hc X_ne_zero
  have := Polynomial.natDegree_le_of_dvd hdvd hne
  rw [natDegree_mul hc X_ne_zero, hdeg, natDegree_X, natDegree_pow,
    natDegree_X] at this
  omega

/-- **`P₂` is Eisenstein at `(w)`** — the checkable input to the cited
total-ramification argument over the two points with `w = 0` (design doc
§3). Concretely: the leading coefficient `B·Z²` is not divisible by `w`,
the lower coefficients `w`, `0`, `Z·w`, `0` all are, and the constant
coefficient `w` is not divisible by `w²`. -/
theorem p2Poly_isEisensteinAt :
    G.p2Poly.IsEisensteinAt (Ideal.span {(X : Polynomial F)}) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := G.p2Poly_coeff
  have hdeg := G.p2Poly_natDegree
  constructor
  · -- The leading coefficient `B·Z²` is a unit, not in `(w)`.
    rw [Polynomial.leadingCoeff, hdeg, h4, Ideal.mem_span_singleton,
      X_dvd_iff, coeff_C]
    exact fun h => G.E.B_nonzero (by
      rcases mul_eq_zero.mp h with hB | hZ
      · exact hB
      · exact absurd hZ (pow_ne_zero 2 G.Z_nonzero))
  · -- Every lower coefficient is divisible by `w`.
    intro n hn
    rw [hdeg] at hn
    interval_cases n <;>
      simp [h0, h1, h2, h3, Ideal.mem_span_singleton, dvd_mul_left]
  · -- The constant coefficient `w` is not in `(w)²`.
    rw [h0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    have := Polynomial.natDegree_le_of_dvd hdvd X_ne_zero
    rw [natDegree_pow, natDegree_X] at this
    omega

/-- **The reciprocal of `P₁` is Eisenstein at `(w)`**; with
`p2Poly_isEisensteinAt`, both covers are totally ramified over `w = 0` in
the cited argument. -/
theorem p1RecipPoly_isEisensteinAt :
    G.p1RecipPoly.IsEisensteinAt (Ideal.span {(X : Polynomial F)}) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := G.p1RecipPoly_coeff
  have hdeg := G.p1RecipPoly_natDegree
  constructor
  · rw [Polynomial.leadingCoeff, hdeg, h4, Ideal.mem_span_singleton,
      X_dvd_iff, coeff_C]
    exact G.E.B_nonzero
  · intro n hn
    rw [hdeg] at hn
    interval_cases n <;>
      simp [h0, h1, h2, h3, Ideal.mem_span_singleton, dvd_mul_left]
  · rw [h0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact not_X_sq_dvd (C_ne_zero.mpr (pow_ne_zero 2 G.Z_nonzero))
      (natDegree_C _)

/-! ## The fibre over `w = 0` -/

/-- `g(-B/A) = -(B/A)³`: the curve equation at the abscissa of the two
points over `w = 0`. -/
theorem eval_g_neg_B_div_A :
    (-(G.E.B/G.E.A))^3 + G.E.A * -(G.E.B/G.E.A) + G.E.B
      = -(G.E.B/G.E.A)^3 := by
  have hA := G.A_nonzero
  field_simp
  ring

/-- `g(-B/A) ≠ 0`: the two points over `w = 0` have nonzero ordinate, so
`w` vanishes simply at each — the input that makes the Eisenstein pattern
mean total ramification in the cited argument. -/
theorem g_neg_B_div_A_ne_zero :
    (-(G.E.B/G.E.A))^3 + G.E.A * -(G.E.B/G.E.A) + G.E.B ≠ 0 := by
  rw [G.eval_g_neg_B_div_A]
  exact neg_ne_zero.mpr (pow_ne_zero 3
    (div_ne_zero G.E.B_nonzero G.A_nonzero))

end SSWUParams

end CompElliptic.Hashing
