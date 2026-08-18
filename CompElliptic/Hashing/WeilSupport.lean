/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.BranchCovers
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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

The monodromy cross-check (§3) consumes `v4TestPoly_not_isSquare` and
`c4TestPoly_not_isSquare`: the biquadratic V₄/C₄ square classes
`B·(A·x + B)` and `B·(A·x - 3·B)` are not squares in the function
field. The field is presented via `gPoly` as the quadratic algebra
`K[Y]/(Y² - ĝ)` over `K = F_q(x)`. The section header below describes
the decomposition machinery.

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

/-! ## The core `Φ` as a polynomial -/

/-- The core `Φ(u) = B²·(ta + 1)³ + A³·ta²` as a polynomial in `u`
(`phiCore` is its evaluation). -/
noncomputable def phiPoly : Polynomial F :=
  (C G.E.B)^2 * (G.taPoly + 1)^3 + (C G.E.A)^3 * G.taPoly^2

/-- `phiPoly` evaluates to the pointwise core `phiCore`. -/
theorem eval_phiPoly (u : F) : G.phiPoly.eval u = G.phiCore u := by
  simp only [phiPoly, phiCore, taPoly, tPoly, eval_add, eval_mul, eval_pow,
    eval_C, eval_X, eval_one]

/-- `Φ` has degree exactly 12; its leading coefficient is `B²·Z⁶`. -/
theorem phiPoly_natDegree : G.phiPoly.natDegree = 12 := by
  rw [phiPoly, taPoly, tPoly]
  compute_degree!
  exact ⟨G.E.B_nonzero, G.Z_nonzero⟩

/-! ## The models `H_j = d_j·(Z·u²+1)·Φ` as polynomials -/

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

/-! ## The genus inputs: `Φ` at `u = 0`, and coprime to `Z·X² + 1` -/

/-- `Φ` has constant coefficient `B²`: it is coprime to `X`. This is the
design doc's `φ(ta(0)) = B² ≠ 0` case of the squarefreeness lemma. -/
theorem phiPoly_coeff_zero : G.phiPoly.coeff 0 = G.E.B^2 := by
  rw [coeff_zero_eq_eval_zero, G.eval_phiPoly, G.phiCore_zero]

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

/-! ## Separability of the cubic, by Bézout certificate

The cofactors were computed by `xgcd` in `scripts/weil-derivation-checks.sage`;
the identity's constant is `A³·B²·(4·A³ + 27·B²)`, nonzero exactly from the
standing assumptions plus ellipticity. -/

/-- The cubic `φ(T) = B²·(T + 1)³ + A³·T²` through which the core factors:
`Φ = φ ∘ ta` (design doc §2, the squarefreeness lemma). -/
noncomputable def phiCubic : Polynomial F :=
  (C G.E.B)^2 * (X + 1)^3 + (C G.E.A)^3 * X^2

/-- `Φ` factors through `ta`: `Φ = φ ∘ ta`. -/
theorem phiPoly_eq_comp : G.phiPoly = G.phiCubic.comp G.taPoly := by
  simp only [phiPoly, phiCubic, add_comp, mul_comp, pow_comp, C_comp, X_comp,
    one_comp]

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

/-! ## The models are squarefree of degree 14 -/

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

/-! ## The monodromy square exclusions

Design doc §3 pins the monodromy group at full `D₄`: the biquadratic
V₄/C₄ square-class tests reduce to `B·(A·x + B)` and `B·(A·x - 3·B)`
being squares in `F_q(E′)`, and both fail. The paper argument is
divisor parity. Its checkable core is elementary, because `F_q(E′)` is
the quadratic algebra `K[Y]/(Y² - ĝ)` over `K = F_q(x)`:

* a square from the base decomposes there — `a = p²` or `a = ĝ·p²` in
  `K` (`sq_or_mul_sq_of_isSquare_adjoinRoot`);
* a rational square root of a polynomial is a polynomial
  (`exists_sq_eq_of_ratFunc_sq` — `F[X]` is integrally closed);
* a squarefree polynomial of positive degree is not a polynomial square
  (`not_isSquare_ratFunc_of_squarefree`) — the affine shadow of the
  divisor parity.

The Kappe–Warren reduction to the two square classes stays cited; it is
checked symbolically in `scripts/weil-derivation-checks.sage`, along
with the Bézout certificates used below. -/

/-- A rational square root of a polynomial is a polynomial: `F[X]` is
integrally closed in `F(X)`, and an element whose square is a polynomial
is integral over `F[X]`. -/
theorem _root_.CompElliptic.Hashing.exists_sq_eq_of_ratFunc_sq
    {F : Type*} [Field F] {n : Polynomial F} {p : RatFunc F}
    (h : p^2 = algebraMap (Polynomial F) (RatFunc F) n) :
    ∃ f : Polynomial F, f^2 = n := by
  have hint : IsIntegral (Polynomial F) p :=
    ⟨X^2 - C n, monic_X_pow_sub_C n (by norm_num), by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [h, sub_self]⟩
  obtain ⟨f, hf⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨f, IsFractionRing.injective (Polynomial F) (RatFunc F) ?_⟩
  rw [map_pow, hf, h]

/-- A squarefree polynomial of positive degree is not a square in the
rational-function field: a rational square root would be a polynomial
(`exists_sq_eq_of_ratFunc_sq`). Its square divides the squarefree
target, so it is a unit and the target is constant. -/
theorem _root_.CompElliptic.Hashing.not_isSquare_ratFunc_of_squarefree
    {F : Type*} [Field F] {n : Polynomial F} (hsf : Squarefree n)
    (hdeg : n.natDegree ≠ 0) :
    ¬ IsSquare (algebraMap (Polynomial F) (RatFunc F) n) := by
  rintro ⟨p, hp⟩
  obtain ⟨f, hf⟩ := exists_sq_eq_of_ratFunc_sq (p := p)
    (by rw [sq]; exact hp.symm)
  have hunit : IsUnit f := hsf f ⟨1, by rw [← hf]; ring⟩
  refine hdeg ?_
  rw [← hf, natDegree_pow, natDegree_eq_zero_of_isUnit hunit, mul_zero]

/-- **Squares from the base of a quadratic extension decompose**. Write
a square root of `a` in `K[Y]/(Y² - g)` as `p₀ + p₁·Y`; its square is
`(p₀² + g·p₁²) + 2·p₀·p₁·Y`. So away from characteristic 2, either
`a = p₀²` or `a = g·p₁²` in `K`. -/
theorem _root_.CompElliptic.Hashing.sq_or_mul_sq_of_isSquare_adjoinRoot
    {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {g a : K}
    (h : IsSquare (AdjoinRoot.of (X^2 - C g) a)) :
    (∃ p : K, a = p^2) ∨ ∃ p : K, a = g * p^2 := by
  have hmonic : (X^2 - C g).Monic := monic_X_pow_sub_C g (by norm_num)
  have hdeg2 : (X^2 - C g).degree = 2 := degree_X_pow_sub_C (by norm_num) g
  -- Representations `of x + of y · root` are unique: a difference lifts
  -- to a polynomial of degree at most 1 divisible by the monic quadratic.
  have huniq : ∀ x y x' y' : K,
      AdjoinRoot.of (X^2 - C g) x
          + AdjoinRoot.of (X^2 - C g) y * AdjoinRoot.root (X^2 - C g)
        = AdjoinRoot.of (X^2 - C g) x'
          + AdjoinRoot.of (X^2 - C g) y' * AdjoinRoot.root (X^2 - C g) →
      x = x' ∧ y = y' := by
    intro x y x' y' hxy
    have hmk : AdjoinRoot.mk (X^2 - C g)
        (C (x - x') + C (y - y') * X) = 0 := by
      rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
        AdjoinRoot.mk_X, map_sub, map_sub]
      linear_combination hxy
    have hzero : (C (x - x') + C (y - y') * X : Polynomial K) = 0 := by
      refine eq_zero_of_dvd_of_degree_lt (AdjoinRoot.mk_eq_zero.mp hmk) ?_
      rw [hdeg2, add_comm]
      exact lt_of_le_of_lt degree_linear_le
        (by exact_mod_cast (by norm_num : (1 : ℕ) < 2))
    constructor
    · have h0 : x - x' = 0 := by
        simpa using congrArg (fun p => Polynomial.coeff p 0) hzero
      exact sub_eq_zero.mp h0
    · have h1 : y - y' = 0 := by
        simpa using congrArg (fun p => Polynomial.coeff p 1) hzero
      exact sub_eq_zero.mp h1
  obtain ⟨z, hz⟩ := h
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective z
  -- Reduce the representative modulo the monic quadratic.
  have hzr : AdjoinRoot.mk (X^2 - C g) r
      = AdjoinRoot.mk (X^2 - C g) (r %ₘ (X^2 - C g)) := by
    conv_lhs => rw [← modByMonic_add_div r (X^2 - C g)]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  set p0 := (r %ₘ (X^2 - C g)).coeff 0 with hp0
  set p1 := (r %ₘ (X^2 - C g)).coeff 1 with hp1
  have hrep : r %ₘ (X^2 - C g) = C p1 * X + C p0 := by
    rcases eq_or_ne (r %ₘ (X^2 - C g)) 0 with h0 | h0
    · rw [hp0, hp1, h0]
      simp
    · refine eq_X_add_C_of_degree_le_one ?_
      have hlt := degree_modByMonic_lt r hmonic
      rw [hdeg2, degree_eq_natDegree h0] at hlt
      rw [degree_eq_natDegree h0]
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
  have hroot : (AdjoinRoot.root (X^2 - C g))^2
      = AdjoinRoot.of (X^2 - C g) g := by
    have h0 := AdjoinRoot.mk_self (f := X^2 - C g)
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      sub_eq_zero] at h0
    exact h0
  -- Expand `of a = (of p1 · root + of p0)²` over the basis `{1, root}`.
  have hexpand : AdjoinRoot.of (X^2 - C g) a
      = AdjoinRoot.of (X^2 - C g) (p0^2 + g * p1^2)
        + AdjoinRoot.of (X^2 - C g) (2 * p0 * p1)
          * AdjoinRoot.root (X^2 - C g) := by
    rw [hz, hzr, hrep]
    simp only [map_add, map_mul, map_pow, map_ofNat, AdjoinRoot.mk_C,
      AdjoinRoot.mk_X]
    linear_combination (AdjoinRoot.of (X^2 - C g) p1)^2 * hroot
  obtain ⟨ha, hb⟩ := huniq a 0 (p0^2 + g * p1^2) (2 * p0 * p1) (by
    rw [map_zero, zero_mul, add_zero]
    exact hexpand)
  have hzero : p0 = 0 ∨ p1 = 0 := by
    rcases mul_eq_zero.mp hb.symm with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' h2
      · exact Or.inl h''
    · exact Or.inr h'
  rcases hzero with h' | h'
  · exact Or.inr ⟨p1, by rw [ha, h']; ring⟩
  · exact Or.inl ⟨p0, by rw [ha, h']; ring⟩

/-- The curve cubic `g = X³ + A·X + B` as a polynomial over `F`.
Adjoining a square root of its image `ĝ` in `K = F_q(x)` presents the
function field `F_q(E′)`. -/
noncomputable def gPoly : Polynomial F := X^3 + C G.E.A * X + C G.E.B

/-- `g` is separable, by the Bézout certificate
`(27·B - 18·A·X)·g + (6·A·X² - 9·B·X + 4·A²)·g′ = 4·A³ + 27·B²`
(checked in `scripts/weil-derivation-checks.sage`): the constant is
nonzero exactly by ellipticity. -/
theorem gPoly_separable (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    G.gPoly.Separable := by
  have hd : G.gPoly.derivative = 3 * X^2 + C G.E.A := by
    simp only [gPoly, derivative_add, derivative_mul, derivative_pow,
      derivative_C, derivative_X, Nat.cast_ofNat, map_ofNat]
    ring
  rw [Polynomial.separable_def, hd]
  refine isCoprime_of_bezout
    (u := 27 * C G.E.B - 18 * C G.E.A * X)
    (v := 6 * C G.E.A * X^2 - 9 * C G.E.B * X + 4 * (C G.E.A)^2)
    (c := 4*G.E.A^3 + 27*G.E.B^2) hdisc ?_
  have hC : (C (4*G.E.A^3 + 27*G.E.B^2) : Polynomial F)
      = 4*(C G.E.A)^3 + 27*(C G.E.B)^2 := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [gPoly, hC]
  ring

/-- `ĝ` is not a square in `F_q(x)`: `g` is squarefree of odd degree. So
`Y² - ĝ` is irreducible and the quadratic algebra below is the function
field `F_q(E′)` itself. (The exclusions need only the ring structure, so
that last step stays informal.) -/
theorem gPoly_not_isSquare_ratFunc
    (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    ¬ IsSquare (algebraMap (Polynomial F) (RatFunc F) G.gPoly) := by
  refine not_isSquare_ratFunc_of_squarefree
    (G.gPoly_separable hdisc).squarefree ?_
  have h3 : G.gPoly.natDegree = 3 := by unfold gPoly; compute_degree!
  omega

/-- **The common core of the two exclusions**: for any linear `l`
coprime to `g`, the class `B·l` is not a square in the quadratic
algebra `K[Y]/(Y² - ĝ)`. A square would decompose as `p²` or `ĝ·p²`
over `K` (`sq_or_mul_sq_of_isSquare_adjoinRoot`), and each case
descends to a polynomial square (`exists_sq_eq_of_ratFunc_sq`). That
contradicts the squarefreeness of `B·l` (degree 1) and of `B·l·g`
(degree 4) respectively, by `not_isSquare_ratFunc_of_squarefree`. -/
theorem not_isSquare_adjoinRoot_of_linear
    (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) {l : Polynomial F}
    (hdeg : l.natDegree = 1) (hcop : IsCoprime l G.gPoly) :
    ¬ IsSquare (AdjoinRoot.of
      (X^2 - C (algebraMap (Polynomial F) (RatFunc F) G.gPoly))
      (algebraMap (Polynomial F) (RatFunc F) (C G.E.B * l))) := by
  intro hsq
  -- Characteristic ≠ 2 (`Z` is a nonsquare) transfers to `F_q(x)`.
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero G.ringChar_ne_two
  have h2P : (2 : Polynomial F) ≠ 0 := fun h => h2F (by
    simpa using congrArg (fun p => Polynomial.coeff p 0) h)
  have h2 : (2 : RatFunc F) ≠ 0 := fun h => h2P
    (IsFractionRing.injective (Polynomial F) (RatFunc F)
      (by rw [map_ofNat, map_zero]; exact h))
  -- The linear factor and both products are squarefree, with known
  -- degrees.
  have hl0 : l ≠ 0 := fun h => by simp [h] at hdeg
  have hl1 : l.coeff 1 ≠ 0 := by
    have hlc := leadingCoeff_ne_zero.mpr hl0
    rwa [Polynomial.leadingCoeff, hdeg] at hlc
  have hlsep : l.Separable := by
    have hd : l.derivative = C (l.coeff 1) := by
      conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg.le]
      simp only [derivative_add, derivative_mul, derivative_C,
        derivative_X, zero_mul, mul_one, zero_add, add_zero]
    rw [Polynomial.separable_def, hd]
    exact isCoprime_C_of_ne_zero hl1
  have hτsep : (C G.E.B * l).Separable :=
    Polynomial.Separable.mul ((separable_C _).mpr G.E.B_nonzero.isUnit)
      hlsep ((isCoprime_C_of_ne_zero G.E.B_nonzero).symm)
  have hτdeg : (C G.E.B * l).natDegree = 1 := by
    rw [natDegree_mul (C_ne_zero.mpr G.E.B_nonzero) hl0, natDegree_C,
      zero_add, hdeg]
  have hgm : G.gPoly.Monic := by
    unfold gPoly
    rw [add_assoc]
    exact monic_X_pow_add (lt_of_le_of_lt degree_linear_le
      (by exact_mod_cast (by norm_num : (1 : ℕ) < 3)))
  have hg3 : G.gPoly.natDegree = 3 := by unfold gPoly; compute_degree!
  have hτgsf : Squarefree (C G.E.B * l * G.gPoly) :=
    (Polynomial.Separable.mul hτsep (G.gPoly_separable hdisc)
      (IsCoprime.mul_left ((isCoprime_C_of_ne_zero G.E.B_nonzero).symm)
        hcop)).squarefree
  -- Decompose the square over the base field and refute both cases.
  rcases sq_or_mul_sq_of_isSquare_adjoinRoot h2 hsq with ⟨p, hp⟩ | ⟨p, hp⟩
  · exact not_isSquare_ratFunc_of_squarefree hτsep.squarefree
      (by rw [hτdeg]; norm_num) ⟨p, by rw [hp, sq]⟩
  · refine not_isSquare_ratFunc_of_squarefree hτgsf
      (by rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr G.E.B_nonzero) hl0)
        hgm.ne_zero, hτdeg, hg3]; norm_num)
      ⟨algebraMap (Polynomial F) (RatFunc F) G.gPoly * p, ?_⟩
    rw [map_mul, hp]
    ring

/-- The V₄-test square class of the branch quartics: `B·w = B·(A·x + B)`. -/
noncomputable def v4TestPoly : Polynomial F :=
  C G.E.B * (C G.E.A * X + C G.E.B)

/-- The C₄-test square class of the branch quartics: `B·(A·x - 3·B)`. -/
noncomputable def c4TestPoly : Polynomial F :=
  C G.E.B * (C G.E.A * X - 3 * C G.E.B)

/-- **The V₄ exclusion** (design doc §3): `B·(A·x + B)` is not a square
in the function field. The coprimality certificate is
`(A²·X² - A·B·X + (B² + A³))·(A·X + B) - A³·g = B³` (checked in
`scripts/weil-derivation-checks.sage`). -/
theorem v4TestPoly_not_isSquare (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    ¬ IsSquare (AdjoinRoot.of
      (X^2 - C (algebraMap (Polynomial F) (RatFunc F) G.gPoly))
      (algebraMap (Polynomial F) (RatFunc F) G.v4TestPoly)) := by
  have hdeg : (C G.E.A * X + C G.E.B).natDegree = 1 := by
    compute_degree!
    all_goals exact G.A_nonzero
  have hcop : IsCoprime (C G.E.A * X + C G.E.B) G.gPoly := by
    refine isCoprime_of_bezout
      (u := (C G.E.A)^2 * X^2 - C G.E.A * C G.E.B * X
        + ((C G.E.B)^2 + (C G.E.A)^3))
      (v := -(C G.E.A)^3)
      (c := G.E.B^3) (pow_ne_zero 3 G.E.B_nonzero) ?_
    have hC : (C (G.E.B^3) : Polynomial F) = (C G.E.B)^3 := map_pow _ _ _
    rw [gPoly, hC]
    ring
  unfold v4TestPoly
  exact G.not_isSquare_adjoinRoot_of_linear hdisc hdeg hcop

/-- **The C₄ exclusion** (design doc §3): `B·(A·x - 3·B)` is not a square
in the function field. The coprimality certificate is
`A³·g - (A²·X² + 3·A·B·X + (9·B² + A³))·(A·X - 3·B) = B·(4·A³ + 27·B²)`
(checked in `scripts/weil-derivation-checks.sage`); its constant is again
a product of the standing nonzero quantities. -/
theorem c4TestPoly_not_isSquare (hdisc : 4*G.E.A^3 + 27*G.E.B^2 ≠ 0) :
    ¬ IsSquare (AdjoinRoot.of
      (X^2 - C (algebraMap (Polynomial F) (RatFunc F) G.gPoly))
      (algebraMap (Polynomial F) (RatFunc F) G.c4TestPoly)) := by
  have hdeg : (C G.E.A * X - 3 * C G.E.B).natDegree = 1 := by
    compute_degree!
    all_goals exact G.A_nonzero
  have hcop : IsCoprime (C G.E.A * X - 3 * C G.E.B) G.gPoly := by
    refine isCoprime_of_bezout
      (u := -((C G.E.A)^2 * X^2 + 3 * C G.E.A * C G.E.B * X
        + (9*(C G.E.B)^2 + (C G.E.A)^3)))
      (v := (C G.E.A)^3)
      (c := G.E.B * (4*G.E.A^3 + 27*G.E.B^2))
      (mul_ne_zero G.E.B_nonzero hdisc) ?_
    have hC : (C (G.E.B * (4*G.E.A^3 + 27*G.E.B^2)) : Polynomial F)
        = C G.E.B * (4*(C G.E.A)^3 + 27*(C G.E.B)^2) := by
      simp only [map_mul, map_add, map_pow, map_ofNat]
    rw [gPoly, hC]
    ring
  unfold c4TestPoly
  exact G.not_isSquare_adjoinRoot_of_linear hdisc hdeg hcop

end SSWUParams

end CompElliptic.Hashing
