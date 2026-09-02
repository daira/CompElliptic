/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The Eisenstein integers, parametrically: `R[ω]` with `ω² = -1 - ω`

`Eisenstein R` is `R[X] / (X² + X + 1)`, presented concretely as a pair `⟨a, b⟩`
standing for `a + b·ω`. Specialised at `R = ℤ` it is the Eisenstein integers
`ℤ[ω]`, the ring of integers of `ℚ(ζ₃)`; specialised at `R = ZMod (2^w)` it *is*
the finite quotient `ℤ[ω]/2^w`.

**Why parametric rather than a quotient type.** `Eisenstein` is a functor
`CommRing → CommRing` that commutes with base change:
`Eisenstein (R/I) = (Eisenstein R)/(I · Eisenstein R)`. Taking the quotient on
the *coefficients* rather than on the ring means `Eisenstein (ZMod (2^w))`
inherits `DecidableEq` and `Fintype` from `ZMod`, so the finite claims in
`Rings.Eisenstein.Orbits` are settled by kernel `decide` with no axiom cost. A
`Quotient`/`Ideal.Quotient` presentation would be mathematically equivalent and
computationally useless here.

**Not `Zsqrtd (-3)`.** `ℤ[√-3]` is the suborder of `ℤ[ω]` of index 2; the
maximal order is `ℤ[ω] = ℤ[(1+√-3)/2]`. Since everything downstream is about
halving and 2-adic structure, modelling this as `Zsqrtd (-3)` would be wrong in
exactly the place it matters, while still typechecking.

**Naming.** "Eisenstein" already occurs in this repository as Eisenstein's
polynomial irreducibility *criterion* (`Mathlib`'s `Polynomial.IsEisensteinAt`,
used in `Hashing/WeilSupport.lean`). That is a different Eisenstein object;
there is no relationship beyond the name.

## Main definitions

* `Eisenstein R` — the carrier, with its `CommRing` instance.
* `Eisenstein.omega` — the adjoined primitive cube root of unity, `⟨0, 1⟩`.
* `Eisenstein.conj`, `Eisenstein.norm` — conjugation and the norm form
  `N(a + b·ω) = a² - a·b + b²`.
* `Eisenstein.map` — functoriality along a ring hom of coefficients.
* `Eisenstein.evalHom` — the universal property: evaluation at any `z` with
  `z² + z + 1 = 0`. This is the bridge to the curve side, where the scalar
  `LAMBDA` of the GLV endomorphism satisfies exactly that relation.

## Main results

* `Eisenstein.omega_sq` — `ω² = -1 - ω`, the defining relation.
* `Eisenstein.mul_conj` — `x · conj x = N x`.
* `Eisenstein.norm_mul` — `N` is multiplicative, which is what makes the unit
  classification and the freeness arguments go through.
-/

namespace CompElliptic.Rings

/-- An element `a + b·ω` of `R[ω] = R[X]/(X² + X + 1)`. -/
structure Eisenstein (R : Type*) where
  /-- The coefficient of `1`. -/
  a : R
  /-- The coefficient of `ω`. -/
  b : R
deriving DecidableEq, Repr

namespace Eisenstein

variable {R : Type*} {S : Type*}

/-- Two elements agree when both coordinates do. -/
@[ext]
theorem ext {x y : Eisenstein R} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

section Basic

variable [CommRing R]

/-! ### The operations

Following `Mathlib`'s `Zsqrtd`: notation instances first, their coordinate
projections as `@[simp]` lemmas, then the `CommRing` whose fields *are* those
operations, so the two agree and there is no diamond. -/

instance : Zero (Eisenstein R) := ⟨⟨0, 0⟩⟩
instance : One (Eisenstein R) := ⟨⟨1, 0⟩⟩
instance : Add (Eisenstein R) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg (Eisenstein R) := ⟨fun x => ⟨-x.a, -x.b⟩⟩

/-- Multiplication, with `ω² = -1 - ω` already substituted:
`(a₁ + b₁ω)(a₂ + b₂ω) = (a₁a₂ - b₁b₂) + (a₁b₂ + a₂b₁ - b₁b₂)ω`. Written out
rather than derived, so that it reduces in the kernel — which is what makes the
finite claims in `Rings.Eisenstein.Orbits` provable by `decide`. -/
instance : Mul (Eisenstein R) :=
  ⟨fun x y => ⟨x.a * y.a - x.b * y.b, x.a * y.b + y.a * x.b - x.b * y.b⟩⟩

omit [CommRing R] in
@[simp] theorem mk_a (u v : R) : (⟨u, v⟩ : Eisenstein R).a = u := rfl

omit [CommRing R] in
@[simp] theorem mk_b (u v : R) : (⟨u, v⟩ : Eisenstein R).b = v := rfl
@[simp] theorem zero_a : (0 : Eisenstein R).a = 0 := rfl
@[simp] theorem zero_b : (0 : Eisenstein R).b = 0 := rfl
@[simp] theorem one_a : (1 : Eisenstein R).a = 1 := rfl
@[simp] theorem one_b : (1 : Eisenstein R).b = 0 := rfl
@[simp] theorem add_a (x y : Eisenstein R) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Eisenstein R) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : Eisenstein R) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Eisenstein R) : (-x).b = -x.b := rfl
@[simp] theorem mul_a (x y : Eisenstein R) : (x * y).a = x.a * y.a - x.b * y.b := rfl
@[simp] theorem mul_b (x y : Eisenstein R) :
    (x * y).b = x.a * y.b + y.a * x.b - x.b * y.b := rfl

/-- `R[ω]` is a commutative ring. Every axiom reduces, after `ext`, to a
polynomial identity in `R` that `ring` closes. -/
instance instCommRing : CommRing (Eisenstein R) := by
  refine
  { add := (· + ·), zero := (0 : Eisenstein R), neg := Neg.neg, mul := (· * ·),
    one := (1 : Eisenstein R)
    sub := fun x y => x + -y
    npow := @npowRec _ ⟨(1 : Eisenstein R)⟩ ⟨(· * ·)⟩
    nsmul := @nsmulRec _ ⟨(0 : Eisenstein R)⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec _ ⟨(0 : Eisenstein R)⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
      (@nsmulRec _ ⟨(0 : Eisenstein R)⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

@[simp] theorem sub_a (x y : Eisenstein R) : (x - y).a = x.a - y.a := by
  simp [sub_eq_add_neg]
@[simp] theorem sub_b (x y : Eisenstein R) : (x - y).b = x.b - y.b := by
  simp [sub_eq_add_neg]

/-- The adjoined primitive cube root of unity. -/
def omega : Eisenstein R := ⟨0, 1⟩

@[simp] theorem omega_a : (omega : Eisenstein R).a = 0 := rfl
@[simp] theorem omega_b : (omega : Eisenstein R).b = 1 := rfl

/-- The defining relation `ω² = -1 - ω`. -/
theorem omega_sq : (omega : Eisenstein R) ^ 2 = -1 - omega := by
  ext <;> simp [pow_two]

/-- `ω² + ω + 1 = 0`: the form in which the relation is matched against the
curve-side scalar (`LAMBDA_quad` in the GLV endomorphism work). -/
theorem omega_quad : (omega : Eisenstein R) ^ 2 + omega + 1 = 0 := by
  ext <;> simp [pow_two]

/-- `ω³ = 1`, so `ω` really is a cube root of unity. -/
theorem omega_cube : (omega : Eisenstein R) ^ 3 = 1 := by
  ext <;> simp [pow_succ]

/-- Conjugation, the nontrivial automorphism `ω ↦ ω²`. -/
def conj (x : Eisenstein R) : Eisenstein R := ⟨x.a - x.b, -x.b⟩

@[simp] theorem conj_a (x : Eisenstein R) : (conj x).a = x.a - x.b := rfl
@[simp] theorem conj_b (x : Eisenstein R) : (conj x).b = -x.b := rfl

/-- The norm form `N(a + b·ω) = a² - a·b + b²`: the positive-definite quadratic
form of discriminant `-3`. -/
def norm (x : Eisenstein R) : R := x.a ^ 2 - x.a * x.b + x.b ^ 2

@[simp] theorem norm_mk (u v : R) :
    norm (⟨u, v⟩ : Eisenstein R) = u ^ 2 - u * v + v ^ 2 := rfl

/-- `x · conj x = N x`, so the norm is realised inside the ring. -/
theorem mul_conj (x : Eisenstein R) : x * conj x = ⟨norm x, 0⟩ := by
  ext <;> simp [norm, pow_two] <;> ring

/-- **The norm is multiplicative.** This single fact drives the unit
classification, the inertness of `2`, and the freeness of the `μ₆` action. -/
theorem norm_mul (x y : Eisenstein R) : norm (x * y) = norm x * norm y := by
  simp only [norm, mul_a, mul_b]; ring

@[simp] theorem norm_one : norm (1 : Eisenstein R) = 1 := by simp [norm]
@[simp] theorem norm_zero : norm (0 : Eisenstein R) = 0 := by simp [norm]
@[simp] theorem norm_omega : norm (omega : Eisenstein R) = 1 := by simp [norm]

end Basic

section Map

variable [CommRing R] [CommRing S]

/-- **Functoriality.** `Eisenstein` is a functor `CommRing → CommRing`, acting on
a coefficient hom coordinate-wise. Composed with `ZMod.castHom` this is the
reduction `ℤ[ω] → ℤ[ω]/n` used throughout `Rings.Eisenstein.Mod`. -/
def map (f : R →+* S) : Eisenstein R →+* Eisenstein S where
  toFun x := ⟨f x.a, f x.b⟩
  map_one' := by ext <;> simp
  map_mul' := by intros; ext <;> simp
  map_zero' := by ext <;> simp
  map_add' := by intros; ext <;> simp

@[simp] theorem map_apply_a (f : R →+* S) (x : Eisenstein R) : (map f x).a = f x.a := rfl
@[simp] theorem map_apply_b (f : R →+* S) (x : Eisenstein R) : (map f x).b = f x.b := rfl

/-- The coefficient embedding `R → R[ω]`, `r ↦ r + 0·ω`. -/
def coeffHom : R →+* Eisenstein R where
  toFun r := ⟨r, 0⟩
  map_one' := rfl
  map_mul' := by intros; ext <;> simp
  map_zero' := rfl
  map_add' := by intros; ext <;> simp

@[simp] theorem coeffHom_a (r : R) : (coeffHom r : Eisenstein R).a = r := rfl
@[simp] theorem coeffHom_b (r : R) : (coeffHom r : Eisenstein R).b = 0 := rfl

/-- `R[ω]` is an `R`-algebra, free of rank two on `{1, ω}`. -/
instance instAlgebra : Algebra R (Eisenstein R) := (coeffHom (R := R)).toAlgebra

/-- **The universal property.** `R[ω]` is initial among `R`-algebras carrying a
root of `X² + X + 1`: given a coefficient hom `f : R →+* S` and any `z : S` with
`z² + z + 1 = 0`, evaluation `a + b·ω ↦ f a + f b · z` is a ring hom.

This is the bridge to the curve side. The GLV endomorphism's scalar satisfies
`LAMBDA² + LAMBDA + 1 = 0` in the scalar field, so a GLV pair `(k₁, k₂)` is
literally the image of `k₁ + k₂·ω` under this map, so such a pair *is* an
Eisenstein integer rather than merely resembling one. -/
def evalHom (f : R →+* S) (z : S) (hz : z ^ 2 + z + 1 = 0) : Eisenstein R →+* S where
  toFun x := f x.a + f x.b * z
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [mul_a, mul_b, map_sub, map_add, map_mul]
    linear_combination (-(f x.b * f y.b)) * hz
  map_zero' := by simp
  map_add' := by intros; simp; ring

@[simp] theorem evalHom_apply (f : R →+* S) (z : S) (hz : z ^ 2 + z + 1 = 0)
    (x : Eisenstein R) : evalHom f z hz x = f x.a + f x.b * z := rfl

/-- Evaluation sends `ω` to the chosen root. -/
@[simp] theorem evalHom_omega (f : R →+* S) (z : S) (hz : z ^ 2 + z + 1 = 0) :
    evalHom f z hz omega = z := by simp

end Map

end Eisenstein

end CompElliptic.Rings
