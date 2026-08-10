/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.CurveForms.ShortWeierstrass
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Degree-3 isogenies from Vélu's formulae

An *isogeny* is a nonconstant rational map between elliptic curves that sends the
identity to the identity; it is automatically a group homomorphism. A degree-3 isogeny
sends three points of the domain (counted over the algebraic closure) to each point of
the codomain, and its *kernel* — the three points sent to the identity — determines it
up to isomorphism.

The reason this library needs one: the simplified SWU mapping requires a curve
coefficient `A ≠ 0`, and both Pasta curves have `A = 0`. RFC 9380 handles such targets
by mapping to an auxiliary curve that is 3-isogenous to the target and then carrying
the result across the isogeny.

This module formalizes the method behind the specified maps, not only their
coefficients. The maps in the protocol specification are the `rational_maps()` of the
isogenies that `zcash/pasta`'s `amicable.sage` found with Sage's
`isogenies_prime_degree(3)`; Sage builds such maps by Vélu's formulae from the
kernel, composed with the isomorphism `(x, y) ↦ (s²·x, s³·y)` that normalizes the
codomain. `ThreeIsogeny` takes exactly that input —
the kernel abscissa `x₀` and the normalizing scalar `s` — and derives the rational
maps and the codomain coefficients from them. A concrete instance then only has to
check that its specified coefficients match what the derivation yields, which is a
handful of numeral equations rather than a curve-sized polynomial identity.

A kernel of size 3 is `{𝒪, T, -T}` for a point `T = (x₀, ±y₀)` of order 3, and `x₀`
being a root of the degree-3 division polynomial `ψ₃` says exactly that. The two
kernel points share the abscissa, so Vélu's sums over the kernel collapse to
polynomials in `x₀` and `y₀² = x₀³ + A·x₀ + B`; everything stays rational in `x₀` even
when `y₀` itself lies in a quadratic extension. For the instances used here `y₀²` is a
nonsquare, so the kernel points have no rational ordinate at all. That hypothesis
(`kernel_irrational`) is what makes the affine rational map total on rational points:
its denominators vanish only on the kernel fibre `x = x₀`, and no rational point of
the domain lies there (`ne_x₀`).

The maps take an affine point `(x, y)` of the domain to
`(s² · xnum x / (x - x₀)², s³ · y · ynum x / (x - x₀)³)`, and `onCurve_mapXY` proves
the result lands on the codomain. The ordinate is `y` times a function of `x` alone,
so negating the input negates the output (`mapXY_neg`): the isogeny commutes with
negation, which the hash-to-curve analysis consumes as oddness.

## References

- J. Vélu, "Isogénies entre courbes elliptiques", Comptes Rendus de l'Académie des
  Sciences de Paris, Série A, 273 (1971), A238–A241. (The formulae giving a separable
  isogeny with prescribed kernel, and its codomain.)
- S. D. Galbraith, "Mathematics of Public Key Cryptography", Cambridge University
  Press, 2012. Extended Chapter 25, "Isogenies of elliptic curves":
  <https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch25.pdf>. Theorem 25.1.6
  states Vélu's formulae in the Weierstrass form used here (section 25.1.1).
-/

open CompElliptic.CurveForms.ShortWeierstrass

namespace CompElliptic.Isogenies

variable {F : Type*} [Field F]

/-- A degree-3 isogeny in the normalized form produced by Sage's `rational_maps()`:
Vélu's formulae for the kernel `{𝒪, (x₀, ±y₀)}`, composed with the curve isomorphism
`(x, y) ↦ (s²·x, s³·y)`. The `psi3` field says `x₀` is a root of the degree-3 division
polynomial of the domain, so the fibre over `x₀` together with `𝒪` is a subgroup of
order 3 over the algebraic closure; `kernel_irrational` says the two kernel points are
not rational. The codomain is pinned by the two coefficient equations that Vélu's
formulae dictate. -/
structure ThreeIsogeny (F : Type*) [Field F] where
  /-- The domain curve (the auxiliary "iso-curve" in the hash-to-curve application). -/
  domain : SWCurve F
  /-- The codomain curve (the target of the hash-to-curve application). -/
  codomain : SWCurve F
  /-- The shared abscissa of the two affine kernel points. -/
  x₀ : F
  /-- The scaling of the isomorphism composed after Vélu's isogeny. -/
  s : F
  s_nonzero : s ≠ 0
  /-- `x₀` is a root of the domain's degree-3 division polynomial
  `ψ₃(X) = 3·X⁴ + 6·A·X² + 12·B·X - A²`. -/
  psi3 : 3 * x₀^4 + 6 * domain.A * x₀^2 + 12 * domain.B * x₀ - domain.A^2 = 0
  /-- The square of the kernel ordinate, `y₀² = x₀³ + A·x₀ + B`, is a nonsquare: the
  kernel points exist only over a quadratic extension. -/
  kernel_irrational : ¬ IsSquare (x₀^3 + domain.A * x₀ + domain.B)
  /-- The codomain's `A`, as Vélu's formulae and the scaling dictate. -/
  codomain_A : codomain.A = s^4 * (domain.A - 10 * (3 * x₀^2 + domain.A))
  /-- The codomain's `B`, as Vélu's formulae and the scaling dictate. -/
  codomain_B : codomain.B =
    s^6 * (domain.B - 7 * (4 * (x₀^3 + domain.A * x₀ + domain.B)
      + 2 * (3 * x₀^2 + domain.A) * x₀))

namespace ThreeIsogeny

variable (I : ThreeIsogeny F)

/-- Vélu's linear coefficient, summed over the two kernel points: `v = 2·(3·x₀² + A)`. -/
def v : F := 2 * (3 * I.x₀^2 + I.domain.A)

/-- Vélu's constant coefficient, summed over the two kernel points: `u = 4·y₀²`. -/
def u : F := 4 * (I.x₀^3 + I.domain.A * I.x₀ + I.domain.B)

/-- The numerator of the abscissa map over the denominator `(x - x₀)²`. -/
def xnum (x : F) : F := x * (x - I.x₀)^2 + I.v * (x - I.x₀) + I.u

/-- The `x`-dependent factor of the ordinate map's numerator, over the denominator
`(x - x₀)³`. The full ordinate map is `y` times this ratio, which is exactly the
derivative of the abscissa map — Vélu's isogeny is normalized, so it pulls the
invariant differential back to itself. -/
def ynum (x : F) : F := (x - I.x₀)^3 - I.v * (x - I.x₀) - 2 * I.u

/-- The affine rational map: Vélu's isogeny followed by the normalizing isomorphism. -/
def mapXY (x y : F) : F × F :=
  (I.s^2 * I.xnum x / (x - I.x₀)^2, I.s^3 * (y * I.ynum x) / (x - I.x₀)^3)

/-- No rational point of the domain has the kernel abscissa: its ordinate would be a
rational square root of the nonsquare `y₀²`. Hence the denominators of `mapXY` do not
vanish on rational points. -/
theorem ne_x₀ {x y : F} (h : OnCurve I.domain.A I.domain.B (x, y)) : x ≠ I.x₀ := by
  intro hx
  subst hx
  refine I.kernel_irrational ⟨y, ?_⟩
  have h' : y^2 = I.x₀^3 + I.domain.A * I.x₀ + I.domain.B := h
  linear_combination -h'

/- The cleared on-curve identity behind `onCurve_mapXY` was checked, and its
`linear_combination` cofactor computed, with this Sage script:

  R.<x, x0, a, b> = PolynomialRing(QQ, order='lex')
  g    = x^3 + a*x + b
  psi3 = 3*x0^4 + 6*a*x0^2 + 12*b*x0 - a^2
  v    = 2*(3*x0^2 + a)
  u    = 4*(x0^3 + a*x0 + b)
  D    = x - x0
  xnum = x*D^2 + v*D + u
  ynum = D^3 - v*D - 2*u
  A1   = a - 5*v
  B1   = b - 7*(u + v*x0)
  diff = g*ynum^2 - (xnum^3 + A1*xnum*D^4 + B1*D^6)
  q, r = diff.quo_rem(psi3)
  assert r == 0
  print(q)

The remainder is zero — the identity holds modulo `ψ₃` alone — and `q` is the
cofactor used below. -/

/-- The on-curve identity with denominators cleared: multiplying the codomain equation
at `mapXY x y` through by `(x - x₀)⁶` leaves a polynomial identity that follows from
the curve equation and `ψ₃(x₀) = 0`. -/
theorem key_identity {x y : F} (h : OnCurve I.domain.A I.domain.B (x, y)) :
    I.s^6 * (y * I.ynum x)^2 =
      (I.s^2 * I.xnum x)^3 + I.codomain.A * (I.s^2 * I.xnum x) * (x - I.x₀)^4
        + I.codomain.B * (x - I.x₀)^6 := by
  have hy : y^2 = x^3 + I.domain.A * x + I.domain.B := h
  rw [I.codomain_A, I.codomain_B]
  simp only [xnum, ynum, v, u]
  linear_combination (I.s^6 * ((x - I.x₀)^3 - (2 * (3 * I.x₀^2 + I.domain.A)) * (x - I.x₀)
      - 2 * (4 * (I.x₀^3 + I.domain.A * I.x₀ + I.domain.B)))^2) * hy
    + (I.s^6 * (-6 * x^5 + 30 * x^4 * I.x₀ - 48 * x^3 * I.x₀^2 + 4 * x^3 * I.domain.A
      + 36 * x^2 * I.x₀^3 + 12 * x^2 * I.domain.B - 18 * x * I.x₀^4
      - 12 * x * I.x₀^2 * I.domain.A - 24 * x * I.x₀ * I.domain.B + 6 * I.x₀^5
      + 8 * I.x₀^3 * I.domain.A + 12 * I.x₀^2 * I.domain.B)) * I.psi3

/-- Every rational point of the domain maps onto the codomain. -/
theorem onCurve_mapXY {x y : F} (h : OnCurve I.domain.A I.domain.B (x, y)) :
    OnCurve I.codomain.A I.codomain.B (I.mapXY x y) := by
  have hD : x - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h)
  have key := I.key_identity h
  show (I.s^3 * (y * I.ynum x) / (x - I.x₀)^3)^2 =
    (I.s^2 * I.xnum x / (x - I.x₀)^2)^3
      + I.codomain.A * (I.s^2 * I.xnum x / (x - I.x₀)^2) + I.codomain.B
  field_simp [hD]
  linear_combination key

/-- The isogeny commutes with negation: the ordinate map is `y` times a function of
the abscissa alone. -/
theorem mapXY_neg (x y : F) :
    I.mapXY x (-y) = ((I.mapXY x y).1, -(I.mapXY x y).2) := by
  simp only [mapXY, Prod.mk.injEq]
  exact ⟨trivial, by ring⟩

/-- Freedom from rational 2-torsion transports backwards along the isogeny: a rational
point of the domain with `y = 0` would map to a point of the codomain with `y = 0`,
because the image ordinate carries the factor `y`. -/
theorem no_y_zero_of_codomain
    (hc : ∀ X : F, ¬ OnCurve I.codomain.A I.codomain.B (X, 0)) (x : F) :
    ¬ OnCurve I.domain.A I.domain.B (x, 0) := by
  intro h
  have himg := I.onCurve_mapXY h
  have hy : (I.mapXY x 0).2 = 0 := by simp [mapXY]
  exact hc (I.mapXY x 0).1 (hy ▸ himg)

end ThreeIsogeny

end CompElliptic.Isogenies
