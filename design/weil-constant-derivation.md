# The Weil character-sum constant for the deployed simplified SWU

This is the derivation behind the calculation in zcash/pasta's
[`weilbound.sage`](https://github.com/zcash/pasta/blob/acc1384bfa7a079b7ecc59182ac821215605cd39/weilbound.sage),
supporting [#28](https://github.com/daira/CompElliptic/issues/28).
It derives, for the deployed simplified-SWU mappings, the bound

> for every nontrivial character χ of E′(F_q):  |S_f(χ)| ≤ 10·√q + 1,

where S_f(χ) = Σ_{u ∈ F_q} χ(f(u)) and f is the odd (zero-repaired) form
of `map_to_curve_simple_swu` into the iso-curve E′. This discharges the
`WeilBounded` hypothesis of `Hashing/WellDistributed.lean` at C = 21/2
with enormous margin: (10√q + 1)² ≤ (21/2)²·q needs 10.25·q ≥ 20√q + 1,
and q > 2²⁵⁴.

Status: this document is a hand derivation whose computational steps are
verified by `weilbound.sage` (genus, monodromy statistics, square-class
witnesses) and by the symbolic identity checks in
`scripts/weil-derivation-checks.sage`. It cites Weil's theorem (via
FFSTV's Lemma 1 and Theorem 3) as established mathematics; it is not a
formal proof. Steps that a full write-up for publication would still
expand are marked ⟨gap⟩.

## Background

Concepts from algebraic geometry, with how each is used here and where
to read more. The references: [Galbraith] (S. Galbraith, *Mathematics of
Public Key Cryptography*, CUP 2012, free at
<https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>),
[Stichtenoth] (H. Stichtenoth, *Algebraic Function Fields and Codes*,
2nd ed., Springer GTM 254, 2009, full text at
<https://link.springer.com/book/10.1007/978-3-540-76878-4>), and FFSTV
as above.

- **Curves via their function fields.** We work with a curve through its
  field of rational functions; points of the curve correspond to
  *places* of the field, and a function *vanishes simply* at a place
  when it is a local coordinate (a *uniformizer*) there. Everything
  below is arithmetic in explicit function fields like F_q(E′)(u).
  [Stichtenoth, ch. 1]
- **Covers and ramification.** A degree-n cover C → E′ presents each
  point of E′ with n preimages, except at finitely many points where
  preimages merge — the cover *ramifies*, and merging all n at once is
  *total* ramification. Here the covers are cut out by quartics in u,
  and ramification is where a specialized quartic has repeated roots.
  [Stichtenoth, ch. 3; FFSTV, §4]
- **Genus, and the hyperelliptic shortcut.** The genus is the invariant
  that Weil's bound charges for: sums over a curve's rational points
  deviate from q + 1 by at most 2g·√q, and character sums obey the
  analogous (2g − 2 + conductor)·√q of FFSTV's Lemma 1. We only ever
  compute genus for curves W² = h(u): with h squarefree of degree d,
  the genus is ⌊(d − 1)/2⌋. [Galbraith, ch. 10; Stichtenoth, ch. 6]
- **Divisors and the parity argument.** A function's divisor is the
  formal sum of its zeros minus poles, with multiplicities. A square
  function has a divisor of the form 2·D, so exhibiting a simple
  (multiplicity-1) zero shows a function is not a square — used below
  to pin the monodromy group. [Galbraith, ch. 7]
- **Quadratic twists.** Two curves W² = d·h(u) and W² = d′·h(u) with
  d/d′ a nonsquare are *twists*: isomorphic over the algebraic closure
  (so same genus), different over F_q (different rational points). The
  two branch covers below are twists of one curve by Z.
  [Galbraith, §9.5]
- **Characters and character sums.** A character χ of the finite
  abelian group E′(F_q) is a homomorphism to the unit circle in ℂ;
  well-distributedness is the statement that Σ_u χ(f(u)) is O(√q) for
  every nontrivial χ. The transfer of such sums to sums over covering
  curves, and Weil's Riemann-hypothesis bound on the latter, is used
  as a black box through FFSTV's Lemma 1 and Theorem 3. [FFSTV, §3–4]
- **Monodromy and the Galois correspondence.** The splitting field of
  the quartic over F_q(E′) has a Galois group permuting the four roots
  (the *monodromy group*); subgroups between a root's stabilizer and
  the whole group correspond exactly to intermediate covers. For a
  biquadratic quartic u⁴ + p·u² + q the group is inside D₄, with the
  classical square-class tests deciding V₄/C₄/D₄. [Stichtenoth, ch. 3
  (Galois extensions); L.-C. Kappe and B. Warren, "An elementary test
  for the Galois group of a quartic polynomial", Amer. Math. Monthly
  96 (1989), 133–137 (paywalled; a free exposition of the quartic
  test is in
  <https://dummit.cos.northeastern.edu/teaching_fa20_5111/5111_lecture_23_computing_galois_groups_of_polynomials.pdf>)]
- **Eisenstein criterion at a place.** The classical irreducibility
  test transplants to function fields with "prime" replaced by "place
  of the base curve": lower coefficients vanishing at the place, the
  constant term exactly once, leading coefficient a unit. Its
  conclusion is what we use: the polynomial is irreducible there and
  the cover is *totally ramified* over that place. [Stichtenoth, ch. 3]

Throughout: q ≡ 1 (mod 4) is the base field size; E′ : y² = g(x) with
g(x) = x³ + A·x + B, A·B ≠ 0, and #E′(F_q) an odd prime; Z is a
nonsquare with Z ∉ {0, −1}; t = Z·u² and ta = t² + t. The deployed
instances are iso-Pallas and iso-Vesta with Z = −13 and B = 1265. We
follow Farashahi–Fouque–Shparlinski–Tibouchi–Voloch
([eprint 2010/539](https://eprint.iacr.org/2010/539), "FFSTV"),
Theorem 6, adapted to these parameters and to sign-freeness.

## 1. The branch covers

For ta ≠ 0 the simplified SWU abscissae are

    x₁(u) = B·(ta + 1) / (A·(−ta)),        x₂(u) = t·x₁(u),

and exactly one of g(x₁(u)), g(x₂(u)) is a square, by the identity
g(x₂) = t³·g(x₁) with t = Z·u² in the square class of Z. The mapping
outputs the point with the square candidate, with its ordinate's sign
set by `sgn0`; the zero-repaired form sets f(0) = 𝒪, which makes f odd:
f(−u) = −f(u) for all u.

Since q ≡ 1 (mod 4), −1 is a square, so −1/Z is a nonsquare and t = −1
has no solutions: **ta vanishes only at u = 0**, and the exceptional
input set is exactly {0}. (This is where the deployed setting is simpler
than FFSTV's q ≡ 3 (mod 4), whose t = −1 fibre is inhabited.)

Rearranging x = x_j(u) gives the covers of E′ as quartics in u over the
function field F_q(E′), writing w = A·x + B:

    P₁(u) = Z²·w·u⁴ + Z·w·u² + B,
    P₂(u) = B·Z²·u⁴ + Z·w·u² + w      (using x₂ = −B·(ta+1)/(A·(Z·u²+1))).

Both are biquadratic — the geometric face of oddness. Let C_j be the
smooth projective curve with function field F_q(E′)[u]/(P_j), and
h_j : C_j → E′ the covering map, of degree 4.

## 2. One curve, two twists

The quartics are linear in x, so each cover re-roots over the u-line:
x_j(u) is a rational function of u, and F_q(C_j) = F_q(u)(y) with
y² = g(x_j(u)). Direct computation (verified symbolically) factors both:

    g(x₁(u)) = −B·Φ(u) / (A³·ta³),
    g(x₂(u)) = −B·Φ(u) / (A³·(Z·u²+1)³),

with the **shared degree-12 core**

    Φ(u) = B²·(ta + 1)³ + A³·ta².

Using ta = Z·u²·(Z·u²+1) and clearing squares, the two curves have
hyperelliptic models

    C₁ :  W² = d₁·(Z·u²+1)·Φ(u),     d₁ = −A³·B·Z³ ≡ −A·B·Z (mod squares),
    C₂ :  W² = d₂·(Z·u²+1)·Φ(u),     d₂ = −A³·B    ≡ −A·B   (mod squares).

So C₁ and C₂ are **quadratic twists of one another by Z** — one
geometric curve, two F_q-forms; the twist is the branch dichotomy
itself.

**Genus.** Φ(0) = B² and Φ = B² at t = −1, so Φ is coprime to u and to
Z·u²+1; its degree is exactly 12 (leading coefficient B²·Z⁶ ≠ 0). Under
the nondegeneracy condition

  ⟨N⟩: Φ is squarefree,

the odd-multiplicity part of the right-hand side is (Z·u²+1)·Φ, of
degree 14, so each C_j is hyperelliptic of genus ⌊(14 − 1)/2⌋ = 6.
Condition ⟨N⟩ is verified at the deployed parameters by the script
(odd-multiplicity part of degree 14 on every branch of both curves), and
cross-checked by Sage's own genus computation at small-prime surrogates
and over ℚ with the exact constants. ⟨gap⟩ A parameter-generic proof of
⟨N⟩ (disc Φ ≠ 0 as a polynomial identity in A, B, Z away from an
explicit degeneracy locus) would replace the per-instance check.

## 3. No unramified subcover

FFSTV's Theorem 3(6) applies to h_j provided C_j → E′ does not factor
through a nontrivial unramified cover of E′. One totally ramified point
rules every intermediate out at a stroke, since ramification indices
multiply along a tower.

Consider the fibre w = 0 of E′, i.e. the two geometric points
(−B/A, ±y₀) with y₀² = g(−B/A) = −(B/A)³ ≠ 0 (B ≠ 0). Since y₀ ≠ 0, the
function w vanishes simply at each, so it is a uniformizer there.

- P₂ = B·Z²·u⁴ + Z·w·u² + w is **Eisenstein** at each such point: lower
  coefficients divisible by w, constant term w exactly once, leading
  coefficient B·Z² a unit. So C₂ → E′ is totally ramified over w = 0.
- P₁ = Z²·w·u⁴ + Z·w·u² + B is Eisenstein *reversed*: its reciprocal
  polynomial B·u⁴ + Z·w·u² + Z²·w is Eisenstein at the same points, so
  C₁ → E′ is totally ramified over w = 0 with the four roots merging at
  u = ∞.

Hence neither cover factors through a nontrivial unramified subcover,
with no condition beyond A·B ≠ 0.

Independently, the biquadratic shape puts the monodromy inside D₄, and
the biquadratic Galois classification pins it: the group drops to V₄
(three intermediate quadratics) only if the normalized constant term is
a square in F_q(E′), and to C₄ only if q·(p² − 4q) is. These reduce to
B·(A·x + B) and B·(A·x − 3·B) being squares in F_q(E′), which fail by
divisor parity (each has two simple zeros and a double pole, so its
divisor is not twice a divisor). So the monodromy is full D₄ and the
v = u² subcover is the unique intermediate — consistent with the
script's Frobenius statistics (5000 samples per branch match the D₄
cycle-type proportions ⅛, ¼, ⅜, ¼ to within ±0.006) and its nonsquare
specialization witnesses.

## 4. The sign-free assembly

By Theorem 3(6), for every nontrivial character χ of E′(F_q):

    |S_{C_j}(χ)| := |Σ_{P ∈ C_j(F_q)} χ(h_j(P))| ≤ (2·6 − 2)·√q = 10·√q.

FFSTV additionally needed the sign of the ordinate as an Artin
character (their conductor term deg y = 12), because their sum selects
one point per input. Oddness makes that unnecessary: substituting
u → −u shows S_f(χ) is real, so

    2·S_f(χ) = Σ_{u} (χ + χ̄)(f(u)),

and (χ + χ̄)(f(u)) = χ(P) + χ(−P) depends only on the ±-class of f(u) —
which the sign rule never influences. This is the same reduction that
`CharacterSum.lean` formalizes as the ±-class multiplicity form.

**The correspondence.** Fix u ∉ {0}. On the branch j with g(x_j(u)) a
square, the fibre of C_j over u consists of the two ordinate-conjugate
points (W = ±), which map under h_j to f(u) and −f(u), contributing
exactly (χ + χ̄)(f(u)); the other branch's fibre has no rational points.
Two boundary cases:

- **W = 0** would merge the two points; it happens only at rational
  roots of Φ, whose h_j-images are rational 2-torsion points of E′.
  Since #E′(F_q) is an odd prime, E′ has no rational 2-torsion, so Φ
  has no rational roots and this case is empty.
- **u = 0 and u = ∞** are the points of C_j(F_q) not accounted for by
  inputs. Over u = 0 the model gives W² = d_j·B²: rational exactly when
  d_j is a square. At u = ∞ (degree 14 is even, so two points) the
  relevant class is d_j·Z·(leading coefficient of Φ) ≡ d_j·Z. Since
  d₁ ≡ −A·B·Z and d₂ ≡ −A·B with Z a nonsquare, **exactly one** of each
  pair is rational — two extra points on each cover in total. Their
  images: x₁(u) → ∞ as u → 0 and x₂(u) → ∞ as u → ∞, so all four extra
  points map to 𝒪. (At the deployed parameters −A·B is a nonsquare —
  the script's empty w = 0 fibre — so the rational pairs are C₁'s over
  u = 0 and C₂'s at ∞; if −A·B were square they would swap, with the
  same count.)

Summing, with f(0) = 𝒪 and χ(𝒪) = 1:

    S_{C₁}(χ) + S_{C₂}(χ) = Σ_{u ≠ 0} (χ + χ̄)(f(u)) + 4
                          = 2·S_f(χ) − 2·χ(𝒪) + 4 = 2·S_f(χ) + 2.

⟨gap⟩ The identification of the smooth-model points over u = 0 and ∞
with the stated square classes is routine hyperelliptic bookkeeping but
is asserted here, not derived.

## 5. Conclusion

    2·|S_f(χ)| ≤ |S_{C₁}(χ)| + |S_{C₂}(χ)| + 2 ≤ 20·√q + 2,

so |S_f(χ)| ≤ 10·√q + 1 for every nontrivial χ, on both deployed
iso-curves. The comparison with FFSTV's Theorem 6 (52·√q + 151 for
Z = −1, q ≡ 3 (mod 4), residue-status sign rule): sign-freeness removes
their conductor term and the per-branch double-count, and the deployed
covers have genus 6 against their 8.

The composition through the deployed 3-isogeny costs nothing: the
isogeny is bijective on rational points, so χ ∘ iso ranges over the
nontrivial characters of the iso-curve as χ does, and the bound
transfers to the full `mapToCurve` verbatim.

For `WeilBounded` (squared form): C = 21/2 satisfies
(10·√q + 1)² ≤ C²·q at the deployed sizes with margin ≈ 2¹²⁷. The
downstream regularity distance ε ≈ C²·√(#G)/#F comes to about 2⁻¹²⁰,
improving the ≈ 2⁻¹¹⁶ previously quoted from the FFSTV-sized constant.
