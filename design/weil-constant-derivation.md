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
and q > 2^{254}.

Status: this document is a proof of the bound, modulo results cited as
established mathematics: Weil's theorem in the form of FFSTV's Lemma 1
and Theorem 3, and the standard point bookkeeping for hyperelliptic
models [Galbraith, ch. 10]. The symbolic identities it relies on are
checked by `scripts/check_weil_derivations.sage`; the per-instance
facts (the empty w = 0 fibre, the Frobenius statistics, the
square-class witnesses) by `weilbound.sage`. The calculation from the
per-cover Weil inputs to the deployed constants is machine-checked
(CompElliptic's `Hashing/BranchCovers.lean`, `Hashing/WeilInstance.lean`,
and `Hashing/PastaSSWU.lean`), and so are the checkable inputs of the two
cited steps (`Hashing/WeilSupport.lean`, whose facts are referenced at
their points of use below; CI checks that this document references all
of that file's declarations). The cited steps themselves and Weil's
theorem stay on paper — the vocabulary they need is tracked at #30.

## Background

Concepts from algebraic geometry, with how each is used here and where
to read more. The references: [Galbraith] (S. Galbraith, *Mathematics of
Public Key Cryptography*, CUP 2012, free at
<https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>),
[Stichtenoth] (H. Stichtenoth, *Algebraic Function Fields and Codes*,
2nd ed., Springer GTM 254, 2009, full text at
<https://link.springer.com/book/10.1007/978-3-540-76878-4>), and FFSTV
as above.

- **Curves via their function fields.** We work with a curve through
  its field of rational functions; points of the curve correspond to
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
  constant term exactly once, leading coefficient a unit. The
  transplant is an instantiation rather than a new theorem — the
  criterion is a statement about any discrete valuation, whose
  hypotheses force the Newton polygon to a single segment of slope
  −1/n, so every root has valuation 1/n. Its conclusion is what we
  use: the polynomial is irreducible there and the cover is *totally
  ramified* over that place. [Stichtenoth, ch. 3] [Newton polygons:
  J. S. Milne, *Algebraic Number Theory*, course notes, ch. 7,
  Prop. 7.44 (stated for characteristic zero, but the argument is
  characteristic-free) — free at <https://www.jmilne.org/math/CourseNotes/ant.html>]

Throughout: q ≡ 1 (mod 4) is the base field size; E′ : y² = g(x) with
g(x) = x³ + A·x + B, A·B ≠ 0, and #E′(F_q) an odd prime; Z is a
nonsquare with Z ∉ {0, −1}; t = Z·u² and ta = t² + t. The deployed
instances are iso-Pallas and iso-Vesta with Z = −13 and B = 1265. We
follow Farashahi–Fouque–Shparlinski–Tibouchi–Voloch
([eprint 2010/539](https://eprint.iacr.org/2010/539), "FFSTV"),
Theorem 6, adapted to these parameters and to sign-freeness.

## 1. The branch covers

For ta ≠ 0 the simplified SWU abscissae are (`x1`, `x2`)

    x₁(u) = B·(ta + 1) / (A·(−ta)),        x₂(u) = t·x₁(u),

and exactly one of g(x₁(u)), g(x₂(u)) is a square, by the identity
g(x₂) = t³·g(x₁) with t = Z·u² in the square class of Z (in cleared
form, `g_x2_eq`). The mapping outputs the point with the square
candidate, with its ordinate's sign set by `sgn0`; the zero-repaired
form sets f(0) = 𝒪, which makes f odd: f(−u) = −f(u) for all u (`map_neg`
away from 0; on each deployed curve, `isOdd_zeroRepaired_mapToCurve`).

Since q ≡ 1 (mod 4), −1 is a square, so −1/Z is a nonsquare and t = −1
has no solutions (`Zuu_add_one_ne_zero`): **ta vanishes only at u = 0**
(`ta_ne_zero_of_u_ne_zero`), and the exceptional input set is exactly
{0}. (This is where the deployed setting is simpler than FFSTV's
q ≡ 3 (mod 4), whose t = −1 fibre is inhabited.)

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

with the **shared degree-12 core** (`phiPoly`, matching the pointwise
`phiCore` by `eval_phiPoly`)

    Φ(u) = B²·(ta + 1)³ + A³·ta².

Using ta = Z·u²·(Z·u²+1) and clearing squares, the two curves have
hyperelliptic models (`model1Poly`, `model2Poly`, evaluating to the
pointwise `model1`, `model2` by `eval_model1Poly`, `eval_model2Poly`;
their relation to the curve equation at x_j is `model1_eq`, `model2_eq`)

    C₁ :  W² = d₁·(Z·u²+1)·Φ(u),     d₁ = −A³·B·Z³ ≡ −A·B·Z (mod squares),
    C₂ :  W² = d₂·(Z·u²+1)·Φ(u),     d₂ = −A³·B    ≡ −A·B   (mod squares).

So C₁ and C₂ are **quadratic twists of one another by Z** (`twist1`,
`twist2`, differing by Z³ = Z times a square) — one geometric curve,
two F_q-forms; the twist is the branch dichotomy itself.

**Genus.** Φ(0) = B² and Φ = B² at t = −1, so Φ is coprime to u and to
Z·u²+1 (`phiPoly_coeff_zero`, `phiPoly_isCoprime_tPoly_add_one`, with the
quadratic factor separable, `tPoly_add_one_separable`); its degree is
exactly 12 (leading coefficient B²·Z⁶ ≠ 0; `phiPoly_natDegree`). The
odd-multiplicity part of the right-hand side is therefore (Z·u²+1)·Φ,
of degree 14 — provided Φ is squarefree, which holds unconditionally:

**Lemma (Φ is squarefree).** Under the standing assumptions, Φ has no
repeated root over the algebraic closure.

*Proof.* Φ is a composition: Φ(u) = φ(ta(u)) with the cubic
φ(T) = B²·(T+1)³ + A³·T² = B²·T³ + (A³+3·B²)·T² + 3·B²·T + B²
(`phiCubic`, `phiPoly`, `phiPoly_eq_comp`; the derivative
`phiCubic_derivative`). A repeated root u₀ of Φ has Φ(u₀) = 0 and
Φ′(u₀) = φ′(ta(u₀))·ta′(u₀) = 0. If φ′(ta(u₀)) = 0, then ta(u₀) is a
repeated root of φ; but

    disc(φ) = −A⁶·B²·(4·A³ + 27·B²) ≠ 0,

since A·B ≠ 0 and 4·A³ + 27·B² ≠ 0 is exactly the ellipticity of E′.
(The formal counterpart avoids the discriminant: `phiCubic_separable`
witnesses coprimality of φ and φ′ directly, by a Bézout identity with
constant A³·B²·(4·A³ + 27·B²), through the generic `isCoprime_of_bezout`.)
Otherwise ta′(u₀) = 2·Z·u₀·(2·Z·u₀² + 1) = 0 (char ≠ 2;
`taPoly_derivative`), so either u₀ = 0, where φ(ta(0)) = φ(0) = B² ≠ 0
(`phiPoly_coeff_zero`, via `isCoprime_X_of_coeff_zero`), or Z·u₀² = −1/2,
where ta(u₀) = −1/4 and 64·φ(−1/4) = 4·A³ + 27·B² ≠ 0 — again ellipticity.
(Formally: the re-expansion 64·Φ = Ψ(2·Z·u² + 1), `psiPoly`,
`phiPoly_64_eq`, has constant term the ellipticity, `psiPoly_coeff_zero`,
giving `phiPoly_isCoprime_snd`.) Either way Φ(u₀) ≠ 0, a contradiction. ∎

The lemma is `phiPoly_squarefree` in `Hashing/WeilSupport.lean`
(separability `phiPoly_separable`, assembled with the generic
`isCoprime_C_of_ne_zero`), and the models inherit it:
`model1Poly_squarefree` and `model2Poly_squarefree`, squarefree of
degree exactly 14 (`model1Poly_natDegree`, `model2Poly_natDegree`).

The discriminant factorization and both critical values are checked
symbolically in `scripts/check_weil_derivations.sage`. So each C_j is
hyperelliptic of genus ⌊(14 − 1)/2⌋ = 6, for **every** valid parameter
set — the pleasant surprise being that the two quantities the argument
needs to be nonzero are the curve discriminant and A·B, both already
assumed. The script's per-instance evidence (odd-multiplicity part of
degree 14 on every branch, Sage's genus at small-prime surrogates and
over ℚ) serves as cross-check rather than hypothesis discharge.

## 3. No unramified subcover

FFSTV's Theorem 3(6) applies to h_j provided C_j → E′ does not factor
through a nontrivial unramified cover of E′. One totally ramified point
rules every intermediate out at a stroke, since ramification indices
multiply along a tower.

Consider the fibre w = 0 of E′, i.e. the two geometric points
(−B/A, ±y₀) with y₀² = g(−B/A) = −(B/A)³ ≠ 0 (B ≠ 0;
`eval_g_neg_B_div_A`, `g_neg_B_div_A_ne_zero`). Since y₀ ≠ 0, the
function w vanishes simply at each, so it is a uniformizer there.

- P₂ = B·Z²·u⁴ + Z·w·u² + w is **Eisenstein** at each such point: lower
  coefficients divisible by w, constant term w exactly once, leading
  coefficient B·Z² a unit (`p2Poly`, with the coefficient pattern
  `p2Poly_coeff`, degree `p2Poly_natDegree`, and the criterion
  `p2Poly_isEisensteinAt`). So C₂ → E′ is totally ramified over w = 0.
- P₁ = Z²·w·u⁴ + Z·w·u² + B is Eisenstein *reversed*: its reciprocal
  polynomial B·u⁴ + Z·w·u² + Z²·w is Eisenstein at the same points
  (`p1RecipPoly`, `p1RecipPoly_coeff`, `p1RecipPoly_natDegree`,
  `p1RecipPoly_isEisensteinAt`, with `not_X_sq_dvd` for the (w)²
  condition), so C₁ → E′ is totally ramified over w = 0 with the four
  roots merging at u = ∞.

Hence neither cover factors through a nontrivial unramified subcover,
with no condition beyond A·B ≠ 0. The coefficient patterns and the
fibre ordinate above are the formalized inputs; the step from them to
total ramification is the cited part.

Independently, the biquadratic shape puts the monodromy inside D₄,
and the biquadratic Galois classification pins it. The group drops to
V₄ (three intermediate quadratics) only if the normalized constant
term is a square in F_q(E′), and to C₄ only if q·(p² − 4q) is. For
both quartics, these reduce to the same two classes: B·(A·x + B) and
B·(A·x − 3·B) being squares in F_q(E′). (The reductions are checked
symbolically in `scripts/check_weil_derivations.sage`.) Both fail by
divisor parity: each class has two simple zeros and a double pole, so
its divisor is not twice a divisor. So the monodromy is full D₄, and
the v = u² subcover is the unique intermediate. This is consistent
with the script's Frobenius statistics (5000 samples per branch match
the D₄ cycle-type proportions ⅛, ¼, ⅜, ¼ to within ±0.006) and with
its nonsquare specialization witnesses.

The two failures are formalized as `v4TestPoly_not_isSquare` and
`c4TestPoly_not_isSquare` (the classes are `v4TestPoly`, `c4TestPoly`),
with no vocabulary beyond polynomials. F_q(E′) is the quadratic algebra
K[Y]/(Y² − ĝ) over K = F_q(x), for ĝ the image of the curve cubic
`gPoly`. The algebra is the field itself, because ĝ is not a square in
K (`gPoly_not_isSquare_ratFunc`, via `gPoly_separable`). The parity
argument's affine form rests on three facts:

- a square from the base decomposes as p² or ĝ·p²
  (`sq_or_mul_sq_of_isSquare_adjoinRoot`, in characteristic ≠ 2);
- a rational square root of a polynomial is a polynomial
  (`exists_sq_eq_of_ratFunc_sq` — F_q[x] is integrally closed);
- a squarefree polynomial of positive degree is not a polynomial
  square (`not_isSquare_ratFunc_of_squarefree`).

The shared core `not_isSquare_adjoinRoot_of_linear` applies these to
B·l of degree 1 and to B·l·g of degree 4. The coprimality of each
linear factor l with g comes from a Bézout certificate. The two
constants are B³ and B·(4·A³ + 27·B²) — ellipticity yet again. (The
certificates are normalized with positive constants. That matches the
file's other certificates, and it keeps a negation out of the
constant-lifting step of the Lean proofs; it is why they differ by
sign from the naïve division remainders.)

## 4. The sign-free assembly

By Theorem 3(6), for every nontrivial character χ of E′(F_q):

    |S_{C_j}(χ)| := |Σ_{P ∈ C_j(F_q)} χ(h_j(P))| ≤ (2·6 − 2)·√q = 10·√q.

(This is the cited Weil input. It enters the formal development squared
and over the model point sets, as the two `CharSumBounded` hypotheses
at bound 100·q.)

FFSTV additionally needed the sign of the ordinate as an Artin
character (their conductor term deg y = 12), because their sum selects
one point per input. Oddness makes that unnecessary: substituting
u → −u shows S_f(χ) is real (`IsOdd.conj_charSum`), so

    2·S_f(χ) = Σ_{u} (χ + χ̄)(f(u)),

(`IsOdd.two_mul_charSum`), and (χ + χ̄)(f(u)) = χ(P) + χ(−P) depends
only on the ±-class of f(u) — which the sign rule never influences
(the identity χ(−P) = χ̄(P) behind the pairing is
`addChar_map_neg_eq_conj`). This is the same reduction that
`CharacterSum.lean` formalizes as the ±-class multiplicity form
(`charSum_eq`, with the symmetry from `IsOdd.mult_neg`).

**The correspondence.** All counting happens on the smooth model
W² = H_j(u), with H_j = d_j·(Z·u²+1)·Φ squarefree of degree 14 by the
Lemma. For such a model the rational points are read off in the
standard way [Galbraith, ch. 10]. The affine locus is smooth, since a
singular point would need W = 0 at a repeated root of H_j. Over each
u₀ there are two rational points when H_j(u₀) is a nonzero square, one
when H_j(u₀) = 0, and none when H_j(u₀) is a nonsquare. Since the
degree 14 is even, there are two more points at infinity, rational
exactly when the leading coefficient of H_j is a square. This reading
is what the point sets `modelPoints1`, `modelPoints2` encode: the
affine solutions of W² = H_j(u), plus the pair at infinity exactly
when the leading square class d_j·Z is a square.

The model coordinate is W = y·s_j(u), with s₁ = A³·Z³·u³·(Z·u²+1)² and
s₂ = A³·(Z·u²+1)² (`scale1`, `scale2`); the identities
g(x_j(u))·s_j(u)² = H_j(u) are checked symbolically and proven as
`model1_eq`, `model2_eq`. Since Z·u²+1 has no rational roots (−1/Z is
a nonsquare; `Zuu_add_one_ne_zero`), s_j(u₀) ≠ 0 for every input
u₀ ∉ {0} (`scale1_ne_zero`, `scale2_ne_zero`). Over such a u₀, then,
y ↦ W = y·s_j(u₀) is a bijection between the rational points of
y² = g(x_j(u)) and those of the model, and H_j(u₀) is a square exactly
when g(x_j(u₀)) is. So on the branch j with g(x_j(u₀)) a square, the
fibre of C_j over u₀ consists of the two ordinate-conjugate points,
which map under h_j to f(u₀) and −f(u₀), contributing exactly
(χ + χ̄)(f(u₀)); the other branch's fibre has no rational points. The
last two sentences are `fibre_sum`, with h_j in model coordinates as
`cover1Map`, `cover2Map`. Three boundary cases:

- **W = 0** would merge the two points. It happens only at rational
  roots of (Z·u²+1)·Φ, hence only at rational roots of Φ; and a
  rational root u₀ of Φ has g(x_j(u₀)) = 0, so its h_j-image is a
  rational 2-torsion point of E′. Since #E′(F_q) is an odd prime, E′
  has no rational 2-torsion, so Φ has no rational roots and this case
  is empty.
- **u = 0**: H_j(0) = d_j·B², in the square class of d_j
  (`model1_zero`, `model2_zero`).
- **u = ∞**: the leading coefficient of H_j is d_j·B²·Z⁷, in the
  square class of d_j·Z.

Since d₁ ≡ −A·B·Z and d₂ ≡ −A·B differ by the nonsquare Z, exactly one
of {C₁, C₂} has a rational pair over u = 0, and the other has its pair
of rational points at infinity: four extra points in total, not
accounted for by inputs. Their images under h_j are read off the
abscissa functions (checked symbolically): x₁ has a pole at u = 0 and
tends to −B/A at u = ∞, while x₂(0) = −B/A and x₂ has a pole at
u = ∞. A pole of x_j at the place means the point maps to 𝒪. At the
deployed parameters −A·B is a nonsquare (the script's empty w = 0
fibre; the Euler certificates `neg_AB_not_isSquare`, one per
iso-curve), so the rational pairs are C₁'s over u = 0 and C₂'s at
infinity —both pole loci— and all four extra points map to 𝒪.

Summing, with f(0) = 𝒪 and χ(𝒪) = 1:

    S_{C₁}(χ) + S_{C₂}(χ) = Σ_{u ≠ 0} (χ + χ̄)(f(u)) + 4
                          = 2·S_f(χ) − 2·χ(𝒪) + 4 = 2·S_f(χ) + 2.

The first equality is `modelPoints_sum`, stated for any
commutative-monoid-valued φ with the boundary contributing 4·φ(𝒪);
the character form through to the + 2 is `cover_charSum`.

(If −A·B were a square, the rational pairs would swap to the −B/A
loci: all four extra points would map to the two rational points of E′
over w = 0, contributing 2·(χ + χ̄)(P₀) for P₀ one of them — bounded by
4 rather than equal to 4. The bound of §5 then holds with additive
constant 3 instead of 1. The deployed instances are in the nonsquare
case, so this variant is not needed for them.)

## 5. Conclusion

    2·|S_f(χ)| ≤ |S_{C₁}(χ)| + |S_{C₂}(χ)| + 2 ≤ 20·√q + 2,

so |S_f(χ)| ≤ 10·√q + 1 for every nontrivial χ, on both deployed
iso-curves. (For a valid parameter set with −A·B square, §4's variant
gives 10·√q + 3.) The square-root-free formal counterpart is
`weilBounded_zeroRepaired`: two `CharSumBounded` inputs at c²·#F yield
`WeilBounded` at c + 1/2, parametrically in the per-cover constant c;
the deployed c = 10 gives the recorded 21/2. The comparison with
FFSTV's Theorem 6 (52·√q + 151 for Z = −1, q ≡ 3 (mod 4),
residue-status sign rule): sign-freeness removes their conductor term
and the per-branch double-count, and the deployed covers have genus 6
against their 8.

The composition through the deployed 3-isogeny costs nothing: the
isogeny is bijective on rational points, so χ ∘ iso ranges over the
nontrivial characters of the iso-curve as χ does, and the bound
transfers to the full `mapToCurve` verbatim (`WeilBounded.comp`; per
curve, `weilBounded_zeroRepaired_mapToCurve`).

For `WeilBounded` (squared form): C = 21/2 satisfies
(10·√q + 1)² ≤ C²·q at the deployed sizes with margin ≈ 2^{127}. The
downstream regularity distance ε ≈ C²·√(#G)/#F (the budget shape of
`sum_abs_prob_dev_le`, carried to the deployed mapping by
`sum_abs_prob_dev_transport_le`) comes to about 2^{-120}, improving
the ≈ 2^{-116} previously quoted from the FFSTV-sized constant.
