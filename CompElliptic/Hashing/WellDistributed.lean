/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.CharacterSum

/-!
# Well-distributed mappings and the Weil bound as an external input

A mapping `f : F → G` (from a finite field `F` to a finite abelian group `G`) is
*well-distributed* when its nontrivial character sums are small: `‖∑ u, ψ (f u)‖`
is `O(√#F)` for every nontrivial character `ψ`. Well-distributedness is what makes
a two-term hash `m ↦ f (h₁ m) + f (h₂ m)` statistically close to uniform on `G`.
That regularity is one ingredient of indifferentiability from a random oracle
into `G` — the mathematically deep one. The remaining ingredient, an efficient
preimage simulator, is tracked in <https://github.com/daira/CompElliptic/issues/25>.
The inner hash (`h₁`, `h₂`, the two `hash_to_field` outputs) stays abstract
throughout, modelled as a random oracle: only its type matters to the
formalization.

`CharacterSum.lean` reduces that character sum, for the odd mappings used in
hash-to-curve, to the sign-free covering-multiplicity deviation `mult f · - 1`,
using only group orthogonality. The one remaining ingredient —the actual bound
`‖∑ u, ψ (f u)‖ ≤ C·√#F`— is the Weil bound, and it is a genuine external input.
We state it as the hypothesis `WeilBounded` below rather than proving it.

## Why the Weil bound is not the target curve's order

It is tempting to hope that `#G` —the order of the target elliptic curve, which
CompElliptic pins exactly and elementarily (`CurveOrder`)— supplies this bound.
It does not, for four reasons that compound.

1. **It is a bound on a different curve.** The character sum `∑ u, ψ (f u)` equals,
   up to `O(1)`, a character sum over the *covering curve* `C` attached to the
   mapping (for simplified SWU, of genus 8). Its size is governed by Hasse–Weil
   for `C` (`|#C(F) - (#F + 1)| ≤ 2·genus·√#F`), not by the order of the target
   curve `E`. The order of `E` does not determine the order of `C`.

2. **One order is not a uniform family bound.** Well-distributedness needs the
   bound to hold *uniformly over every nontrivial character* `ψ`, i.e. over roughly
   `#G` distinct twists of the covering, each its own curve. Weil delivers that
   uniformity as a theorem. A single point count is one number, not a bound on a
   family of size `≈ #G`.

3. **CompElliptic's order method is special to near-prime-order elliptic curves.**
   `CurveOrder` pins `#E` from a prime-order witness (`r • P = 0`) plus the fibre
   bound `#E ≤ 2·#F + 1`. For a genus-8 curve the group to count is its Jacobian
   (the curve's own points carry no group law; the Jacobian's degree-0 divisor
   classes do, with the curve embedded in it), and that group has composite order
   `≈ (#F)⁸` — no prime to pin, which is the decisive obstruction. And the fibre
   bound is only good to a factor of about two, whereas the character sum needs
   `√#F`-precision — a far finer target than "pin to a prime". So the elementary
   method does not transfer.

4. **Jacobian arithmetic is necessary but not sufficient.** Even implementing the
   Jacobian's group operations (which we do not), there is no witness-plus-fibre
   shortcut at genus 8, and direct point counting over a field of size `≈ 2^{254}`
   is infeasible (no verified higher-genus counting algorithm; the naive count is
   `≈ 2^{254}` points). Off-line tools (e.g. Sage) can in principle count Jacobian
   points, but the result is one order, not the uniform family bound of (2), and
   using it in a proof would still require the Riemann-hypothesis-for-curves
   machinery that connects point counts to character sums — exactly the theorem
   being assumed.

So the Weil bound (the Riemann hypothesis for curves) enters exactly once, as the
hypothesis below. Everything upstream of it —the removal of the sign convention—
is the elementary, orthogonality-only content of `CharacterSum.lean`.

## References

- A. Weil, "Sur les courbes algébriques et les variétés qui s'en déduisent",
  Actualités Scientifiques et Industrielles 1041, Hermann, Paris, 1948.
  <http://denise.vella.chemla.free.fr/Weil-courbes-varietes.pdf> (The Riemann
  hypothesis for curves over finite fields, from which both the point-count bound
  `|#C(F) - (#F + 1)| ≤ 2·genus·√#F` and the character-sum form below follow.)
- R. R. Farashahi, P.-A. Fouque, I. E. Shparlinski, M. Tibouchi, and J. F. Voloch,
  "Indifferentiable deterministic hashing to elliptic and hyperelliptic curves", IACR
  Cryptology ePrint Archive, Report 2010/539, <https://eprint.iacr.org/2010/539>
  (later published in Mathematics of Computation 82 (2013), pp. 491–512). Lemma 1 is
  the character-sum form intended to discharge `WeilBounded`: for a nontrivial Artin
  character `χ` of conductor `𝔣` on a curve `X` of genus `g` over a field of size `q`,
  `|∑_{P ∈ X(F)} χ(P)| ≤ (2g − 2 + deg 𝔣(χ))·√q`. Theorem 3 is its workhorse form for
  encodings presented by a covering `C → E`. Theorem 6 instantiates it for the
  simplified SWU encoding of Brier et al. with the residue-status sign rule of
  Fouque-Tibouchi: `Z = -1`, fields of size `≡ 3 (mod 4)`, and the
  `y`-coordinate's sign given by its quadratic-residue status. It obtains
  `|S_f(χ)| ≤ 52·√q + 151` from genus-8 branch coverings; the conductor term
  `deg y = 12` accounts for the residue-status indicator, which enters the
  proof as a multiplicative character. The deployed variant differs in all
  three parameters. RFC 9380's `Z` criteria exclude `Z = -1` outright, and the
  deployed `Z = -13` is the first admissible candidate for each iso-curve
  independently under the RFC's search order. The Pasta base fields have size
  `≡ 1 (mod 4)`. The sign rule is the parity-based `sgn0`, which is not a
  multiplicative character, so the indicator step of the proof does not apply
  as written — though the sign-convention-free reduction in `CharacterSum.lean`
  makes the hypothesis depend only on the ±-class multiplicities, so a redone
  bound should not need a sign indicator at all. The genus computation for the
  `Z = -13` branch curves remains to be carried out and does not seem to be
  covered in the literature. Separately, `WeilBounded` itself is an external
  input to the formalization.
-/

namespace CompElliptic.Hashing

open Finset

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The Weil bound for a mapping `f : F → G`, in squared (exact-arithmetic) form:
every nontrivial character sum satisfies `‖∑ u, ψ (f u)‖² ≤ C²·#F`, the squared form
of `‖∑ u, ψ (f u)‖ ≤ C·√#F`. Squaring keeps the statement in exact real arithmetic
and avoids `Real.sqrt` (which is exact but noncomputable). This is the sole external
input —Hasse–Weil for the mapping's covering curve— that well-distributedness
rests on; see the module docstring for why it is not the target curve's order. -/
def WeilBounded (f : F → G) (C : ℝ) : Prop :=
  ∀ ψ : AddChar G ℂ, ψ ≠ 1 → ‖∑ u, ψ (f u)‖^2 ≤ C^2 * (Fintype.card F : ℝ)

omit [AddCommGroup F] [DecidableEq F] in
/-- The Weil bound, restated through the sign-convention-free reduction of
`charSum_eq`: it is equivalently a bound on the covering-multiplicity deviation
`mult f · - 1`. This is the form downstream uniformity estimates consume. -/
theorem WeilBounded.deviation {f : F → G} {C : ℝ} (h : WeilBounded f C)
    (ψ : AddChar G ℂ) (hψ : ψ ≠ 1) :
    ‖∑ Q, ((mult f Q : ℂ) - 1) * ψ Q‖^2 ≤ C^2 * (Fintype.card F : ℝ) := by
  rw [← charSum_eq hψ]; exact h ψ hψ

end CompElliptic.Hashing
