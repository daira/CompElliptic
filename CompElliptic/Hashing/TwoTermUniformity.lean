/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.WellDistributed
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Two-term hash uniformity from character sums

The hash-to-curve construction deployed for the Pasta curves computes
`m ↦ f (h₁ m) + f (h₂ m)`: hash to two field elements, map each through `f` to
a curve point, and add the two points. A single evaluation of `f` is visibly
non-uniform (its image covers only a constant fraction of the curve), so the
construction sums two independent copies. This file proves that the repair works:
if all the nontrivial "character sums" of `f` are small —the `WeilBounded`
hypothesis— then the two-term output distribution is within a small statistical
distance of uniform on the whole group.

## Characters, for readers who know the DFT

The DFT analyzes a signal on `ℤ/N` against the reference waves
`a ↦ exp (2πi·k·a/N)`, one per frequency `k`. What makes those waves work is not
anything analytic about the exponential — it is the identity
`exp(2πi·k·(a + b)/N) = exp(2πi·k·a/N) · exp(2πi·k·b/N)`, which turns addition of
signal positions into multiplication of wave values. A **character** of a finite
abelian group `G` keeps exactly that property and discards the rest: it is a map
`ψ : G → ℂ` with `ψ (a + b) = ψ a * ψ b` (so `ψ 0 = 1`, and every value is a root
of unity, hence on the unit circle). Mathlib packages these as `AddChar G ℂ`.
For `G = ℤ/N` the characters are precisely the `N` reference waves of the DFT;
for a general finite abelian `G` there are exactly `#G` of them
(`AddChar.card_eq`), and they support the same Fourier toolkit. Two facts carry
the whole file, and both are the finite-group forms of facts commonly used with
the DFT:

* **Orthogonality**: summing a nontrivial wave over a full period gives zero.
* **Parseval**: total energy is the same whether you sum squares in the signal
  domain or in the frequency domain.

Elliptic-curve points under point addition are a finite abelian group, so all of
this applies to them directly; no geometry enters this file.

## The pipeline

`pairCount f Q` counts pairs `(u₀, u₁)` with `f u₀ + f u₁ = Q`. Dividing by
`(#F)²` gives the probability that the two-term hash outputs `Q`, so uniformity
means `pairCount` is close to the constant `(#F)²/#G`. The proofs mirror the
standard DFT pipeline for analyzing a convolution — the distribution of a sum of
independent variables is a convolution, and convolution in the signal domain is
multiplication in the frequency domain:

* `sum_addChar_apply` (orthogonality over frequencies): `∑ ψ, ψ a` is `#G` when
  `a = 0` and `0` otherwise. This is the "delta function as a sum of waves"
  identity underlying Fourier inversion.
* `card_mul_pairCount` (the Fourier expansion): the transform of `pairCount` at
  frequency `ψ` is the square of `S ψ := ∑ u, ψ (f u)` — squared because the two
  inputs are independent, exactly as convolving a signal with itself squares its
  spectrum.
* `card_mul_sum_sq_pairCount` (Parseval): `#G * ∑ Q, (pairCount f Q)² =
  ∑ ψ, ‖S ψ‖⁴`. Note this identity consumes no Weil bound: it is the exact
  second moment of the output distribution, valid for every `f`.
* `sum_sq_dev_le`: feeding `WeilBounded f C` into Parseval bounds the summed
  squared deviation of `pairCount` from its uniform value. The trivial character
  contributes the main term and is removed exactly; each of the `#G - 1`
  nontrivial frequencies contributes at most `(C²·#F)²`.
* `sq_sum_abs_dev_le` and `sq_sum_abs_prob_dev_le`: Cauchy–Schwarz converts the
  squared-deviation bound into (the square of) the L¹ deviation — twice the
  statistical distance. In the deployed setting `#G ≈ #F = q ≈ 2^{254}` and the
  constant expected from FFSTV is `C ≈ 52`, making the statistical distance
  about `C²/√q ≈ 2^{-116}`. That figure relies on the `WeilBounded` hypothesis:
  established mathematics, but an unformalized input here (see
  `WellDistributed.lean`).

Everything here is stated for an arbitrary function `f : F → G` from a finite
type into a finite abelian group; oddness of the mapping and the elliptic curve
itself play no role in this file (they enter upstream, in `CharacterSum.lean`,
where the Weil-bound hypothesis is connected to the sign-free geometry).
-/

namespace CompElliptic.Hashing

open Finset
open scoped ComplexConjugate

variable {F : Type*} [Fintype F]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- `pairCount f Q` is the number of input pairs `(u₀, u₁)` with
`f u₀ + f u₁ = Q` — the unnormalized distribution of the two-term hash output
`f u₀ + f u₁` for independent uniform inputs. Dividing by `(#F)²` gives the
probability of the output `Q`; uniformity means `pairCount f` is close to the
constant `(#F)²/#G`. -/
def pairCount (f : F → G) (Q : G) : ℕ :=
  (univ.filter fun p : F × F => f p.1 + f p.2 = Q).card

/-- The pair counts total `(#F)²`: every pair lands somewhere. -/
theorem sum_pairCount (f : F → G) :
    ∑ Q, pairCount f Q = (Fintype.card F)^2 := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun p : F × F => f p.1 + f p.2) (s := univ) (t := univ)
    (fun p _ => mem_univ _)
  simpa [pairCount, Finset.card_univ, Fintype.card_prod, sq] using h.symm

/-- **Orthogonality over frequencies.** Summing every character at a fixed point
`a` detects whether `a = 0`: the sum is `#G` at `a = 0` (all waves read `1`
there) and `0` elsewhere. This is the finite-group form of "a delta function is
the average of all reference waves", the identity behind Fourier inversion.

The proof is a neat self-application: `a` evaluates characters, so `a` *is* a
character of the character group (`AddChar.doubleDualEmb`), and the sum over the
dual group is handled by the same one-line trick that proves orthogonality over
the group itself (`AddChar.sum_eq_ite`). Pontryagin duality supplies the two
facts that make the answer come out right: evaluation at `a ≠ 0` is a nontrivial
character of the dual (`AddChar.doubleDualEmb_injective`), and the dual has
exactly `#G` elements (`AddChar.card_eq`). -/
theorem sum_addChar_apply (a : G) :
    ∑ ψ : AddChar G ℂ, ψ a = if a = 0 then (Fintype.card G : ℂ) else 0 := by
  classical
  rw [Finset.sum_congr rfl fun ψ _ => (AddChar.doubleDualEmb_apply a ψ).symm,
    AddChar.sum_eq_ite]
  by_cases ha : a = 0
  · rw [if_pos (by rw [ha]; exact map_zero _), if_pos ha, AddChar.card_eq]
  · rw [if_neg (fun h0 => ha (AddChar.doubleDualEmb_injective
      (h0.trans (map_zero _).symm))), if_neg ha]

/-- **The Fourier expansion of the pair count.** The distribution of a sum of two
independent variables is a convolution, and convolution in the signal domain is
multiplication in the frequency domain — here the two summands are identically
distributed, so the transform of `pairCount f` at frequency `ψ` is the *square*
of the single-copy character sum `S ψ = ∑ u, ψ (f u)`. Concretely:

`#G * pairCount f Q = ∑ ψ, ψ (-Q) * (S ψ)²`.

This squaring is the entire reason the deployed hash sums two independent
copies: whatever bound the nontrivial `S ψ` satisfy, the two-term construction
satisfies its square. -/
theorem card_mul_pairCount (f : F → G) (Q : G) :
    (Fintype.card G : ℂ) * pairCount f Q
      = ∑ ψ : AddChar G ℂ, ψ (-Q) * (∑ u, ψ (f u))^2 := by
  classical
  have expand : ∀ ψ : AddChar G ℂ,
      ψ (-Q) * (∑ u, ψ (f u))^2 = ∑ p : F × F, ψ (f p.1 + f p.2 - Q) := by
    intro ψ
    rw [sq, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun u₀ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u₁ _ => ?_
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun ψ _ => expand ψ, Finset.sum_comm]
  have inner : ∀ p : F × F,
      ∑ ψ : AddChar G ℂ, ψ (f p.1 + f p.2 - Q)
        = if f p.1 + f p.2 = Q then (Fintype.card G : ℂ) else 0 := by
    intro p
    rw [sum_addChar_apply]
    simp only [sub_eq_zero]
  rw [Finset.sum_congr rfl fun p _ => inner p, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, pairCount, mul_comm]

/-- **Parseval, a.k.a. the second moment of the output distribution.** Energy can
be computed in either domain: `#G` times the sum of the squared pair counts
equals the sum over all frequencies of `‖S ψ‖⁴`. (In additive-combinatorics
language, the left-hand side is `#G` times the *additive energy* of `f`.)

This identity involves no Weil bound and no hypothesis on `f` whatsoever — it is
exact bookkeeping, and it already gives the *average* size of the nontrivial
`‖S ψ‖`: everything the curve's group order can say about uniformity is
contained here. What it cannot give is a bound on the *worst* frequency, which
is what the statistical-distance estimate needs and what `WeilBounded`
supplies. -/
theorem card_mul_sum_sq_pairCount (f : F → G) :
    (Fintype.card G : ℝ) * ∑ Q, (pairCount f Q : ℝ)^2
      = ∑ ψ : AddChar G ℂ, ‖∑ u, ψ (f u)‖^4 := by
  classical
  -- Cross-frequency orthogonality: distinct waves cancel over the group.
  have ortho : ∀ ψ φ : AddChar G ℂ,
      ∑ Q, ψ (-Q) * conj (φ (-Q)) = if φ = ψ then (Fintype.card G : ℂ) else 0 := by
    intro ψ φ
    have step : ∀ Q : G, ψ (-Q) * conj (φ (-Q)) = (φ - ψ) Q := by
      intro Q
      rw [AddChar.map_neg_eq_conj φ, Complex.conj_conj, AddChar.sub_apply,
        AddChar.map_neg_eq_inv]
      ring
    rw [Finset.sum_congr rfl fun Q _ => step Q, AddChar.sum_eq_ite]
    simp [sub_eq_zero]
  -- Expand `(#G · pairCount)·conj(#G · pairCount)` through the Fourier expansion
  -- and collapse the double frequency sum with `ortho`.
  have key : (Fintype.card G : ℂ)^2 * ∑ Q, (pairCount f Q : ℂ)^2
      = (Fintype.card G : ℂ)
          * ∑ ψ : AddChar G ℂ, (∑ u, ψ (f u))^2 * conj ((∑ u, ψ (f u))^2) := by
    calc (Fintype.card G : ℂ)^2 * ∑ Q, (pairCount f Q : ℂ)^2
        = ∑ Q, ((Fintype.card G : ℂ) * pairCount f Q)
            * conj ((Fintype.card G : ℂ) * pairCount f Q) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun Q _ => ?_
          have : conj ((Fintype.card G : ℂ) * pairCount f Q)
              = (Fintype.card G : ℂ) * pairCount f Q := by simp
          rw [this]; ring
      _ = ∑ Q, (∑ ψ : AddChar G ℂ, ψ (-Q) * (∑ u, ψ (f u))^2)
            * conj (∑ φ : AddChar G ℂ, φ (-Q) * (∑ u, φ (f u))^2) := by
          refine Finset.sum_congr rfl fun Q _ => ?_
          rw [card_mul_pairCount]
      _ = ∑ ψ : AddChar G ℂ, ∑ φ : AddChar G ℂ,
            ((∑ u, ψ (f u))^2 * conj ((∑ u, φ (f u))^2))
              * ∑ Q, ψ (-Q) * conj (φ (-Q)) := by
          simp_rw [map_sum, Finset.sum_mul_sum, map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ψ _ => Finset.sum_comm.trans ?_
          refine Finset.sum_congr rfl fun φ _ => ?_
          exact Finset.sum_congr rfl fun Q _ => by ring
      _ = (Fintype.card G : ℂ)
            * ∑ ψ : AddChar G ℂ, (∑ u, ψ (f u))^2 * conj ((∑ u, ψ (f u))^2) := by
          simp_rw [ortho]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ψ _ => ?_
          simp_rw [mul_ite, mul_zero]
          rw [Finset.sum_ite_eq' univ ψ]
          simp only [mem_univ, if_true]
          ring
  -- Take the identity down to `ℝ`.
  have cast_lhs : (Fintype.card G : ℂ)^2 * ∑ Q, (pairCount f Q : ℂ)^2
      = ((Fintype.card G : ℝ)^2 * ∑ Q, (pairCount f Q : ℝ)^2 : ℝ) := by
    push_cast; ring
  have cast_rhs : (Fintype.card G : ℂ)
        * ∑ ψ : AddChar G ℂ, (∑ u, ψ (f u))^2 * conj ((∑ u, ψ (f u))^2)
      = ((Fintype.card G : ℝ) * ∑ ψ : AddChar G ℂ, ‖∑ u, ψ (f u)‖^4 : ℝ) := by
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [Complex.mul_conj']
    norm_cast
    rw [norm_pow]
    ring
  rw [cast_lhs, cast_rhs] at key
  have real_eq := Complex.ofReal_injective key
  have hG : (Fintype.card G : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨0⟩).ne'
  refine mul_left_cancel₀ hG ?_
  rw [← mul_assoc, ← sq]
  exact real_eq

/-- **The squared deviation from uniform, bounded.** Feeding the Weil bound into
Parseval: the trivial character's contribution to the second moment is exactly the
uniform main term and cancels, and each of the `#G - 1` nontrivial frequencies
contributes at most `(C²·#F)²` — the square coming from the two-term
construction. What remains is the summed squared deviation of the (scaled) pair
counts from their uniform value `(#F)²/#G`:

`∑ Q, (#G·pairCount f Q - (#F)²)² ≤ #G·(#G - 1)·(C²·#F)²`.

Dividing through by `(#G·(#F)²)²` reads this as: the output distribution is
within L² distance about `C²/(#F·√#G)` of uniform. -/
theorem sum_sq_dev_le (f : F → G) {C : ℝ} (h : WeilBounded f C) :
    ∑ Q, ((Fintype.card G : ℝ) * pairCount f Q - (Fintype.card F : ℝ)^2)^2
      ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) - 1)
          * (C^2 * Fintype.card F)^2 := by
  classical
  have hsum : ∑ Q, (pairCount f Q : ℝ) = (Fintype.card F : ℝ)^2 := by
    exact_mod_cast sum_pairCount f
  -- Expand the square and collapse the cross term with `hsum`.
  have expand : ∑ Q, ((Fintype.card G : ℝ) * pairCount f Q
        - (Fintype.card F : ℝ)^2)^2
      = (Fintype.card G : ℝ)^2 * ∑ Q, (pairCount f Q : ℝ)^2
          - (Fintype.card G : ℝ) * (Fintype.card F : ℝ)^4 := by
    have step : ∀ Q : G, ((Fintype.card G : ℝ) * pairCount f Q
          - (Fintype.card F : ℝ)^2)^2
        = (Fintype.card G : ℝ)^2 * (pairCount f Q : ℝ)^2
            - 2 * (Fintype.card F : ℝ)^2 * (Fintype.card G : ℝ)
              * (pairCount f Q : ℝ)
            + (Fintype.card F : ℝ)^4 := fun Q => by ring
    rw [Finset.sum_congr rfl fun Q _ => step Q, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- Parseval, with the trivial frequency split off.
  have parseval := card_mul_sum_sq_pairCount f
  have split : ∑ ψ : AddChar G ℂ, ‖∑ u, ψ (f u)‖^4
      = (Fintype.card F : ℝ)^4
          + ∑ ψ ∈ univ.erase (1 : AddChar G ℂ), ‖∑ u, ψ (f u)‖^4 := by
    rw [← Finset.add_sum_erase univ _ (mem_univ (1 : AddChar G ℂ))]
    congr 1
    simp
  -- Each nontrivial frequency obeys the (squared) Weil bound.
  have bound : ∑ ψ ∈ univ.erase (1 : AddChar G ℂ), ‖∑ u, ψ (f u)‖^4
      ≤ ((Fintype.card G : ℝ) - 1) * (C^2 * Fintype.card F)^2 := by
    have each : ∀ ψ ∈ univ.erase (1 : AddChar G ℂ),
        ‖∑ u, ψ (f u)‖^4 ≤ (C^2 * Fintype.card F)^2 := by
      intro ψ hψ
      have h2 := h ψ (Finset.mem_erase.mp hψ).1
      calc ‖∑ u, ψ (f u)‖^4 = (‖∑ u, ψ (f u)‖^2)^2 := by ring
        _ ≤ (C^2 * Fintype.card F)^2 := by gcongr
    calc ∑ ψ ∈ univ.erase (1 : AddChar G ℂ), ‖∑ u, ψ (f u)‖^4
        ≤ (univ.erase (1 : AddChar G ℂ)).card • (C^2 * Fintype.card F)^2 :=
          Finset.sum_le_card_nsmul _ _ _ each
      _ = ((Fintype.card G : ℝ) - 1) * (C^2 * Fintype.card F)^2 := by
          rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
            AddChar.card_eq, nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
          norm_num
  -- Combine: the deviation is `#G` times the nontrivial part of the spectrum.
  have collapse : ∑ Q, ((Fintype.card G : ℝ) * pairCount f Q
        - (Fintype.card F : ℝ)^2)^2
      = (Fintype.card G : ℝ)
          * ∑ ψ ∈ univ.erase (1 : AddChar G ℂ), ‖∑ u, ψ (f u)‖^4 := by
    rw [expand, sq, mul_assoc, parseval, split]
    ring
  rw [collapse, mul_assoc]
  exact mul_le_mul_of_nonneg_left bound (by positivity)

/-- **The L¹ deviation, squared, via Cauchy–Schwarz.** The statistical distance of
the two-term output from uniform is half the L¹ deviation of the probabilities;
this bounds the square of the (scaled) L¹ deviation, avoiding any square root. -/
theorem sq_sum_abs_dev_le (f : F → G) {C : ℝ} (h : WeilBounded f C) :
    (∑ Q, |(Fintype.card G : ℝ) * pairCount f Q - (Fintype.card F : ℝ)^2|)^2
      ≤ (Fintype.card G : ℝ)^2 * ((Fintype.card G : ℝ) - 1)
          * (C^2 * Fintype.card F)^2 := by
  classical
  have cs := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun Q => |(Fintype.card G : ℝ) * pairCount f Q - (Fintype.card F : ℝ)^2|)
    (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, sq_abs] at cs
  calc (∑ Q, |(Fintype.card G : ℝ) * pairCount f Q - (Fintype.card F : ℝ)^2|)^2
      ≤ (∑ Q, ((Fintype.card G : ℝ) * pairCount f Q - (Fintype.card F : ℝ)^2)^2)
          * (Fintype.card G : ℝ) := cs
    _ ≤ ((Fintype.card G : ℝ) * ((Fintype.card G : ℝ) - 1)
          * (C^2 * Fintype.card F)^2) * (Fintype.card G : ℝ) := by
        have := sum_sq_dev_le f h
        gcongr
    _ = (Fintype.card G : ℝ)^2 * ((Fintype.card G : ℝ) - 1)
          * (C^2 * Fintype.card F)^2 := by ring

/-- **The headline: statistical distance from uniform, squared.** In probability
form, `pairCount f Q / (#F)²` is the chance the two-term hash outputs `Q`, and
`1/#G` is the uniform chance, so the total variation distance is half of
`∑ Q, |probability - uniform|`. This theorem bounds that sum's square by
`(#G - 1)·C⁴/(#F)²`. For the deployed parameters (`#G ≈ #F = q ≈ 2^{254}`, with
`C ≈ 52` the constant expected from FFSTV for the hypothesis `h`) the
statistical distance is about `C²/√q ≈ 2^{-116}`. The two-term hash output is
therefore indistinguishable from a uniformly random group element up to that
error, which is the quantitative content of "the construction repairs the
non-uniformity of a single evaluation of `f`". -/
theorem sq_sum_abs_prob_dev_le [Nonempty F] (f : F → G) {C : ℝ}
    (h : WeilBounded f C) :
    (∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)|)^2
      ≤ ((Fintype.card G : ℝ) - 1) * C^4 / (Fintype.card F : ℝ)^2 := by
  classical
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have rewrite : ∀ Q : G, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)|
      = |(Fintype.card G : ℝ) * pairCount f Q - (Fintype.card F : ℝ)^2|
          / ((Fintype.card G : ℝ) * (Fintype.card F : ℝ)^2) := by
    intro Q
    rw [show (pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
          - 1 / (Fintype.card G : ℝ)
        = ((Fintype.card G : ℝ) * pairCount f Q - (Fintype.card F : ℝ)^2)
            / ((Fintype.card G : ℝ) * (Fintype.card F : ℝ)^2) from by
      field_simp]
    rw [abs_div]
    all_goals rw [abs_of_pos (show (0 : ℝ)
      < (Fintype.card G : ℝ) * (Fintype.card F : ℝ)^2 by positivity)]
  rw [Finset.sum_congr rfl fun Q _ => rewrite Q, ← Finset.sum_div, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∑ Q, |(Fintype.card G : ℝ) * pairCount f Q - (Fintype.card F : ℝ)^2|)^2
        * (Fintype.card F : ℝ)^2
      ≤ ((Fintype.card G : ℝ)^2 * ((Fintype.card G : ℝ) - 1)
          * (C^2 * Fintype.card F)^2) * (Fintype.card F : ℝ)^2 := by
        have := sq_sum_abs_dev_le f h
        gcongr
    _ = ((Fintype.card G : ℝ) - 1) * C^4
          * ((Fintype.card G : ℝ) * (Fintype.card F : ℝ)^2)^2 := by ring


/-! ## Exports for the indifferentiability arc

The game-side consumer (zcash/ironwood#198) works in `ℝ≥0∞` and should never
need a square root. `sum_abs_prob_dev_le` states the L¹ bound against any
budget `ε` whose square dominates the squared bound, so a concrete `ε` is
checked by squaring, in exact arithmetic. `card_dev_ge_le` is the
Chebyshev-style counting form of the L² bound: regularity does not
lower-bound individual fibres, so the rejection sampler's acceptance
constant holds only outside a bad set of fibres, whose size this bounds.
`sum_abs_pairCount_sub_le` prices replacing the zero-repaired mapping by the
deployed one: the two mappings differ at the single input `0`, so their
two-term pair counts differ only on pairs containing it. -/

/-- The L¹ probability deviation, unsquared, against an arbitrary budget: if
`ε²` dominates the squared bound then the deviation is at most `ε`. -/
theorem sum_abs_prob_dev_le [Nonempty F] (f : F → G) {C : ℝ}
    (h : WeilBounded f C) {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ((Fintype.card G : ℝ) - 1) * C^4 / (Fintype.card F : ℝ)^2
      ≤ ε^2) :
    ∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)| ≤ ε := by
  have hx : 0 ≤ ∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
      - 1 / (Fintype.card G : ℝ)| :=
    Finset.sum_nonneg fun Q _ => abs_nonneg _
  have hsq := (sq_sum_abs_prob_dev_le f h).trans hbound
  nlinarith [hsq, hx, hε]

/-- **Chebyshev-style bad-set counting**: the number of outputs whose pair
count deviates from its uniform value by at least `τ`, multiplied by `τ²`,
is at most the summed squared deviation. -/
theorem card_dev_ge_le (f : F → G) {C : ℝ} (h : WeilBounded f C) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    ((univ.filter fun Q => τ ≤ |(Fintype.card G : ℝ) * pairCount f Q
        - (Fintype.card F : ℝ)^2|).card : ℝ) * τ^2
      ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) - 1)
          * (C^2 * Fintype.card F)^2 := by
  classical
  refine le_trans ?_ (sum_sq_dev_le f h)
  calc ((univ.filter fun Q => τ ≤ |(Fintype.card G : ℝ) * pairCount f Q
          - (Fintype.card F : ℝ)^2|).card : ℝ) * τ^2
      = ∑ _Q ∈ univ.filter (fun Q => τ ≤ |(Fintype.card G : ℝ) * pairCount f Q
          - (Fintype.card F : ℝ)^2|), τ^2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ Q ∈ univ.filter (fun Q => τ ≤ |(Fintype.card G : ℝ) * pairCount f Q
          - (Fintype.card F : ℝ)^2|),
          ((Fintype.card G : ℝ) * pairCount f Q
            - (Fintype.card F : ℝ)^2)^2 := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        have hdev := (Finset.mem_filter.mp hQ).2
        calc τ^2 ≤ |(Fintype.card G : ℝ) * pairCount f Q
              - (Fintype.card F : ℝ)^2|^2 := pow_le_pow_left₀ hτ hdev 2
          _ = _ := sq_abs _
    _ ≤ ∑ Q, ((Fintype.card G : ℝ) * pairCount f Q
          - (Fintype.card F : ℝ)^2)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun Q _ _ => sq_nonneg _

/-- **The zero-repair transport for pair counts**: two mappings agreeing away
from a single input have two-term pair counts within `4·#F - 2` of each other
in L¹, because only the pairs containing that input can differ. -/
theorem sum_abs_pairCount_sub_le [Nonempty F] (f g : F → G) (u₀ : F)
    (h : ∀ u, u ≠ u₀ → f u = g u) :
    ∑ Q, |(pairCount f Q : ℝ) - (pairCount g Q : ℝ)|
      ≤ 4 * Fintype.card F - 2 := by
  classical
  set T : Finset (F × F) := univ.filter (fun p => p.1 = u₀ ∨ p.2 = u₀)
    with hT
  -- Pairs away from `T` have equal sums under `f` and `g`.
  have hagree : ∀ p : F × F, p ∉ T → f p.1 + f p.2 = g p.1 + g p.2 := by
    intro p hp
    simp only [hT, mem_filter, mem_univ, true_and, not_or] at hp
    rw [h p.1 hp.1, h p.2 hp.2]
  -- Each pair count splits at `T`, and the parts away from `T` agree.
  have hsplit : ∀ (m : F → G) (Q : G), (pairCount m Q : ℕ)
      = ((univ.filter fun p : F × F => m p.1 + m p.2 = Q) \ T).card
        + (T.filter fun p => m p.1 + m p.2 = Q).card := by
    intro m Q
    have hinter : (univ.filter fun p : F × F => m p.1 + m p.2 = Q) ∩ T
        = T.filter fun p => m p.1 + m p.2 = Q := by
      ext p
      simp only [Finset.mem_inter, mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
    rw [pairCount, ← hinter, add_comm]
    exact (Finset.card_inter_add_card_sdiff _ _).symm
  have hkey : ∀ Q : G, |(pairCount f Q : ℝ) - (pairCount g Q : ℝ)|
      ≤ ((T.filter fun p => f p.1 + f p.2 = Q).card : ℝ)
        + ((T.filter fun p => g p.1 + g p.2 = Q).card : ℝ) := by
    intro Q
    have hsdiff : ((univ.filter fun p : F × F => f p.1 + f p.2 = Q) \ T)
        = ((univ.filter fun p : F × F => g p.1 + g p.2 = Q) \ T) := by
      ext p
      simp only [Finset.mem_sdiff, mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨hpQ, hpT⟩ => ⟨by rw [← hagree p hpT]; exact hpQ, hpT⟩,
        fun ⟨hpQ, hpT⟩ => ⟨by rw [hagree p hpT]; exact hpQ, hpT⟩⟩
    rw [hsplit f Q, hsplit g Q, hsdiff]
    push_cast
    have hx : (0 : ℝ) ≤ (T.filter fun p => f p.1 + f p.2 = Q).card :=
      Nat.cast_nonneg _
    have hy : (0 : ℝ) ≤ (T.filter fun p => g p.1 + g p.2 = Q).card :=
      Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> [linarith; linarith]
  -- Sum the per-output bounds; each side totals `T.card` fibrewise.
  have hfib : ∀ m : F → G, ∑ Q : G,
      ((T.filter fun p => m p.1 + m p.2 = Q).card : ℝ) = (T.card : ℝ) := by
    intro m
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (f := fun p : F × F => m p.1 + m p.2) (s := T) (t := univ)
      fun p _ => mem_univ _).symm
  -- `T` is two axis copies of `F` overlapping in one pair.
  have hTcard : T.card = 2 * Fintype.card F - 1 := by
    have h1 : (univ.filter fun p : F × F => p.1 = u₀) = {u₀} ×ˢ univ := by
      ext p
      simp only [mem_filter, mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, and_true]
    have h2 : (univ.filter fun p : F × F => p.2 = u₀) = univ ×ˢ {u₀} := by
      ext p
      simp only [mem_filter, mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, true_and]
    have hint : (univ.filter fun p : F × F => p.1 = u₀)
        ∩ (univ.filter fun p : F × F => p.2 = u₀) = {(u₀, u₀)} := by
      ext p
      simp [Finset.mem_inter, Prod.ext_iff]
    have hcards := Finset.card_union_add_card_inter
      (univ.filter fun p : F × F => p.1 = u₀)
      (univ.filter fun p : F × F => p.2 = u₀)
    rw [hint, h1, h2] at hcards
    simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ,
      one_mul, mul_one] at hcards
    rw [hT, Finset.filter_or, h1, h2]
    omega
  have hF1 : 1 ≤ 2 * Fintype.card F := by
    have := Fintype.card_pos (α := F)
    omega
  calc ∑ Q, |(pairCount f Q : ℝ) - (pairCount g Q : ℝ)|
      ≤ ∑ Q : G, (((T.filter fun p => f p.1 + f p.2 = Q).card : ℝ)
          + ((T.filter fun p => g p.1 + g p.2 = Q).card : ℝ)) :=
        Finset.sum_le_sum fun Q _ => hkey Q
    _ = (T.card : ℝ) + (T.card : ℝ) := by
        rw [Finset.sum_add_distrib, hfib f, hfib g]
    _ = 4 * Fintype.card F - 2 := by
        rw [hTcard]
        push_cast [Nat.cast_sub hF1]
        ring

end CompElliptic.Hashing
