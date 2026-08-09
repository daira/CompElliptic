/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Character sums of odd mappings

A *mapping* here is any function `f : F → G` from a finite domain into a finite
abelian group — the term is RFC 9380's, whose `map_to_curve` functions are the
motivating instances. (The mathematical literature calls the same objects
*encodings*, as in "admissible encoding" and "well-distributed encoding";
CompElliptic reserves *encoding* for the scheme used to translate group elements
into their bit- or byte-sequence depictions and back. See
`design/naming-survey.md`.)

We study the character sum `∑ u, ψ (f u)` for an additive character `ψ` of `G`.
These sums control how close `f`, and sums of independent copies of it, come to
the uniform distribution on `G`.

The mappings used to hash to elliptic curves (simplified SWU and its relatives)
choose the sign of the `y`-coordinate from the sign of the input. That sign rule
makes the mapping **odd**: `f (-u) = -f u`. This file proves that oddness alone
forces two facts:

* the value multiplicity is symmetric under negation (`IsOdd.mult_neg`); and
* `f` sends `0` to `0` when `G` has odd order (`IsOdd.map_zero`).

The main identity (`charSum_eq`) rewrites `∑ u, ψ (f u)` as the character transform
of `fun Q => mult f Q - 1`, the deviation of the value multiplicity from a perfect
covering. The sign convention has disappeared. What remains is a statement about
which group elements `f` covers, and with what multiplicity; `IsOdd.mult_neg` says
that residual is negation-symmetric. Bounding it is out of scope here — it rests on
the Weil bound (the Riemann hypothesis for curves) applied to the encoding's
covering curve. This file isolates the elementary reduction that removes the sign
convention from the problem.
-/

namespace CompElliptic.Hashing

open Finset

variable {F : Type*} [AddGroup F] [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {f : F → G}

/-- `mult f Q` is the number of inputs that `f` maps to `Q`. -/
def mult (f : F → G) (Q : G) : ℕ := (univ.filter fun u => f u = Q).card

/-- A mapping is *odd* when negating the input negates the output. The simplified
SWU sign convention —choose the square root `y` with `sgn0 y = sgn0 u`— makes the
mapping odd in this sense: `-u` has the opposite input sign, so it selects `-y`. -/
def IsOdd (f : F → G) : Prop := ∀ u, f (-u) = -f u

omit [Fintype F] [DecidableEq F] [DecidableEq G] in
/-- An odd mapping sends `0` to `0`, provided `G` has odd order. `f 0` equals its own
negation, so it is a `2`-torsion element; a group of odd order has none except `0`. -/
theorem IsOdd.map_zero (hf : IsOdd f) (hG : Odd (Fintype.card G)) : f 0 = 0 := by
  have h2 : (2 : ℕ) • f 0 = 0 := by
    have h0 := hf 0
    rw [neg_zero] at h0
    rw [two_nsmul]; nth_rewrite 2 [h0]; exact add_neg_cancel (f 0)
  have hdvd2 : addOrderOf (f 0) ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2
  have hdvdc : addOrderOf (f 0) ∣ Fintype.card G := addOrderOf_dvd_card
  have hg : Nat.gcd 2 (Fintype.card G) = 1 := hG.coprime_two_left
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd hdvd2 hdvdc))

omit [Fintype G] in
/-- **Symmetrization.** The value multiplicity of an odd mapping is invariant under
negation: `f` covers `Q` and `-Q` equally often, with input negation the witnessing
bijection. This is the entire effect of the sign convention —over each fibre `{u, -u}`
it produces a value and its negation— and it is what makes the residual in
`charSum_eq` negation-symmetric. -/
theorem IsOdd.mult_neg (hf : IsOdd f) (Q : G) : mult f (-Q) = mult f Q := by
  unfold mult
  have hset : (univ.filter fun u => f u = -Q)
      = (univ.filter fun u => f u = Q).image (fun u => -u) := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hu; exact ⟨-u, by rw [hf u, hu, neg_neg], neg_neg u⟩
    · rintro ⟨v, hv, rfl⟩; rw [hf v, hv]
  rw [hset, Finset.card_image_of_injective _ neg_injective]

omit [AddGroup F] [DecidableEq F] in
/-- Regrouping the character sum by value: each `Q` is hit `mult f Q` times. Holds
for every mapping; no oddness is needed. -/
theorem charSum_eq_mult (ψ : AddChar G ℂ) :
    ∑ u, ψ (f u) = ∑ Q, (mult f Q : ℂ) * ψ Q := by
  classical
  have step1 : ∀ u, ψ (f u) = ∑ Q, if f u = Q then ψ Q else 0 := fun u => by
    rw [Finset.sum_ite_eq univ (f u) fun Q => ψ Q]; simp
  simp_rw [step1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

omit [AddGroup F] [DecidableEq F] in
/-- **The character sum, with the sign convention removed.** For a nontrivial
character `ψ`, the sum `∑ u, ψ (f u)` equals the character transform of
`fun Q => mult f Q - 1` — the deviation of the value multiplicity from a perfect
covering. The identity itself needs no oddness (only that a nontrivial character
sums to zero over `G`); oddness enters through `IsOdd.mult_neg`, which makes that
deviation negation-symmetric and hence amenable to a Weil bound on the covering. -/
theorem charSum_eq {ψ : AddChar G ℂ} (hψ : ψ ≠ 1) :
    ∑ u, ψ (f u) = ∑ Q, ((mult f Q : ℂ) - 1) * ψ Q := by
  rw [charSum_eq_mult]
  have hzero : ∑ Q, ψ Q = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  have hsplit : ∑ Q, ((mult f Q : ℂ) - 1) * ψ Q
      = (∑ Q, (mult f Q : ℂ) * ψ Q) - ∑ Q, ψ Q := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun Q _ => by ring
  rw [hsplit, hzero, sub_zero]

end CompElliptic.Hashing
