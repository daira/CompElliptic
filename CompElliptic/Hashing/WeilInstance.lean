/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.BranchCovers
import CompElliptic.Hashing.WellDistributed

/-!
# The Weil input at the branch covers

This file states the shape in which Weil's theorem enters the formalization,
and derives `WeilBounded` for the zero-repaired mapping from it.

`CharSumBounded s h B` says every nontrivial character of the target group
sums to at most `B` on the images of the point set `s` under `h`, in squared
norm. Weil's theorem — in the form of FFSTV's Lemma 1 and Theorem 3
(<https://eprint.iacr.org/2010/539>) — bounds such a sum over a genus-`g̃`
covering of an elliptic curve by `(2·g̃ - 2)·√q`, provided the covering does
not factor through a nontrivial unramified subcover. The branch covers have
genus 6, and their total ramification over `A·x + B = 0` rules every
unramified subcover out; both derivations are cited from
`design/weil-constant-derivation.md` §2–3, because even their statements
need machinery absent from Mathlib (genus, places, covers). So the intended
instantiations take `B = 100·#F`, the squared form of `10·√q` with
`10 = 2·6 - 2`; this hypothesis is the cited boundary. Progress is tracked
at <https://github.com/daira/CompElliptic/issues/28>.

`cover_charSum` is the sign-free assembly (design doc §4): for every
character `ψ`,

`S₁(ψ) + S₂(ψ) = 2·S(ψ) + 2`,

where `S_j` sums `ψ` over cover `j`'s images and `S` sums it over the
zero-repaired mapping's outputs. `weilBounded_zeroRepaired` combines the
assembly with the two cover bounds and exact square-free arithmetic:

`‖S(ψ)‖² ≤ (21/2)²·#F`   for every nontrivial `ψ`,

that is, `WeilBounded (zeroRepaired G.map) (21/2)`, on any field with
`#F ≥ 44` where `-1` is a square, `-A·B` is a nonsquare, the curve has no
2-torsion, and the sign function is genuine.
-/

namespace CompElliptic.Hashing

open Finset CompElliptic.CurveForms.ShortWeierstrass

/-- A squared character-sum bound over a finite point set: every nontrivial
character of the target group sums to at most `B` on the images, in squared
norm. Weil's theorem supplies such bounds for the rational points of curve
coverings, with `B = ((2·g̃ - 2))²·q` for a genus-`g̃` covering over a field
of size `q`; see the module docstring. -/
def CharSumBounded {ι G' : Type*} [AddCommGroup G'] (s : Finset ι)
    (h : ι → G') (B : ℝ) : Prop :=
  ∀ ψ : AddChar G' ℂ, ψ ≠ 1 → ‖∑ P ∈ s, ψ (h P)‖^2 ≤ B

namespace SSWUParams

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (G : SSWUParams F)

/-- **The sign-free assembly** (design doc §4): for every character `ψ` of
the curve group, the two covers' character sums combine to

`S₁(ψ) + S₂(ψ) = 2·S(ψ) + 2`,

with `S(ψ)` the character sum of the zero-repaired mapping. Negating the
input permutes the nonzero inputs and negates the output, so the two
per-input images `±(map u)` sum to twice the mapping's character sum; the
four boundary points contribute `ψ 𝒪 = 1` each, and the repaired `u = 0`
input supplies the `-2` that turns `+ 4` into `+ 2`. -/
theorem cover_charSum (hsq : IsSquare (-1 : F))
    (hy0 : ∀ x : F, ¬ OnCurve G.E.A G.E.B (x, 0))
    (hAB : ¬ IsSquare (-(G.E.A * G.E.B))) (hsgn : IsSignFunction G.sgn)
    (ψ : AddChar (SWPoint G.E) ℂ) :
    (∑ P ∈ G.modelPoints1, ψ (G.cover1Map hsq P))
      + (∑ P ∈ G.modelPoints2, ψ (G.cover2Map hsq P))
      = 2 * (∑ u, ψ (zeroRepaired G.map u)) + 2 := by
  rw [G.modelPoints_sum hsq hy0 hAB (fun P => ψ P), Finset.sum_add_distrib]
  have hneg : (∑ u ∈ (univ : Finset F).erase 0, ψ (-(G.map u)))
      = ∑ u ∈ (univ : Finset F).erase 0, ψ (G.map u) := by
    refine Finset.sum_equiv (Equiv.neg F) (fun u => ?_) (fun u hu => ?_)
    · simp [Finset.mem_erase]
    · simp only [Equiv.neg_apply,
        G.map_neg hsgn (Finset.mem_erase.mp hu).1]
  have hfull : (∑ u, ψ (zeroRepaired G.map u))
      = 1 + ∑ u ∈ (univ : Finset F).erase 0, ψ (G.map u) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : F))]
    congr 1
    · simp [zeroRepaired]
    · exact Finset.sum_congr rfl fun u hu => by
        simp [zeroRepaired, (Finset.mem_erase.mp hu).1]
  rw [hneg, hfull, AddChar.map_zero_eq_one]
  push_cast
  ring

/-- **`WeilBounded` from the two cover bounds.** Weil's theorem at the two
branch covers —`CharSumBounded` at `100·#F`, the squared `(2·6 - 2)·√q` of
the genus-6 coverings— yields the deployed Weil bound

`‖S(ψ)‖² ≤ (21/2)²·#F`

for the zero-repaired mapping. The margin between the additive-constant
sharp `10·√q + 1` and the recorded `(21/2)·√q` absorbs the boundary terms
once `#F ≥ 44`; the arithmetic stays square-root-free throughout. -/
theorem weilBounded_zeroRepaired (hsq : IsSquare (-1 : F))
    (hy0 : ∀ x : F, ¬ OnCurve G.E.A G.E.B (x, 0))
    (hAB : ¬ IsSquare (-(G.E.A * G.E.B))) (hsgn : IsSignFunction G.sgn)
    (hq : (44 : ℕ) ≤ Fintype.card F)
    (h1 : CharSumBounded G.modelPoints1 (G.cover1Map hsq)
      (100 * (Fintype.card F : ℝ)))
    (h2 : CharSumBounded G.modelPoints2 (G.cover2Map hsq)
      (100 * (Fintype.card F : ℝ))) :
    WeilBounded (zeroRepaired G.map) (21/2) := by
  intro ψ hψ
  have hid := G.cover_charSum hsq hy0 hAB hsgn ψ
  have ha := h1 ψ hψ
  have hb := h2 ψ hψ
  set S := ∑ u, ψ (zeroRepaired G.map u) with hS
  set S₁ := ∑ P ∈ G.modelPoints1, ψ (G.cover1Map hsq P) with hS₁
  set S₂ := ∑ P ∈ G.modelPoints2, ψ (G.cover2Map hsq P) with hS₂
  have hnorm : 2 * ‖S‖ ≤ ‖S₁‖ + ‖S₂‖ + 2 := by
    calc 2 * ‖S‖ = ‖(2 : ℂ) * S‖ := by
          rw [norm_mul, RCLike.norm_ofNat]
      _ = ‖S₁ + S₂ - 2‖ := by rw [show (2 : ℂ) * S = S₁ + S₂ - 2 from by
            linear_combination -hid]
      _ ≤ ‖S₁ + S₂‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖S₁‖ + ‖S₂‖) + 2 := by
          rw [RCLike.norm_ofNat]
          gcongr
          exact norm_add_le _ _
  have hq' : (44 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq
  have h4 : 4 * ‖S‖^2 ≤ (‖S₁‖ + ‖S₂‖ + 2)^2 := by
    nlinarith [hnorm, norm_nonneg S, norm_nonneg S₁, norm_nonneg S₂]
  nlinarith [h4, ha, hb, hq', norm_nonneg S₁, norm_nonneg S₂,
    sq_nonneg (‖S₁‖ - ‖S₂‖), sq_nonneg (‖S₁‖ + ‖S₂‖ - 20)]

end SSWUParams

end CompElliptic.Hashing
