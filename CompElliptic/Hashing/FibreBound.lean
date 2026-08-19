/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.SimplifiedSWU
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree

/-!
# Fibre bounds for the simplified SWU mapping

Away from the input `u = 0`, every point of the target curve has at most 10
preimages under `SSWUParams.map`. This is the counting fact the
indifferentiability arc's rejection sampler consumes (zcash/ironwood#198,
CompElliptic#25): to sample a uniform preimage of a point under the deployed
two-term construction, the sampler needs each single-term fibre to be
computable and small; smallness is what makes its acceptance probability an
explicit constant. The input `u = 0` is excluded from the count; a consumer
needing the unconditional bound can add it back, as at most one extra
preimage per point.

The bound is by abscissa, and the argument is elementary root counting. On a
field where `-1` is a square (both Pasta base fields, `q ≡ 1 (mod 4)`), a
nonzero input is never exceptional: `ta = t² + t = 0` forces `t = 0` (which
is `u = 0`) or `t = -1` (which would make `-1/Z = u²` a square against `Z`
nonsquare). So a nonzero preimage `u` of a point with abscissa `x` satisfies
`xnum/xdiv = x`, where `xnum` is one of the two branch numerators and the
denominator is `xdiv = A·(-ta)`. Clearing the denominator turns membership
in *either* branch into the vanishing of the product polynomial

`Φ_x(u) = (x·(-A·ta) - x1num) · (x·(-A·ta) - x2num)`.

This is an explicit polynomial in `u` through `t = Z·u²`. Its second factor has
degree exactly 6 with leading coefficient `-B·Z³ ≠ 0`, so `Φ_x` is a nonzero
polynomial of degree at most 10, and has at most 10 roots.

The constant is deliberately crude; the proof stays at the level of one
product polynomial. The optimal constant is 4: each branch equation is a
quadratic in `t`, and oddness pairs `±u` across `P` and `-P` (which are
distinct — the target curves have no 2-torsion), so each `t` contributes one
preimage. Tightening to that constant is a planned follow-up.
-/

namespace CompElliptic.Hashing

open Finset Polynomial CompElliptic.CurveForms.ShortWeierstrass

namespace SSWUParams

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The polynomial `t = Z·u²`, as a polynomial in `u`. -/
noncomputable def tPoly (G : SSWUParams F) : Polynomial F := C G.Z * X^2

/-- The polynomial `ta = t² + t`, as a polynomial in `u`. -/
noncomputable def taPoly (G : SSWUParams F) : Polynomial F :=
  G.tPoly^2 + G.tPoly

/-- The abscissa-fibre polynomial `Φ_x`: away from `u = 0`, a preimage of
abscissa `x` under either branch is a root. The first factor is the branch-1
equation `x·(-A·ta) = x1num`, the second the branch-2 equation
`x·(-A·ta) = x2num`, both cleared of the denominator `xdiv = A·(-ta)`. -/
noncomputable def fibrePoly (G : SSWUParams F) (x : F) : Polynomial F :=
  (C x * (-(C G.E.A) * G.taPoly) - C G.E.B * (G.taPoly + 1)) *
    (C x * (-(C G.E.A) * G.taPoly) - G.tPoly * (C G.E.B * (G.taPoly + 1)))

/-- The second factor of `Φ_x` has degree exactly 6, because its leading
coefficient `-B·Z³` does not vanish for any `x`. -/
theorem fibrePoly_snd_natDegree (G : SSWUParams F) (x : F) :
    (C x * (-(C G.E.A) * G.taPoly)
      - G.tPoly * (C G.E.B * (G.taPoly + 1))).natDegree = 6 := by
  rw [taPoly, tPoly]
  compute_degree!
  exact ⟨G.Z_nonzero, G.E.B_nonzero, G.Z_nonzero⟩

/-- The second factor of `Φ_x` is nonzero, because it has degree 6. -/
theorem fibrePoly_snd_ne_zero (G : SSWUParams F) (x : F) :
    C x * (-(C G.E.A) * G.taPoly)
      - G.tPoly * (C G.E.B * (G.taPoly + 1)) ≠ 0 := by
  intro h
  have hdeg := G.fibrePoly_snd_natDegree x
  rw [h, natDegree_zero] at hdeg
  exact absurd hdeg (by norm_num)

/-- The first factor of `Φ_x` is nonzero, because it either has degree 4
(when `A·x + B ≠ 0`) or is the nonzero constant `-B`. -/
theorem fibrePoly_fst_ne_zero (G : SSWUParams F) (x : F) :
    C x * (-(C G.E.A) * G.taPoly) - C G.E.B * (G.taPoly + 1) ≠ 0 := by
  have hexpand : C x * (-(C G.E.A) * G.taPoly) - C G.E.B * (G.taPoly + 1)
      = -(C (G.E.A * x + G.E.B)) * G.taPoly - C G.E.B := by
    rw [map_add, map_mul]
    ring
  rw [hexpand]
  intro h
  by_cases hAB : G.E.A * x + G.E.B = 0
  · rw [hAB, map_zero, neg_zero, zero_mul, zero_sub, neg_eq_zero,
      C_eq_zero] at h
    exact G.E.B_nonzero h
  · have hdeg : (-(C (G.E.A * x + G.E.B)) * G.taPoly - C G.E.B).natDegree
        = 4 := by
      rw [taPoly, tPoly]
      compute_degree!
      refine ⟨fun hc => hAB ?_, G.Z_nonzero⟩
      linear_combination -hc
    rw [h, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)

/-- `Φ_x` is nonzero, because both its factors are. -/
theorem fibrePoly_ne_zero (G : SSWUParams F) (x : F) : G.fibrePoly x ≠ 0 :=
  mul_ne_zero (G.fibrePoly_fst_ne_zero x) (G.fibrePoly_snd_ne_zero x)

/-- `Φ_x` has degree at most 10: its first factor has degree at most 4,
and its second exactly 6 (`fibrePoly_snd_natDegree`). -/
theorem fibrePoly_natDegree_le (G : SSWUParams F) (x : F) :
    (G.fibrePoly x).natDegree ≤ 10 := by
  refine natDegree_mul_le.trans ?_
  have h1 : (C x * (-(C G.E.A) * G.taPoly)
      - C G.E.B * (G.taPoly + 1)).natDegree ≤ 4 := by
    rw [taPoly, tPoly]
    compute_degree
  have h2 := (G.fibrePoly_snd_natDegree x).le
  omega

/-- Away from `u = 0`, a preimage of abscissa `x` is a root of `Φ_x`. The
denominator is `A·(-ta)` with `ta ≠ 0`, and whichever branch the square-root
split took, the corresponding factor of `Φ_x` vanishes. -/
theorem eval_fibrePoly_eq_zero (G : SSWUParams F) {x u : F}
    (hta : (G.Z * u^2)^2 + G.Z * u^2 ≠ 0)
    (hx : (G.mapXYUpToSign u).1 = x) :
    (G.fibrePoly x).eval u = 0 := by
  have heval_t : G.tPoly.eval u = G.Z * u^2 := by
    simp [tPoly]
  have heval_ta : G.taPoly.eval u = (G.Z * u^2)^2 + G.Z * u^2 := by
    simp [taPoly, tPoly]
  simp only [mapXYUpToSign] at hx
  rw [if_neg hta] at hx
  have hxdiv : G.E.A * -((G.Z * u^2)^2 + G.Z * u^2) ≠ 0 :=
    mul_ne_zero G.A_nonzero (neg_ne_zero.mpr hta)
  rw [div_eq_iff hxdiv] at hx
  rw [fibrePoly, eval_mul]
  split_ifs at hx with hsr
  · apply mul_eq_zero_of_left
    simp only [eval_sub, eval_mul, eval_neg, eval_C, eval_add, eval_one,
      heval_ta]
    linear_combination -hx
  · apply mul_eq_zero_of_right
    simp only [eval_sub, eval_mul, eval_neg, eval_C, eval_add, eval_one,
      heval_ta, heval_t]
    linear_combination -hx

/-- A nonzero input is never exceptional when `-1` is a square, because
`ta = 0` forces `t = 0` (that is, `u = 0`) or `t = -1`, and the latter would
exhibit the nonsquare `Z` as `-1` times a square of an inverse. -/
theorem ta_ne_zero_of_u_ne_zero (G : SSWUParams F) (hsq : IsSquare (-1 : F)) {u : F}
    (hu : u ≠ 0) : (G.Z * u^2)^2 + G.Z * u^2 ≠ 0 := by
  intro h
  have hfac : G.Z * u^2 * (G.Z * u^2 + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h0 | h1
  · rcases mul_eq_zero.mp h0 with hZ | hu2
    · exact G.Z_nonzero hZ
    · exact hu (sq_eq_zero_iff.mp hu2)
  · obtain ⟨s, hs⟩ := hsq
    have hZu : G.Z * u^2 = -1 := by linear_combination h1
    refine G.Z_nonsquare ⟨s/u, ?_⟩
    rw [div_mul_div_comm, show u*u = u^2 from (pow_two u).symm]
    exact (eq_div_iff (pow_ne_zero 2 hu)).mpr (hZu.trans hs)

/-- **At most 10 nonzero preimages per abscissa.** On a field where `-1` is
a square, every nonzero preimage is a root of the degree-≤10 polynomial
`Φ_x`. -/
theorem card_abscissaFibre_le (G : SSWUParams F) (hsq : IsSquare (-1 : F))
    (x : F) :
    (univ.filter fun u => u ≠ 0 ∧ (G.mapXYUpToSign u).1 = x).card ≤ 10 := by
  have hsub : univ.filter (fun u => u ≠ 0 ∧ (G.mapXYUpToSign u).1 = x)
      ⊆ (G.fibrePoly x).roots.toFinset := by
    intro u hu
    rw [mem_filter] at hu
    rw [Multiset.mem_toFinset, mem_roots (G.fibrePoly_ne_zero x)]
    exact G.eval_fibrePoly_eq_zero (G.ta_ne_zero_of_u_ne_zero hsq hu.2.1) hu.2.2
  calc (univ.filter fun u => u ≠ 0 ∧ (G.mapXYUpToSign u).1 = x).card
      ≤ (G.fibrePoly x).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (G.fibrePoly x).roots.card := Multiset.toFinset_card_le _
    _ ≤ (G.fibrePoly x).natDegree := (G.fibrePoly x).card_roots'
    _ ≤ 10 := G.fibrePoly_natDegree_le x

/-- **At most 10 nonzero preimages per point** under the simplified SWU
mapping. A preimage of `P` is in particular a preimage of its abscissa. The
optimal constant is 4; the input `u = 0` is excluded, and a consumer can
count it separately as at most one extra preimage. -/
theorem card_map_fibre_le (G : SSWUParams F) (hsq : IsSquare (-1 : F))
    (P : SWPoint G.E) :
    (univ.filter fun u => u ≠ 0 ∧ G.map u = P).card ≤ 10 := by
  refine (Finset.card_le_card ?_).trans (G.card_abscissaFibre_le hsq P.x)
  intro u hu
  rw [mem_filter] at hu ⊢
  exact ⟨mem_univ u, hu.2.1,
    by rw [show (G.mapXYUpToSign u).1 = (G.map u).x from rfl, hu.2.2]⟩

end SSWUParams

/-- Composing with an injective map does not grow fibres: a fibre bound for
`f` is a fibre bound for `g ∘ f`. Stated with the auxiliary predicate that
the fibre-bound statements carry. -/
theorem card_fibre_comp_le {α β γ : Type*} [Fintype α] [DecidableEq β]
    [DecidableEq γ] {f : α → β} {g : β → γ} (hg : Function.Injective g)
    {pred : α → Prop} [DecidablePred pred] {n : ℕ}
    (h : ∀ Q : β, (univ.filter fun u => pred u ∧ f u = Q).card ≤ n)
    (P : γ) :
    (univ.filter fun u => pred u ∧ g (f u) = P).card ≤ n := by
  rcases (univ.filter fun u => pred u ∧ g (f u) = P).eq_empty_or_nonempty
    with he | ⟨u₀, hu₀⟩
  · rw [he, Finset.card_empty]
    exact Nat.zero_le n
  · rw [mem_filter] at hu₀
    refine (Finset.card_le_card ?_).trans (h (f u₀))
    intro u hu
    rw [mem_filter] at hu ⊢
    exact ⟨mem_univ u, hu.2.1, hg (hu.2.2.trans hu₀.2.2.symm)⟩

end CompElliptic.Hashing
