/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood, Gregor Mitscha-Baude
-/
import CompElliptic.CurveForms.ShortWeierstrass
import Mathlib.GroupTheory.OrderOfElement

/-!
# Pinning a prime-order curve group's order without point-counting

For a curve whose group is *known to have prime order* r, fixing the order to exactly r needs
no point-counting algorithm (no Schoof, no proof of a counting algorithm's correctness).
It needs only:

1. a non-identity point P killed by r (so r ∣ #G, since r is prime); and
2. an upper bound on #G that leaves r (rather than some multiple ≥ 2r) as the only possible #G.

This module supplies both layers, and neither assumes any general theorem — in particular not
Hasse's theorem, which Mathlib lacks for `WeierstrassCurve`.

* **Layer 1 — pure finite-group theory.** `card_eq_of_prime_witness` holds for *any* finite
  additive group, with no reference to elliptic curves. A witness of r • P = 0 forces r ∣ #G,
  and #G < 2r then forces #G = r. `card_eq_of_prime_witness_of_lt_three_mul` reaches the same
  conclusion from the weaker #G < 3r, at the price of ruling out 2-torsion (which kills the extra
  candidate 2r by Cauchy's theorem).

* **Layer 2 — the fibre bound.** For a short-Weierstrass curve E over any finite field F, the
  equation y² = x³ + A x + B has at most two roots y for each fixed x; summing over #F choices of
  x and adding 𝒪 gives `#E(F) ≤ 2·#F + 1` (`card_le_two_mul_card_add_one`), with no arithmetic
  geometry. This overshoots the true count by a factor of about two where Hasse overshoots by only
  2√q, but it is unconditional, and it is enough whenever the prime r is close to the field size —
  exactly the situation for a prime-order cryptographic curve. Which of Layer 1's thresholds it
  clears is then decided by the two concrete numbers #F and r.

This is an application of the *Independently re-checkable trust* principle: no general theorem is
assumed, and all that a caller must discharge are closed numeric facts about #F and r, verifiable
by any independent tool.
-/

namespace CompElliptic.CurveOrder

open CompElliptic.CurveForms.ShortWeierstrass

/-! ## Layer 1: pin the order from a prime-order witness (any finite additive group) -/

/-- **The prime-order witness step.** A non-identity `P` killed by a prime `r` has `addOrderOf P`
exactly `r` (`addOrderOf_eq_prime`), so `r ∣ #G` by Lagrange.

This is the half of the argument that uses the witness, and the only half; everything downstream
just rules out the remaining multiples of `r` using an upper bound on `#G`. -/
theorem dvd_natCard_of_prime_witness {G : Type*} [AddGroup G] [Finite G] {r : ℕ}
    (hr : r.Prime) {P : G} (hP : P ≠ 0) (hPr : r • P = 0) : r ∣ Nat.card G := by
  haveI := Fact.mk hr
  exact addOrderOf_eq_prime hPr hP ▸ addOrderOf_dvd_natCard P

/-- If `r` is prime, the finite additive group `G` has a non-identity element `P` killed by `r`
(`r • P = 0`), and `#G < 2r`, then `#G = r`.

The witness gives `r ∣ #G` (`dvd_natCard_of_prime_witness`); with `0 < #G < 2r` the only multiple
of `r` available is `r` itself. -/
theorem card_eq_of_prime_witness {G : Type*} [AddGroup G] [Finite G] {r : ℕ}
    (hr : r.Prime) {P : G} (hP : P ≠ 0) (hPr : r • P = 0)
    (hlt2r : Nat.card G < 2 * r) : Nat.card G = r := by
  have hne0 : Nat.card G ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨P⟩, inferInstance⟩
  exact Nat.eq_of_dvd_of_lt_two_mul hne0 (dvd_natCard_of_prime_witness hr hP hPr) hlt2r

/-- The same conclusion as `card_eq_of_prime_witness` from a weaker bound `#G < 3r`, at the price
of ruling out 2-torsion (`hOdd`).

`#G < 2r` leaves `r` as the only multiple of `r` in range; `#G < 3r` also admits `2r`. That case is
excluded by parity rather than by counting: `#G = 2r` is even, so Cauchy's theorem would supply an
element of order exactly 2, which `hOdd` forbids.

The weaker bound is what an elementary point count affords when the prime sits just below the field
size, so this is the entry point for callers who cannot reach `2r` — but the argument is pure
finite-group theory and mentions no curve. -/
theorem card_eq_of_prime_witness_of_lt_three_mul {G : Type*} [AddGroup G] [Finite G] {r : ℕ}
    (hrPrime : r.Prime) {P : G} (hP : P ≠ 0) (hrP : r • P = 0)
    (hlt3r : Nat.card G < 3 * r) (hOdd : ∀ Q : G, 2 • Q = 0 → Q = 0) : Nat.card G = r := by
  obtain ⟨k, hk⟩ := dvd_natCard_of_prime_witness hrPrime hP hrP
  -- `#G = r * k` with `r * k < 3 * r`, so `k < 3`; `k = 0` contradicts `0 < #G`.
  have hklt3 : k < 3 := by
    refine Nat.lt_of_mul_lt_mul_left (a := r) ?_
    simp_all only [nsmul_zero, ne_eq, mul_comm]
  have hkne0 : k ≠ 0 := by
    rintro rfl
    exact absurd (hk.trans (Nat.mul_zero r)) Nat.card_pos.ne'
  -- `k = 2` would make `#G` even, so Cauchy would give an element of order 2 — excluded by `hOdd`.
  have hkne2 : k ≠ 2 := by
    rintro rfl
    haveI : Fintype G := Fintype.ofFinite _
    have hEven : 2 ∣ Fintype.card G := ⟨r, by rw [← Nat.card_eq_fintype_card, hk]; ring⟩
    obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card 2 hEven
    have hQ0 : Q ≠ 0 := fun h => by simp [h, addOrderOf_zero] at hQ
    exact hQ0 (hOdd Q (hQ ▸ addOrderOf_nsmul_eq_zero Q))
  rw [hk, show k = 1 by omega, Nat.mul_one]

/-- `SWPoint E` is finite whenever the base field is: it is a subtype of `F × F`
(`SWPoint.equivSubtype`). -/
instance instFiniteSWPoint {F : Type*} [Field F] [DecidableEq F] [Fintype F] (E : SWCurve F) :
    Finite (SWPoint E) :=
  Finite.of_equiv _ (SWPoint.equivSubtype E).symm

/-! ## Layer 2: the fibre bound `#E(F) ≤ 2 · #F + 1` -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- **At most two points share an x-coordinate.** Two on-curve points sharing an `x` have
`y² = x³ + A x + B` for the *same* right-hand side, so `(y₁ − y₂)(y₁ + y₂) = 0` and hence
`y₁ = y₂ ∨ y₁ = −y₂` — the short-Weierstrass form of `WeierstrassCurve.Affine.Y_eq_of_X_eq`.
The fibre for any point is therefore contained in the two-element set `{(x, y), (x, −y)}`. -/
theorem card_fibre_le_two [Fintype F] (E : SWCurve F) (x : F) :
    ((Finset.univ.filter fun R : F × F => OnCurve E.A E.B R).filter
      fun R => R.1 = x).card ≤ 2 := by
  rcases ((Finset.univ.filter fun R : F × F => OnCurve E.A E.B R).filter
      fun R => R.1 = x).eq_empty_or_nonempty with hR | ⟨P, hP⟩
  · simp [hR]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
    obtain ⟨hPOnCurve, hxP⟩ := hP
    refine le_trans (Finset.card_le_card ?_) ((Finset.card_insert_le P {(x, -P.2)}).trans (by simp))
    intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    obtain ⟨hQOnCurve, hxQ⟩ := hQ
    have hsq : Q.2 ^ 2 = P.2 ^ 2 := by
      simp only [OnCurve] at hPOnCurve hQOnCurve
      rw [hPOnCurve, hQOnCurve, hxP, hxQ]
    have hfac : (Q.2 - P.2) * (Q.2 + P.2) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext (hxQ.trans hxP.symm) (sub_eq_zero.mp h)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr (Prod.ext hxQ (eq_neg_of_add_eq_zero_left h))))

/-- **The unconditional cardinality bound**: at most two points per `x`-coordinate
(`card_fibre_le_two`) over `#F` choices of `x`, plus the identity `𝒪`.

This is elementary and holds for every short-Weierstrass curve over every finite field; it is
looser than Hasse (which Mathlib lacks) but needs no algebraic geometry. -/
theorem card_le_two_mul_card_add_one [Fintype F] (E : SWCurve F) :
    Nat.card (SWPoint E) ≤ 2 * Fintype.card F + 1 := by
  rw [Nat.card_congr (SWPoint.equivSubtype E), Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : (Finset.univ.filter fun R : F × F => Valid E.A E.B R) ⊆
      (Finset.univ.filter fun R : F × F => OnCurve E.A E.B R) ∪ {((0 : F), (0 : F))} := by
    intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton] at hR ⊢
    exact hR
  calc (Finset.univ.filter fun R : F × F => Valid E.A E.B R).card
      ≤ ((Finset.univ.filter fun R : F × F => OnCurve E.A E.B R) ∪ {0}).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun R : F × F => OnCurve E.A E.B R).card + 1 :=
        le_trans (Finset.card_union_le _ _) (by simp)
    _ ≤ 2 * Fintype.card F + 1 := by
        have h := Finset.card_le_mul_card_image_of_maps_to
          (f := Prod.fst) (t := (Finset.univ : Finset F))
          (fun _ _ => Finset.mem_univ _) 2 (fun x _ => card_fibre_le_two E x)
        rw [Finset.card_univ] at h
        omega

/-! ## Order pinning from the fibre bound

Both results below feed `card_le_two_mul_card_add_one` into Layer 1, replacing its `#G < 2r` (resp.
`#G < 3r`) premiss by a closed numeric comparison between `#F` and `r`. -/

/-- **Order of a prime-order curve group whose prime exceeds the field size.** If the prime `r`
kills the non-identity point `P` and `2 · #F + 1 < 2r`, the curve group has exactly `r` points.

The Layer 1 core `card_eq_of_prime_witness`, with the upper bound supplied by
`card_le_two_mul_card_add_one`. -/
theorem card_eq_of_prime_witness_of_card_lt_two_mul [Fintype F] (E : SWCurve F) {r : ℕ}
    (hrPrime : r.Prime) {P : SWPoint E} (hP : P ≠ 0) (hPr : r • P = 0)
    (hBound : 2 * Fintype.card F + 1 < 2 * r) :
    Nat.card (SWPoint E) = r :=
  card_eq_of_prime_witness hrPrime hP hPr
    (lt_of_le_of_lt (card_le_two_mul_card_add_one E) hBound)

/-- No 2-torsion on a curve, in odd characteristic, no point of which has `y = 0`.

A point with `2 • Q = 0` satisfies `Q = -Q`, hence `Q.y = -Q.y` and so `2 · Q.y = 0`; with
`2 ≠ 0` that forces `Q.y = 0`. An on-curve point cannot then exist by hypothesis, leaving
only the sentinel `𝒪`. This discharges the `hOdd` side condition of
`card_eq_of_prime_witness_of_card_lt_three_mul`. -/
theorem eq_zero_of_two_nsmul_eq_zero {E : SWCurve F} (h2ne0 : (2 : F) ≠ 0)
    (hy : ∀ x : F, ¬ OnCurve E.A E.B (x, 0)) {Q : SWPoint E} (hQ : 2 • Q = 0) : Q = 0 := by
  rw [two_nsmul] at hQ
  have hNeg : Q = -Q := eq_neg_of_add_eq_zero_left hQ
  have hyy : Q.y = -Q.y := by rw [← SWPoint.neg_y Q, ← hNeg]
  have hQy : Q.y = 0 := by
    have h2y : 2 * Q.y = 0 := by linear_combination hyy
    exact (mul_eq_zero.mp h2y).resolve_left h2ne0
  rcases Q.onCurve with hc | h0
  · rw [hQy] at hc
    exact absurd hc (hy Q.x)
  · exact SWPoint.ext_pair h0

/-- **Order of a prime-order curve group whose prime is below the field size.** There the fibre
bound only yields `#E(F) < 3r`, admitting `#E(F) = 2r` alongside `#E(F) = r`. Given additionally
that the group has no 2-torsion, `2r` is impossible, and `#E(F) = r`.

The curve-free half is Layer 1's `card_eq_of_prime_witness_of_lt_three_mul`; all this adds is the
fibre bound, so that the caller supplies a comparison between `#F` and `r` rather than one against
`#E(F)`. Use `eq_zero_of_two_nsmul_eq_zero` to supply `hOdd` from the absence of curve points with
`y = 0`. -/
theorem card_eq_of_prime_witness_of_card_lt_three_mul [Fintype F] (E : SWCurve F) {r : ℕ}
    (hrPrime : r.Prime) {P : SWPoint E} (hP : P ≠ 0) (hPr : r • P = 0)
    (hBound : 2 * Fintype.card F + 1 < 3 * r)
    (hOdd : ∀ Q : SWPoint E, 2 • Q = 0 → Q = 0) :
    Nat.card (SWPoint E) = r :=
  card_eq_of_prime_witness_of_lt_three_mul hrPrime hP hPr
    (lt_of_le_of_lt (card_le_two_mul_card_add_one E) hBound) hOdd

end CompElliptic.CurveOrder
