/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Higher-power residues in a finite field

Mathlib covers *quadratic* residues thoroughly (`ZMod.euler_criterion`, `FiniteField.isSquare_iff`,
the `LegendreSymbol` hierarchy), but all of that hard-codes the exponent 2; there is no n'th power
analogue.

We only need the *easy* direction of the residue criterion: a single power that misses 1 certifies
a non-residue. That direction is a two-line consequence of Fermat's little theorem and needs
nothing about the structure of `Fˣ`, whereas the converse would need its cyclicity.

This is used to derive the concrete non-residue facts about the Pasta base fields in `Curves.Pasta`
(`5` is not a square, and `-5` is not a cube in either field).

`cubic_no_root_of_resolvent_noncube` turns the cube case of that certificate into a no-root
certificate for a depressed cubic, via Cardano's method. `Hashing/PastaSSWU.lean` uses it to
discharge RFC 9380's criterion 3 (irreducibility of `g(X) - Z`) for the deployed hash-to-curve
parameters.
-/

namespace CompElliptic.Fields

/-- If `n ∣ #F - 1` and `a^((#F - 1) / n) ≠ 1`, then `a` is not an `n`-th power in `F`.

An `n`-th root `x` of `a` is nonzero along with `a`, so Fermat's little theorem forces
`a^((#F - 1) / n) = x^(n * ((#F - 1) / n)) = x^(#F - 1) = 1`. Contrapositively, evaluating
that one power and finding it is not `1` rules out every root at once. -/
theorem not_exists_pow_eq_of_pow_ne_one {F : Type*} [Field F] [Fintype F] {n : ℕ} {a : F}
    (hn : n ∣ Fintype.card F - 1) (ha : a ≠ 0)
    (h : a^((Fintype.card F - 1) / n) ≠ 1) : ¬ ∃ x : F, x^n = a := by
  -- `n = 0` is already impossible: the exponent `(#F - 1) / 0` is `0`, so `h` reads `1 ≠ 1`.
  have hn0 : n ≠ 0 := by rintro rfl; simp at h
  rintro ⟨x, rfl⟩
  refine h ?_
  have hx : x ≠ 0 := by intro hzero; exact ha (by rw [hzero, zero_pow hn0])
  rw [← pow_mul, Nat.mul_div_cancel' hn]
  exact FiniteField.pow_card_sub_one_eq_one x hx

/-- **Cardano's method as a no-root certificate for a depressed cubic.** Suppose `s` is a
square root of the discriminant of the resolvent quadratic (`27·s² = 27·q² + 4·A³`) and `w`
is the corresponding resolvent root (`2·w = -q + s`). If `w` is not a cube, then
`x³ + A·x + q` has no roots.

This is Cardano's formula run backwards. A root would split as `x = u + v` with
`3·u·v = -A`, making `u³` and `v³` the two roots of the resolvent quadratic `t² + q·t - A³/27`;
`w` is one of those roots, so it would be a cube. The proof stays inside `F`, with no
splitting field: for a root `x` with `3·x² + A ≠ 0`, setting `r := 3·s/(3·x² + A)` gives
`((x + r)³ - 8·w)·((x - r)³ - 8·w) = 0` as a polynomial consequence of the hypotheses, so `w` is
the cube of `(x + r)/2` or of `(x - r)/2`. A root with `3·x² + A = 0` forces `s = 0` and
`w = (-x)³` directly.

Over a finite field a cubic with no roots is irreducible. So this lemma, with
`not_exists_pow_eq_of_pow_ne_one` certifying the non-cube, makes RFC 9380's criterion 3
checkable by `decide` from two precomputed field elements. -/
theorem cubic_no_root_of_resolvent_noncube {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {A q s w : F}
    (hs : 27 * s^2 = 27 * q^2 + 4 * A^3)
    (hw : 2*w = -q + s)
    (hnc : ¬ ∃ u : F, u^3 = w) :
    ∀ x : F, x^3 + A*x + q ≠ 0 := by
  intro x hx
  have h27 : (27 : F) ≠ 0 := by
    have h := pow_ne_zero 3 h3
    norm_num at h
    exact h
  by_cases hd : 3 * x^2 + A = 0
  · -- A root that is also a critical point: then `s = 0` and `w = (-x)³`, a cube.
    have hq : q = 2 * x^3 := by linear_combination hx - x*hd
    have hs0 : s = 0 := by
      have h0 : 27 * s^2 = 0 := by
        linear_combination hs + 27 * (q + 2 * x^3) * hq
          + 4 * (A^2 - 3 * A * x^2 + 9 * x^4) * hd
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h0).resolve_left h27)
    refine hnc ⟨-x, mul_left_cancel₀ h2 ?_⟩
    linear_combination -hw + hq - hs0
  · -- Cardano's split inside `F`: `(x + r)/2` and `(x - r)/2` play the roles of `u` and `v`.
    obtain ⟨r, hr⟩ : ∃ r : F, r = 3*s / (3 * x^2 + A) := ⟨_, rfl⟩
    have hkey : 27 * s^2 = (3 * x^2 + A)^2 * (3 * x^2 + 4*A) := by
      linear_combination hs + 27 * (q - x^3 - A*x) * hx
    have hr3 : 3 * r^2 = 3 * x^2 + 4*A := by
      rw [hr]
      field_simp
      linear_combination hkey
    have hpr : 3 * ((x + r) * (x - r)) = -(4*A) := by linear_combination -hr3
    have hsum : (x + r)^3 + (x - r)^3 = -(8*q) := by
      linear_combination 2*x*hr3 + 8*hx
    have hwq : 108 * (w^2 + q*w) = 4 * A^3 := by
      linear_combination hs + 27 * (2*w + q + s) * hw
    have h0 : 27 * (((x + r)^3 - 8*w) * ((x - r)^3 - 8*w)) = 0 := by
      linear_combination
        (9 * ((x + r) * (x - r))^2 - 12 * ((x + r) * (x - r)) * A + 16 * A^2) * hpr
          - 216*w*hsum + 16*hwq
    rcases mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h27) with h | h
    · refine hnc ⟨(x + r) / 2, ?_⟩
      field_simp
      linear_combination h
    · refine hnc ⟨(x - r) / 2, ?_⟩
      field_simp
      linear_combination h

end CompElliptic.Fields
