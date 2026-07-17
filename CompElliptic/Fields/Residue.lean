/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import Mathlib.FieldTheory.Finite.Basic

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
-/

namespace CompElliptic.Fields

/-- If `n ∣ #F - 1` and `a ^ ((#F - 1) / n) ≠ 1`, then `a` is not an `n`-th power in `F`.

An `n`-th root `x` of `a` is nonzero along with `a`, so Fermat's little theorem forces
`a ^ ((#F - 1) / n) = x ^ (n * ((#F - 1) / n)) = x ^ (#F - 1) = 1`. Contrapositively, evaluating
that one power and finding it is not `1` rules out every root at once. -/
theorem not_exists_pow_eq_of_pow_ne_one {F : Type*} [Field F] [Fintype F] {n : ℕ} {a : F}
    (hn : n ∣ Fintype.card F - 1) (ha : a ≠ 0)
    (h : a ^ ((Fintype.card F - 1) / n) ≠ 1) : ¬ ∃ x : F, x^n = a := by
  -- `n = 0` is already impossible: the exponent `(#F - 1) / 0` is `0`, so `h` reads `1 ≠ 1`.
  have hn0 : n ≠ 0 := by rintro rfl; simp at h
  rintro ⟨x, rfl⟩
  refine h ?_
  have hx : x ≠ 0 := by intro hzero; exact ha (by rw [hzero, zero_pow hn0])
  rw [← pow_mul, Nat.mul_div_cancel' hn]
  exact FiniteField.pow_card_sub_one_eq_one x hx

end CompElliptic.Fields
