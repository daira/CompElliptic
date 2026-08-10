/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.SignedLift
import CompElliptic.Fields.Sqrt
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The simplified SWU mapping: `sqrt_ratio`

This file begins the deployed hash-to-curve mapping of the Zcash protocol
specification, mirrored from §5.4.9.8 ("Group Hash into Pallas and Vesta"). The
spec's presentation takes precedence over RFC 9380 by its own declaration; the
two agree on every step used here, and the intent is to check the construction
against the `pasta_curves` Rust implementation, the `zcash-test-vectors` Python
code, and the underlying papers as each piece lands.

This slice defines `sqrt_ratio` (spec notation `sqrt_ratio_{GF(q)}(num, div)`):
divide, take a square root if one exists, and otherwise take a square root of
the ratio multiplied by a fixed nonsquare `lam` — which always exists, because a
nonsquare times a nonsquare is a square in a finite field
(`isSquare_mul_of_not_isSquare`, by multiplicativity of the quadratic
character). The `Bool` component reports which case occurred; the spec notes the
result is never `⊥`, which here is the fact that the `.getD 0` default is dead
code (`sqrtRatio_false_sq` proves the false branch still returns a genuine
root). The spec allows an arbitrary square root and an arbitrary nonsquare
`lam`; this implementation fixes the Tonelli–Shanks root of `Fields/Sqrt.lean`
and takes `lam` as a parameter, which matches the spec's note that neither
choice affects the mapping's output.
-/

namespace CompElliptic.Hashing

open CompElliptic.Fields

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- In a finite field, a nonsquare times a nonsquare is a square: the quadratic
character is multiplicative and takes the value `-1` on exactly the nonsquares,
so the product's character is `(-1)·(-1) = 1`. (In characteristic 2 the
hypothesis `¬ IsSquare a` is vacuous —every element is a square— so no
characteristic assumption is needed.) -/
theorem isSquare_mul_of_not_isSquare {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, (mul_zero 0).symm⟩)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ ⟨0, (mul_zero 0).symm⟩)
  have hχa : quadraticChar F a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have hχb : quadraticChar F b = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  refine (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).mp ?_
  rw [map_mul, hχa, hχb]
  ring

/-- `sqrt_ratio` of protocol spec §5.4.9.8: `(√(num/div), 1)` when `num/div` is
square, else `(√(lam·num/div), 0)` for the fixed nonsquare `lam`. The square
root is the Tonelli–Shanks root; the spec permits any root and any nonsquare
`lam`, and its output-independence note is what licenses fixing them. -/
def sqrtRatio (d : TonelliShanks F) (lam num div : F) : F × Bool :=
  match d.sqrt? (num / div) with
  | some r => (r, true)
  | none => ((d.sqrt? (lam * (num / div))).getD 0, false)

/-- The `Bool` component of `sqrt_ratio` reports squareness of the ratio. -/
theorem sqrtRatio_true_iff (d : TonelliShanks F) (lam num div : F) :
    (sqrtRatio d lam num div).2 = true ↔ IsSquare (num / div) := by
  rcases hs : d.sqrt? (num / div) with _ | r
  · simp only [sqrtRatio, hs]
    exact iff_of_false (by simp) fun hsq => by
      obtain ⟨r, hr⟩ := TonelliShanks.sqrt?_isSome_of_isSquare d hsq
      rw [hs] at hr
      cases hr
  · simp only [sqrtRatio, hs]
    exact iff_of_true trivial ⟨r, (TonelliShanks.sqrt?_mul_self d hs).symm⟩

/-- In the square case, `sqrt_ratio` returns a square root of the ratio. -/
theorem sqrtRatio_true_sq (d : TonelliShanks F) {lam num div : F}
    (h : (sqrtRatio d lam num div).2 = true) :
    (sqrtRatio d lam num div).1 * (sqrtRatio d lam num div).1 = num / div := by
  rcases hs : d.sqrt? (num / div) with _ | r
  · rw [sqrtRatio, hs] at h ⊢
    cases h
  · rw [sqrtRatio, hs]
    exact TonelliShanks.sqrt?_mul_self d hs

/-- In the nonsquare case, `sqrt_ratio` returns a square root of `lam` times the
ratio — never `⊥`, as the spec notes: the ratio is a nonzero nonsquare there, so
multiplying by the nonsquare `lam` makes it a square. -/
theorem sqrtRatio_false_sq (d : TonelliShanks F)
    {lam : F} (hlam : ¬ IsSquare lam) {num div : F}
    (h : (sqrtRatio d lam num div).2 = false) :
    (sqrtRatio d lam num div).1 * (sqrtRatio d lam num div).1
      = lam * (num / div) := by
  rcases hs : d.sqrt? (num / div) with _ | r
  · have hns : ¬ IsSquare (num / div) := fun hsq => by
      obtain ⟨r, hr⟩ := TonelliShanks.sqrt?_isSome_of_isSquare d hsq
      rw [hs] at hr
      cases hr
    obtain ⟨r, hr⟩ := TonelliShanks.sqrt?_isSome_of_isSquare d
      (isSquare_mul_of_not_isSquare hlam hns)
    rw [sqrtRatio, hs]
    simp only [hr, Option.getD_some]
    exact TonelliShanks.sqrt?_mul_self d hr
  · rw [sqrtRatio, hs] at h
    cases h

end CompElliptic.Hashing
