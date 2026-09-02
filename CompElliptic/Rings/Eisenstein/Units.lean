/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Rings.Eisenstein.Mod
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The units of `ℤ[ω]`, and `2` as a prime

The arithmetic of `ℤ[ω]` that the finite claims in `Rings.Eisenstein.Orbits`
rest on, proved over `ℤ` rather than checked mod `8`.

Everything here follows from one fact: the norm `N(a + b·ω) = a² - a·b + b²` is
multiplicative (`norm_mul`), and over `ℤ` it is positive definite, because
`4·N = (2a - b)² + 3b²`. That identity is the whole file — it bounds the
solutions of `N = 1` to a box small enough to enumerate, which is what makes the
unit group finite and equal to `μ₆`.

## Main results

* `Eisenstein.isUnit_iff_norm_eq_one` — `x` is a unit iff `N x = 1`.
* `Eisenstein.norm_eq_one_iff`, `Eisenstein.isUnit_iff_mem_mu6Z` — the unit group
  is exactly `μ₆ = {±1, ±ω, ±ω²}`, six elements. These are the six automorphisms
  of a `j = 0` curve, which is why the orbit structure of
  `Rings.Eisenstein.Orbits` is the curve's own symmetry group acting.
* `Eisenstein.prime_two` — abstractly, `2` is a prime
  element of `ℤ[ω]` (it is *inert*, not split). The concrete input is the
  `16`-case check `mul_eq_zero_mod_two` in `Mod.lean`; here it is transported
  along the reduction `ℤ[ω] → ℤ[ω]/2 = 𝔽₄`.
* `Eisenstein.not_two_pow_dvd_unit_sub_one` — **the reason the freeness is not
  special to `w = 3`.** For a nontrivial unit `u`, `N(u - 1) ∈ {1, 3, 4}`, whereas
  `2^w ∣ u - 1` would force `4^w ∣ N(u - 1)`. Since `4^w ≥ 16` for `w ≥ 2`, the
  reduction `μ₆ → (ℤ[ω]/2^w)ˣ` is injective at every width `w ≥ 2`, so the unit
  action is free on the odd classes for every width. The article's `w = 3` is a
  cost choice, not a structural one. (At `w = 1` it genuinely fails: `-1 ≡ 1`
  mod `2`, and the six units collapse to three.)
-/

namespace CompElliptic.Rings.Eisenstein

/-! ## The norm as a monoid hom, and divisibility -/

section Hom

variable {R : Type*} [CommRing R]

/-- The norm packaged as a monoid hom `(R[ω], ×) → (R, ×)`, so that `map_pow`
and friends apply. -/
def normHom : Eisenstein R →* R where
  toFun := norm
  map_one' := norm_one
  map_mul' := norm_mul

@[simp] theorem normHom_apply (x : Eisenstein R) : normHom x = norm x := rfl

/-- `N(xⁿ) = (N x)ⁿ`. -/
theorem norm_pow (x : Eisenstein R) (n : ℕ) : norm (x ^ n) = norm x ^ n :=
  map_pow normHom x n

/-- The norm carries divisibility from `R[ω]` down to `R`. This is the step that
turns "`2^w` divides `u - 1`" into an arithmetic impossibility. -/
theorem norm_dvd_norm {x y : Eisenstein R} (h : x ∣ y) : norm x ∣ norm y := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨norm c, norm_mul x c⟩

/-- `4·N(a + b·ω) = (2a - b)² + 3b²`: completing the square. Over `ℤ` this makes
the norm positive definite, and it is the bound that makes `N = 1` finite. -/
theorem four_mul_norm (x : Eisenstein R) :
    4 * norm x = (2 * x.a - x.b) ^ 2 + 3 * x.b ^ 2 := by
  simp only [norm]; ring

end Hom

/-! ## Over `ℤ`: positive definiteness and the unit group -/

/-- The norm is nonnegative on `ℤ[ω]`: it is the quadratic form of discriminant
`-3`, which is definite. -/
theorem norm_nonneg (x : Eisenstein ℤ) : 0 ≤ norm x := by
  have h := four_mul_norm x
  nlinarith [sq_nonneg (2 * x.a - x.b), sq_nonneg x.b]

/-- `N 2 = 4`, so `2` is not a unit. -/
theorem norm_two : norm (2 : Eisenstein ℤ) = 4 := by
  rw [two_eq]; norm_num [norm]

/-- **`x` is a unit exactly when its norm is `1`.** Forward: `N` is
multiplicative, so `N x` is a unit of `ℤ`, hence `±1`, hence `1` by
positive definiteness. Backward: `x · conj x = N x = 1` exhibits the inverse. -/
theorem isUnit_iff_norm_eq_one (x : Eisenstein ℤ) : IsUnit x ↔ norm x = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : norm (u : Eisenstein ℤ) * norm (↑u⁻¹ : Eisenstein ℤ) = 1 := by
      rw [← norm_mul]; simp
    have hu : IsUnit (norm (u : Eisenstein ℤ)) := by
      rw [isUnit_iff_exists_and_exists]
      exact ⟨⟨_, h⟩, ⟨_, by rw [mul_comm]; exact h⟩⟩
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact h1
    · have := norm_nonneg (u : Eisenstein ℤ); omega
  · intro h
    have hx : x * conj x = 1 := by rw [mul_conj, h]; rfl
    rw [isUnit_iff_exists_and_exists]
    exact ⟨⟨conj x, hx⟩, ⟨conj x, by rw [mul_comm]; exact hx⟩⟩

/-- **The unit group is `μ₆`.** `N = 1` forces `(2a - b)² + 3b² = 4`, so
`|b| ≤ 1` and `|a| ≤ 1`, and the box has exactly six solutions. -/
theorem norm_eq_one_iff (x : Eisenstein ℤ) :
    norm x = 1 ↔ x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩ ∨ x = ⟨0, 1⟩ ∨ x = ⟨0, -1⟩ ∨
      x = ⟨1, 1⟩ ∨ x = ⟨-1, -1⟩ := by
  obtain ⟨a, b⟩ := x
  simp only [norm_mk, Eisenstein.mk.injEq]
  constructor
  · intro h
    have hb : -1 ≤ b ∧ b ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (2 * a - b)]
    have ha : -1 ≤ a ∧ a ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg b, sq_nonneg (2 * a - b)]
    obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨ha1, ha2⟩ := ha
    interval_cases a <;> interval_cases b <;> revert h <;> decide
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩) <;> norm_num

/-- The six units of `ℤ[ω]`: `{1, -1, ω, -ω, -ω², ω²}`. These are exactly the
six automorphisms `(x, y) ↦ (ζ₃ᵏ·x, ±y)` of a `j = 0` curve, which is why the
recoding's orbit structure is the curve's own symmetry. -/
def mu6Z : Finset (Eisenstein ℤ) :=
  {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩}

theorem mu6Z_card : mu6Z.card = 6 := by decide

/-- The unit group of `ℤ[ω]` is `μ₆`, and it has order `6`. -/
theorem isUnit_iff_mem_mu6Z (x : Eisenstein ℤ) : IsUnit x ↔ x ∈ mu6Z := by
  rw [isUnit_iff_norm_eq_one, norm_eq_one_iff]
  simp [mu6Z]

/-! ## `2` is prime in `ℤ[ω]` -/

/-- Reduction `ℤ[ω] → ℤ[ω]/2 = 𝔽₄`, coefficient-wise. -/
def redTwo : Eisenstein ℤ →+* Eisenstein (ZMod 2) :=
  Eisenstein.map (Int.castRingHom (ZMod 2))

/-- Being even is being zero in the residue field. -/
theorem two_dvd_iff_redTwo_eq_zero (x : Eisenstein ℤ) :
    (2 : Eisenstein ℤ) ∣ x ↔ redTwo x = 0 := by
  rw [two_dvd_iff]
  constructor
  · rintro ⟨ha, hb⟩
    ext <;> simp [redTwo, map, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr, ha, hb]
  · intro h
    have ha : ((x.a : ZMod 2)) = 0 := congrArg Eisenstein.a h
    have hb : ((x.b : ZMod 2)) = 0 := congrArg Eisenstein.b h
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp ha,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hb⟩

/-- `2` is a prime element of `ℤ[ω]`: it is INERT, so
`ℤ[ω]/2` is the field `𝔽₄` rather than a product. This is what makes "even" and
"odd" mean the same in `ℤ[ω]` as coordinate-wise, makes halving exact, and makes
`ℤ[ω]/2^w` a local ring whose units are exactly the odd classes — the fact
behind `card_odd = 48`. -/
theorem prime_two : Prime (2 : Eisenstein ℤ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [show (0 : Eisenstein ℤ) = ⟨0, 0⟩ from rfl, two_eq] at h
    simp at h
  · rw [isUnit_iff_norm_eq_one, norm_two]
    norm_num
  · intro x y hxy
    rw [two_dvd_iff_redTwo_eq_zero] at hxy ⊢
    rw [two_dvd_iff_redTwo_eq_zero]
    rw [map_mul] at hxy
    exact mul_eq_zero_mod_two _ _ hxy

/-! ## Why the freeness holds at every width `w ≥ 2` -/

/-- For each of the five nontrivial units, `N(u - 1)` is `1`, `3` or `4` — in
particular nonzero and at most `4`. The three values are `N(-2) = 4`,
`N(ω - 1) = N(ω² - 1) = 3` and `N(-ω - 1) = N(-ω² - 1) = 1`. -/
theorem norm_sub_one_of_mem_mu6Z :
    ∀ u ∈ mu6Z, u ≠ 1 → 0 < norm (u - 1) ∧ norm (u - 1) ≤ 4 := by decide

/-- **The reduction `μ₆ → (ℤ[ω]/2^w)ˣ` is injective for every `w ≥ 2`**, so the
unit action is free on the odd classes at every width, not only at the `w = 3`
the article uses.

The argument is the norm: `2^w ∣ u - 1` would give `4^w ∣ N(u - 1)`, hence
`4^w ≤ N(u - 1) ≤ 4`, contradicting `4^w ≥ 16`. This fails at `w = 1` exactly
because `4 ≤ 4`, and indeed `-1 ≡ 1 (mod 2)`. -/
theorem not_two_pow_dvd_unit_sub_one {w : ℕ} (hw : 2 ≤ w) {u : Eisenstein ℤ}
    (hu : IsUnit u) (hu1 : u ≠ 1) : ¬ ((2 : Eisenstein ℤ) ^ w ∣ u - 1) := by
  intro hdvd
  obtain ⟨hpos, hle⟩ := norm_sub_one_of_mem_mu6Z u ((isUnit_iff_mem_mu6Z u).mp hu) hu1
  have hn : norm ((2 : Eisenstein ℤ) ^ w) ∣ norm (u - 1) := norm_dvd_norm hdvd
  rw [norm_pow, norm_two] at hn
  have h1 : (4 : ℤ) ^ w ≤ norm (u - 1) := Int.le_of_dvd hpos hn
  have h2 : (4 : ℤ) ^ 2 ≤ (4 : ℤ) ^ w := pow_le_pow_right₀ (by norm_num) hw
  norm_num at h2
  omega

end CompElliptic.Rings.Eisenstein
