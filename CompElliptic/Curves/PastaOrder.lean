/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood, Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta
import CompElliptic.CurveOrder

/-!
# Orders of the Pasta curve groups (Pallas and Vesta)

Instantiates the `CompElliptic.CurveOrder` fibre bound at the two Pasta curves, with no assumption:
the Pallas group has order `PALLAS_SCALAR_CARD` and the Vesta group has order `PALLAS_BASE_CARD`
(the Pasta cycle: each curve's order is the other's base-field size).

The test point `G = (-1, 2)` is the prime-order witness, and the witness fact `[order] G = 𝒪`
(a `≈ 2^254` scalar multiplication) is a one-line `native_decide` now that the `SWPoint` scalar
action `•` itself computes in `O(log n)`. The only *upper* bound needed is the elementary fibre
bound `#E(F) ≤ 2·#F + 1`; whether it clears the order threshold is decided by a closed comparison
of the two field sizes, and the Pasta cycle puts the two curves on opposite sides of it:

* **Pallas** — order `q = PALLAS_SCALAR_CARD` over the base field of size `p`, and `p < q`, so
  `2p + 1 < 2q` outright: `card_eq_of_prime_witness_of_card_lt_two_mul` closes it.
* **Vesta** — order `p = PALLAS_BASE_CARD` over the base field of size `q`, and `p < q`, so only
  `2q + 1 < 3p` is available. `#E = 2p` is ruled out separately: a 2-torsion point needs `y = 0`,
  i.e. `x³ = -5`, which `Pasta.Vesta.no_onCurve_y_zero` forbids.

Per the *Independently re-checkable trust* principle every obligation here is a closed numeric fact
(`2p + 1 < 2q`, `2q + 1 < 3p`), discharged by kernel `decide`; the only trust is the prime-order
witnesses (`q_nsmul_Gpt`, `p_nsmul_Gpt`), proved by `native_decide` and appearing in `#print axioms`
for the two theorems below.
-/

namespace CompElliptic.Curves.Pasta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder CompElliptic.Fields.Pasta

namespace Pallas

/-- The test point `(-1, 2)` as a point of the Pallas curve — the prime-order witness. -/
def Gpt : SWPoint curve := ⟨-1, 2, Or.inl (by decide)⟩

theorem Gpt_ne_zero : Gpt ≠ 0 := by decide

/-- `[q] G = 𝒪`, where `q = PALLAS_SCALAR_CARD` is the Pallas group order. -/
theorem q_nsmul_Gpt : PALLAS_SCALAR_CARD • Gpt = 0 := by native_decide

/-- **The Pallas curve group has order `PALLAS_SCALAR_CARD`**, unconditionally.

The Pallas group order `q` exceeds its base-field size `p`, so the fibre bound `#E ≤ 2p + 1`
already sits below `2q`, and the prime-order witness `G = (-1, 2)` pins the order outright. -/
theorem card_eq : Nat.card (SWPoint curve) = PALLAS_SCALAR_CARD := by
  refine card_eq_of_prime_witness_of_card_lt_two_mul curve PALLAS_SCALAR_is_prime Gpt_ne_zero
    q_nsmul_Gpt ?_
  rw [show Fintype.card PallasBaseField = PALLAS_BASE_CARD from ZMod.card _]
  decide

end Pallas

namespace Vesta

/-- The test point `(-1, 2)` as a point of the Vesta curve — the prime-order witness. -/
def Gpt : SWPoint curve := ⟨-1, 2, Or.inl (by decide)⟩

theorem Gpt_ne_zero : Gpt ≠ 0 := by decide

/-- `[p] G = 𝒪`, where `p = PALLAS_BASE_CARD` is the Vesta group order. -/
theorem p_nsmul_Gpt : PALLAS_BASE_CARD • Gpt = 0 := by native_decide

/-- **The Vesta curve group has order `PALLAS_BASE_CARD`**, unconditionally.

Here the group order `p` is *below* the base-field size `q`, so the fibre bound only gives
`#E ≤ 2q + 1 < 3p`, leaving `#E = 2p` open. That case needs a point of order 2, which would have
`y = 0` — impossible by `no_onCurve_y_zero`. -/
theorem card_eq : Nat.card (SWPoint curve) = PALLAS_BASE_CARD := by
  refine card_eq_of_prime_witness_of_card_lt_three_mul curve PALLAS_BASE_is_prime Gpt_ne_zero
    p_nsmul_Gpt ?_ ?_
  · rw [show Fintype.card VestaBaseField = PALLAS_SCALAR_CARD from ZMod.card _]
    decide
  · exact fun _ => eq_zero_of_two_nsmul_eq_zero (by decide) no_onCurve_y_zero

end Vesta

end CompElliptic.Curves.Pasta
