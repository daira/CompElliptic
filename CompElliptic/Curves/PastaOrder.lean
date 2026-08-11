/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood, Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.IsoPasta
import CompElliptic.CurveOrder
import CompElliptic.Isogenies.Homomorphism

/-!
# Orders of the Pasta and iso-Pasta curve groups

Instantiates the `CompElliptic.CurveOrder` fibre bound at the two Pasta curves and their
3-isogenous auxiliaries, with no assumption: the Pallas and iso-Pallas groups have order
`PALLAS_SCALAR_CARD`, and the Vesta and iso-Vesta groups have order `PALLAS_BASE_CARD`
(the Pasta cycle: each curve's order is the other's base-field size; isogenous curves have
equal orders, though here each order is pinned by its own witness rather than by the
isogeny).

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

With the orders in hand, each isogeny's injectivity upgrades to bijectivity on rational
points by counting (`iso_map_bijective`). Injectivity is `ThreeIsogeny.map_injective`: an
abscissa collision would exhibit the nonsquare `y₀²` as a square, contradicting the
kernel's irrationality. No homomorphism property is consumed.

The iso-curves take the same two routes as their targets. The one new ingredient is
iso-Vesta's 2-torsion exclusion: its curve cubic has a linear term, so the cube-residue
argument does not apply, but none is needed — a `y = 0` point of iso-Vesta would map to a
`y = 0` point of Vesta under the isogeny (`ThreeIsogeny.no_y_zero_of_codomain`), and Vesta
has none.

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

/-- A prime-order witness on iso-Pallas, at the smallest square abscissa `x = 1`. -/
def isoGpt : SWPoint isoCurve :=
  ⟨1, 181637241052482785468502922954224147219384682169221362737776065992881747347,
    Or.inl (by decide)⟩

theorem isoGpt_ne_zero : isoGpt ≠ 0 := by decide

/-- `[q] G = 𝒪` on iso-Pallas, where `q = PALLAS_SCALAR_CARD` is the iso-Pallas group order. -/
theorem q_nsmul_isoGpt : PALLAS_SCALAR_CARD • isoGpt = 0 := by native_decide

/-- **The iso-Pallas curve group has order `PALLAS_SCALAR_CARD`**, unconditionally — the same
order as Pallas, by the same route. -/
theorem iso_card_eq : Nat.card (SWPoint isoCurve) = PALLAS_SCALAR_CARD := by
  refine card_eq_of_prime_witness_of_card_lt_two_mul isoCurve PALLAS_SCALAR_is_prime
    isoGpt_ne_zero q_nsmul_isoGpt ?_
  rw [show Fintype.card PallasBaseField = PALLAS_BASE_CARD from ZMod.card _]
  decide

/-- The isogeny iso-Pallas → Pallas is a bijection on rational points, by counting: it is
injective with no homomorphism property consumed (`ThreeIsogeny.map_injective`), and the
two groups have the same order. -/
theorem iso_map_bijective : Function.Bijective iso.map :=
  iso.map_bijective (by decide) no_onCurve_y_zero (iso_card_eq.trans card_eq.symm)


/-- No point of iso-Pallas has `y = 0`: such a point would map to a `y = 0` point of
Pallas under the isogeny, and Pallas has none. -/
theorem iso_no_onCurve_y_zero (x : PallasBaseField) :
    ¬ OnCurve isoCurve.A isoCurve.B (x, 0) :=
  iso.no_y_zero_of_codomain no_onCurve_y_zero x

/-- **The deployed Pallas isogeny is a group homomorphism on rational points.** All
of its hypotheses are discharged by the 2-torsion exclusions. -/
theorem iso_map_add (P Q : SWPoint isoCurve) :
    iso.map (P + Q) = iso.map P + iso.map Q :=
  iso.map_add (by decide) iso_no_onCurve_y_zero no_onCurve_y_zero P Q

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

/-- A prime-order witness on iso-Vesta, at the smallest square abscissa `x = 4`. -/
def isoGpt : SWPoint isoCurve :=
  ⟨4, 2165270085553270387583265107994083524758817942147891525126107618954199130179,
    Or.inl (by decide)⟩

theorem isoGpt_ne_zero : isoGpt ≠ 0 := by decide

/-- `[p] G = 𝒪` on iso-Vesta, where `p = PALLAS_BASE_CARD` is the iso-Vesta group order. -/
theorem p_nsmul_isoGpt : PALLAS_BASE_CARD • isoGpt = 0 := by native_decide

/-- No point of iso-Vesta has `y = 0`: it would map to a `y = 0` point of Vesta under the
isogeny, and Vesta has none. -/
theorem iso_no_onCurve_y_zero (x : VestaBaseField) :
    ¬ OnCurve isoCurve.A isoCurve.B (x, 0) :=
  iso.no_y_zero_of_codomain no_onCurve_y_zero x

/-- **The iso-Vesta curve group has order `PALLAS_BASE_CARD`**, unconditionally — the same
order as Vesta, by the same route, with the 2-torsion exclusion transported through the
isogeny. -/
theorem iso_card_eq : Nat.card (SWPoint isoCurve) = PALLAS_BASE_CARD := by
  refine card_eq_of_prime_witness_of_card_lt_three_mul isoCurve PALLAS_BASE_is_prime
    isoGpt_ne_zero p_nsmul_isoGpt ?_ ?_
  · rw [show Fintype.card VestaBaseField = PALLAS_SCALAR_CARD from ZMod.card _]
    decide
  · exact fun _ => eq_zero_of_two_nsmul_eq_zero (by decide) iso_no_onCurve_y_zero

/-- The isogeny iso-Vesta → Vesta is a bijection on rational points, by counting: it is
injective with no homomorphism property consumed (`ThreeIsogeny.map_injective`), and the
two groups have the same order. -/
theorem iso_map_bijective : Function.Bijective iso.map :=
  iso.map_bijective (by decide) no_onCurve_y_zero (iso_card_eq.trans card_eq.symm)


/-- **The deployed Vesta isogeny is a group homomorphism on rational points.** All
of its hypotheses are discharged by the 2-torsion exclusions. -/
theorem iso_map_add (P Q : SWPoint isoCurve) :
    iso.map (P + Q) = iso.map P + iso.map Q :=
  iso.map_add (by decide) iso_no_onCurve_y_zero no_onCurve_y_zero P Q

end Vesta

end CompElliptic.Curves.Pasta
