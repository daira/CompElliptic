/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Rings.Eisenstein.Mod

/-!
# The unit action on `ℤ[ω]/8`, and the orbit count

The finite core of the Eisenstein-recoding argument. Everything here is a kernel
`decide` over a 64-element ring, so nothing below leaves the standard axioms.

## Two different orbit counts

Tabulating the odd classes and bucketing every nonzero residue are *different*
problems, and only the first involves a free action. Both are settled here.

* **On the ODD classes** — those not divisible by `2`, which are exactly the
  units, since `2` is inert. There the `μ₆` action is FREE, so the `48` odd
  classes fall into exactly `48 / 6 = 8` orbits and eight representatives
  suffice.
* **On ALL nonzero residues** the action is *not* free. `-1` fixes the four
  `2`-torsion classes, so the count is a Burnside count: `(B² + 8) / 6` orbits
  including zero, hence `(B² + 2) / 6 = 11` buckets at `B = 8`. The three
  nonzero `2`-torsion classes form a single orbit of size `3` whose
  representative `(B/2, 0)` admits TWO unit factorizations, so a bucket
  assignment has to agree on either choice or the result would be wrong;
  `orbit_mul_unit` is that obligation.

The structural reason the exception is exactly `-1`: a unit `u` fixes `x` iff
`(u - 1)·x = 0`, and for `u ∈ {±ω, ±ω²}` the element `u - 1` has ODD norm
(`N(ω - 1) = N(ω² - 1) = 3`, `N(-ω - 1) = N(-ω² - 1) = 1`) hence is invertible
mod `2^w`, forcing `x = 0`. Only `u = -1` has `N(u - 1) = N(-2) = 4`, even — and
its fixed set is the `2`-torsion.

That same norm computation shows `μ₆ → (ℤ[ω]/2^w)ˣ` is injective for every
`w ≥ 2`, since `8 ∣ (u - 1)` would force `64 ∣ N(u - 1) ∈ {1, 3, 4}`. So the
freeness is not special to `w = 3`, which is a cost choice rather than a
structural one.
-/

namespace CompElliptic.Rings.Eisenstein

/-- `ℤ[ω]/8`, the ring the width-3 recoding works in. -/
abbrev Eis8 : Type := Eisenstein (ZMod 8)

/-- The six units `{±1, ±ω, ±ω²}` of `ℤ[ω]`, reduced mod `8`. These are exactly
the six automorphisms available on a `j = 0` curve. -/
def mu6 : Finset Eis8 := {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩}

/-- The six units stay distinct mod `8`: `μ₆ → (ℤ[ω]/8)ˣ` is injective. This is
the reduction-injectivity that makes the action free on the units. -/
theorem mu6_card : mu6.card = 6 := by decide

/-- A class is ODD when it is not divisible by `2`. Since `2` is inert and the
residue field is `𝔽₄`, these are exactly the units of `ℤ[ω]/8`. -/
def IsOdd (x : Eis8) : Prop := ¬ (2 ∣ x.a.val ∧ 2 ∣ x.b.val)

instance : DecidablePred IsOdd := fun _ => by unfold IsOdd; infer_instance

/-- The orbit of `x` under the unit action — the "bucket" the recoder assigns. -/
def orbit (x : Eis8) : Finset Eis8 := mu6.image (· * x)

/-! ## There are 48 odd classes -/

/-- `#(ℤ[ω]/8)ˣ = 48`. Conceptually this is `64 - 16`: `2` is
inert, so `ℤ[ω]/8` is a LOCAL ring whose maximal ideal is `(2)`, and the units
are precisely the complement of that ideal. -/
theorem card_odd : (Finset.univ.filter IsOdd).card = 48 := by decide

/-- The even classes are the other `16`, i.e. `2 · ℤ[ω]/8`. -/
theorem card_even : (Finset.univ.filter (fun x => ¬ IsOdd x)).card = 16 := by decide

/-! ## The action is free on the odd classes -/

set_option maxRecDepth 8000 in
/-- On the odd classes the `μ₆` action is FREE: no nonidentity unit fixes an odd
class. This is what licenses the division `48 / 6 = 8`. Without it a table built
from eight representatives would be incomplete, which is a soundness failure
rather than a performance one. -/
theorem mu6_free_on_odd :
    ∀ u ∈ mu6, ∀ x : Eis8, IsOdd x → u * x = x → u = ⟨1, 0⟩ := by decide

set_option maxRecDepth 8000 in
/-- Every odd class therefore has a full orbit of six. -/
theorem card_orbit_of_odd : ∀ x : Eis8, IsOdd x → (orbit x).card = 6 := by decide

/-! ## Eight representatives cover all 48 -/

/-- Eight odd classes, one per orbit: the lexicographically least element of each
orbit. Any eight pairwise non-associate odd classes would do — see
`reps_cover` — so this is *a* valid table, and the article's specific table can
be checked against it by a single `decide` once its digits are read off the
published page. -/
def reps : Finset Eis8 :=
  {⟨0, 1⟩, ⟨0, 3⟩, ⟨1, 2⟩, ⟨1, 3⟩, ⟨1, 4⟩, ⟨1, 5⟩, ⟨1, 6⟩, ⟨2, 5⟩}

theorem reps_card : reps.card = 8 := by decide

theorem reps_odd : ∀ r ∈ reps, IsOdd r := by decide

/-- The eight orbits are pairwise disjoint: the representatives are pairwise
non-associate. -/
theorem reps_pairwise_disjoint :
    ∀ r ∈ reps, ∀ s ∈ reps, r ≠ s → Disjoint (orbit r) (orbit s) := by decide

/-- The eight representatives' orbits cover every odd class exactly. With
`reps_pairwise_disjoint` and `card_orbit_of_odd` this makes `48 / 6 = 8` a
theorem rather than a division. -/
theorem reps_cover : reps.biUnion orbit = Finset.univ.filter IsOdd := by decide

/-- There are exactly eight orbits of odd classes. -/
theorem card_orbits_odd :
    ((Finset.univ.filter IsOdd).image orbit).card = 8 := by decide

/-! ## The Burnside count over all nonzero residues -/

/-- The fixed set of `-1` is the `2`-torsion: four classes, not just zero. This
is the single exception that breaks freeness on the non-unit classes. -/
theorem fix_neg_one :
    Finset.univ.filter (fun x : Eis8 => (⟨-1, 0⟩ : Eis8) * x = x)
      = {⟨0, 0⟩, ⟨0, 4⟩, ⟨4, 0⟩, ⟨4, 4⟩} := by decide

/-- Each of the four remaining nonidentity units fixes only zero, because `u - 1`
has odd norm and is therefore invertible mod `8`. -/
theorem fix_others :
    ∀ u ∈ ({⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩} : Finset Eis8),
      Finset.univ.filter (fun x : Eis8 => u * x = x) = {⟨0, 0⟩} := by decide

/-- Burnside: `(B² + 8) / 6 = 12` orbits including zero, so `(B² + 2) / 6 = 11`
nonzero buckets. Of those, `8` are the free unit orbits above and `3` are not. -/
theorem card_orbits_all : (Finset.univ.image orbit).card = 12 := by decide

theorem card_orbits_nonzero :
    ((Finset.univ.filter (fun x : Eis8 => x ≠ 0)).image orbit).card = 11 := by decide

/-- The three nonzero `2`-torsion classes form ONE orbit, of size `3` rather than
`6` — the visible symptom of the stabilizer being nontrivial. -/
theorem orbit_two_torsion : orbit ⟨4, 0⟩ = {⟨0, 4⟩, ⟨4, 0⟩, ⟨4, 4⟩} := by decide

/-- **The two unit factorizations.** `(B/2, 0) = (4, 0)` is fixed by both `1` and
`-1`, so it has two distinct representations as `unit × representative`. -/
theorem stabilizer_two_torsion :
    mu6.filter (fun u => u * (⟨4, 0⟩ : Eis8) = ⟨4, 0⟩) = {⟨1, 0⟩, ⟨-1, 0⟩} := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **The correctness obligation.** The bucket is well defined: it
does not depend on which unit factorization is chosen, because multiplying by any
unit leaves the orbit unchanged. This is what makes the ambiguity at `(4, 0)`
harmless; had the two factorizations landed in different buckets, the recoding
would produce a wrong result. -/
theorem orbit_mul_unit : ∀ u ∈ mu6, ∀ x : Eis8, orbit (u * x) = orbit x := by decide

end CompElliptic.Rings.Eisenstein
