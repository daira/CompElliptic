/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.CharacterSum
import CompElliptic.CurveForms.ShortWeierstrass
import Mathlib.Data.ZMod.Basic

/-!
# The signed lift, and why hash-to-curve mappings are odd

Hash-to-curve mappings compute an abscissa from the input and then choose between
the two points over it —`(x, y)` and `(x, -y)`— by a sign rule: take the `y` whose
"sign" matches the input's (RFC 9380's `sgn0`, the parity of the least
representative). This file isolates that mechanism as the *signed lift* of an
abscissa map through a *sign function*, and proves the structural consequence the
character-sum analysis rests on: the lift is odd, `f (-u) = -f u`, for every
nonzero input. Only two facts about the deployed construction enter:

* the abscissa depends on the input only through its square, so it is *even*
  (`u` and `-u` share an abscissa); and
* negation flips the sign of every nonzero field element, so it flips which of the
  two points the sign rule selects.

## The zero exception, made explicit

The deployed mapping is *not* odd at `u = 0`: `-0 = 0`, so oddness there would
force `f 0 = -f 0` — a point of order dividing 2, which an odd-order curve group
does not have (except the identity, and the deployed mapping sends `0` to an
ordinary finite point via its exceptional branch). The mismatch is confined to
that single input. `zeroRepaired` is the variant sending `0` to the identity; it
is odd everywhere (`isOdd_zeroRepaired`), and `sum_apply_sub_of_eq_except` makes
the modelling cost exact: repairing one input shifts every character sum by the
difference of the two character values there — in norm, at most `2`. This is the
`O(1)` bookkeeping term of the pencil-and-paper analysis, carried here as an
identity rather than an estimate.

This file provides the generic layer, with the sign-function half instantiated
(`sgn0` on `ZMod p`, `isSignFunction_sgn0`). The concrete simplified-SWU
candidate map is `SSWUParams.candidateMap` (`Hashing/SimplifiedSWU.lean`), whose
signed lift is the mapping itself (`SSWUParams.map_eq_signedLift`);
`Hashing/PastaSSWU.lean` composes it with the isogenies as the deployed
`mapToCurve`.
-/

namespace CompElliptic.Hashing

open Finset
open CompElliptic.CurveForms.ShortWeierstrass

/-! ## Sign functions -/

section SignFunction

variable {F : Type*} [AddGroup F]

/-- A *sign function* labels each field element with a `Bool` so that negation
flips the label of every nonzero element. That is the only property of RFC 9380's
`sgn0` that the oddness of hash-to-curve mappings uses. (No constraint is placed
at `0`: negation fixes `0`, so no two-valued label can flip there.) -/
def IsSignFunction (sgn : F → Bool) : Prop := ∀ v : F, v ≠ 0 → sgn (-v) ≠ sgn v

end SignFunction

/-- RFC 9380's `sgn0` for a prime field: the parity of the least nonnegative
representative. -/
def sgn0 {p : ℕ} (v : ZMod p) : Bool := decide (v.val % 2 = 1)

/-- For an odd modulus, parity is a sign function: a nonzero `v` has `-v`
represented by `p - val v`, and subtracting from the odd `p` flips parity. -/
theorem isSignFunction_sgn0 {p : ℕ} [NeZero p] (hp : Odd p) :
    IsSignFunction (sgn0 (p := p)) := by
  intro v hv
  haveI : NeZero v := ⟨hv⟩
  have hneg : (-v).val = p - v.val := ZMod.val_neg_of_ne_zero v
  have hlt : v.val < p := ZMod.val_lt v
  have hpos : 0 < v.val :=
    Nat.pos_of_ne_zero fun h0 => hv ((ZMod.val_eq_zero v).mp h0)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hp
  simp only [sgn0, hneg, ne_eq, decide_eq_decide]
  omega

/-! ## The signed lift -/

section SignedLift

variable {F : Type*} [Field F] [DecidableEq F] {E : SWCurve F}

omit [DecidableEq F] in
/-- Negation on `SWPoint` fixes the abscissa. -/
@[simp] theorem SWPoint.neg_x (P : SWPoint E) : (-P).x = P.x := rfl

omit [DecidableEq F] in
/-- Negation on `SWPoint` negates the ordinate. -/
@[simp] theorem SWPoint.neg_y (P : SWPoint E) : (-P).y = -P.y := rfl

/-- The *signed lift*: given a candidate point map `m`, correct the sign of
each output by matching the sign of its ordinate to the sign of the input.
This is the shape of RFC 9380's step "if `sgn0 u ≠ sgn0 y`, set `y = -y`". -/
def signedLift (m : F → SWPoint E) (sgn : F → Bool) (u : F) : SWPoint E :=
  if sgn (m u).y = sgn u then m u else -(m u)

omit [DecidableEq F] in
/-- **The signed lift is odd away from `0`.** The candidate map only has to be
even *up to sign* —`m (-u) = ±(m u)`— and the sign rule must flip on negation;
then negating a nonzero input negates the output point. The up-to-sign
allowance is what the deployed algorithm needs: its nonsquare branch computes
the candidate root as `θ·Z·u²·u·y1`, whose bare factor of `u` makes the
chooser odd rather than even there. That is harmless: at a fixed input, the
sign-matching step selects the same point whichever sign the chooser produced,
because the output's sign is re-derived from `sgn0 u`. Across `±u` the outputs
still have opposite signs — `sgn0` flips on negation — which is exactly the
oddness proved here. -/
theorem signedLift_neg {m : F → SWPoint E} {sgn : F → Bool}
    (hm : ∀ u, m (-u) = m u ∨ m (-u) = -(m u))
    (hsgn : IsSignFunction sgn) {u : F} (hu : u ≠ 0) :
    signedLift m sgn (-u) = -(signedLift m sgn u) := by
  have hflip : sgn (-u) ≠ sgn u := hsgn u hu
  have hnn : ∀ P : SWPoint E, - -P = P := fun P => SWPoint.ext_pair (by simp)
  have even_case : m (-u) = m u →
      signedLift m sgn (-u) = -(signedLift m sgn u) := by
    intro hre
    by_cases h : sgn (m u).y = sgn u
    · have h' : ¬ sgn (m (-u)).y = sgn (-u) := by
        rw [hre]
        exact fun hc => hflip (by rw [← hc, h])
      simp only [signedLift, if_pos h, if_neg h']
      rw [hre]
    · have h' : sgn (m (-u)).y = sgn (-u) := by
        rw [hre]
        cases hb : sgn u <;> cases hc : sgn (m u).y <;> cases hd : sgn (-u) <;>
          simp_all
      simp only [signedLift, if_neg h, if_pos h']
      rw [hre, hnn]
  rcases hm u with hr | hr
  · exact even_case hr
  · by_cases hy0 : (m u).y = 0
    · exact even_case (hr.trans (SWPoint.ext_pair
        (by rw [SWPoint.neg_x, SWPoint.neg_y, hy0, neg_zero])))
    · have hyflip : sgn (m (-u)).y ≠ sgn (m u).y := by
        rw [hr, SWPoint.neg_y]
        exact hsgn (m u).y hy0
      by_cases h : sgn (m u).y = sgn u
      · have h' : sgn (m (-u)).y = sgn (-u) := by
          cases hb : sgn u <;> cases hc : sgn (m u).y <;> cases hd : sgn (-u) <;>
            cases he : sgn (m (-u)).y <;> simp_all
        simp only [signedLift, if_pos h, if_pos h']
        rw [hr]
      · have h' : ¬ sgn (m (-u)).y = sgn (-u) := by
          cases hb : sgn u <;> cases hc : sgn (m u).y <;> cases hd : sgn (-u) <;>
            cases he : sgn (m (-u)).y <;> simp_all
        simp only [signedLift, if_neg h, if_neg h']
        rw [hr]

/-! ## Repairing the zero exception -/

variable {G : Type*} [AddCommGroup G]

/-- The variant of a mapping that sends `0` to the identity and agrees with the
mapping everywhere else. The deployed hash-to-curve mapping differs from its
zero-repaired variant at the single input `0` (its exceptional branch produces a
finite point there); the repaired variant is what is literally odd. -/
def zeroRepaired {F : Type*} [Zero F] [DecidableEq F] (f : F → G) : F → G :=
  fun u => if u = 0 then 0 else f u

/-- A mapping that is odd away from `0` has an odd zero-repaired variant: at `0`
both sides are the identity, and elsewhere the repair does not fire. -/
theorem isOdd_zeroRepaired {F : Type*} [AddGroup F] [DecidableEq F] {f : F → G}
    (hodd : ∀ u : F, u ≠ 0 → f (-u) = -f u) : IsOdd (zeroRepaired f) := by
  intro u
  by_cases hu : u = 0
  · simp [zeroRepaired, hu]
  · have hnu : -u ≠ 0 := neg_ne_zero.mpr hu
    simp [zeroRepaired, hu, hnu, hodd u hu]

/-- **The exact cost of the repair.** Two mappings that agree except at one input
have character sums (indeed, sums of any function of their outputs) differing by
exactly the difference of the two values there. Applied to a deployed mapping and
its zero-repaired variant, this is the `O(1)` term of the character-sum analysis,
as an identity: in norm the shift is at most `2`, against sums of size `√#F`. -/
theorem sum_apply_sub_of_eq_except {F : Type*} [Fintype F] [DecidableEq F]
    {G : Type*} {f g : F → G} {u₀ : F} (h : ∀ u, u ≠ u₀ → f u = g u)
    (φ : G → ℂ) :
    ∑ u, φ (f u) - ∑ u, φ (g u) = φ (f u₀) - φ (g u₀) := by
  rw [← Finset.add_sum_erase univ (fun u => φ (f u)) (mem_univ u₀),
    ← Finset.add_sum_erase univ (fun u => φ (g u)) (mem_univ u₀),
    Finset.sum_congr rfl fun u hu => by rw [h u (Finset.mem_erase.mp hu).1]]
  ring

end SignedLift

end CompElliptic.Hashing
