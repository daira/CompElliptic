/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Curves.PastaOrder
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# A 2-cycle of curves shares its CM discriminant

The two curves of a cycle cannot be chosen independently: fixing one constrains the other so
tightly that both end up with Complex Multiplication by an order in the *same* imaginary
quadratic field. That is the fact usually quoted to explain why the Pasta curves have
`j`-invariant `0`, and it is the only half of that explanation which is a theorem; the other
half (that a cycle is only *findable* when the discriminant is small) is a statement about the
construction methods we know, not about what exists.

## The argument

Everything follows from *counting alone*. Write the trace of Frobenius by definition rather
than by any structure theory,

`t(E) = #F + 1 - #E(F)`,

and let `frobDisc E = t(E)² - 4·#F`. If `E₁/F₁` and `E₂/F₂` form a 2-cycle, meaning
`#E₁(F₁) = #F₂` and `#E₂(F₂) = #F₁`, then the two counting equations read
`#F₂ = #F₁ + 1 - t₁` and `#F₁ = #F₂ + 1 - t₂`. Adding them cancels the field sizes and leaves
`t₁ + t₂ = 2` (`trace_add_trace`), and substituting `t₂ = 2 - t₁` gives

`t₂² - 4·#F₂ = (2 - t₁)² - 4(#F₁ + 1 - t₁) = t₁² - 4·#F₁`,

which is `frobDisc_eq`: the two Frobenius discriminants are equal *as integers*, not merely up
to squares. Every invariant read off that integer therefore agrees, in particular the CM field
`ℚ(√(t² - 4·#F))`, its fundamental discriminant, and the conductor of the Frobenius order
(`hasCMDiscriminant_congr`).

## The order `ℤ[π]`, as a definition

Since the discriminant is only a shadow of the ring it comes from, that ring is defined too:
`frobCharPoly` is `X² - t·X + #F`, `frobeniusOrder` is `ℤ[X]/(frobCharPoly)`, which is `ℤ[π]`,
`frobeniusElt` is the class of `X`, which is `π`, and `frobeniusElt_charEq` is its defining
relation. The cycle statement then strengthens from an equality of integers to an isomorphism
of rings, `frobeniusOrderEquiv : ℤ[π₁] ≃ₐ[ℤ] ℤ[π₂]`, given explicitly by `π₁ ↦ π₂ + (t₁ - 1)`.
That is the form to reuse: it survives any later change of how the discriminant is packaged,
and it is what "the same order" actually means.

## What is and is not assumed

The proof is counting plus integer algebra: no theorem about endomorphism rings, and no
arithmetic geometry. It therefore holds for *any* pair of curves satisfying the cycle
equations.

Ordinariness is a hypothesis nowhere below. It governs only whether the shared integer may be
*called* a CM discriminant, which needs `End E` to be a quadratic order; the statement proved
here is the count-level one, which is the part the cycle forces.

## Provenance

This is Proposition 6.1 of Alessandro Chiesa, Lynn Chua and Matthew Weidner, *On cycles of
pairing-friendly elliptic curves*, SIAM J. Appl. Algebra Geom. 3(2):175-192, 2019
(arXiv:1803.02067), restated as Proposition 3.3(iv) of Marta Bellés-Muñoz, Jorge Jiménez Urroz
and Javier Silva, *Revisiting cycles of pairing-friendly elliptic curves*, CRYPTO 2023
(ia.cr/2022/1662). The proof there is the same three lines; this module mechanises it, and adds
the Pasta instance below.

Both papers state the discriminant with the opposite sign, as the squarefree part of
`4·#F - t²`, which is positive by Hasse; the sign convention here is the one under which the
discriminant is that of the order `ℤ[π]`, so `D = -3` below is their `D = 3`.

## The Pasta instance

`Pasta.isCycle₂` feeds the Pallas and Vesta group orders (`Curves.Pasta.Pallas.card_eq` and
`Curves.Pasta.Vesta.card_eq`) into the general theorem, and `Pasta.frobDisc_pallas`
exhibits the shared discriminant explicitly:

`t² - 4p = -3 · V²`, with `V = 0x93cd3a2c8198e2690c7c095a00000001`,

so the fundamental discriminant is `D = -3` and the CM field is `ℚ(√-3)`. That is exactly the
`j = 0` case, which is why both curves have the form `y² = x³ + b` and why Simplified SWU
(needing `a ≠ 0`) has to detour through an isogenous curve. Note also that `V ≡ 1 (mod 2³²)`,
the 2-adicity that the search was steering for.
-/

namespace CompElliptic.CurveCycle

open CompElliptic.CurveForms.ShortWeierstrass

/-! ## Trace and Frobenius discriminant, by counting -/

section Defs

variable {F : Type*} [Field F] [Fintype F]

/-- The **trace of Frobenius** of `E/F`, *defined* as `#F + 1 - #E(F)` rather than as an
eigenvalue: this is the only property of the trace any statement below uses, and taking it as
the definition keeps the module free of arithmetic geometry. -/
noncomputable def trace (E : SWCurve F) : ℤ := (Fintype.card F : ℤ) + 1 - (Nat.card (SWPoint E) : ℤ)

/-- The **Frobenius discriminant** `t² - 4·#F` of `E/F`, i.e. the discriminant of the
characteristic polynomial `X² - tX + #F` of Frobenius.

Unfolding the `ℤ[π]` this module keeps referring to, since it is not obvious: `π` is the
Frobenius endomorphism `(x, y) ↦ (x^#F, y^#F)` of `E`. It is an endomorphism because raising to
the `#F`-th power is a field homomorphism in characteristic `p`, and its fixed points are
exactly the rational points, `E(F) = ker (π - 1)`, because `x^#F = x` holds iff `x ∈ F`. Now
`End E` is a ring (add pointwise, multiply by composing) containing `ℤ` as the
multiplication-by-`n` maps, and `ℤ[π] = {a + b·π}` is the subring `π` generates over it. There
Frobenius satisfies `π² - t·π + #F = 0`, which is also where the counting definition of `t`
comes from (`#E(F) = deg (1 - π) = #F + 1 - t`), so

`ℤ[π] ≅ ℤ[X]/(X² - tX + #F)`,

and the integer defined here is the discriminant of *that* quadratic ring: `frobDisc E` is
`disc (ℤ[π])` on the nose, not an analogue of one.

For an ordinary curve `π ∉ ℤ` and `t² - 4·#F < 0` by Hasse, so `ℤ[π]` is an order in the
imaginary quadratic field `K = ℚ(π) = ℚ(√(t² - 4·#F))`, sitting in a chain of orders
`ℤ[π] ⊆ End E ⊆ 𝒪_K`. Its squarefree part is then what the literature calls the curve's CM
discriminant, and writing `t² - 4·#F = D·f²` with `D` fundamental makes `f` the conductor of
`ℤ[π]` (the conductor of `End E` divides it, and can be smaller: that is exactly the gap
between "has CM by an order in `ℚ(√-3)`" and "has `j = 0`", see `Pasta.frobDisc_pallas`).

`ℤ[π]` is not left as prose: `frobeniusOrder` below *is* that ring, `frobeniusElt` is its `π`,
and `frobeniusElt_charEq` is the relation above. The cycle theorem is then available in two
forms, as the integer identity `frobDisc_eq` and as the ring isomorphism
`frobeniusOrderEquiv`. -/
noncomputable def frobDisc (E : SWCurve F) : ℤ := trace E ^ 2 - 4 * (Fintype.card F : ℤ)

/-- `D` is a **CM discriminant** of `E` when the Frobenius discriminant is `D` times a square
with `D` squarefree, i.e. `D` is the squarefree part of `t² - 4·#F`. -/
def HasCMDiscriminant (E : SWCurve F) (D : ℤ) : Prop :=
  Squarefree D ∧ ∃ f : ℤ, frobDisc E = D * f ^ 2

end Defs

/-! ## `ℤ[π]` as a definition, not only as a comment -/

section FrobeniusOrder

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- The **characteristic polynomial of Frobenius**, `X² - t·X + #F`, over `ℤ`. -/
noncomputable def frobCharPoly (E : SWCurve F) : ℤ[X] :=
  X ^ 2 - C (trace E) * X + C (Fintype.card F : ℤ)

/-- The **Frobenius order** `ℤ[π] = ℤ[X]/(X² - t·X + #F)` of `E`.

This is the abstract form of the ring the comments above describe. The geometric `π` itself is
not available here: as an endomorphism it acts on points over extensions of `F`, and on `E(F)`
alone it is the identity (`x^(#F) = x`), so nothing would be gained by defining it on `SWPoint`.
For an ordinary curve the ring below is genuinely `ℤ[π] ⊆ End E`, by the characteristic equation
`π² - t·π + #F = 0`. -/
abbrev frobeniusOrder (E : SWCurve F) : Type := AdjoinRoot (frobCharPoly E)

/-- The formal Frobenius: the image of `X` in `ℤ[X]/(X² - t·X + #F)`. -/
noncomputable def frobeniusElt (E : SWCurve F) : frobeniusOrder E := AdjoinRoot.root _

/-- The definitional unfolding, stated as an equation so `simp` can *fold* an `AdjoinRoot.root`
back into `frobeniusElt` with `← frobeniusElt_def`; `simp` cannot refold a definition by name.
Used in the round-trip proofs of `frobeniusOrderEquiv`, where the `ext` lemma leaves the goal in
terms of `root`. -/
theorem frobeniusElt_def (E : SWCurve F) :
    frobeniusElt E = AdjoinRoot.root (frobCharPoly E) := rfl

/-- **The characteristic equation**, `π² - t·π + #F = 0`, holding in `ℤ[π]` by construction. -/
theorem frobeniusElt_charEq (E : SWCurve F) :
    frobeniusElt E ^ 2 - (trace E : frobeniusOrder E) * frobeniusElt E
      + ((Fintype.card F : ℤ) : frobeniusOrder E) = 0 := by
  have h : AdjoinRoot.mk (frobCharPoly E) (frobCharPoly E) = 0 := AdjoinRoot.mk_self
  rw [frobCharPoly] at h
  simp only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  simpa [frobeniusElt] using h

end FrobeniusOrder

/-! ## The cycle condition -/

section Cycle

open Polynomial

variable {F₁ F₂ : Type*} [Field F₁] [Fintype F₁] [Field F₂] [Fintype F₂]
  {E₁ : SWCurve F₁} {E₂ : SWCurve F₂}

/-- `E₁/F₁` and `E₂/F₂` form a **2-cycle**: each curve's group order is the other's field size.
(The Pasta cycle: `#Pallas(𝔽_p) = q` and `#Vesta(𝔽_q) = p`.) -/
structure IsCycle₂ (E₁ : SWCurve F₁) (E₂ : SWCurve F₂) : Prop where
  /-- The first curve's group order is the second curve's field size. -/
  card_fst : Nat.card (SWPoint E₁) = Fintype.card F₂
  /-- The second curve's group order is the first curve's field size. -/
  card_snd : Nat.card (SWPoint E₂) = Fintype.card F₁

/-- A 2-cycle read the other way round is again a 2-cycle. -/
theorem IsCycle₂.symm (h : IsCycle₂ E₁ E₂) : IsCycle₂ E₂ E₁ :=
  ⟨h.card_snd, h.card_fst⟩

/-- **The traces of a 2-cycle sum to `2`.** Adding the two counting equations
`#F₂ = #F₁ + 1 - t₁` and `#F₁ = #F₂ + 1 - t₂` cancels both field sizes.

This is the whole content of the cycle condition; `frobDisc_eq` is then substitution. -/
theorem trace_add_trace (h : IsCycle₂ E₁ E₂) : trace E₁ + trace E₂ = 2 := by
  simp only [trace, h.card_fst, h.card_snd]
  ring

/-- The second trace is determined by the first, `t₂ = 2 - t₁`. -/
theorem trace_snd (h : IsCycle₂ E₁ E₂) : trace E₂ = 2 - trace E₁ := by
  have := trace_add_trace h
  linarith

/-- **The two curves of a 2-cycle have equal Frobenius discriminants**, as integers:

`t₂² - 4·#F₂ = (2 - t₁)² - 4(#F₁ + 1 - t₁) = t₁² - 4·#F₁`.

Chiesa-Chua-Weidner, Proposition 6.1. Note the conclusion is stronger than the usual phrasing
"the same CM discriminant", which compares only squarefree parts. -/
theorem frobDisc_eq (h : IsCycle₂ E₁ E₂) : frobDisc E₁ = frobDisc E₂ := by
  simp only [frobDisc, trace, h.card_fst, h.card_snd]
  ring

/-! ### The two Frobenius orders are isomorphic

`frobDisc_eq` says the two orders `ℤ[π₁]` and `ℤ[π₂]` have the same discriminant. Since both are
quadratic orders in the same field, that already forces them to be the *same* order, and the
isomorphism is explicit: inside `K`, `π₁ = (t₁ + √D)/2` and `π₂ = (t₂ + √D)/2` differ by the
integer `(t₁ - t₂)/2 = t₁ - 1`, using `t₁ + t₂ = 2`. So `π₁ ↦ π₂ + (t₁ - 1)` is a ring map, and
its mirror image is its inverse. This is the statement to reuse: it is strictly stronger than
equality of discriminants, and it needs no square roots to state. -/

/-- `π₂ + (t₁ - 1)` is a root of `E₁`'s characteristic polynomial, which is what makes
`frobeniusOrderHom` well defined. -/
theorem aeval_frobCharPoly_shift (h : IsCycle₂ E₁ E₂) :
    aeval (frobeniusElt E₂ + ((trace E₁ - 1 : ℤ) : frobeniusOrder E₂)) (frobCharPoly E₁) = 0 := by
  have ht₁ : trace E₁ = (Fintype.card F₁ : ℤ) + 1 - (Fintype.card F₂ : ℤ) := by
    simp [trace, h.card_fst]
  have ht₂ : trace E₂ = (Fintype.card F₂ : ℤ) + 1 - (Fintype.card F₁ : ℤ) := by
    simp [trace, h.card_snd]
  have hrel := frobeniusElt_charEq E₂
  rw [ht₂] at hrel
  -- Reduce `aeval` first: rewriting `C` into a cast before that would leave `aeval` stuck on the
  -- coefficients.
  simp only [frobCharPoly, ht₁, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
  simp only [eq_intCast]
  push_cast at hrel ⊢
  linear_combination hrel

/-- **`π₁ ↦ π₂ + (t₁ - 1)`**, the comparison map between the two Frobenius orders of a 2-cycle. -/
noncomputable def frobeniusOrderHom (h : IsCycle₂ E₁ E₂) :
    frobeniusOrder E₁ →ₐ[ℤ] frobeniusOrder E₂ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId ℤ (frobeniusOrder E₂))
    (frobeniusElt E₂ + ((trace E₁ - 1 : ℤ) : frobeniusOrder E₂))
    (aeval_frobCharPoly_shift h)

/-- What the comparison map does to the generator, which is the only fact about it any proof
here needs: `AdjoinRoot.algHom_ext` reduces every identity between maps out of `ℤ[π₁]` to their
value on `π₁`, so this is the simp lemma the round trip in `frobeniusOrderEquiv` runs on. -/
@[simp]
theorem frobeniusOrderHom_frobeniusElt (h : IsCycle₂ E₁ E₂) :
    frobeniusOrderHom h (frobeniusElt E₁)
      = frobeniusElt E₂ + ((trace E₁ - 1 : ℤ) : frobeniusOrder E₂) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- **The two curves of a 2-cycle have isomorphic Frobenius orders**, `ℤ[π₁] ≃ ℤ[π₂]`, by the
generator shift above in both directions: the round trip moves the generator by
`(t₁ - 1) + (t₂ - 1)`, which is `0` by `trace_add_trace`. -/
noncomputable def frobeniusOrderEquiv (h : IsCycle₂ E₁ E₂) :
    frobeniusOrder E₁ ≃ₐ[ℤ] frobeniusOrder E₂ :=
  AlgEquiv.ofAlgHom (frobeniusOrderHom h) (frobeniusOrderHom h.symm)
    (by
      have h2 : ((trace E₁ : frobeniusOrder E₂)) + (trace E₂ : frobeniusOrder E₂) = 2 := by
        exact_mod_cast congrArg (fun n : ℤ => (n : frobeniusOrder E₂)) (trace_add_trace h)
      ext
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, ← frobeniusElt_def,
        frobeniusOrderHom_frobeniusElt, map_add, map_intCast]
      push_cast
      linear_combination h2)
    (by
      have h2 : ((trace E₁ : frobeniusOrder E₁)) + (trace E₂ : frobeniusOrder E₁) = 2 := by
        exact_mod_cast congrArg (fun n : ℤ => (n : frobeniusOrder E₁)) (trace_add_trace h)
      ext
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, ← frobeniusElt_def,
        frobeniusOrderHom_frobeniusElt, map_add, map_intCast]
      push_cast
      linear_combination h2)

/-- **The CM discriminant is shared**: a squarefree `D` is a CM discriminant of one curve of a
2-cycle exactly when it is one of the other. No uniqueness of squarefree parts is needed, since
the two discriminants are the same integer. -/
theorem hasCMDiscriminant_congr (h : IsCycle₂ E₁ E₂) {D : ℤ} :
    HasCMDiscriminant E₁ D ↔ HasCMDiscriminant E₂ D := by
  simp only [HasCMDiscriminant, frobDisc_eq h]

end Cycle

/-! ## The Pasta cycle: the shared discriminant is `-3`, i.e. `j = 0` -/

namespace Pasta

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta

/-- The Pallas base field has `PALLAS_BASE_CARD` elements. -/
theorem card_pallasBaseField : Fintype.card PallasBaseField = PALLAS_BASE_CARD := ZMod.card _

/-- The Vesta base field has `PALLAS_SCALAR_CARD` elements. -/
theorem card_vestaBaseField : Fintype.card VestaBaseField = PALLAS_SCALAR_CARD := ZMod.card _

/-- **Pallas and Vesta form a 2-cycle**: `#Pallas(𝔽_p) = q = #𝔽_q` and `#Vesta(𝔽_q) = p = #𝔽_p`,
from the two unconditional order computations in `Curves.PastaOrder`. -/
theorem isCycle₂ : IsCycle₂ Pallas.curve Vesta.curve where
  card_fst := by rw [Pallas.card_eq, card_vestaBaseField]
  card_snd := by rw [Vesta.card_eq, card_pallasBaseField]

/-- The Pallas trace of Frobenius, `t = p + 1 - q`. -/
theorem trace_pallas : trace Pallas.curve = -86663725065984043395317759 := by
  simp only [trace, Pallas.card_eq, card_pallasBaseField]
  decide

/-- The Vesta trace, `2 - t`, as `trace_snd` predicts. -/
theorem trace_vesta : trace Vesta.curve = 86663725065984043395317761 := by
  rw [trace_snd isCycle₂, trace_pallas]
  decide

/-- **The Pasta cycle's shared Frobenius discriminant is `-3 · V²`** with
`V = 0x93cd3a2c8198e2690c7c095a00000001`, so the CM field is `ℚ(√-3)`. Equivalently
`4p = t² + 3V²`, the CM norm equation at `|D| = 3` that the Pasta search solved.

Sharing the field is not by itself `j = 0`: an order of conductor `f > 1` in `ℚ(√-3)` has other
`j`-invariants. What a cycle forces is the field; what the search additionally fixed, by taking
`|D| = 3` and reading off the six twists per prime, is the *maximal* order `ℤ[ζ₃]`, whose extra
automorphisms are the `j = 0` ones. Pallas and Vesta are `y² = x³ + 5`, so they do realise it. -/
theorem frobDisc_pallas :
    frobDisc Pallas.curve = -3 * 196462116142286827589391630752301449217 ^ 2 := by
  simp only [frobDisc, trace_pallas, card_pallasBaseField]
  decide

/-- `-3` is squarefree, as an integer. -/
theorem squarefree_neg_three : Squarefree (-3 : ℤ) :=
  (Int.prime_iff_natAbs_prime.mpr (by decide)).irreducible.squarefree

/-- Vesta's Frobenius discriminant, which by `frobDisc_eq` is the same integer as Pallas's. -/
theorem frobDisc_vesta :
    frobDisc Vesta.curve = -3 * 196462116142286827589391630752301449217 ^ 2 :=
  (frobDisc_eq isCycle₂).symm.trans frobDisc_pallas

/-- **The Pasta CM discriminant is `-3`**, by the explicit factorisation above. -/
theorem hasCMDiscriminant_pallas : HasCMDiscriminant Pallas.curve (-3) :=
  ⟨squarefree_neg_three, 196462116142286827589391630752301449217, frobDisc_pallas⟩

/-- The same for Vesta, obtained by transport along the cycle rather than by recounting. -/
theorem hasCMDiscriminant_vesta : HasCMDiscriminant Vesta.curve (-3) :=
  (hasCMDiscriminant_congr isCycle₂).mp hasCMDiscriminant_pallas

/-- **The two Pasta Frobenius orders are the same order**, `ℤ[π_Pallas] ≃ ℤ[π_Vesta]`, by the
generator shift `π_Pallas ↦ π_Vesta + (t - 1)`. -/
noncomputable def frobeniusOrderEquiv :
    frobeniusOrder Pallas.curve ≃ₐ[ℤ] frobeniusOrder Vesta.curve :=
  CurveCycle.frobeniusOrderEquiv isCycle₂

end Pasta

end CompElliptic.CurveCycle
