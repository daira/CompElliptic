/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.PastaOrder
import CompElliptic.Hashing.PastaSSWU
import CompElliptic.Curves.Pasta.Fast.Projective
import CompElliptic.Curves.Pasta.Fast.Msm
import CompElliptic.Curves.Pasta.Fast.ProjectiveMontEquiv
import CompElliptic.Fields.Sqrt
import CompElliptic.Meta.AxiomCheck

/-!
# Trust boundary, build-checked

The library-wide census that makes the *independently re-checkable trust* principle (see the
README) a build-time check rather than a prose claim. Each `assert_axioms` below pins an *upper
bound* on a declaration's trusted base, so a change that widens it — a `sorry`, a new axiom in a
general theorem, or `native_decide` creeping into a quantified result — fails this file rather than
passing silently. The declarations are grouped by trust tier:

* **General theorems** rest only on `propext` / `Classical.choice` / `Quot.sound`. A quantified
  result has no independent spot-check, so it must not reach beyond Lean's standard axioms.
* **Concrete closed facts checked by the kernel** (Pratt primality certificates) add nothing beyond
  those same axioms: the kernel evaluates them directly, trusting only its GMP bignum arithmetic
  (which even ordinary `decide` relies on and which axiom collection does not surface).
* **Concrete closed facts trusting the compiler** (`native_decide`, marked `+native(...)`) each add
  a per-declaration compiler-trust axiom. This is the whole compiler-trust surface, confined to
  falsifiable numeric facts about the Pasta fields and curves — chiefly the order of the
  Tonelli–Shanks roots of unity (`pallasBase`/`vestaBase`) and the two prime-order witnesses behind
  the group orders. Each such fact is reproducible by an independent tool, so a miscompiled oracle
  could in principle be caught by disagreement (the catch requires someone actually performing the
  independent check).

`assert_axioms` matches a permitted `native_decide` axiom by its owning declaration — named inside
`+native(...)` — rather than by the exact axiom name (whose tail is toolchain-dependent). The
census therefore stays green across toolchain bumps while still catching any tier violation, and
it states exactly which native certificates each entry trusts: a new certificate entering a cone,
or a stale owner list, fails the build with the list to write.
-/

open CompElliptic.Meta

/-! ## General theorems — standard axioms only -/

assert_axioms CompElliptic.CurveOrder.card_fibre_le_two
assert_axioms CompElliptic.CurveOrder.card_eq_of_prime_witness_of_card_lt_two_mul
assert_axioms CompElliptic.CurveOrder.card_eq_of_prime_witness_of_card_lt_three_mul
assert_axioms CompElliptic.Fields.TonelliShanks.sqrt?_mul_self
assert_axioms CompElliptic.Fields.TonelliShanks.sqrt?_isSome_of_isSquare

/-! ## Concrete closed facts checked by the kernel (Pratt certificates) — standard axioms only -/

assert_axioms CompElliptic.Fields.Pasta.PALLAS_BASE_is_prime
assert_axioms CompElliptic.Fields.Pasta.PALLAS_SCALAR_is_prime

/-! ## The isogeny layer's headline general theorems — standard axioms only -/

assert_axioms CompElliptic.Curves.Pasta.Pallas.iso_map_eq
assert_axioms CompElliptic.Curves.Pasta.Vesta.iso_map_eq
assert_axioms CompElliptic.Curves.Pasta.Pallas.onCurve_iso_map
assert_axioms CompElliptic.Curves.Pasta.Vesta.onCurve_iso_map
assert_axioms CompElliptic.Isogenies.ThreeIsogeny.map_add
assert_axioms CompElliptic.Curves.Pasta.Pallas.iso_map_add
assert_axioms CompElliptic.Curves.Pasta.Vesta.iso_map_add

/-! ## Computable point enumeration — the curve group's `Fintype`, as plain data

`Classical.choice` enters only through erased `Prop` fields of the Mathlib `Finset` lemmas;
the plain-`def` check certifies the enumeration itself is compiled code, not conjured by
choice. -/

assert_computable CompElliptic.CurveForms.ShortWeierstrass.instFintypeSWPoint +choice
assert_computable CompElliptic.Curves.Pasta.Pallas.fintypePoints +choice
assert_computable CompElliptic.Curves.Pasta.Vesta.fintypePoints +choice

/-! ## Concrete closed facts trusting the compiler (`native_decide`) -/

assert_axioms CompElliptic.Fields.Pasta.pallasBase +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_axioms CompElliptic.Fields.Pasta.vestaBase +native(
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms CompElliptic.Curves.Pasta.Pallas.card_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms CompElliptic.Curves.Pasta.Vesta.card_eq +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms CompElliptic.Curves.Pasta.Pallas.q_nsmul_isoGpt +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_isoGpt)
assert_axioms CompElliptic.Curves.Pasta.Vesta.p_nsmul_isoGpt +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_isoGpt)
assert_axioms CompElliptic.Curves.Pasta.Pallas.iso_card_eq +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_isoGpt)
assert_axioms CompElliptic.Curves.Pasta.Vesta.iso_card_eq +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_isoGpt)
assert_axioms CompElliptic.Curves.Pasta.Pallas.iso_map_bijective +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_isoGpt,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms CompElliptic.Curves.Pasta.Vesta.iso_map_bijective +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_isoGpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms CompElliptic.Curves.Pasta.Pallas.isOdd_zeroRepaired_mapToCurve +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_axioms CompElliptic.Curves.Pasta.Vesta.isOdd_zeroRepaired_mapToCurve +native(
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms CompElliptic.Curves.Pasta.Pallas.norm_charSum_mapToCurve_sub_zeroRepaired +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_axioms CompElliptic.Curves.Pasta.Vesta.norm_charSum_mapToCurve_sub_zeroRepaired +native(
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms CompElliptic.Curves.Pasta.Pallas.card_mapToCurve_fibre_le +native(
  CompElliptic.Fields.Pasta.pallasBase,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_isoGpt)
assert_axioms CompElliptic.Curves.Pasta.Vesta.card_mapToCurve_fibre_le +native(
  CompElliptic.Fields.Pasta.vestaBase,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_isoGpt)
assert_axioms CompElliptic.Curves.Pasta.Pallas.mapHashOutputsToCurve_eq +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_axioms CompElliptic.Curves.Pasta.Vesta.mapHashOutputsToCurve_eq +native(
  CompElliptic.Fields.Pasta.vestaBase)

/-! ## Fast Vesta arithmetic — proven against the affine group law, standard axioms only

The fast tier's headline correctness theorems: the RCB projective addition is the affine
group law (`toAffine_padd`), the projective scalar ladder and the windowed Pippenger MSM
compute the operations they replace, the raw-`ℕ` spelling is `padd`, and the Montgomery
kernel computes the same schedules. Completeness routes through `no_onCurve_y_zero`
(a kernel `decide`), so nothing here reaches `native_decide`. -/

assert_axioms CompElliptic.Curves.Pasta.Fast.Projective.PVes.toAffine_padd
assert_axioms CompElliptic.Curves.Pasta.Fast.Projective.PVes.smulFast_eq
assert_axioms CompElliptic.Curves.Pasta.Fast.Projective.PVes.padd_eq_paddFast
assert_axioms CompElliptic.Curves.Pasta.Fast.Msm.pippengerFastPar_eq_msm
assert_axioms CompElliptic.Curves.Pasta.Fast.Msm.commitLagrangeFastWith_eq
assert_axioms CompElliptic.Curves.Pasta.Fast.ProjectiveMont.pnsmulM_spec
assert_axioms CompElliptic.Curves.Pasta.Fast.ProjectiveMont.msmM_spec
