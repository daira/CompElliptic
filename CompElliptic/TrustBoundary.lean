/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.PastaOrder
import CompElliptic.Hashing.PastaSSWU
import CompElliptic.Hashing.TwoTermUniformity
import CompElliptic.Hashing.WeilSupport
import CompElliptic.Curves.Pasta.Fast.Projective
import CompElliptic.Curves.Pasta.Fast.Msm
import CompElliptic.Curves.Pasta.Fast.ProjectiveMontEquiv
import CompElliptic.Fields.Sqrt
import CompElliptic.Rings.Eisenstein.Units
import CompElliptic.Rings.Eisenstein.Orbits
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

/-! ## The Eisenstein ring `ℤ[ω]` and its unit action — standard axioms only

The finite claims (`card_odd`, the freeness and Burnside counts, the covering)
are quantified statements, but over a 64-element ring, so they are discharged by
KERNEL `decide` and add no axiom. That is deliberate: a quantified result must
not reach for `native_decide`, and here it does not have to. -/

assert_axioms CompElliptic.Rings.Eisenstein.norm_mul
assert_axioms CompElliptic.Rings.Eisenstein.two_dvd_iff
assert_axioms CompElliptic.Rings.Eisenstein.isUnit_iff_norm_eq_one
assert_axioms CompElliptic.Rings.Eisenstein.isUnit_iff_mem_mu6Z
assert_axioms CompElliptic.Rings.Eisenstein.prime_two
assert_axioms CompElliptic.Rings.Eisenstein.not_two_pow_dvd_unit_sub_one
assert_axioms CompElliptic.Rings.Eisenstein.mul_eq_zero_mod_two
assert_axioms CompElliptic.Rings.Eisenstein.card_odd
assert_axioms CompElliptic.Rings.Eisenstein.mu6_free_on_odd
assert_axioms CompElliptic.Rings.Eisenstein.reps_cover
assert_axioms CompElliptic.Rings.Eisenstein.card_orbits_all
assert_axioms CompElliptic.Rings.Eisenstein.orbit_mul_unit

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

/-! ## The Weil-derivation design doc's citations

`design/weil-constant-derivation.md` is a pencil-and-paper proof whose reader relies on
every Lean declaration it cites. To avoid a resulting axiom-checking gap, every such
declaration must be pinned here (checked in CI by `scripts/check_weil_support_refs.py`).
Definitions of polynomials in these modules use Mathlib's noncomputable ones, so they
take `assert_axioms` like the theorems and `Prop`-shaped definitions. -/

/-! ### The abscissae, branch covers, and models (`Hashing/BranchCovers.lean`,
`Hashing/FibreBound.lean`, `Hashing/SimplifiedSWU.lean`, `Hashing/SignedLift.lean`) -/

assert_computable CompElliptic.Hashing.SSWUParams.x1
assert_computable CompElliptic.Hashing.SSWUParams.x2
assert_computable CompElliptic.Hashing.SSWUParams.phiCore
assert_computable CompElliptic.Hashing.SSWUParams.twist1
assert_computable CompElliptic.Hashing.SSWUParams.twist2
assert_computable CompElliptic.Hashing.SSWUParams.model1
assert_computable CompElliptic.Hashing.SSWUParams.model2
assert_computable CompElliptic.Hashing.SSWUParams.scale1
assert_computable CompElliptic.Hashing.SSWUParams.scale2
assert_computable CompElliptic.Hashing.sgn0
assert_axioms CompElliptic.Hashing.SSWUParams.map_neg
assert_axioms CompElliptic.Hashing.SSWUParams.Zuu_add_one_ne_zero
assert_axioms CompElliptic.Hashing.SSWUParams.ta_ne_zero_of_u_ne_zero
assert_axioms CompElliptic.Hashing.SSWUParams.g_x2_eq
assert_axioms CompElliptic.Hashing.SSWUParams.model1_eq
assert_axioms CompElliptic.Hashing.SSWUParams.model2_eq
assert_axioms CompElliptic.Hashing.SSWUParams.model1_zero
assert_axioms CompElliptic.Hashing.SSWUParams.model2_zero
assert_axioms CompElliptic.Hashing.SSWUParams.scale1_ne_zero
assert_axioms CompElliptic.Hashing.SSWUParams.scale2_ne_zero

/-! ### The model point sets and covering maps (`Hashing/BranchCovers.lean`) -/

assert_computable CompElliptic.Hashing.SSWUParams.modelPoints1 +choice
assert_computable CompElliptic.Hashing.SSWUParams.modelPoints2 +choice
assert_computable CompElliptic.Hashing.SSWUParams.cover1Map +choice
assert_computable CompElliptic.Hashing.SSWUParams.cover2Map +choice
assert_axioms CompElliptic.Hashing.SSWUParams.fibre_sum
assert_axioms CompElliptic.Hashing.SSWUParams.modelPoints_sum

/-! ### The supporting facts of the cited steps (`Hashing/WeilSupport.lean`) -/

assert_axioms CompElliptic.Hashing.isCoprime_of_bezout
assert_axioms CompElliptic.Hashing.isCoprime_X_of_coeff_zero
assert_axioms CompElliptic.Hashing.isCoprime_C_of_ne_zero
assert_axioms CompElliptic.Hashing.not_X_sq_dvd
assert_axioms CompElliptic.Hashing.SSWUParams.gPoly
assert_axioms CompElliptic.Hashing.SSWUParams.gPoly_separable
assert_axioms CompElliptic.Hashing.SSWUParams.eval_g_neg_B_div_A
assert_axioms CompElliptic.Hashing.SSWUParams.g_neg_B_div_A_ne_zero
assert_axioms CompElliptic.Hashing.SSWUParams.phiCubic
assert_axioms CompElliptic.Hashing.SSWUParams.phiCubic_derivative
assert_axioms CompElliptic.Hashing.SSWUParams.phiCubic_separable
assert_axioms CompElliptic.Hashing.SSWUParams.taPoly_derivative
assert_axioms CompElliptic.Hashing.SSWUParams.tPoly_add_one_separable
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly
assert_axioms CompElliptic.Hashing.SSWUParams.eval_phiPoly
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly_eq_comp
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly_natDegree
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly_coeff_zero
assert_axioms CompElliptic.Hashing.SSWUParams.psiPoly
assert_axioms CompElliptic.Hashing.SSWUParams.psiPoly_coeff_zero
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly_64_eq
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly_isCoprime_snd
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly_isCoprime_tPoly_add_one
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly_separable
assert_axioms CompElliptic.Hashing.SSWUParams.phiPoly_squarefree
assert_axioms CompElliptic.Hashing.SSWUParams.model1Poly
assert_axioms CompElliptic.Hashing.SSWUParams.model2Poly
assert_axioms CompElliptic.Hashing.SSWUParams.eval_model1Poly
assert_axioms CompElliptic.Hashing.SSWUParams.eval_model2Poly
assert_axioms CompElliptic.Hashing.SSWUParams.model1Poly_natDegree
assert_axioms CompElliptic.Hashing.SSWUParams.model2Poly_natDegree
assert_axioms CompElliptic.Hashing.SSWUParams.model1Poly_squarefree
assert_axioms CompElliptic.Hashing.SSWUParams.model2Poly_squarefree
assert_axioms CompElliptic.Hashing.SSWUParams.p2Poly
assert_axioms CompElliptic.Hashing.SSWUParams.p2Poly_coeff
assert_axioms CompElliptic.Hashing.SSWUParams.p2Poly_natDegree
assert_axioms CompElliptic.Hashing.SSWUParams.p2Poly_isEisensteinAt
assert_axioms CompElliptic.Hashing.SSWUParams.p1RecipPoly
assert_axioms CompElliptic.Hashing.SSWUParams.p1RecipPoly_coeff
assert_axioms CompElliptic.Hashing.SSWUParams.p1RecipPoly_natDegree
assert_axioms CompElliptic.Hashing.SSWUParams.p1RecipPoly_isEisensteinAt
assert_axioms CompElliptic.Hashing.not_isSquare_ratFunc_of_squarefree
assert_axioms CompElliptic.Hashing.exists_sq_eq_of_ratFunc_sq
assert_axioms CompElliptic.Hashing.sq_or_mul_sq_of_isSquare_adjoinRoot
assert_axioms CompElliptic.Hashing.SSWUParams.not_isSquare_adjoinRoot_of_linear
assert_axioms CompElliptic.Hashing.SSWUParams.gPoly_not_isSquare_ratFunc
assert_axioms CompElliptic.Hashing.SSWUParams.v4TestPoly
assert_axioms CompElliptic.Hashing.SSWUParams.v4TestPoly_not_isSquare
assert_axioms CompElliptic.Hashing.SSWUParams.c4TestPoly
assert_axioms CompElliptic.Hashing.SSWUParams.c4TestPoly_not_isSquare

/-! ### Characters and realness (`Hashing/CharacterSum.lean`) -/

assert_axioms CompElliptic.Hashing.charSum_eq
assert_axioms CompElliptic.Hashing.addChar_map_neg_eq_conj
assert_axioms CompElliptic.Hashing.IsOdd.mult_neg
assert_axioms CompElliptic.Hashing.IsOdd.conj_charSum
assert_axioms CompElliptic.Hashing.IsOdd.two_mul_charSum

/-! ### The Weil-input shape and the assembly (`Hashing/WeilInstance.lean`,
`Hashing/WellDistributed.lean`, `Hashing/TwoTermUniformity.lean`) -/

assert_axioms CompElliptic.Hashing.CharSumBounded
assert_axioms CompElliptic.Hashing.SSWUParams.cover_charSum
assert_axioms CompElliptic.Hashing.SSWUParams.weilBounded_zeroRepaired
assert_axioms CompElliptic.Hashing.WeilBounded
assert_axioms CompElliptic.Hashing.WeilBounded.comp
assert_axioms CompElliptic.Hashing.sum_abs_prob_dev_le
assert_axioms CompElliptic.Hashing.sum_abs_prob_dev_transport_le

/-! ### The deployed instances (`Hashing/PastaSSWU.lean`) -/

assert_computable CompElliptic.Curves.Pasta.Pallas.mapToCurve +choice +native(
  CompElliptic.Fields.Pasta.pallasBase)
assert_computable CompElliptic.Curves.Pasta.Vesta.mapToCurve +choice +native(
  CompElliptic.Fields.Pasta.vestaBase)
assert_axioms CompElliptic.Curves.Pasta.Pallas.neg_AB_not_isSquare
assert_axioms CompElliptic.Curves.Pasta.Vesta.neg_AB_not_isSquare
assert_axioms CompElliptic.Curves.Pasta.Pallas.weilBounded_zeroRepaired_mapToCurve +native(
  CompElliptic.Fields.Pasta.pallasBase,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_isoGpt)
assert_axioms CompElliptic.Curves.Pasta.Vesta.weilBounded_zeroRepaired_mapToCurve +native(
  CompElliptic.Fields.Pasta.vestaBase,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_isoGpt)
