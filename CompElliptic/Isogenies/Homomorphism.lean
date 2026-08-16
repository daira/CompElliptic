/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.CurveOrder
import CompElliptic.Isogenies.ThreeIsogeny
import CompElliptic.Isogenies.VeluCertificates

/-!
# The homomorphism property of the 3-isogeny

This module proves that `ThreeIsogeny.map` is a group homomorphism on rational
points (`map_add`). That an isogeny is automatically a group homomorphism is a
standard fact (Galbraith §25.1; Silverman, Theorem III.4.8), but Mathlib does
not have the general theorem, and this development does not rely on it: the
property is proved directly for the particular isogeny maps in use.

The proof is layered. The coordinate-level theorems `chord_x_compat` and
`tangent_x_compat` say that the image of a sum's third point has exactly the
abscissa the codomain group law computes from the two image points. They consume
the generated certificates and support lemmas of `Isogenies/VeluCertificates.lean`,
and their parameters are pinned by defining equations so that the point-level
layer can instantiate them against the branches of `add`. The point level then
assembles `map_add_x` (abscissa agreement for every pair of points), upgrades it
to `map_add_pm` (agreement up to sign, because two on-curve points sharing an
abscissa are equal or negatives), and resolves the sign by group algebra. The
ambiguous cases force an element of order two, and the codomain has none —
rational 2-torsion needs a point with `y = 0`, which `hc` already excludes
(`map_add`, through `eq_zero_of_two_nsmul_eq_zero`). Negation-compatibility
(`map_neg`) carries the sentinel cases.
-/

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

namespace CompElliptic.Isogenies.ThreeIsogeny

variable {F : Type*} [Field F] (I : ThreeIsogeny F)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Chord compatibility at the coordinate level: for two on-curve points with
distinct abscissas, the image of the chord's third point has exactly the abscissa
the codomain chord computes from the two image points. The parameters `lam`, `x₃`,
`y₃` are pinned by defining equations, so a caller can instantiate them with the
chord branch of `add`; the caller supplies `h₃` (the third point is on the curve,
from closure of point addition). Consumes the generated certificate and support
lemmas of `Isogenies/VeluCertificates.lean`. -/
theorem chord_x_compat (h2 : (2 : F) ≠ 0)
    (hd : ∀ X : F, ¬ OnCurve I.domain.A I.domain.B (X, 0))
    {x₁ y₁ x₂ y₂ lam x₃ y₃ : F}
    (h₁ : OnCurve I.domain.A I.domain.B (x₁, y₁))
    (h₂ : OnCurve I.domain.A I.domain.B (x₂, y₂))
    (h₃ : OnCurve I.domain.A I.domain.B (x₃, y₃))
    (hne : x₁ ≠ x₂)
    (hlam : lam = (y₂ - y₁) / (x₂ - x₁))
    (hx₃ : x₃ = lam^2 - x₁ - x₂)
    (hy₃ : y₃ = lam * (x₁ - x₃) - y₁) :
    (I.mapXY x₃ y₃).1 =
      (((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2)
          / ((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1))^2
        - (I.mapXY x₁ y₁).1 - (I.mapXY x₂ y₂).1 := by
  have hdd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hxx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hd₁ : x₁ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₁)
  have hd₂ : x₂ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₂)
  have hd₃ : x₃ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₃)
  have hc₁ : y₁^2 = x₁^3 + I.domain.A * x₁ + I.domain.B := h₁
  have hc₂ : y₂^2 = x₂^3 + I.domain.A * x₂ + I.domain.B := h₂
  have hslope : y₂ - y₁ = lam * (x₂ - x₁) := by
    rw [hlam, div_mul_cancel₀ _ hxx]
  set m' : F := y₁ - lam * (x₁ - I.x₀) with hm'
  have hL1 : y₁ = lam * (x₁ - I.x₀) + m' := by linear_combination -hm'
  have hL2 : y₂ = lam * (x₂ - I.x₀) + m' := by linear_combination hslope - hm'
  have hbridge := chord_psi3_bridge ((x₁ - I.x₀) + (x₂ - I.x₀)) (x₁ - x₂) lam m' I.x₀
    I.domain.A I.domain.B
    (by linear_combination 8*hc₁ - 8 * (y₁ + lam * (x₁ - I.x₀) + m') * hL1)
    (by linear_combination 8*hc₂ - 8 * (y₂ + lam * (x₂ - I.x₀) + m') * hL2)
    I.psi3
  have hp_inst := (mul_eq_zero.mp hbridge).resolve_left
    (mul_ne_zero hdd (pow_ne_zero 1 h2))
  have h2p4 : ((2 : F)^4) ≠ 0 := pow_ne_zero _ h2
  have h2p6 : ((2 : F)^6) ≠ 0 := pow_ne_zero _ h2
  have hsem_ns := chord_ns_semantics ((x₁ - I.x₀) + (x₂ - I.x₀)) (x₁ - x₂) lam m' I.x₀
    I.domain.A I.domain.B
    (by linear_combination 8*hc₁ - 8 * (y₁ + lam * (x₁ - I.x₀) + m') * hL1)
    (by linear_combination 8*hc₂ - 8 * (y₂ + lam * (x₂ - I.x₀) + m') * hL2)
  have hsem_ws := chord_ws_semantics ((x₁ - I.x₀) + (x₂ - I.x₀)) (x₁ - x₂) lam m' I.x₀
    I.domain.A I.domain.B
    (by linear_combination 8*hc₁ - 8 * (y₁ + lam * (x₁ - I.x₀) + m') * hL1)
    (by linear_combination 8*hc₂ - 8 * (y₂ + lam * (x₂ - I.x₀) + m') * hL2)
  obtain ⟨nsv, hnsv⟩ : ∃ n : F,
      n = (I.xnum x₂ * (x₁ - I.x₀)^2 - I.xnum x₁ * (x₂ - I.x₀)^2) / (x₁ - x₂) := ⟨_, rfl⟩
  obtain ⟨wsv, hwsv⟩ : ∃ w : F,
      w = ((lam * (x₂ - I.x₀) + m') * I.ynum x₂ * (x₁ - I.x₀)^3
        - (lam * (x₁ - I.x₀) + m') * I.ynum x₁ * (x₂ - I.x₀)^3) / (x₁ - x₂) := ⟨_, rfl⟩
  have hNNv : (x₁ - x₂) * nsv
      = I.xnum x₂ * (x₁ - I.x₀)^2 - I.xnum x₁ * (x₂ - I.x₀)^2 := by
    rw [hnsv]; field_simp
  have hWv : (x₁ - x₂) * wsv
      = (lam * (x₂ - I.x₀) + m') * I.ynum x₂ * (x₁ - I.x₀)^3
        - (lam * (x₁ - I.x₀) + m') * I.ynum x₁ * (x₂ - I.x₀)^3 := by
    rw [hwsv]; field_simp
  have hcert := chord_x_certificate ((x₁ - I.x₀) + (x₂ - I.x₀)) (x₁ - x₂) lam m' I.x₀
    nsv wsv hp_inst
    (mul_left_cancel₀ (mul_ne_zero hdd h2p4) (by
      have hN := hNNv
      simp only [xnum, v, u] at hN
      linear_combination ((2 : F)^8) * hN + hsem_ns))
    (mul_left_cancel₀ (mul_ne_zero hdd h2p6) (by
      have hW := hWv
      simp only [ynum, v, u] at hW
      linear_combination ((2 : F)^12) * hW + hsem_ws))
  have hcorr := chord_final_correction ((x₁ - I.x₀) + (x₂ - I.x₀)) (x₁ - x₂) lam m' I.x₀
    I.domain.A I.domain.B
    (by linear_combination 8*hc₁ - 8 * (y₁ + lam * (x₁ - I.x₀) + m') * hL1)
    (by linear_combination 8*hc₂ - 8 * (y₂ + lam * (x₂ - I.x₀) + m') * hL2)
    I.psi3
  -- defining equations of the image values, cleared of their denominators
  have hX₁ : (I.mapXY x₁ y₁).1 * (x₁ - I.x₀)^2 = I.s^2 * I.xnum x₁ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₁)
  have hX₂ : (I.mapXY x₂ y₂).1 * (x₂ - I.x₀)^2 = I.s^2 * I.xnum x₂ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₂)
  have hX₃ : (I.mapXY x₃ y₃).1 * (x₃ - I.x₀)^2 = I.s^2 * I.xnum x₃ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₃)
  have hY₁ : (I.mapXY x₁ y₁).2 * (x₁ - I.x₀)^3
      = I.s^3 * ((lam * (x₁ - I.x₀) + m') * I.ynum x₁) := by
    simp only [mapXY]
    rw [← hL1]
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hd₁)
  have hY₂ : (I.mapXY x₂ y₂).2 * (x₂ - I.x₀)^3
      = I.s^3 * ((lam * (x₂ - I.x₀) + m') * I.ynum x₂) := by
    simp only [mapXY]
    rw [← hL2]
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hd₂)
  -- the difference and sum equations, in terms of the atoms
  have hΔX : ((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1) * ((x₁ - I.x₀)^2 * (x₂ - I.x₀)^2)
      = I.s^2 * ((x₁ - x₂) * nsv) := by
    linear_combination (x₁ - I.x₀)^2 * hX₂ - (x₂ - I.x₀)^2 * hX₁ - I.s^2 * hNNv
  have hΔY : ((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2) * ((x₁ - I.x₀)^3 * (x₂ - I.x₀)^3)
      = I.s^3 * ((x₁ - x₂) * wsv) := by
    linear_combination (x₁ - I.x₀)^3 * hY₂ - (x₂ - I.x₀)^3 * hY₁ - I.s^3 * hWv
  have hsumX : ((I.mapXY x₃ y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₂ y₂).1)
        * ((x₁ - I.x₀)^2 * (x₂ - I.x₀)^2 * (x₃ - I.x₀)^2)
      = I.s^2 * (I.xnum x₃ * (x₁ - I.x₀)^2 * (x₂ - I.x₀)^2
          + I.xnum x₁ * (x₂ - I.x₀)^2 * (x₃ - I.x₀)^2
          + I.xnum x₂ * (x₁ - I.x₀)^2 * (x₃ - I.x₀)^2) := by
    linear_combination (x₁ - I.x₀)^2 * (x₂ - I.x₀)^2 * hX₃
      + (x₂ - I.x₀)^2 * (x₃ - I.x₀)^2 * hX₁ + (x₁ - I.x₀)^2 * (x₃ - I.x₀)^2 * hX₂
  -- the image abscissas are distinct
  have hXne : (I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1 ≠ 0 := by
    intro h0
    exact hne (I.abscissa_inj h2 hd h₁ h₂ (sub_eq_zero.mp h0).symm)
  subst hx₃
  -- the cleared, slope-free key equation, closed by the certificate and correction
  have hkeyc : (2 : F)^10
        * ((((I.mapXY (lam^2 - x₁ - x₂) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₂ y₂).1)
            * ((x₁ - I.x₀)^2 * (x₂ - I.x₀)^2 * (lam^2 - x₁ - x₂ - I.x₀)^2))
          * (((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1) * ((x₁ - I.x₀)^2 * (x₂ - I.x₀)^2))^2)
      = (2 : F)^10
        * ((((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2) * ((x₁ - I.x₀)^3 * (x₂ - I.x₀)^3))^2
          * (lam^2 - x₁ - x₂ - I.x₀)^2) := by
    have hN₁ : I.xnum x₁ = x₁ * (x₁ - I.x₀)^2
        + 2 * (3 * I.x₀^2 + I.domain.A) * (x₁ - I.x₀)
        + 4 * (I.x₀^3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    have hN₂ : I.xnum x₂ = x₂ * (x₂ - I.x₀)^2
        + 2 * (3 * I.x₀^2 + I.domain.A) * (x₂ - I.x₀)
        + 4 * (I.x₀^3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    have hN₃ : I.xnum (lam^2 - x₁ - x₂) = (lam^2 - x₁ - x₂) * (lam^2 - x₁ - x₂ - I.x₀)^2
        + 2 * (3 * I.x₀^2 + I.domain.A) * (lam^2 - x₁ - x₂ - I.x₀)
        + 4 * (I.x₀^3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    rw [hsumX, hΔX, hΔY, hN₁, hN₂, hN₃]
    linear_combination I.s^6 * hcert + I.s^6 * (x₁ - x₂) * nsv^2 * hcorr
  have hkey : ((I.mapXY (lam^2 - x₁ - x₂) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₂ y₂).1)
        * ((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1)^2
      = ((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2)^2 :=
    mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 hd₁) (pow_ne_zero 6 hd₂))
      (pow_ne_zero 2 hd₃))
      (mul_left_cancel₀ (pow_ne_zero 10 h2) (by linear_combination hkeyc))
  have hdiv : (((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2)
        / ((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1))^2
      = (I.mapXY (lam^2 - x₁ - x₂) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₂ y₂).1 := by
    rw [div_pow, ← hkey]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hXne)
  linear_combination -hdiv

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Doubling compatibility at the coordinate level: the image of the doubled
point has exactly the abscissa the codomain doubling computes from the image
point. Parameters are pinned as in `chord_x_compat`; `hc` excludes rational
2-torsion on the codomain, which makes the image ordinate nonzero. -/
theorem tangent_x_compat (h2 : (2 : F) ≠ 0)
    (hc : ∀ X : F, ¬ OnCurve I.codomain.A I.codomain.B (X, 0))
    {x₁ y₁ lam x₃ y₃ : F}
    (h₁ : OnCurve I.domain.A I.domain.B (x₁, y₁))
    (h₃ : OnCurve I.domain.A I.domain.B (x₃, y₃))
    (hy₁ : y₁ ≠ 0)
    (hlam : lam = (3 * x₁^2 + I.domain.A) / (2*y₁))
    (hx₃ : x₃ = lam^2 - x₁ - x₁)
    (hy₃ : y₃ = lam * (x₁ - x₃) - y₁) :
    (I.mapXY x₃ y₃).1 =
      ((3 * (I.mapXY x₁ y₁).1^2 + I.codomain.A) / (2 * (I.mapXY x₁ y₁).2))^2
        - (I.mapXY x₁ y₁).1 - (I.mapXY x₁ y₁).1 := by
  have hd₁ : x₁ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₁)
  have hd₃ : x₃ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₃)
  have hc₁ : y₁^2 = x₁^3 + I.domain.A * x₁ + I.domain.B := h₁
  have h2y : (2 : F) * y₁ ≠ 0 := mul_ne_zero h2 hy₁
  have hslope : lam * (2*y₁) = 3 * x₁^2 + I.domain.A := by
    rw [hlam, div_mul_cancel₀ _ h2y]
  set v' : F := y₁ - lam * (x₁ - I.x₀) with hv'
  have hL : y₁ = lam * (x₁ - I.x₀) + v' := by linear_combination -hv'
  have hbridgeT := tangent_psi3_bridge (x₁ - I.x₀) lam v' I.x₀ I.domain.A I.domain.B
    (by linear_combination hc₁ - (y₁ + lam * (x₁ - I.x₀) + v') * hL)
    (by linear_combination hslope - 2*lam*hL)
    I.psi3
  have hsem_k := tangent_k_semantics (x₁ - I.x₀) lam v' I.x₀ I.domain.A I.domain.B
    (by linear_combination hc₁ - (y₁ + lam * (x₁ - I.x₀) + v') * hL)
    (by linear_combination hslope - 2*lam*hL)
  have hsem_t := tangent_t_semantics (x₁ - I.x₀) lam v' I.x₀ I.domain.A I.domain.B
    (by linear_combination hc₁ - (y₁ + lam * (x₁ - I.x₀) + v') * hL)
    (by linear_combination hslope - 2*lam*hL)
  have hcorrT := tangent_correction (x₁ - I.x₀) lam v' I.x₀ I.domain.A I.domain.B
    (by linear_combination hc₁ - (y₁ + lam * (x₁ - I.x₀) + v') * hL)
    (by linear_combination hslope - 2*lam*hL)
  obtain ⟨kv, hkv⟩ : ∃ k : F,
      k = 2 * (lam * (x₁ - I.x₀) + v') * I.ynum x₁ * (x₁ - I.x₀) := ⟨_, rfl⟩
  obtain ⟨tv, htv⟩ : ∃ t : F,
      t = 3 * (I.xnum x₁)^2
        + (I.domain.A - 10 * (3 * I.x₀^2 + I.domain.A)) * (x₁ - I.x₀)^4 := ⟨_, rfl⟩
  have hcertT := tangent_x_certificate (x₁ - I.x₀) lam v' I.x₀ kv tv
    hbridgeT
    (by
      have hk := hkv
      simp only [ynum, v, u] at hk
      linear_combination hk + hsem_k)
    (by
      have ht := htv
      simp only [xnum, v, u] at ht
      linear_combination ht + hsem_t)
  have hX₁ : (I.mapXY x₁ y₁).1 * (x₁ - I.x₀)^2 = I.s^2 * I.xnum x₁ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₁)
  have hX₃ : (I.mapXY x₃ y₃).1 * (x₃ - I.x₀)^2 = I.s^2 * I.xnum x₃ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₃)
  have hY₁ : (I.mapXY x₁ y₁).2 * (x₁ - I.x₀)^3
      = I.s^3 * ((lam * (x₁ - I.x₀) + v') * I.ynum x₁) := by
    simp only [mapXY]
    rw [← hL]
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hd₁)
  have hY₁ne : (I.mapXY x₁ y₁).2 ≠ 0 := by
    intro h0
    have himg := I.onCurve_mapXY h₁
    exact hc (I.mapXY x₁ y₁).1 (by rw [← h0, Prod.mk.eta]; exact himg)
  have h2Y : ((2 : F) * (I.mapXY x₁ y₁).2) * (x₁ - I.x₀)^4 = I.s^3 * kv := by
    linear_combination 2 * (x₁ - I.x₀) * hY₁ - I.s^3 * hkv
  have h3X : (3 * (I.mapXY x₁ y₁).1^2 + I.codomain.A) * (x₁ - I.x₀)^4
      = I.s^4 * tv := by
    linear_combination
      3 * ((I.mapXY x₁ y₁).1 * (x₁ - I.x₀)^2 + I.s^2 * I.xnum x₁) * hX₁
        + (x₁ - I.x₀)^4 * I.codomain_A - I.s^4 * htv
  have hsumXT : ((I.mapXY x₃ y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₁ y₁).1)
        * ((x₁ - I.x₀)^2 * (x₃ - I.x₀)^2)
      = I.s^2 * (I.xnum x₃ * (x₁ - I.x₀)^2 + 2 * I.xnum x₁ * (x₃ - I.x₀)^2) := by
    linear_combination (x₁ - I.x₀)^2 * hX₃ + 2 * (x₃ - I.x₀)^2 * hX₁
  subst hx₃
  have hkeycT : (2 : F)^2
        * ((((I.mapXY (lam^2 - x₁ - x₁) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₁ y₁).1)
            * ((x₁ - I.x₀)^2 * (lam^2 - x₁ - x₁ - I.x₀)^2))
          * (((2 : F) * (I.mapXY x₁ y₁).2) * (x₁ - I.x₀)^4)^2)
      = (2 : F)^2
        * (((3 * (I.mapXY x₁ y₁).1^2 + I.codomain.A) * (x₁ - I.x₀)^4)^2
          * ((x₁ - I.x₀)^2 * (lam^2 - x₁ - x₁ - I.x₀)^2)) := by
    have hN₁ : I.xnum x₁ = x₁ * (x₁ - I.x₀)^2
        + 2 * (3 * I.x₀^2 + I.domain.A) * (x₁ - I.x₀)
        + 4 * (I.x₀^3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    have hN₃ : I.xnum (lam^2 - x₁ - x₁) = (lam^2 - x₁ - x₁) * (lam^2 - x₁ - x₁ - I.x₀)^2
        + 2 * (3 * I.x₀^2 + I.domain.A) * (lam^2 - x₁ - x₁ - I.x₀)
        + 4 * (I.x₀^3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    rw [hsumXT, h2Y, h3X, hN₁, hN₃]
    linear_combination I.s^8 * hcertT + I.s^8 * kv^2 * hcorrT
  have hkeyT : ((I.mapXY (lam^2 - x₁ - x₁) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₁ y₁).1)
        * ((2 : F) * (I.mapXY x₁ y₁).2)^2
      = (3 * (I.mapXY x₁ y₁).1^2 + I.codomain.A)^2 :=
    mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 10 hd₁) (pow_ne_zero 2 hd₃))
      (mul_left_cancel₀ (pow_ne_zero 2 h2) (by linear_combination hkeycT))
  have hdivT : ((3 * (I.mapXY x₁ y₁).1^2 + I.codomain.A)
        / (2 * (I.mapXY x₁ y₁).2))^2
      = (I.mapXY (lam^2 - x₁ - x₁) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₁ y₁).1 := by
    rw [div_pow, ← hkeyT]
    have h2Yne : ((2 : F) * (I.mapXY x₁ y₁).2)^2 ≠ 0 :=
      pow_ne_zero 2 (mul_ne_zero h2 hY₁ne)
    exact mul_div_cancel_right₀ _ h2Yne
  linear_combination -hdivT

variable [DecidableEq F]

set_option maxHeartbeats 1000000 in
/-- The isogeny respects addition at the abscissa level, for every pair of
points: each branch of `add` matches the corresponding branch on the images,
through `chord_x_compat` and `tangent_x_compat`. -/
theorem map_add_x (h2 : (2 : F) ≠ 0)
    (hd : ∀ X : F, ¬ OnCurve I.domain.A I.domain.B (X, 0))
    (hc : ∀ X : F, ¬ OnCurve I.codomain.A I.codomain.B (X, 0))
    (P Q : SWPoint I.domain) :
    (I.map (P + Q)).x = (I.map P + I.map Q).x := by
  by_cases hP0 : (P.x, P.y) = ((0 : F), (0 : F))
  · rw [SWPoint.ext_pair (E := I.domain) (Q := 0) hP0, _root_.zero_add, I.map_zero,
      _root_.zero_add]
  by_cases hQ0 : (Q.x, Q.y) = ((0 : F), (0 : F))
  · rw [SWPoint.ext_pair (E := I.domain) (Q := 0) hQ0, _root_.add_zero, I.map_zero,
      _root_.add_zero]
  have hP1 : OnCurve I.domain.A I.domain.B (P.x, P.y) := P.onCurve.resolve_right hP0
  have hQ1 : OnCurve I.domain.A I.domain.B (Q.x, Q.y) := Q.onCurve.resolve_right hQ0
  have himgP := I.onCurve_mapXY hP1
  have himgQ := I.onCurve_mapXY hQ1
  have himgP0 : ((I.mapXY P.x P.y).1, (I.mapXY P.x P.y).2) ≠ ((0 : F), (0 : F)) := by
    intro hcon
    exact origin_not_on_curve I.codomain (by rw [← Prod.mk.eta (p := I.mapXY P.x P.y), hcon] at himgP; exact himgP)
  have himgQ0 : ((I.mapXY Q.x Q.y).1, (I.mapXY Q.x Q.y).2) ≠ ((0 : F), (0 : F)) := by
    intro hcon
    exact origin_not_on_curve I.codomain (by rw [← Prod.mk.eta (p := I.mapXY Q.x Q.y), hcon] at himgQ; exact himgQ)
  by_cases hxx : P.x = Q.x
  · by_cases hyy : P.y + Q.y = 0
    · -- inverse pair: both sides are the identity
      have hsum : P + Q = 0 := SWPoint.ext_pair (by
        show add I.domain.A (P.x, P.y) (Q.x, Q.y) = (0, 0)
        unfold add
        rw [if_neg hP0, if_neg hQ0, if_pos hxx, if_pos hyy])
      rw [hsum, I.map_zero]
      suffices h : I.map P + I.map Q = 0 by rw [h]
      have hQy : Q.y = -P.y := by linear_combination hyy
      have hQpair : I.mapXY Q.x Q.y = ((I.mapXY P.x P.y).1, -(I.mapXY P.x P.y).2) := by
        rw [← hxx, hQy]
        exact I.mapXY_neg P.x P.y
      rw [map, dif_pos hP1, map, dif_pos hQ1]
      apply SWPoint.ext_pair
      show add I.codomain.A ((I.mapXY P.x P.y).1, (I.mapXY P.x P.y).2)
          ((I.mapXY Q.x Q.y).1, (I.mapXY Q.x Q.y).2) = (0, 0)
      unfold add
      rw [if_neg himgP0, if_neg himgQ0,
        if_pos (show (I.mapXY P.x P.y).1 = (I.mapXY Q.x Q.y).1 by rw [hQpair]),
        if_pos (show (I.mapXY P.x P.y).2 + (I.mapXY Q.x Q.y).2 = 0 by rw [hQpair]; ring)]
    · -- doubling
      have hyq : Q.y = P.y := by
        have hsq : (P.y - Q.y) * (P.y + Q.y) = 0 := by
          have e1 : P.y^2 = P.x^3 + I.domain.A * P.x + I.domain.B := hP1
          have e2 : Q.y^2 = Q.x^3 + I.domain.A * Q.x + I.domain.B := hQ1
          rw [hxx] at e1
          linear_combination e1 - e2
        rcases mul_eq_zero.mp hsq with h | h
        · linear_combination -h
        · exact absurd h hyy
      have hy1 : P.y ≠ 0 := by
        intro h0
        exact hyy (by rw [hyq, h0]; ring)
      have hQP : Q = P := SWPoint.ext_pair (Prod.ext_iff.mpr ⟨hxx.symm, hyq⟩)
      subst hQP
      -- the domain doubling output
      have hpair : add I.domain.A (Q.x, Q.y) (Q.x, Q.y)
          = (((3 * Q.x^2 + I.domain.A) / (2 * Q.y))^2 - Q.x - Q.x,
             ((3 * Q.x^2 + I.domain.A) / (2 * Q.y))
               * (Q.x - (((3 * Q.x^2 + I.domain.A) / (2 * Q.y))^2 - Q.x - Q.x)) - Q.y) := by
        unfold add
        rw [if_neg hQ0, if_neg hQ0, if_pos rfl, if_neg hyy]
      have hxagree : (Q + Q).x = ((3 * Q.x^2 + I.domain.A) / (2 * Q.y))^2 - Q.x - Q.x := by
        show (add I.domain.A (Q.x, Q.y) (Q.x, Q.y)).1 = _
        rw [hpair]
      have hyagree : (Q + Q).y = ((3 * Q.x^2 + I.domain.A) / (2 * Q.y))
          * (Q.x - (((3 * Q.x^2 + I.domain.A) / (2 * Q.y))^2 - Q.x - Q.x)) - Q.y := by
        show (add I.domain.A (Q.x, Q.y) (Q.x, Q.y)).2 = _
        rw [hpair]
      have h₃ : OnCurve I.domain.A I.domain.B ((Q + Q).x, (Q + Q).y) := by
        refine (Q + Q).onCurve.resolve_right ?_
        intro h0
        have h2Q : Q + Q = 0 := SWPoint.ext_pair h0
        have hQn : Q = -Q := add_eq_zero_iff_eq_neg.mp h2Q
        have hyneg : Q.y = -Q.y := by
          have h := congrArg SWPoint.y hQn
          rwa [SWPoint.neg_y] at h
        exact hy1 (by
          have h2y : (2 : F) * Q.y = 0 := by linear_combination hyneg
          exact (mul_eq_zero.mp h2y).resolve_left h2)
      -- the image side: doubling of the image point
      have hY1ne : (I.mapXY Q.x Q.y).2 ≠ 0 := by
        intro h0
        exact hc (I.mapXY Q.x Q.y).1 (by rw [← h0, Prod.mk.eta]; exact himgQ)
      rw [map, dif_pos h₃, map, dif_pos hQ1]
      show (I.mapXY (Q + Q).x (Q + Q).y).1
        = (add I.codomain.A ((I.mapXY Q.x Q.y).1, (I.mapXY Q.x Q.y).2)
            ((I.mapXY Q.x Q.y).1, (I.mapXY Q.x Q.y).2)).1
      have haddimg : (add I.codomain.A ((I.mapXY Q.x Q.y).1, (I.mapXY Q.x Q.y).2)
            ((I.mapXY Q.x Q.y).1, (I.mapXY Q.x Q.y).2)).1
          = ((3 * (I.mapXY Q.x Q.y).1^2 + I.codomain.A) / (2 * (I.mapXY Q.x Q.y).2))^2
            - (I.mapXY Q.x Q.y).1 - (I.mapXY Q.x Q.y).1 := by
        unfold add
        rw [if_neg himgQ0, if_neg himgQ0, if_pos rfl,
          if_neg (fun hcon => hY1ne ((mul_eq_zero.mp (by linear_combination hcon)).resolve_left h2))]
      rw [haddimg]
      exact I.tangent_x_compat h2 hc hQ1 h₃ hy1 rfl hxagree (by rw [hyagree, hxagree])
  · -- chord
    have hXne : (I.mapXY P.x P.y).1 ≠ (I.mapXY Q.x Q.y).1 := by
      intro hcon
      exact hxx (I.abscissa_inj h2 hd hP1 hQ1 hcon)
    have hpair : add I.domain.A (P.x, P.y) (Q.x, Q.y)
        = (((Q.y - P.y) / (Q.x - P.x))^2 - P.x - Q.x,
           ((Q.y - P.y) / (Q.x - P.x))
             * (P.x - (((Q.y - P.y) / (Q.x - P.x))^2 - P.x - Q.x)) - P.y) := by
      unfold add
      rw [if_neg hP0, if_neg hQ0, if_neg hxx]
    have hxagree : (P + Q).x = ((Q.y - P.y) / (Q.x - P.x))^2 - P.x - Q.x := by
      show (add I.domain.A (P.x, P.y) (Q.x, Q.y)).1 = _
      rw [hpair]
    have hyagree : (P + Q).y = ((Q.y - P.y) / (Q.x - P.x))
        * (P.x - (((Q.y - P.y) / (Q.x - P.x))^2 - P.x - Q.x)) - P.y := by
      show (add I.domain.A (P.x, P.y) (Q.x, Q.y)).2 = _
      rw [hpair]
    have h₃ : OnCurve I.domain.A I.domain.B ((P + Q).x, (P + Q).y) := by
      refine (P + Q).onCurve.resolve_right ?_
      intro h0
      have hPQ : P + Q = 0 := SWPoint.ext_pair h0
      have hQn : Q = -P := by
        have := add_eq_zero_iff_neg_eq.mp hPQ
        exact this.symm
      exact hxx (by rw [hQn]; exact (SWPoint.neg_x P).symm)
    rw [map, dif_pos h₃, map, dif_pos hP1, map, dif_pos hQ1]
    show (I.mapXY (P + Q).x (P + Q).y).1
      = (add I.codomain.A ((I.mapXY P.x P.y).1, (I.mapXY P.x P.y).2)
          ((I.mapXY Q.x Q.y).1, (I.mapXY Q.x Q.y).2)).1
    have haddimg : (add I.codomain.A ((I.mapXY P.x P.y).1, (I.mapXY P.x P.y).2)
          ((I.mapXY Q.x Q.y).1, (I.mapXY Q.x Q.y).2)).1
        = (((I.mapXY Q.x Q.y).2 - (I.mapXY P.x P.y).2)
            / ((I.mapXY Q.x Q.y).1 - (I.mapXY P.x P.y).1))^2
          - (I.mapXY P.x P.y).1 - (I.mapXY Q.x Q.y).1 := by
      unfold add
      rw [if_neg himgP0, if_neg himgQ0, if_neg hXne]
    rw [haddimg]
    exact I.chord_x_compat h2 hd hP1 hQ1 h₃ hxx rfl hxagree (by rw [hyagree, hxagree])

/-- The isogeny commutes with negation on points. -/
theorem map_neg (P : SWPoint I.domain) : I.map (-P) = -I.map P := by
  by_cases hP : OnCurve I.domain.A I.domain.B (P.x, P.y)
  · have hnP : OnCurve I.domain.A I.domain.B ((-P).x, (-P).y) := by
      have h : P.y^2 = P.x^3 + I.domain.A * P.x + I.domain.B := hP
      show (-P.y)^2 = P.x^3 + I.domain.A * P.x + I.domain.B
      linear_combination h
    apply SWPoint.ext_pair
    rw [map, dif_pos hnP, map, dif_pos hP]
    show ((I.mapXY P.x (-P.y)).1, (I.mapXY P.x (-P.y)).2)
      = ((I.mapXY P.x P.y).1, -(I.mapXY P.x P.y).2)
    rw [Prod.mk.eta, I.mapXY_neg]
  · have hP0 : (P.x, P.y) = ((0 : F), (0 : F)) := P.onCurve.resolve_left hP
    rw [SWPoint.ext_pair (E := I.domain) (Q := 0) hP0, neg_zero, I.map_zero, neg_zero]

omit [DecidableEq F] in
/-- Two on-curve points with the same abscissa are equal or negatives. -/
private theorem eq_or_eq_neg_of_x_eq {E : SWCurve F} {R S : SWPoint E}
    (hR : OnCurve E.A E.B (R.x, R.y)) (hS : OnCurve E.A E.B (S.x, S.y))
    (hx : R.x = S.x) : R = S ∨ R = -S := by
  have h1 : R.y^2 = R.x^3 + E.A * R.x + E.B := hR
  have h2 : S.y^2 = S.x^3 + E.A * S.x + E.B := hS
  rw [hx] at h1
  have h0 : (R.y - S.y) * (R.y + S.y) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (SWPoint.ext_pair (Prod.ext_iff.mpr ⟨hx, sub_eq_zero.mp h⟩))
  · exact Or.inr (SWPoint.ext_pair (Prod.ext_iff.mpr
      ⟨by rw [SWPoint.neg_x]; exact hx, by rw [SWPoint.neg_y]; linear_combination h⟩))

/-- The image of a sum is the sum of the images, up to sign. -/
theorem map_add_pm (h2 : (2 : F) ≠ 0)
    (hd : ∀ X : F, ¬ OnCurve I.domain.A I.domain.B (X, 0))
    (hc : ∀ X : F, ¬ OnCurve I.codomain.A I.codomain.B (X, 0))
    (P Q : SWPoint I.domain) :
    I.map (P + Q) = I.map P + I.map Q ∨ I.map (P + Q) = -(I.map P + I.map Q) := by
  by_cases hs : OnCurve I.domain.A I.domain.B ((P + Q).x, (P + Q).y)
  · by_cases hi : OnCurve I.codomain.A I.codomain.B
        ((I.map P + I.map Q).x, (I.map P + I.map Q).y)
    · have hLon : OnCurve I.codomain.A I.codomain.B
          ((I.map (P + Q)).x, (I.map (P + Q)).y) := by
        rw [map, dif_pos hs]
        exact I.onCurve_mapXY hs
      exact eq_or_eq_neg_of_x_eq hLon hi (I.map_add_x h2 hd hc P Q)
    · exfalso
      have hi0 : ((I.map P + I.map Q).x, (I.map P + I.map Q).y) = ((0 : F), (0 : F)) :=
        (I.map P + I.map Q).onCurve.resolve_left hi
      have hsum0 : I.map P + I.map Q = 0 := SWPoint.ext_pair hi0
      have hQn : I.map Q = I.map (-P) := by
        rw [I.map_neg]
        exact (add_eq_zero_iff_neg_eq.mp hsum0).symm
      have hQP : Q = -P := I.map_injective h2 hc hQn
      have hPQ0 : P + Q = 0 := by rw [hQP]; exact add_neg_cancel P
      rw [hPQ0] at hs
      exact origin_not_on_curve I.domain hs
  · have hs0 : ((P + Q).x, (P + Q).y) = ((0 : F), (0 : F)) :=
      (P + Q).onCurve.resolve_left hs
    have hPQ : P + Q = 0 := SWPoint.ext_pair hs0
    have hQ : Q = -P := (add_eq_zero_iff_neg_eq.mp hPQ).symm
    left
    rw [hPQ, I.map_zero, hQ, I.map_neg]
    exact (add_neg_cancel _).symm

/-- The homomorphism property: the isogeny respects addition on rational points. -/
theorem map_add (h2 : (2 : F) ≠ 0)
    (hd : ∀ X : F, ¬ OnCurve I.domain.A I.domain.B (X, 0))
    (hc : ∀ X : F, ¬ OnCurve I.codomain.A I.codomain.B (X, 0))
    (P Q : SWPoint I.domain) :
    I.map (P + Q) = I.map P + I.map Q := by
  rcases I.map_add_pm h2 hd hc P Q with h | h
  · exact h
  · rcases I.map_add_pm h2 hd hc (P + Q) (-Q) with h' | h'
    · rw [add_neg_cancel_right, I.map_neg, h] at h'
      have hstep : I.map P + (I.map P + I.map Q + I.map Q) = 0 := by
        nth_rewrite 1 [h']
        abel
      have h20 : (I.map P + I.map Q) + (I.map P + I.map Q) = 0 := by
        calc (I.map P + I.map Q) + (I.map P + I.map Q)
            = I.map P + (I.map P + I.map Q + I.map Q) := by abel
          _ = 0 := hstep
      have hz := eq_zero_of_two_nsmul_eq_zero h2 hc (by rw [two_nsmul]; exact h20)
      rw [h, hz, neg_zero]
    · rw [add_neg_cancel_right, I.map_neg, h] at h'
      have hh : I.map P = I.map P + I.map Q + I.map Q := by
        calc I.map P = -(-(I.map P + I.map Q) + -I.map Q) := h'
          _ = I.map P + I.map Q + I.map Q := by abel
      have h2Q : I.map Q + I.map Q = 0 := by
        calc I.map Q + I.map Q = -I.map P + (I.map P + I.map Q + I.map Q) := by abel
          _ = -I.map P + I.map P := by rw [← hh]
          _ = 0 := by abel
      have hQ0 : I.map Q = 0 :=
        eq_zero_of_two_nsmul_eq_zero h2 hc (by rw [two_nsmul]; exact h2Q)
      have hQz : Q = 0 := I.map_injective h2 hc (by rw [hQ0, I.map_zero])
      rw [hQz, _root_.add_zero, I.map_zero, _root_.add_zero]

/-! ## The deployed hash-to-curve construction -/

/-- The deployed hash-to-curve construction after `hash_to_field`, which stays
abstract here — RFC 9380's `hash_to_curve` includes it, hence the distinct
name. The RFC intentionally does not provide this composition as a named
operation: it is cryptographically hazardous unless composed with
`hash_to_field`, and naming it could mislead people into thinking it can be
modelled as a random oracle by itself. Maps two field elements, intended to
be outputs of `hash_to_field`, to the isogeny's domain curve, adds there, and
applies the isogeny once (spec §5.4.9.8). -/
def mapHashOutputsToCurve (f : F → SWPoint I.domain) (u₀ u₁ : F) : SWPoint I.codomain :=
  I.map (f u₀ + f u₁)

/-- `mapHashOutputsToCurve` agrees with applying the isogeny to each point and
adding on the codomain. RFC 9380 §6.6.3 notes exactly this optimization —add on
the isogenous curve, so the isogeny map is evaluated once— "relying on iso_map
being a group homomorphism"; `map_add` is that fact for the deployed maps. The
spec and `hashtocurve.sage` use the one-evaluation order, while
`zcash-test-vectors` and `pasta_curves` map each point and add on the codomain. -/
theorem mapHashOutputsToCurve_eq (h2 : (2 : F) ≠ 0)
    (hd : ∀ X : F, ¬ OnCurve I.domain.A I.domain.B (X, 0))
    (hc : ∀ X : F, ¬ OnCurve I.codomain.A I.codomain.B (X, 0))
    (f : F → SWPoint I.domain) (u₀ u₁ : F) :
    I.mapHashOutputsToCurve f u₀ u₁ = I.map (f u₀) + I.map (f u₁) :=
  I.map_add h2 hd hc (f u₀) (f u₁)

end CompElliptic.Isogenies.ThreeIsogeny
