/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Isogenies.ThreeIsogeny
import CompElliptic.Isogenies.VeluCertificates

/-!
# The homomorphism property of the 3-isogeny

This module proves that `ThreeIsogeny.map` respects addition, in layers. The
coordinate-level theorems `chord_x_compat` and `tangent_x_compat` say that the
image of a sum's third point has exactly the abscissa the codomain group law
computes from the two image points, for the chord and doubling cases. They
consume the generated certificates and support lemmas of
`Isogenies/VeluCertificates.lean`, and their parameters are pinned by defining
equations so that the point-level layer can instantiate them against the
branches of `add`.
-/

open CompElliptic.CurveForms.ShortWeierstrass

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
    (hx₃ : x₃ = lam ^ 2 - x₁ - x₂)
    (hy₃ : y₃ = lam * (x₁ - x₃) - y₁) :
    (I.mapXY x₃ y₃).1 =
      (((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2)
          / ((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1)) ^ 2
        - (I.mapXY x₁ y₁).1 - (I.mapXY x₂ y₂).1 := by
  have hdd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hxx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hd₁ : x₁ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₁)
  have hd₂ : x₂ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₂)
  have hd₃ : x₃ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₃)
  have hc₁ : y₁ ^ 2 = x₁ ^ 3 + I.domain.A * x₁ + I.domain.B := h₁
  have hc₂ : y₂ ^ 2 = x₂ ^ 3 + I.domain.A * x₂ + I.domain.B := h₂
  have hslope : y₂ - y₁ = lam * (x₂ - x₁) := by
    rw [hlam, div_mul_cancel₀ _ hxx]
  set m' : F := y₁ - lam * (x₁ - I.x₀) with hm'
  have hL1 : y₁ = lam * (x₁ - I.x₀) + m' := by linear_combination -hm'
  have hL2 : y₂ = lam * (x₂ - I.x₀) + m' := by linear_combination hslope - hm'
  have hbridge := chord_psi3_bridge ((x₁ - I.x₀) + (x₂ - I.x₀)) (x₁ - x₂) lam m' I.x₀
    I.domain.A I.domain.B
    (by linear_combination 8 * hc₁ - 8 * (y₁ + lam * (x₁ - I.x₀) + m') * hL1)
    (by linear_combination 8 * hc₂ - 8 * (y₂ + lam * (x₂ - I.x₀) + m') * hL2)
    I.psi3
  have hp_inst := (mul_eq_zero.mp hbridge).resolve_left
    (mul_ne_zero hdd (pow_ne_zero 1 h2))
  have h2p4 : ((2 : F)^4) ≠ 0 := pow_ne_zero _ h2
  have h2p6 : ((2 : F)^6) ≠ 0 := pow_ne_zero _ h2
  have hsem_ns := chord_ns_semantics ((x₁ - I.x₀) + (x₂ - I.x₀)) (x₁ - x₂) lam m' I.x₀
    I.domain.A I.domain.B
    (by linear_combination 8 * hc₁ - 8 * (y₁ + lam * (x₁ - I.x₀) + m') * hL1)
    (by linear_combination 8 * hc₂ - 8 * (y₂ + lam * (x₂ - I.x₀) + m') * hL2)
  have hsem_ws := chord_ws_semantics ((x₁ - I.x₀) + (x₂ - I.x₀)) (x₁ - x₂) lam m' I.x₀
    I.domain.A I.domain.B
    (by linear_combination 8 * hc₁ - 8 * (y₁ + lam * (x₁ - I.x₀) + m') * hL1)
    (by linear_combination 8 * hc₂ - 8 * (y₂ + lam * (x₂ - I.x₀) + m') * hL2)
  obtain ⟨nsv, hnsv⟩ : ∃ n : F,
      n = (I.xnum x₂ * (x₁ - I.x₀) ^ 2 - I.xnum x₁ * (x₂ - I.x₀) ^ 2) / (x₁ - x₂) := ⟨_, rfl⟩
  obtain ⟨wsv, hwsv⟩ : ∃ w : F,
      w = ((lam * (x₂ - I.x₀) + m') * I.ynum x₂ * (x₁ - I.x₀) ^ 3
        - (lam * (x₁ - I.x₀) + m') * I.ynum x₁ * (x₂ - I.x₀) ^ 3) / (x₁ - x₂) := ⟨_, rfl⟩
  have hNNv : (x₁ - x₂) * nsv
      = I.xnum x₂ * (x₁ - I.x₀) ^ 2 - I.xnum x₁ * (x₂ - I.x₀) ^ 2 := by
    rw [hnsv]; field_simp
  have hWv : (x₁ - x₂) * wsv
      = (lam * (x₂ - I.x₀) + m') * I.ynum x₂ * (x₁ - I.x₀) ^ 3
        - (lam * (x₁ - I.x₀) + m') * I.ynum x₁ * (x₂ - I.x₀) ^ 3 := by
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
    (by linear_combination 8 * hc₁ - 8 * (y₁ + lam * (x₁ - I.x₀) + m') * hL1)
    (by linear_combination 8 * hc₂ - 8 * (y₂ + lam * (x₂ - I.x₀) + m') * hL2)
    I.psi3
  -- defining equations of the image values, cleared of their denominators
  have hX₁ : (I.mapXY x₁ y₁).1 * (x₁ - I.x₀) ^ 2 = I.s ^ 2 * I.xnum x₁ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₁)
  have hX₂ : (I.mapXY x₂ y₂).1 * (x₂ - I.x₀) ^ 2 = I.s ^ 2 * I.xnum x₂ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₂)
  have hX₃ : (I.mapXY x₃ y₃).1 * (x₃ - I.x₀) ^ 2 = I.s ^ 2 * I.xnum x₃ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₃)
  have hY₁ : (I.mapXY x₁ y₁).2 * (x₁ - I.x₀) ^ 3
      = I.s ^ 3 * ((lam * (x₁ - I.x₀) + m') * I.ynum x₁) := by
    simp only [mapXY]
    rw [← hL1]
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hd₁)
  have hY₂ : (I.mapXY x₂ y₂).2 * (x₂ - I.x₀) ^ 3
      = I.s ^ 3 * ((lam * (x₂ - I.x₀) + m') * I.ynum x₂) := by
    simp only [mapXY]
    rw [← hL2]
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hd₂)
  -- the difference and sum equations, in terms of the atoms
  have hΔX : ((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1) * ((x₁ - I.x₀) ^ 2 * (x₂ - I.x₀) ^ 2)
      = I.s ^ 2 * ((x₁ - x₂) * nsv) := by
    linear_combination (x₁ - I.x₀) ^ 2 * hX₂ - (x₂ - I.x₀) ^ 2 * hX₁ - I.s ^ 2 * hNNv
  have hΔY : ((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2) * ((x₁ - I.x₀) ^ 3 * (x₂ - I.x₀) ^ 3)
      = I.s ^ 3 * ((x₁ - x₂) * wsv) := by
    linear_combination (x₁ - I.x₀) ^ 3 * hY₂ - (x₂ - I.x₀) ^ 3 * hY₁ - I.s ^ 3 * hWv
  have hsumX : ((I.mapXY x₃ y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₂ y₂).1)
        * ((x₁ - I.x₀) ^ 2 * (x₂ - I.x₀) ^ 2 * (x₃ - I.x₀) ^ 2)
      = I.s ^ 2 * (I.xnum x₃ * (x₁ - I.x₀) ^ 2 * (x₂ - I.x₀) ^ 2
          + I.xnum x₁ * (x₂ - I.x₀) ^ 2 * (x₃ - I.x₀) ^ 2
          + I.xnum x₂ * (x₁ - I.x₀) ^ 2 * (x₃ - I.x₀) ^ 2) := by
    linear_combination (x₁ - I.x₀) ^ 2 * (x₂ - I.x₀) ^ 2 * hX₃
      + (x₂ - I.x₀) ^ 2 * (x₃ - I.x₀) ^ 2 * hX₁ + (x₁ - I.x₀) ^ 2 * (x₃ - I.x₀) ^ 2 * hX₂
  -- the image abscissas are distinct
  have hXne : (I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1 ≠ 0 := by
    intro h0
    exact hne (I.abscissa_inj h2 hd h₁ h₂ (sub_eq_zero.mp h0).symm)
  subst hx₃
  -- the cleared, slope-free key equation, closed by the certificate and correction
  have hkeyc : (2 : F) ^ 10
        * ((((I.mapXY (lam ^ 2 - x₁ - x₂) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₂ y₂).1)
            * ((x₁ - I.x₀) ^ 2 * (x₂ - I.x₀) ^ 2 * (lam ^ 2 - x₁ - x₂ - I.x₀) ^ 2))
          * (((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1) * ((x₁ - I.x₀) ^ 2 * (x₂ - I.x₀) ^ 2)) ^ 2)
      = (2 : F) ^ 10
        * ((((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2) * ((x₁ - I.x₀) ^ 3 * (x₂ - I.x₀) ^ 3)) ^ 2
          * (lam ^ 2 - x₁ - x₂ - I.x₀) ^ 2) := by
    have hN₁ : I.xnum x₁ = x₁ * (x₁ - I.x₀) ^ 2
        + 2 * (3 * I.x₀ ^ 2 + I.domain.A) * (x₁ - I.x₀)
        + 4 * (I.x₀ ^ 3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    have hN₂ : I.xnum x₂ = x₂ * (x₂ - I.x₀) ^ 2
        + 2 * (3 * I.x₀ ^ 2 + I.domain.A) * (x₂ - I.x₀)
        + 4 * (I.x₀ ^ 3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    have hN₃ : I.xnum (lam ^ 2 - x₁ - x₂) = (lam ^ 2 - x₁ - x₂) * (lam ^ 2 - x₁ - x₂ - I.x₀) ^ 2
        + 2 * (3 * I.x₀ ^ 2 + I.domain.A) * (lam ^ 2 - x₁ - x₂ - I.x₀)
        + 4 * (I.x₀ ^ 3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    rw [hsumX, hΔX, hΔY, hN₁, hN₂, hN₃]
    linear_combination I.s ^ 6 * hcert + I.s ^ 6 * (x₁ - x₂) * nsv ^ 2 * hcorr
  have hkey : ((I.mapXY (lam ^ 2 - x₁ - x₂) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₂ y₂).1)
        * ((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1) ^ 2
      = ((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2) ^ 2 :=
    mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 hd₁) (pow_ne_zero 6 hd₂))
      (pow_ne_zero 2 hd₃))
      (mul_left_cancel₀ (pow_ne_zero 10 h2) (by linear_combination hkeyc))
  have hdiv : (((I.mapXY x₂ y₂).2 - (I.mapXY x₁ y₁).2)
        / ((I.mapXY x₂ y₂).1 - (I.mapXY x₁ y₁).1)) ^ 2
      = (I.mapXY (lam ^ 2 - x₁ - x₂) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₂ y₂).1 := by
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
    (hlam : lam = (3 * x₁ ^ 2 + I.domain.A) / (2 * y₁))
    (hx₃ : x₃ = lam ^ 2 - x₁ - x₁)
    (hy₃ : y₃ = lam * (x₁ - x₃) - y₁) :
    (I.mapXY x₃ y₃).1 =
      ((3 * (I.mapXY x₁ y₁).1 ^ 2 + I.codomain.A) / (2 * (I.mapXY x₁ y₁).2)) ^ 2
        - (I.mapXY x₁ y₁).1 - (I.mapXY x₁ y₁).1 := by
  have hd₁ : x₁ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₁)
  have hd₃ : x₃ - I.x₀ ≠ 0 := sub_ne_zero.mpr (I.ne_x₀ h₃)
  have hc₁ : y₁ ^ 2 = x₁ ^ 3 + I.domain.A * x₁ + I.domain.B := h₁
  have h2y : (2 : F) * y₁ ≠ 0 := mul_ne_zero h2 hy₁
  have hslope : lam * (2 * y₁) = 3 * x₁ ^ 2 + I.domain.A := by
    rw [hlam, div_mul_cancel₀ _ h2y]
  set v' : F := y₁ - lam * (x₁ - I.x₀) with hv'
  have hL : y₁ = lam * (x₁ - I.x₀) + v' := by linear_combination -hv'
  have hbridgeT := tangent_psi3_bridge (x₁ - I.x₀) lam v' I.x₀ I.domain.A I.domain.B
    (by linear_combination hc₁ - (y₁ + lam * (x₁ - I.x₀) + v') * hL)
    (by linear_combination hslope - 2 * lam * hL)
    I.psi3
  have hsem_k := tangent_k_semantics (x₁ - I.x₀) lam v' I.x₀ I.domain.A I.domain.B
    (by linear_combination hc₁ - (y₁ + lam * (x₁ - I.x₀) + v') * hL)
    (by linear_combination hslope - 2 * lam * hL)
  have hsem_t := tangent_t_semantics (x₁ - I.x₀) lam v' I.x₀ I.domain.A I.domain.B
    (by linear_combination hc₁ - (y₁ + lam * (x₁ - I.x₀) + v') * hL)
    (by linear_combination hslope - 2 * lam * hL)
  have hcorrT := tangent_correction (x₁ - I.x₀) lam v' I.x₀ I.domain.A I.domain.B
    (by linear_combination hc₁ - (y₁ + lam * (x₁ - I.x₀) + v') * hL)
    (by linear_combination hslope - 2 * lam * hL)
  obtain ⟨kv, hkv⟩ : ∃ k : F,
      k = 2 * (lam * (x₁ - I.x₀) + v') * I.ynum x₁ * (x₁ - I.x₀) := ⟨_, rfl⟩
  obtain ⟨tv, htv⟩ : ∃ t : F,
      t = 3 * I.xnum x₁ ^ 2
        + (I.domain.A - 10 * (3 * I.x₀ ^ 2 + I.domain.A)) * (x₁ - I.x₀) ^ 4 := ⟨_, rfl⟩
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
  have hX₁ : (I.mapXY x₁ y₁).1 * (x₁ - I.x₀) ^ 2 = I.s ^ 2 * I.xnum x₁ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₁)
  have hX₃ : (I.mapXY x₃ y₃).1 * (x₃ - I.x₀) ^ 2 = I.s ^ 2 * I.xnum x₃ := by
    simp only [mapXY]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd₃)
  have hY₁ : (I.mapXY x₁ y₁).2 * (x₁ - I.x₀) ^ 3
      = I.s ^ 3 * ((lam * (x₁ - I.x₀) + v') * I.ynum x₁) := by
    simp only [mapXY]
    rw [← hL]
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hd₁)
  have hY₁ne : (I.mapXY x₁ y₁).2 ≠ 0 := by
    intro h0
    have himg := I.onCurve_mapXY h₁
    exact hc (I.mapXY x₁ y₁).1 (by rw [← h0, Prod.mk.eta]; exact himg)
  have h2Y : ((2 : F) * (I.mapXY x₁ y₁).2) * (x₁ - I.x₀) ^ 4 = I.s ^ 3 * kv := by
    linear_combination 2 * (x₁ - I.x₀) * hY₁ - I.s ^ 3 * hkv
  have h3X : (3 * (I.mapXY x₁ y₁).1 ^ 2 + I.codomain.A) * (x₁ - I.x₀) ^ 4
      = I.s ^ 4 * tv := by
    linear_combination
      3 * ((I.mapXY x₁ y₁).1 * (x₁ - I.x₀) ^ 2 + I.s ^ 2 * I.xnum x₁) * hX₁
        + (x₁ - I.x₀) ^ 4 * I.codomain_A - I.s ^ 4 * htv
  have hsumXT : ((I.mapXY x₃ y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₁ y₁).1)
        * ((x₁ - I.x₀) ^ 2 * (x₃ - I.x₀) ^ 2)
      = I.s ^ 2 * (I.xnum x₃ * (x₁ - I.x₀) ^ 2 + 2 * I.xnum x₁ * (x₃ - I.x₀) ^ 2) := by
    linear_combination (x₁ - I.x₀) ^ 2 * hX₃ + 2 * (x₃ - I.x₀) ^ 2 * hX₁
  subst hx₃
  have hkeycT : (2 : F) ^ 2
        * ((((I.mapXY (lam ^ 2 - x₁ - x₁) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₁ y₁).1)
            * ((x₁ - I.x₀) ^ 2 * (lam ^ 2 - x₁ - x₁ - I.x₀) ^ 2))
          * (((2 : F) * (I.mapXY x₁ y₁).2) * (x₁ - I.x₀) ^ 4) ^ 2)
      = (2 : F) ^ 2
        * (((3 * (I.mapXY x₁ y₁).1 ^ 2 + I.codomain.A) * (x₁ - I.x₀) ^ 4) ^ 2
          * ((x₁ - I.x₀) ^ 2 * (lam ^ 2 - x₁ - x₁ - I.x₀) ^ 2)) := by
    have hN₁ : I.xnum x₁ = x₁ * (x₁ - I.x₀) ^ 2
        + 2 * (3 * I.x₀ ^ 2 + I.domain.A) * (x₁ - I.x₀)
        + 4 * (I.x₀ ^ 3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    have hN₃ : I.xnum (lam ^ 2 - x₁ - x₁) = (lam ^ 2 - x₁ - x₁) * (lam ^ 2 - x₁ - x₁ - I.x₀) ^ 2
        + 2 * (3 * I.x₀ ^ 2 + I.domain.A) * (lam ^ 2 - x₁ - x₁ - I.x₀)
        + 4 * (I.x₀ ^ 3 + I.domain.A * I.x₀ + I.domain.B) := rfl
    rw [hsumXT, h2Y, h3X, hN₁, hN₃]
    linear_combination I.s ^ 8 * hcertT + I.s ^ 8 * kv ^ 2 * hcorrT
  have hkeyT : ((I.mapXY (lam ^ 2 - x₁ - x₁) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₁ y₁).1)
        * ((2 : F) * (I.mapXY x₁ y₁).2) ^ 2
      = (3 * (I.mapXY x₁ y₁).1 ^ 2 + I.codomain.A) ^ 2 :=
    mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 10 hd₁) (pow_ne_zero 2 hd₃))
      (mul_left_cancel₀ (pow_ne_zero 2 h2) (by linear_combination hkeycT))
  have hdivT : ((3 * (I.mapXY x₁ y₁).1 ^ 2 + I.codomain.A)
        / (2 * (I.mapXY x₁ y₁).2)) ^ 2
      = (I.mapXY (lam ^ 2 - x₁ - x₁) y₃).1 + (I.mapXY x₁ y₁).1 + (I.mapXY x₁ y₁).1 := by
    rw [div_pow, ← hkeyT]
    have h2Yne : ((2 : F) * (I.mapXY x₁ y₁).2) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (mul_ne_zero h2 hY₁ne)
    exact mul_div_cancel_right₀ _ h2Yne
  linear_combination -hdivT

end CompElliptic.Isogenies.ThreeIsogeny
