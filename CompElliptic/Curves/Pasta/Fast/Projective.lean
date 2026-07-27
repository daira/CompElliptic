/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta

/-!
# Projective (Renes–Costello–Batina) point arithmetic for Vesta

The affine group law pays a field inversion per addition.  This module replaces it, for the hot
`n • point` loop, by the complete projective addition formulas of Renes, Costello and Batina
(EUROCRYPT 2016; the EFD `add-2015-rcb` sequence at `a = 0`): single branchless formulas in
`(X : Y : Z)` valid for *all* input pairs, with the inversion paid once in `toAffine`.  Their
completeness needs the curve to have no 2-torsion, which Vesta's odd prime order gives
(`Vesta.no_onCurve_y_zero`); that is what discharges `Z₃ ≠ 0` outside the genuine identity cases.

Specialized to `a = 0`, `b = 5`, `b3 = 15`, the closed forms are

* `X₃ = X₁Y₁Y₂² − 15X₁Y₁Z₂² − 30X₁Z₁Y₂Z₂ + Y₁²X₂Y₂ − 15Z₁²X₂Y₂ − 30Y₁Z₁X₂Z₂`
* `Y₃ = Y₁²Y₂² + 45X₁²X₂Z₂ + 45X₁Z₁X₂² − 225Z₁²Z₂²`
* `Z₃ = Y₁²Y₂Z₂ + Y₁Z₁Y₂² + 3X₁²X₂Y₂ + 3X₁Y₁X₂² + 15Y₁Z₁Z₂² + 15Z₁²Y₂Z₂`
-/

open CompElliptic
open CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta

namespace CompElliptic.Curves.Pasta.Fast.Projective

/-- The Vesta base field `𝔽_q` (= `PallasScalarField`), over which the Vesta curve is defined. -/
abbrev Fq := CompElliptic.Fields.Pasta.VestaBaseField

/-- The downstream affine group: on-curve points of Vesta with the complete affine group law. -/
abbrev G := SWPoint Vesta.curve

/-- A projective point in `(X : Y : Z)` coordinates over `𝔽_q`. -/
structure PVes where
  X : Fq
  Y : Fq
  Z : Fq
deriving DecidableEq

namespace PVes

/-- Renes–Costello–Batina complete addition (`add-2015-rcb`, `a = 0`, `b3 = 15`). -/
def padd (P Q : PVes) : PVes where
  X := P.X*P.Y*Q.Y^2 - 15*P.X*P.Y*Q.Z^2 - 30*P.X*P.Z*Q.Y*Q.Z
       + P.Y^2*Q.X*Q.Y - 15*P.Z^2*Q.X*Q.Y - 30*P.Y*P.Z*Q.X*Q.Z
  Y := P.Y^2*Q.Y^2 + 45*P.X^2*Q.X*Q.Z + 45*P.X*P.Z*Q.X^2 - 225*P.Z^2*Q.Z^2
  Z := P.Y^2*Q.Y*Q.Z + P.Y*P.Z*Q.Y^2 + 3*P.X^2*Q.X*Q.Y + 3*P.X*P.Y*Q.X^2
       + 15*P.Y*P.Z*Q.Z^2 + 15*P.Z^2*Q.Y*Q.Z

/-- Scalar (representative) rescaling `(X : Y : Z) ↦ (uX : uY : uZ)`. -/
def smul (u : Fq) (P : PVes) : PVes := ⟨u*P.X, u*P.Y, u*P.Z⟩

/-- The projective identity `𝒪 = (0 : 1 : 0)`. -/
def pid : PVes := ⟨0, 1, 0⟩

/-- The homogeneous projective curve equation `Y²Z = X³ + 5Z³` (Vesta, `a = 0`, `b = 5`). -/
def OnCurveP (P : PVes) : Prop := P.Y^2*P.Z = P.X^3 + 5*P.Z^3

/-- `OnCurveP` unfolds definitionally to a field equation, hence is decidable. This is what keeps
`toAffine` — and everything downstream of it, `smulFast` in particular — computable. -/
instance (P : PVes) : Decidable (OnCurveP P) :=
  inferInstanceAs (Decidable (P.Y^2*P.Z = P.X^3 + 5*P.Z^3))

/-- A representable projective point: on the projective curve and not the zero vector. -/
def Valid (P : PVes) : Prop := OnCurveP P ∧ (P.X ≠ 0 ∨ P.Y ≠ 0 ∨ P.Z ≠ 0)

/-- Affine interpretation as a raw coordinate pair: `Z ≠ 0 ↦ (X/Z, Y/Z)`, `Z = 0 ↦ 𝒪 = (0,0)`. -/
def aff (P : PVes) : Fq × Fq := if P.Z = 0 then (0, 0) else (P.X / P.Z, P.Y / P.Z)

/-! ## `ring`/`linear_combination` certificates

Each identity below is a polynomial identity over `𝔽_q`, valid modulo the two curve equations
`e1 : y1² = x1³ + 5` and `e2 : y2² = x2³ + 5`. The cofactors were computed by an exact-rational
Gröbner/linear-algebra search over `ℚ[x1,y1,x2,y2]` (offline) and are checked here by `ring`
inside `linear_combination`. The `padd`-of-`Z=1`-points evaluation is spelled by `simp only [padd]`
which reduces the coordinate projections. -/

variable {x1 y1 x2 y2 : Fq}

/-- Reading off the coordinates of `padd` on `Z = 1` representatives. -/
@[simp] theorem padd_z1_X (x1 y1 x2 y2 : Fq) :
    (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).X
      = y1^2*x2*y2 + x1*y1*y2^2 - 15*x2*y2 - 30*y1*x2 - 30*x1*y2 - 15*x1*y1 := by
  simp only [padd]; ring

@[simp] theorem padd_z1_Y (x1 y1 x2 y2 : Fq) :
    (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).Y
      = y1^2*y2^2 + 45*x1*x2^2 + 45*x1^2*x2 - 225 := by
  simp only [padd]; ring

@[simp] theorem padd_z1_Z (x1 y1 x2 y2 : Fq) :
    (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).Z
      = 3*x1*y1*x2^2 + 3*x1^2*x2*y2 + y1*y2^2 + y1^2*y2 + 15*y2 + 15*y1 := by
  simp only [padd]; ring

/-- `X₃·(x₂−x₁)² = x3num·Z₃`, the numerator match for the affine `x`-coordinate (distinct `x`). -/
theorem keyx_dist (e1 : y1^2 = x1^3 + 5) (e2 : y2^2 = x2^3 + 5) :
    (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).X * (x2 - x1)^2
      = ((y2 - y1)^2 - (x1 + x2)*(x2 - x1)^2) * (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).Z := by
  simp only [padd_z1_X, padd_z1_Z]
  linear_combination
    ((2)*x2^3*y2 + (3)*x1*x2^2*y2 + (-3)*x1*y1*x2^2 + (-3)*x1^2*x2*y2 + y2^3 + y1*y2^2 - y1^2*y2 + (10)*y2 + (-15)*y1) * e1
    + ((-3)*x1*y1*x2^2 + (-3)*x1^2*x2*y2 + (3)*x1^2*y1*x2 + x1^3*y2 + (3)*x1^3*y1 - y1*y2^2 + (-10)*y2 + (15)*y1) * e2

/-- `Y₃·(x₂−x₁)³ = y3num·Z₃`, the numerator match for the affine `y`-coordinate (distinct `x`). -/
theorem keyy_dist (e1 : y1^2 = x1^3 + 5) (e2 : y2^2 = x2^3 + 5) :
    (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).Y * (x2 - x1)^3
      = ((y2 - y1)*(x1*(x2 - x1)^2 - ((y2 - y1)^2 - (x1 + x2)*(x2 - x1)^2)) - y1*(x2 - x1)^3)
          * (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).Z := by
  simp only [padd_z1_Y, padd_z1_Z]
  linear_combination
    ((6)*x1*x2^5 + (-9)*x1^2*x2^4 + (2)*x2^3*y2^2 + (2)*y1*x2^3*y2 + (-15)*x1*x2^2*y2^2 + (6)*x1*y1*x2^2*y2 + (-3)*x1*y1^2*x2^2 + (15)*x1^2*x2*y2^2 + (-3)*x1^2*y1*x2*y2 + (-2)*y2^4 + (2)*y1^2*y2^2 - y1^3*y2 + (30)*x2^3 + (-60)*x1*x2^2 + (10)*y2^2 + (25)*y1*y2 + (-15)*y1^2 + (-75)) * e1
    + ((-6)*x1^4*x2^2 + (9)*x1^5*x2 + (3)*x1*y1*x2^2*y2 + (3)*x1^2*x2*y2^2 + (-6)*x1^2*y1*x2*y2 + (-2)*x1^3*y2^2 + (-2)*x1^3*y1*y2 + y1*y2^3 + (-75)*x1*x2^2 + (135)*x1^2*x2 + (-30)*x1^3 + (5)*y2^2 + (-25)*y1*y2 + (75)) * e2

/-- Curve preservation on `Z = 1` representatives: `padd` lands on the projective curve. -/
theorem oncurveP_padd_z1 (e1 : y1^2 = x1^3 + 5) (e2 : y2^2 = x2^3 + 5) :
    OnCurveP (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩) := by
  simp only [OnCurveP, padd_z1_X, padd_z1_Y, padd_z1_Z]
  linear_combination
    (-x1^6*x2^3*y2^3 - x1^3*y1^2*x2^3*y2^3 + x1^6*y2^5 - y1^4*x2^3*y2^3 + (-135)*x1^3*y1*x2^6 + x1^3*y1^2*y2^5 + (-405)*x1^4*x2^5*y2 + (-135)*x1^5*x2^4*y2 + y1^3*y2^6 + y1^4*y2^5 + (135)*x1^2*y1*x2^4*y2^2 + (-135)*x1^2*y1^2*x2^4*y2 + (35)*x1^3*x2^3*y2^3 + (90)*x1^3*y1*x2^3*y2^2 + (405)*x1^4*x2^2*y2^3 + (135)*x1^5*x2*y2^3 + (-5)*x1^6*y2^3 + (40)*y1^2*x2^3*y2^3 + (90)*y1^3*x2^3*y2^2 + (135)*x1*y1*x2^2*y2^4 + (270)*x1*y1^2*x2^2*y2^3 + (270)*x1^2*y1*x2*y2^4 + (135)*x1^2*y1^2*x2*y2^3 + (100)*x1^3*y2^5 + (45)*x1^3*y1*y2^4 + (-5)*x1^3*y1^2*y2^3 + (5)*y1^2*y2^5 + (-5)*y1^4*y2^3 + (-675)*x1^2*x2^4*y2 + (-2025)*x1^2*y1*x2^4 + (-2700)*x1^3*x2^3*y2 + (-2025)*x1^4*x2^2*y2 + (-675)*x1^5*x2*y2 + (-475)*x2^3*y2^3 + (-2250)*y1*x2^3*y2^2 + (-2700)*y1^2*x2^3*y2 + (-4050)*x1*x2^2*y2^3 + (-12150)*x1*y1*x2^2*y2^2 + (-4050)*x1*y1^2*x2^2*y2 + (-11475)*x1^2*x2*y2^3 + (-5400)*x1^2*y1*x2*y2^2 + (-675)*x1^2*y1^2*x2*y2 + (-3875)*x1^3*y2^3 + (-900)*x1^3*y1*y2^2 + (-200)*y2^5 + (-1125)*y1*y2^4 + (-1150)*y1^2*y2^3 + (-225)*y1^3*y2^2 + (27000)*x2^3*y2 + (27000)*y1*x2^3 + (60750)*x1*x2^2*y2 + (30375)*x1*y1*x2^2 + (57375)*x1^2*x2*y2 + (20250)*x1^2*y1*x2 + (16875)*x1^3*y2 + (3375)*x1^3*y1 + (-22625)*y2^3 + (-18000)*y1*y2^2 + (-3375)*y1^2*y2 + (-16875)*y2 + (-16875)*y1) * e1
    + (x1^9*y2^3 + (135)*x1^6*y1*x2^3 + (405)*x1^7*x2^2*y2 + (135)*x1^8*x2*y2 + (270)*x1^5*y1*x2*y2^2 + (105)*x1^6*y2^3 + (45)*x1^6*y1*y2^2 + (-5400)*x1^3*y1*x2^3 + (-4050)*x1^4*x2^2*y2 + (-12150)*x1^4*y1*x2^2 + (-10800)*x1^5*x2*y2 + (-4050)*x1^5*y1*x2 + (-3375)*x1^6*y2 + (-675)*x1^6*y1 + (-2700)*x1^2*y1*x2*y2^2 + (300)*x1^3*y2^3 + (-3600)*x1^3*y1*y2^2 + (-27000)*x1^2*x2*y2 + (40500)*x1^2*y1*x2 + (-13500)*x1^3*y2 + (-1000)*y2^3 + (-9000)*y1*y2^2 + (-135000)*y2 + (-135000)*y1) * e2

/-- **Distinct-`x` completeness (2-torsion-free).** If `Z₃ = 0` for two on-curve `Z = 1` points
with distinct `x`, then `w = wnum/wden` (the `x`-coordinate of `P − Q`) is a cube root of `−5`,
i.e. `(w, 0)` is a 2-torsion point — impossible on Vesta. Hence `Z₃ ≠ 0`. -/
theorem Z_ne_zero_dist (e1 : y1^2 = x1^3 + 5) (e2 : y2^2 = x2^3 + 5) (hne : x1 ≠ x2) :
    (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).Z ≠ 0 := by
  intro hZ
  have hd : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  set wnum : Fq := (y1 + y2)^2 - (x1 + x2)*(x2 - x1)^2 with hwnumE
  set wden : Fq := (x2 - x1)^2 with hwdenE
  have hwdenne : wden ≠ 0 := by rw [hwdenE]; exact pow_ne_zero 2 hd
  have hZpoly : (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).Z
      = 3*x1*y1*x2^2 + 3*x1^2*x2*y2 + y1*y2^2 + y1^2*y2 + 15*y2 + 15*y1 := padd_z1_Z x1 y1 x2 y2
  rw [hZpoly] at hZ
  -- wnum^3 = -5 * wden^3 on the exceptional locus
  have hcube : wnum^3 = -5 * wden^3 := by
    rw [hwnumE, hwdenE]
    linear_combination
      (-x2^3*y2 + (-2)*y1*x2^3 + (3)*x1*y1*x2^2 + (3)*x1^2*x2*y2 + (-2)*x1^3*y2 + (-4)*x1^3*y1 + y2^3 + (3)*y1*y2^2 + (3)*y1^2*y2 + (4)*y1^3 + (-15)*y1) * hZ
      + ((8)*x2^6 + (-6)*x1*x2^5 + (-6)*x1^2*x2^4 + (8)*x1^3*x2^3 + (-3)*x1^5*x2 + x1^6 + (-12)*x2^3*y2^2 + (-6)*y1*x2^3*y2 + (-4)*y1^2*x2^3 + (12)*x1*x2^2*y2^2 + (-9)*x1*y1^2*x2^2 + (3)*x1^2*y1^2*x2 + (-3)*x1^3*y2^2 + (-6)*x1^3*y1*y2 + (-2)*x1^3*y1^2 + (3)*y2^4 + (10)*y1*y2^3 + (9)*y1^2*y2^2 + (2)*y1^3*y2 + y1^4 + (60)*x2^3 + (-75)*x1*x2^2 + (45)*x1^2*x2 + (-10)*x1^3 + (-15)*y2^2 + (-60)*y1*y2 + (-60)*y1^2 + (50)) * e1
      + (x2^6 + (-3)*x1*x2^5 + (-2)*x2^3*y2^2 + (-6)*y1*x2^3*y2 + (5)*y1^2*x2^3 + (3)*x1*x2^2*y2^2 + (9)*x1*y1*x2^2*y2 + (-6)*x1*y1^2*x2^2 + (6)*x1^2*y1^2*x2 + y2^4 + (5)*y1*y2^3 + (8)*y1^2*y2^2 + (4)*y1^3*y2 - y1^4 + (-50)*x2^3 + (75)*x1*x2^2 + (-45)*x1^2*x2 + (5)*y2^2 + (15)*y1*y2 + (25)*y1^2 + (-50)) * e2
  -- so (wnum/wden) is a cube root of -5, contradicting no 2-torsion
  have hw : (wnum / wden)^3 = -5 := by
    rw [div_pow, hcube, mul_div_assoc, div_self (pow_ne_zero 3 hwdenne), mul_one]
  exact Vesta.no_onCurve_y_zero (wnum / wden) (by
    show (0 : Fq)^2 = (wnum / wden)^3 + Vesta.a * (wnum / wden) + Vesta.b
    rw [hw]; simp [Vesta.a, Vesta.b])

/-- **Doubling `Z`-coordinate.** On `Z = 1` representatives with equal points, `Z₃ = 8y³`. -/
theorem Z_doubling (e1 : y1^2 = x1^3 + 5) :
    (padd ⟨x1, y1, 1⟩ ⟨x1, y1, 1⟩).Z = 8 * y1^3 := by
  simp only [padd_z1_Z]
  linear_combination ((-6)*y1) * e1

/-- `X₃·4y² = x3numd·Z₃`, doubling `x`-coordinate numerator match. -/
theorem keyx_dbl (e1 : y1^2 = x1^3 + 5) :
    (padd ⟨x1, y1, 1⟩ ⟨x1, y1, 1⟩).X * (4*y1^2)
      = (9*x1^4 - 8*x1*y1^2) * (padd ⟨x1, y1, 1⟩ ⟨x1, y1, 1⟩).Z := by
  simp only [padd_z1_X, padd_z1_Z]
  linear_combination ((54)*x1^4*y1 + (24)*x1*y1^3) * e1

/-- `Y₃·8y³ = y3numd·Z₃`, doubling `y`-coordinate numerator match. -/
theorem keyy_dbl (e1 : y1^2 = x1^3 + 5) :
    (padd ⟨x1, y1, 1⟩ ⟨x1, y1, 1⟩).Y * (8*y1^3)
      = (3*x1^2*(12*x1*y1^2 - 9*x1^4) - 8*y1^4) * (padd ⟨x1, y1, 1⟩ ⟨x1, y1, 1⟩).Z := by
  simp only [padd_z1_Y, padd_z1_Z]
  linear_combination ((-162)*x1^6*y1 + (24)*y1^5 + (360)*y1^3) * e1

/-- **Inverse-case identity representative is nonzero (2-torsion-free).** `padd P (−P) = (0 : Y₃ : 0)`
with `Y₃ ≠ 0`: if `Y₃ = 0` then `w = wnum2/wden2` (the `x`-coordinate of `2P`) is a cube root of
`−5`, impossible on Vesta. -/
theorem Y_ne_zero_inv (e1 : y1^2 = x1^3 + 5) (hy : y1 ≠ 0) :
    (padd ⟨x1, y1, 1⟩ ⟨x1, -y1, 1⟩).Y ≠ 0 := by
  intro hY
  have hYpoly : (padd ⟨x1, y1, 1⟩ ⟨x1, -y1, 1⟩).Y = y1^4 + 90*x1^3 - 225 := by
    simp only [padd]; ring
  rw [hYpoly] at hY
  set wnum2 : Fq := 9*x1^4 - 8*x1*y1^2 with hwnum2
  set wden2 : Fq := 4*y1^2 with hwden2E
  have hwden2ne : wden2 ≠ 0 := by rw [hwden2E]; exact mul_ne_zero (by decide) (pow_ne_zero 2 hy)
  have hcube : wnum2^3 = -5 * wden2^3 := by
    rw [hwnum2, hwden2E]
    linear_combination
      (x1^6 + (100)*x1^3 - 200) * hY
      + ((-729)*x1^9 + (1215)*x1^6*y1^2 + (-512)*x1^3*y1^4 + (3735)*x1^6 + (-2340)*x1^3*y1^2 + (320)*y1^4 + (-9900)*x1^3 + (1800)*y1^2 + (9000)) * e1
  have hw : (wnum2 / wden2)^3 = -5 := by
    rw [div_pow, hcube, mul_div_assoc, div_self (pow_ne_zero 3 hwden2ne), mul_one]
  exact Vesta.no_onCurve_y_zero (wnum2 / wden2) (by
    show (0 : Fq)^2 = (wnum2 / wden2)^3 + Vesta.a * (wnum2 / wden2) + Vesta.b
    rw [hw]; simp [Vesta.a, Vesta.b])

/-- Inverse `X`-coordinate vanishes: `padd P (−P) = (0 : Y₃ : 0)` (pure identity). -/
theorem X_zero_inv (x1 y1 : Fq) : (padd ⟨x1, y1, 1⟩ ⟨x1, -y1, 1⟩).X = 0 := by
  simp only [padd]; ring

/-- Inverse `Z`-coordinate vanishes (pure identity). -/
theorem Z_zero_inv (x1 y1 : Fq) : (padd ⟨x1, y1, 1⟩ ⟨x1, -y1, 1⟩).Z = 0 := by
  simp only [padd]; ring

/-! ## Scaling (homogeneity) and affine interpretation -/

/-- `padd` is homogeneous of bidegree `(2,2)`: rescaling the inputs rescales the output. -/
theorem smul_padd (u v : Fq) (P Q : PVes) :
    padd (smul u P) (smul v Q) = smul (u^2*v^2) (padd P Q) := by
  simp only [padd, smul, PVes.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `aff` is invariant under nonzero rescaling. -/
theorem aff_smul (u : Fq) (hu : u ≠ 0) (P : PVes) : aff (smul u P) = aff P := by
  rcases eq_or_ne P.Z 0 with h | h
  · simp [aff, smul, h]
  · have huz : u * P.Z ≠ 0 := mul_ne_zero hu h
    simp only [aff, smul, if_neg h, if_neg huz]
    rw [Prod.mk.injEq]
    exact ⟨mul_div_mul_left _ _ hu, mul_div_mul_left _ _ hu⟩

/-- `OnCurveP` is preserved by rescaling. -/
theorem oncurveP_smul (u : Fq) {P : PVes} (h : OnCurveP P) : OnCurveP (smul u P) := by
  simp only [OnCurveP, smul] at h ⊢; linear_combination (u^3) * h

/-- The nonzero-vector condition is preserved by nonzero rescaling. -/
theorem nezVec_smul (u : Fq) (hu : u ≠ 0) {P : PVes}
    (h : P.X ≠ 0 ∨ P.Y ≠ 0 ∨ P.Z ≠ 0) :
    (smul u P).X ≠ 0 ∨ (smul u P).Y ≠ 0 ∨ (smul u P).Z ≠ 0 := by
  simp only [smul]
  rcases h with h | h | h
  · exact Or.inl (mul_ne_zero hu h)
  · exact Or.inr (Or.inl (mul_ne_zero hu h))
  · exact Or.inr (Or.inr (mul_ne_zero hu h))

@[simp] theorem aff_z1 (x y : Fq) : aff ⟨x, y, 1⟩ = (x, y) := by
  simp [aff]

/-- `P = P.Z • (X/Z : Y/Z : 1)` when `Z ≠ 0`: every finite point is a rescaled `Z = 1` rep. -/
theorem eq_smul_normalize {P : PVes} (h : P.Z ≠ 0) :
    P = smul P.Z ⟨P.X / P.Z, P.Y / P.Z, 1⟩ := by
  obtain ⟨X, Y, Z⟩ := P
  simp only [smul, PVes.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-! ## Unfolding the affine group law on `Z = 1` reps -/

/-- `(x₁,y₁)` and `(x₂,y₂)` on the curve are `≠ 𝒪 = (0,0)`. -/
theorem onCurve_ne_zero {x y : Fq} (h : OnCurve 0 5 (x, y)) : (x, y) ≠ ((0 : Fq), (0 : Fq)) := by
  intro he
  rw [Prod.mk.injEq] at he
  obtain ⟨hx, hy⟩ := he; subst hx; subst hy
  exact not_onCurve_zero (show (5 : Fq) ≠ 0 by decide) h

/-- The affine sum in the distinct-`x` branch, with cleared denominators. -/
theorem add_dist {x1 y1 x2 y2 : Fq} (h1 : OnCurve 0 5 (x1, y1)) (h2 : OnCurve 0 5 (x2, y2))
    (hne : x1 ≠ x2) :
    add 0 (x1, y1) (x2, y2)
      = (((y2 - y1)^2 - (x1 + x2)*(x2 - x1)^2) / (x2 - x1)^2,
         ((y2 - y1)*(x1*(x2 - x1)^2 - ((y2 - y1)^2 - (x1 + x2)*(x2 - x1)^2)) - y1*(x2 - x1)^3)
           / (x2 - x1)^3) := by
  have hp0 := onCurve_ne_zero h1
  have hq0 := onCurve_ne_zero h2
  have hd : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  unfold add
  dsimp only
  rw [if_neg hp0, if_neg hq0, if_neg hne]
  rw [Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- The affine sum in the doubling branch (`a = 0`), with cleared denominators. -/
theorem add_dbl {x1 y1 : Fq} (h1 : OnCurve 0 5 (x1, y1)) (hy : y1 ≠ 0) :
    add 0 (x1, y1) (x1, y1)
      = ((9*x1^4 - 8*x1*y1^2) / (4*y1^2),
         (3*x1^2*(12*x1*y1^2 - 9*x1^4) - 8*y1^4) / (8*y1^3)) := by
  have hp0 := onCurve_ne_zero h1
  have h2y : y1 + y1 ≠ 0 := by rw [← two_mul]; exact mul_ne_zero (by decide) hy
  have h2 : (2 : Fq) ≠ 0 := by decide
  have h4 : (4 : Fq) ≠ 0 := by decide
  have h8 : (8 : Fq) ≠ 0 := by decide
  unfold add
  dsimp only
  rw [if_neg hp0, if_neg hp0, if_pos rfl, if_neg h2y]
  rw [Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-! ## The core equivalence -/

/-- **Core equivalence on `Z = 1` representatives.** For on-curve `(x₁,y₁),(x₂,y₂)`, the RCB
projective sum interprets affinely as the complete affine sum, and stays a valid projective point. -/
theorem padd_spec_z1 {x1 y1 x2 y2 : Fq} (h1 : OnCurve 0 5 (x1, y1)) (h2 : OnCurve 0 5 (x2, y2)) :
    aff (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩) = add 0 (x1, y1) (x2, y2)
      ∧ Valid (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩) := by
  have e1 : y1^2 = x1^3 + 5 := by have h := h1; simp only [OnCurve] at h; linear_combination h
  have e2 : y2^2 = x2^3 + 5 := by have h := h2; simp only [OnCurve] at h; linear_combination h
  have hoc : OnCurveP (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩) := oncurveP_padd_z1 e1 e2
  have hy1 : y1 ≠ 0 := by
    intro h; exact Vesta.no_onCurve_y_zero x1 (by rw [← h]; exact h1)
  by_cases hx : x1 = x2
  · subst hx
    by_cases hy : y1 + y2 = 0
    · -- inverse: y2 = -y1
      have hy2 : y2 = -y1 := by linear_combination hy
      subst hy2
      refine ⟨?_, hoc, ?_⟩
      · have hz0 : (padd ⟨x1, y1, 1⟩ ⟨x1, -y1, 1⟩).Z = 0 := Z_zero_inv x1 y1
        rw [aff, if_pos hz0]
        have hnp : (x1, -y1) = CompElliptic.CurveForms.ShortWeierstrass.neg (x1, y1) := by
          simp [CompElliptic.CurveForms.ShortWeierstrass.neg]
        rw [hnp, CompElliptic.CurveForms.ShortWeierstrass.add_neg]
      · exact Or.inr (Or.inl (Y_ne_zero_inv e1 hy1))
    · -- doubling: y1 = y2
      have hyeq : y1 = y2 := by
        have hz : (y1 - y2) * (y1 + y2) = 0 := by linear_combination e1 - e2
        rcases mul_eq_zero.mp hz with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hy
      subst hyeq
      have hZv : (padd ⟨x1, y1, 1⟩ ⟨x1, y1, 1⟩).Z = 8 * y1^3 := Z_doubling e1
      have hZne : (padd ⟨x1, y1, 1⟩ ⟨x1, y1, 1⟩).Z ≠ 0 := by
        rw [hZv]; exact mul_ne_zero (by decide) (pow_ne_zero 3 hy1)
      have hy2 : (4 : Fq) * y1^2 ≠ 0 := mul_ne_zero (by decide) (pow_ne_zero 2 hy1)
      have hy3 : (8 : Fq) * y1^3 ≠ 0 := mul_ne_zero (by decide) (pow_ne_zero 3 hy1)
      refine ⟨?_, hoc, ?_⟩
      · rw [aff, if_neg hZne, add_dbl h1 hy1, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [div_eq_div_iff hZne hy2]; linear_combination keyx_dbl e1
        · rw [div_eq_div_iff hZne hy3]; linear_combination keyy_dbl e1
      · exact Or.inr (Or.inr hZne)
  · -- distinct x
    have hZne : (padd ⟨x1, y1, 1⟩ ⟨x2, y2, 1⟩).Z ≠ 0 := Z_ne_zero_dist e1 e2 hx
    have hd : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hd2 : (x2 - x1)^2 ≠ 0 := pow_ne_zero 2 hd
    have hd3 : (x2 - x1)^3 ≠ 0 := pow_ne_zero 3 hd
    refine ⟨?_, hoc, ?_⟩
    · rw [aff, if_neg hZne, add_dist h1 h2 hx, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [div_eq_div_iff hZne hd2]; linear_combination keyx_dist e1 e2
      · rw [div_eq_div_iff hZne hd3]; linear_combination keyy_dist e1 e2
    · exact Or.inr (Or.inr hZne)

/-! ## Structural facts about `Valid` points and the identity-input reductions -/

/-- A valid point with `Z = 0` has `X = 0` (only the identity is at infinity). -/
theorem X_zero_of_Z_zero {P : PVes} (h : OnCurveP P) (hz : P.Z = 0) : P.X = 0 := by
  have hX3 : P.X ^ 3 = 0 := by rw [OnCurveP, hz] at h; simpa using h.symm
  exact pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hX3

/-- A valid point always has nonzero `Y` (no 2-torsion; the identity is `(0 : 1 : 0)`). -/
theorem Valid.Y_ne_zero {P : PVes} (hP : Valid P) : P.Y ≠ 0 := by
  rcases eq_or_ne P.Z 0 with hz | hz
  · have hX := X_zero_of_Z_zero hP.1 hz
    rcases hP.2 with h | h | h
    · exact absurd hX h
    · exact h
    · exact absurd hz h
  · intro hY
    refine Vesta.no_onCurve_y_zero (P.X / P.Z) ?_
    have key : P.X^3 + 5 * P.Z^3 = 0 := by
      have h := hP.1; rw [OnCurveP, hY] at h; linear_combination -h
    show (0 : Fq)^2 = (P.X / P.Z)^3 + Vesta.a * (P.X / P.Z) + Vesta.b
    rw [Vesta.a, Vesta.b]; field_simp; linear_combination -key

/-- `padd` with the first argument an identity-type point `(0 : Y₁ : 0)` rescales the second. -/
theorem padd_idL {P Q : PVes} (hX : P.X = 0) (hZ : P.Z = 0) :
    padd P Q = smul (P.Y^2 * Q.Y) Q := by
  simp only [padd, smul, hX, hZ, PVes.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `padd` with the second argument an identity-type point `(0 : Y₂ : 0)` rescales the first. -/
theorem padd_idR {P Q : PVes} (hX : Q.X = 0) (hZ : Q.Z = 0) :
    padd P Q = smul (P.Y * Q.Y^2) P := by
  simp only [padd, smul, hX, hZ, PVes.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- On-curve reading of the normalized affine coordinates of a finite valid point. -/
theorem onCurve_norm {P : PVes} (h : OnCurveP P) (hz : P.Z ≠ 0) :
    OnCurve 0 5 (P.X / P.Z, P.Y / P.Z) := by
  have key : P.Y^2 * P.Z = P.X^3 + 5 * P.Z^3 := h
  show (P.Y / P.Z)^2 = (P.X / P.Z)^3 + 0 * (P.X / P.Z) + 5
  field_simp; linear_combination key

/-- **General equivalence.** For any two valid projective points, the RCB sum interprets
affinely as the complete affine sum, and stays valid. -/
theorem padd_spec {P Q : PVes} (hP : Valid P) (hQ : Valid Q) :
    aff (padd P Q) = add 0 (aff P) (aff Q) ∧ Valid (padd P Q) := by
  have hPY := hP.Y_ne_zero
  have hQY := hQ.Y_ne_zero
  by_cases hPz : P.Z = 0
  · -- P is an identity-type point
    have hPX := X_zero_of_Z_zero hP.1 hPz
    have hlam : P.Y^2 * Q.Y ≠ 0 := mul_ne_zero (pow_ne_zero 2 hPY) hQY
    have haffP : aff P = (0, 0) := by rw [aff, if_pos hPz]
    rw [padd_idL hPX hPz, haffP, CompElliptic.CurveForms.ShortWeierstrass.zero_add]
    refine ⟨aff_smul _ hlam Q, oncurveP_smul _ hQ.1, nezVec_smul _ hlam hQ.2⟩
  · by_cases hQz : Q.Z = 0
    · -- Q is an identity-type point
      have hQX := X_zero_of_Z_zero hQ.1 hQz
      have hlam : P.Y * Q.Y^2 ≠ 0 := mul_ne_zero hPY (pow_ne_zero 2 hQY)
      have haffQ : aff Q = (0, 0) := by rw [aff, if_pos hQz]
      rw [padd_idR hQX hQz, haffQ, CompElliptic.CurveForms.ShortWeierstrass.add_zero]
      refine ⟨aff_smul _ hlam P, oncurveP_smul _ hP.1, nezVec_smul _ hlam hP.2⟩
    · -- both finite: normalize to `Z = 1` and use the core lemma
      have hP1 := onCurve_norm hP.1 hPz
      have hQ1 := onCurve_norm hQ.1 hQz
      obtain ⟨haff, hvalid⟩ := padd_spec_z1 hP1 hQ1
      have hu : P.Z^2 * Q.Z^2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)
      have hpadd : padd P Q = smul (P.Z^2 * Q.Z^2) (padd ⟨P.X/P.Z, P.Y/P.Z, 1⟩ ⟨Q.X/Q.Z, Q.Y/Q.Z, 1⟩) := by
        conv_lhs => rw [eq_smul_normalize hPz, eq_smul_normalize hQz]
        rw [smul_padd]
      have haffP : aff P = (P.X / P.Z, P.Y / P.Z) := by rw [aff, if_neg hPz]
      have haffQ : aff Q = (Q.X / Q.Z, Q.Y / Q.Z) := by rw [aff, if_neg hQz]
      refine ⟨?_, ?_⟩
      · rw [hpadd, aff_smul _ hu, haff, haffP, haffQ]
      · rw [hpadd]
        exact ⟨oncurveP_smul _ hvalid.1, nezVec_smul _ hu hvalid.2⟩

/-- Validity is preserved by `padd` (closure). -/
theorem valid_padd {P Q : PVes} (hP : Valid P) (hQ : Valid Q) : Valid (padd P Q) :=
  (padd_spec hP hQ).2

/-- `aff` is a homomorphism from `padd` to the affine group law on valid inputs. -/
theorem aff_padd {P Q : PVes} (hP : Valid P) (hQ : Valid Q) :
    aff (padd P Q) = add 0 (aff P) (aff Q) :=
  (padd_spec hP hQ).1

/-- The identity `(0 : 1 : 0)` is valid. -/
theorem valid_pid : Valid pid := by
  refine ⟨?_, Or.inr (Or.inl one_ne_zero)⟩
  simp [OnCurveP, pid]

/-- `aff pid = 𝒪`. -/
@[simp] theorem aff_pid : aff pid = ((0 : Fq), (0 : Fq)) := by simp [aff, pid]

/-! ## Bridge to the affine group `G = SWPoint Vesta.curve` -/

/-- Interpret a projective point as an element of the affine group: a finite on-curve point maps to
`(X/Z, Y/Z)`, everything else (points at infinity, off-curve junk) to the identity `𝒪`. -/
def toAffine (P : PVes) : G :=
  if h : OnCurveP P ∧ P.Z ≠ 0 then
    ⟨P.X / P.Z, P.Y / P.Z, Or.inl (onCurve_norm h.1 h.2)⟩
  else 0

/-- On valid points, `toAffine` agrees coordinatewise with `aff`. -/
theorem toAffine_coords {P : PVes} (hP : Valid P) :
    ((toAffine P).x, (toAffine P).y) = aff P := by
  rcases eq_or_ne P.Z 0 with hz | hz
  · have h0 : toAffine P = 0 := by rw [toAffine, dif_neg]; rintro ⟨_, h⟩; exact h hz
    rw [h0, aff, if_pos hz]; rfl
  · rw [toAffine, dif_pos ⟨hP.1, hz⟩, aff, if_neg hz]

@[simp] theorem toAffine_pid : toAffine pid = 0 := by
  rw [toAffine, dif_neg]; rintro ⟨_, h⟩; exact h rfl

/-- **The homomorphism.** `toAffine` carries the projective RCB addition to the affine group law. -/
theorem toAffine_padd {P Q : PVes} (hP : Valid P) (hQ : Valid Q) :
    toAffine (padd P Q) = toAffine P + toAffine Q := by
  apply SWPoint.ext_pair
  have hL : ((toAffine (padd P Q)).x, (toAffine (padd P Q)).y) = aff (padd P Q) :=
    toAffine_coords (valid_padd hP hQ)
  have hRc : ((toAffine P + toAffine Q).x, (toAffine P + toAffine Q).y)
      = add Vesta.curve.A ((toAffine P).x, (toAffine P).y) ((toAffine Q).x, (toAffine Q).y) := rfl
  rw [hL, hRc, toAffine_coords hP, toAffine_coords hQ, aff_padd hP hQ]
  rfl

/-- Materialize an affine group element as a projective representative: the identity as `(0 : 1 : 0)`,
a finite point as `(x : y : 1)`. -/
def ofAffine (p : G) : PVes :=
  if p.x = 0 ∧ p.y = 0 then pid else ⟨p.x, p.y, 1⟩

theorem valid_ofAffine (p : G) : Valid (ofAffine p) := by
  rw [ofAffine]
  by_cases h : p.x = 0 ∧ p.y = 0
  · rw [if_pos h]; exact valid_pid
  · rw [if_neg h]
    have hoc : OnCurve 0 5 (p.x, p.y) := by
      have hv := p.onCurve
      exact hv.resolve_right (by rw [Prod.mk.injEq]; exact h)
    have e : p.y^2 = p.x^3 + 5 := by have := hoc; simp only [OnCurve] at this; linear_combination this
    refine ⟨?_, Or.inr (Or.inr one_ne_zero)⟩
    simp only [OnCurveP]; linear_combination e

theorem toAffine_ofAffine (p : G) : toAffine (ofAffine p) = p := by
  rw [ofAffine]
  by_cases h : p.x = 0 ∧ p.y = 0
  · rw [if_pos h, toAffine_pid]
    apply SWPoint.ext_pair
    obtain ⟨hx, hy⟩ := h
    show ((0 : G).x, (0 : G).y) = (p.x, p.y)
    rw [hx, hy]; rfl
  · rw [if_neg h]
    have hoc : OnCurve 0 5 (p.x, p.y) := p.onCurve.resolve_right (by rw [Prod.mk.injEq]; exact h)
    have hZ : ((⟨p.x, p.y, 1⟩ : PVes)).Z ≠ 0 := one_ne_zero
    have hocp : OnCurveP (⟨p.x, p.y, 1⟩ : PVes) := by
      have e : p.y^2 = p.x^3 + 5 := by have := hoc; simp only [OnCurve] at this; linear_combination this
      simp only [OnCurveP]; linear_combination e
    apply SWPoint.ext_pair
    rw [toAffine, dif_pos ⟨hocp, hZ⟩]
    show (p.x / 1, p.y / 1) = (p.x, p.y)
    rw [div_one, div_one]

/-! ## Fast (binary) scalar multiplication -/

/-- Binary double-and-add scalar multiplication over `PVes` using the RCB `padd`, matching the
`CompElliptic.binNsmul` recurrence used by the affine group's `nsmul`. -/
def pnsmulFast (n : ℕ) (P : PVes) : PVes := binNsmul padd pid n P

/-- **Fast scalar multiplication is the genuine group action.** By strong induction along the
`binNsmul` double-and-add recurrence: each intermediate stays valid (`valid_padd`) and `toAffine`
is a homomorphism (`toAffine_padd`), so the projective ladder computes `n • (toAffine P)`. -/
theorem pnsmulFast_spec {P : PVes} (hP : Valid P) : ∀ n : ℕ,
    Valid (pnsmulFast n P) ∧ toAffine (pnsmulFast n P) = n • toAffine P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [pnsmulFast, binNsmul]
    split
    · rename_i h; subst h
      exact ⟨valid_pid, by rw [toAffine_pid, zero_nsmul]⟩
    · rename_i hn
      have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      obtain ⟨hvq, hq⟩ := ih (n / 2) hlt
      rw [pnsmulFast] at hvq hq
      set q := binNsmul padd pid (n / 2) P with hqdef
      have hvd : Valid (padd q q) := valid_padd hvq hvq
      have hdaff : toAffine (padd q q) = (n / 2) • toAffine P + (n / 2) • toAffine P := by
        rw [toAffine_padd hvq hvq, hq]
      have key : n • toAffine P
          = (n / 2) • toAffine P + (n / 2) • toAffine P + (n % 2) • toAffine P := by
        rw [← add_nsmul, ← add_nsmul]; congr 1; omega
      split
      · rename_i hodd
        refine ⟨valid_padd hvd hP, ?_⟩
        rw [toAffine_padd hvd hP, hdaff, key, hodd, one_nsmul]
      · rename_i heven
        refine ⟨hvd, ?_⟩
        rw [hdaff, key, show n % 2 = 0 from by omega, zero_nsmul, _root_.add_zero]

/-- The packaged fast scalar multiplication on `G`, going through projective coordinates. -/
def smulFast (n : ℕ) (p : G) : G := toAffine (pnsmulFast n (ofAffine p))

/-- **Correctness of `smulFast`:** it equals the affine scalar multiplication `n • p`, with the
field inversion paid once (in the final `toAffine`) instead of once per addition. -/
theorem smulFast_eq (n : ℕ) (p : G) : smulFast n p = n • p := by
  rw [smulFast, (pnsmulFast_spec (valid_ofAffine p) n).2, toAffine_ofAffine]

/-! ## Fast compiled spelling of `padd` (compiled-tier only)

Compiled generically, every field operation in `padd` goes through boxed `CommRing (ZMod q)`
dictionary projections.  `paddFast` is the same closed forms over raw `ℕ` representatives with
fused mul-mod, and `padd_eq_paddFast` is the proven equality — the proven counterpart of
`implemented_by` — so `padd` stays the statement surface while compiled call sites run fast. -/

/-- The Vesta base-field order, the modulus of the raw-`ℕ` fast path (reducible so `ZMod qv`
unifies with `Fq`). -/
private abbrev qv : ℕ := CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD

private theorem qv_pos : 0 < qv := by decide

private instance : NeZero qv := ⟨qv_pos.ne'⟩

/-- Fused modular addition on canonical representatives. -/
@[inline] private def fadd (a b : ℕ) : ℕ := (a + b) % qv

/-- Fused modular multiplication: one GMP multiply, one GMP mod. -/
@[inline] private def fmul (a b : ℕ) : ℕ := (a * b) % qv

/-- Modular subtraction without hypotheses: `a + (q − b mod q) ≡ a − b`. -/
@[inline] private def fsub (a b : ℕ) : ℕ := (a + (qv - b % qv)) % qv

private theorem cast_fadd (a b : ℕ) : ((fadd a b : ℕ) : Fq) = (a : Fq) + (b : Fq) := by
  rw [fadd, ZMod.natCast_mod, Nat.cast_add]

private theorem cast_fmul (a b : ℕ) : ((fmul a b : ℕ) : Fq) = (a : Fq) * (b : Fq) := by
  rw [fmul, ZMod.natCast_mod, Nat.cast_mul]

private theorem cast_fsub (a b : ℕ) : ((fsub a b : ℕ) : Fq) = (a : Fq) - (b : Fq) := by
  rw [fsub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ qv_pos).le,
    ZMod.natCast_mod, ZMod.natCast_self]
  ring

private theorem cast_val (a : Fq) : ((ZMod.val a : ℕ) : Fq) = a :=
  ZMod.natCast_rightInverse a

/-- `padd` over raw `ℕ` representatives: same RCB closed forms, fused mul-mod, shared
subproducts. Statement-surface code should keep calling `padd`; the compiler substitutes this
body via `padd_eq_paddFast`. -/
def paddFast (P Q : PVes) : PVes :=
  let x1 := P.X.val; let y1 := P.Y.val; let z1 := P.Z.val
  let x2 := Q.X.val; let y2 := Q.Y.val; let z2 := Q.Z.val
  let y2sq := fmul y2 y2
  let z2sq := fmul z2 z2
  let x1y1 := fmul x1 y1
  let y1sq := fmul y1 y1
  let z1sq := fmul z1 z1
  let x2y2 := fmul x2 y2
  let y1z1 := fmul y1 z1
  let x1z1 := fmul x1 z1
  let y2z2 := fmul y2 z2
  let x2z2 := fmul x2 z2
  let x1sq := fmul x1 x1
  let x2sq := fmul x2 x2
  let X3 := fsub (fadd (fsub (fsub (fmul x1y1 y2sq) (fmul 15 (fmul x1y1 z2sq)))
                    (fmul 30 (fmul x1z1 y2z2)))
               (fsub (fmul y1sq x2y2) (fmul 15 (fmul z1sq x2y2))))
              (fmul 30 (fmul y1z1 x2z2))
  let Y3 := fsub (fadd (fadd (fmul y1sq y2sq) (fmul 45 (fmul x1sq x2z2)))
                    (fmul 45 (fmul x1z1 x2sq)))
              (fmul 225 (fmul z1sq z2sq))
  let Z3 := fadd (fadd (fadd (fadd (fadd (fmul y1sq y2z2) (fmul y1z1 y2sq))
                    (fmul 3 (fmul x1sq x2y2)))
                    (fmul 3 (fmul x1y1 x2sq)))
                    (fmul 15 (fmul y1z1 z2sq)))
                    (fmul 15 (fmul z1sq y2z2))
  ⟨(X3 : Fq), (Y3 : Fq), (Z3 : Fq)⟩

/-- **The fast spelling is `padd`.** NOT registered `@[csimp]`: in the current
`native_decide` tier, library calls execute through interpreted IR, where this raw-`ℕ`
spelling measured ~17× SLOWER than the typeclass path it replaces (1.5 ms vs 85 µs per
add — many small interpreted steps lose to few boxed GMP calls; the same effect that
makes interpreted Montgomery a 40× regression). The equality is kept for the compiled
tier: once the fast-field lib ships precompiled (`precompileModules` dylib), registering
this `@[csimp]` (or the Montgomery successor) makes every compiled call site (including
`native_decide` auxiliaries) run the fused raw-`ℕ` form. -/
theorem padd_eq_paddFast : @padd = @paddFast := by
  funext P Q
  simp only [padd, paddFast, PVes.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cast_fadd, cast_fmul, cast_fsub, cast_val, Nat.cast_ofNat] <;> ring

end PVes
end CompElliptic.Curves.Pasta.Fast.Projective
