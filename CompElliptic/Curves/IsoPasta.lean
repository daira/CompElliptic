/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.Pasta
import CompElliptic.Isogenies.ThreeIsogeny

/-!
# The iso-Pasta curves and their isogenies to Pallas and Vesta

Simplified SWU needs a curve coefficient `A ≠ 0`, and both Pasta curves have `A = 0`,
so hashing to them goes through auxiliary curves: iso-Pallas and iso-Vesta, each
3-isogenous to its target. The curves and their isogeny maps are specified in
§5.4.9.8 of the Zcash protocol specification (`iso_map`); the same constants appear,
in decimal, in `zcash/pasta`'s `hashtocurve.sage`. (`amicable.sage` originally found
the curves with Sage's `isogenies_prime_degree(3)`, and the maps are the isogenies'
affine `rational_maps()`.)

Each isogeny is stated twice here, and that is the point of the design:

* `Pallas.iso` (and `Vesta.iso`) is the `ThreeIsogeny` *derivation* of the map — the
  kernel abscissa `x₀` and normalizing scalar `s`, recovered from the specified
  coefficients (`x₀ = -b₁/2` from the abscissa denominator, `s` from the leading
  coefficients), with Vélu's formulae supplying the rational maps and the codomain.
  Its obligations are numeral checks (`ψ₃(x₀) = 0`, the codomain equations) together
  with the kernel's irrationality: both kernel ordinates satisfy `y₀² = 5`, so that
  is exactly `five_not_isSquare` — the same nonsquare that already pins `x = 0` off
  both curves.
* `Pallas.iso_map` (and `Vesta.iso_map`) is the specified map: its constants
  `CP_1, ..., CP_13` (`CV_*` for Vesta) quote the hex list of §5.4.9.8 verbatim, and
  those agree with the decimal constants of `hashtocurve.sage`. `iso_map_eq` proves
  the map equal to the derivation. The general theorems of `ThreeIsogeny` — totality
  on rational points, landing on the target curve, oddness — then apply to the
  deployed constants; `onCurve_iso_map` states the on-curve consequence directly.
-/

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Fields.Pasta
open CompElliptic.Isogenies

namespace CompElliptic.Curves.Pasta

namespace Pallas

/-- The auxiliary curve 3-isogenous to Pallas ("iso-Pallas"): `y² = x³ + A'·x + 1265`
over the Pallas base field, with `A' ≠ 0` as simplified SWU requires. -/
def isoCurve : SWCurve PallasBaseField where
  A := 0x18354a2eb0ea8c9c49be2d7258370742b74134581a27a59f92bb4b0b657a014b
  B := 1265
  IsElliptic := by rw [isUnit_iff_ne_zero]; decide
  B_nonzero := by decide

/-- The degree-3 isogeny iso-Pallas → Pallas, as its Vélu derivation. -/
def iso : ThreeIsogeny PallasBaseField where
  domain := isoCurve
  codomain := curve
  x₀ := 7838456566140329779539982655430940346658055915816802388238595436199677105265
  s := 19298681539552699237261830834781317975575370987961040477303117842899978420225
  s_nonzero := by decide
  psi3 := by decide
  kernel_irrational := by
    have h : (7838456566140329779539982655430940346658055915816802388238595436199677105265 :
          PallasBaseField)^3
        + isoCurve.A * 7838456566140329779539982655430940346658055915816802388238595436199677105265
        + isoCurve.B = 5 := by decide
    rw [h]
    exact five_not_isSquare
  codomain_A := by decide
  codomain_B := by decide

/-! The thirteen constants of the isogeny map, quoted in hex from the list
`IsoConst` for Pallas in §5.4.9.8 of the protocol specification (decimal in
`hashtocurve.sage`; the two sources agree). -/

def CP_1  : PallasBaseField := 0x0e38e38e38e38e38e38e38e38e38e38e4081775473d8375b775f6034aaaaaaab
def CP_2  : PallasBaseField := 0x3509afd51872d88e267c7ffa51cf412a0f93b82ee4b994958cf863b02814fb76
def CP_3  : PallasBaseField := 0x17329b9ec525375398c7d7ac3d98fd13380af066cfeb6d690eb64faef37ea4f7
def CP_4  : PallasBaseField := 0x1c71c71c71c71c71c71c71c71c71c71c8102eea8e7b06eb6eebec06955555580
def CP_5  : PallasBaseField := 0x1d572e7ddc099cff5a607fcce0494a799c434ac1c96b6980c47f2ab668bcd71f
def CP_6  : PallasBaseField := 0x325669becaecd5d11d13bf2a7f22b105b4abf9fb9a1fc81c2aa3af1eae5b6604
def CP_7  : PallasBaseField := 0x1a12f684bda12f684bda12f684bda12f7642b01ad461bad25ad985b5e38e38e4
def CP_8  : PallasBaseField := 0x1a84d7ea8c396c47133e3ffd28e7a09507c9dc17725cca4ac67c31d8140a7dbb
def CP_9  : PallasBaseField := 0x3fb98ff0d2ddcadd303216cce1db9ff11765e924f745937802e2be87d225b234
def CP_10 : PallasBaseField := 0x025ed097b425ed097b425ed097b425ed0ac03e8e134eb3e493e53ab371c71c4f
def CP_11 : PallasBaseField := 0x0c02c5bcca0e6b7f0790bfb3506defb65941a3a4a97aa1b35a28279b1d1b42ae
def CP_12 : PallasBaseField := 0x17033d3c60c68173573b3d7f7d681310d976bbfabbc5661d4d90ab820b12320a
def CP_13 : PallasBaseField := 0x40000000000000000000000000000000224698fc094cf91b992d30ecfffffde5

/-- The specified map iso-Pallas → Pallas, arranged as in §5.4.9.8. -/
def iso_map (x y : PallasBaseField) : PallasBaseField × PallasBaseField :=
  ((CP_1 * x^3 + CP_2 * x^2 + CP_3 * x + CP_4) / (x^2 + CP_5 * x + CP_6),
   (CP_7 * x^3 + CP_8 * x^2 + CP_9 * x + CP_10) * y / (x^3 + CP_11 * x^2 + CP_12 * x + CP_13))

/-- The specified coefficients are exactly what the Vélu derivation yields: each
coefficient is a numeral identity (`decide`), and the four polynomial identities
assemble by `linear_combination`. -/
theorem iso_map_eq (x y : PallasBaseField) : iso_map x y = iso.mapXY x y := by
  have hs : iso.s
      = (19298681539552699237261830834781317975575370987961040477303117842899978420225 :
        PallasBaseField) := rfl
  have hx0 : iso.x₀
      = (7838456566140329779539982655430940346658055915816802388238595436199677105265 :
        PallasBaseField) := rfl
  have hA : iso.domain.A
      = (10949663248450308183708987909873589833737836120165333298109615750520499732811 :
        PallasBaseField) := rfl
  have hB : iso.domain.B = (1265 : PallasBaseField) := rfl
  simp only [iso_map, ThreeIsogeny.mapXY, ThreeIsogeny.xnum, ThreeIsogeny.ynum,
    ThreeIsogeny.v, ThreeIsogeny.u, hs, hx0, hA, hB, Prod.mk.injEq]
  set s : PallasBaseField :=
    19298681539552699237261830834781317975575370987961040477303117842899978420225 with hsdef
  set x₀ : PallasBaseField :=
    7838456566140329779539982655430940346658055915816802388238595436199677105265 with hx0def
  set A : PallasBaseField :=
    10949663248450308183708987909873589833737836120165333298109615750520499732811 with hAdef
  refine ⟨?_, ?_⟩
  · have e3 : CP_1 = s^2 := by rw [hsdef]; decide
    have e2 : CP_2 = s^2 * (-2 * x₀) := by rw [hsdef, hx0def]; decide
    have e1 : CP_3 = s^2 * (x₀^2 + 2 * (3 * x₀^2 + A)) := by
      rw [hsdef, hx0def, hAdef]; decide
    have e0 : CP_4 = s^2 * (4 * (x₀^3 + A * x₀ + 1265) - 2 * (3 * x₀^2 + A) * x₀) := by
      rw [hsdef, hx0def, hAdef]; decide
    have f1 : CP_5 = -2 * x₀ := by rw [hx0def]; decide
    have f0 : CP_6 = x₀^2 := by rw [hx0def]; decide
    rw [show (x^2 + CP_5 * x + CP_6 : PallasBaseField) = (x - x₀)^2
        from by linear_combination x * f1 + f0,
      show (CP_1 * x^3 + CP_2 * x^2 + CP_3 * x + CP_4 : PallasBaseField)
          = s^2 * (x * (x - x₀)^2 + 2 * (3 * x₀^2 + A) * (x - x₀)
            + 4 * (x₀^3 + A * x₀ + 1265))
        from by linear_combination x^3 * e3 + x^2 * e2 + x * e1 + e0]
  · have g3 : CP_7 = s^3 := by rw [hsdef]; decide
    have g2 : CP_8 = s^3 * (-3 * x₀) := by rw [hsdef, hx0def]; decide
    have g1 : CP_9 = s^3 * (3 * x₀^2 - 2 * (3 * x₀^2 + A)) := by
      rw [hsdef, hx0def, hAdef]; decide
    have g0 : CP_10
        = s^3 * (-x₀^3 + 2 * (3 * x₀^2 + A) * x₀ - 2 * (4 * (x₀^3 + A * x₀ + 1265))) := by
      rw [hsdef, hx0def, hAdef]; decide
    have k2 : CP_11 = -3 * x₀ := by rw [hx0def]; decide
    have k1 : CP_12 = 3 * x₀^2 := by rw [hx0def]; decide
    have k0 : CP_13 = -x₀^3 := by rw [hx0def]; decide
    rw [show (x^3 + CP_11 * x^2 + CP_12 * x + CP_13 : PallasBaseField) = (x - x₀)^3
        from by linear_combination x^2 * k2 + x * k1 + k0,
      show (CP_7 * x^3 + CP_8 * x^2 + CP_9 * x + CP_10 : PallasBaseField)
          = s^3 * ((x - x₀)^3 - 2 * (3 * x₀^2 + A) * (x - x₀)
            - 2 * (4 * (x₀^3 + A * x₀ + 1265)))
        from by linear_combination x^3 * g3 + x^2 * g2 + x * g1 + g0]
    ring

/-- Points of iso-Pallas land on Pallas under the specified map. -/
theorem onCurve_iso_map {x y : PallasBaseField}
    (h : OnCurve isoCurve.A isoCurve.B (x, y)) : OnCurve a b (iso_map x y) := by
  rw [iso_map_eq]
  exact iso.onCurve_mapXY h

end Pallas

namespace Vesta

/-- The auxiliary curve 3-isogenous to Vesta ("iso-Vesta"): `y² = x³ + A'·x + 1265`
over the Vesta base field, with `A' ≠ 0` as simplified SWU requires. -/
def isoCurve : SWCurve VestaBaseField where
  A := 0x267f9b2ee592271a81639c4d96f787739673928c7d01b212c515ad7242eaa6b1
  B := 1265
  IsElliptic := by rw [isUnit_iff_ne_zero]; decide
  B_nonzero := by decide

/-- The degree-3 isogeny iso-Vesta → Vesta, as its Vélu derivation. -/
def iso : ThreeIsogeny VestaBaseField where
  domain := isoCurve
  codomain := curve
  x₀ := 12171904256315698649025652314226635480811313718585433996597634167523473567372
  s := 19298681539552699237261830834781317975575370987961098253119828498928908632065
  s_nonzero := by decide
  psi3 := by decide
  kernel_irrational := by
    have h : (12171904256315698649025652314226635480811313718585433996597634167523473567372 :
          VestaBaseField)^3
        + isoCurve.A * 12171904256315698649025652314226635480811313718585433996597634167523473567372
        + isoCurve.B = 5 := by decide
    rw [h]
    exact five_not_isSquare
  codomain_A := by decide
  codomain_B := by decide

/-! The thirteen constants of the isogeny map, quoted in hex from the list
`IsoConst` for Vesta in §5.4.9.8 of the protocol specification (decimal in
`hashtocurve.sage`; the two sources agree). -/

def CV_1  : VestaBaseField := 0x38e38e38e38e38e38e38e38e38e38e390205dd51cfa0961a43cd42c800000001
def CV_2  : VestaBaseField := 0x1d935247b4473d17acecf10f5f7c09a2216b8861ec72bd5d8b95c6aaf703bcc5
def CV_3  : VestaBaseField := 0x18760c7f7a9ad20ded7ee4a9cdf78f8fd59d03d23b39cb11aeac67bbeb586a3d
def CV_4  : VestaBaseField := 0x31c71c71c71c71c71c71c71c71c71c71e1c521a795ac8356fb539a6f0000002b
def CV_5  : VestaBaseField := 0x0a2de485568125d51454798a5b5c56b2a3ad678129b604d3b7284f7eaf21a2e9
def CV_6  : VestaBaseField := 0x14735171ee5427780c621de8b91c242a30cd6d53df49d235f169c187d2533465
def CV_7  : VestaBaseField := 0x12f684bda12f684bda12f684bda12f685601f4709a8adcb36bef1642aaaaaaab
def CV_8  : VestaBaseField := 0x2ec9a923da239e8bd6767887afbe04d121d910aefb03b31d8bee58e5fb81de63
def CV_9  : VestaBaseField := 0x19b0d87e16e2578866d1466e9de10e6497a3ca5c24e9ea634986913ab4443034
def CV_10 : VestaBaseField := 0x1ed097b425ed097b425ed097b425ed098bc32d36fb21a6a38f64842c55555533
def CV_11 : VestaBaseField := 0x2f44d6c801c1b8bf9e7eb64f890a820c06a767bfc35b5bac58dfecce86b2745e
def CV_12 : VestaBaseField := 0x3d59f455cafc7668252659ba2b546c7e926847fb9ddd76a1d43d449776f99d2f
def CV_13 : VestaBaseField := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb20fffffde5

/-- The specified map iso-Vesta → Vesta, arranged as in §5.4.9.8. -/
def iso_map (x y : VestaBaseField) : VestaBaseField × VestaBaseField :=
  ((CV_1 * x^3 + CV_2 * x^2 + CV_3 * x + CV_4) / (x^2 + CV_5 * x + CV_6),
   (CV_7 * x^3 + CV_8 * x^2 + CV_9 * x + CV_10) * y / (x^3 + CV_11 * x^2 + CV_12 * x + CV_13))

/-- The specified coefficients are exactly what the Vélu derivation yields: each
coefficient is a numeral identity (`decide`), and the four polynomial identities
assemble by `linear_combination`. -/
theorem iso_map_eq (x y : VestaBaseField) : iso_map x y = iso.mapXY x y := by
  have hs : iso.s
      = (19298681539552699237261830834781317975575370987961098253119828498928908632065 :
        VestaBaseField) := rfl
  have hx0 : iso.x₀
      = (12171904256315698649025652314226635480811313718585433996597634167523473567372 :
        VestaBaseField) := rfl
  have hA : iso.domain.A
      = (17413348858408915339762682399132325137863850198379221683097628341577494210225 :
        VestaBaseField) := rfl
  have hB : iso.domain.B = (1265 : VestaBaseField) := rfl
  simp only [iso_map, ThreeIsogeny.mapXY, ThreeIsogeny.xnum, ThreeIsogeny.ynum,
    ThreeIsogeny.v, ThreeIsogeny.u, hs, hx0, hA, hB, Prod.mk.injEq]
  set s : VestaBaseField :=
    19298681539552699237261830834781317975575370987961098253119828498928908632065 with hsdef
  set x₀ : VestaBaseField :=
    12171904256315698649025652314226635480811313718585433996597634167523473567372 with hx0def
  set A : VestaBaseField :=
    17413348858408915339762682399132325137863850198379221683097628341577494210225 with hAdef
  refine ⟨?_, ?_⟩
  · have e3 : CV_1 = s^2 := by rw [hsdef]; decide
    have e2 : CV_2 = s^2 * (-2 * x₀) := by rw [hsdef, hx0def]; decide
    have e1 : CV_3 = s^2 * (x₀^2 + 2 * (3 * x₀^2 + A)) := by
      rw [hsdef, hx0def, hAdef]; decide
    have e0 : CV_4 = s^2 * (4 * (x₀^3 + A * x₀ + 1265) - 2 * (3 * x₀^2 + A) * x₀) := by
      rw [hsdef, hx0def, hAdef]; decide
    have f1 : CV_5 = -2 * x₀ := by rw [hx0def]; decide
    have f0 : CV_6 = x₀^2 := by rw [hx0def]; decide
    rw [show (x^2 + CV_5 * x + CV_6 : VestaBaseField) = (x - x₀)^2
        from by linear_combination x * f1 + f0,
      show (CV_1 * x^3 + CV_2 * x^2 + CV_3 * x + CV_4 : VestaBaseField)
          = s^2 * (x * (x - x₀)^2 + 2 * (3 * x₀^2 + A) * (x - x₀)
            + 4 * (x₀^3 + A * x₀ + 1265))
        from by linear_combination x^3 * e3 + x^2 * e2 + x * e1 + e0]
  · have g3 : CV_7 = s^3 := by rw [hsdef]; decide
    have g2 : CV_8 = s^3 * (-3 * x₀) := by rw [hsdef, hx0def]; decide
    have g1 : CV_9 = s^3 * (3 * x₀^2 - 2 * (3 * x₀^2 + A)) := by
      rw [hsdef, hx0def, hAdef]; decide
    have g0 : CV_10
        = s^3 * (-x₀^3 + 2 * (3 * x₀^2 + A) * x₀ - 2 * (4 * (x₀^3 + A * x₀ + 1265))) := by
      rw [hsdef, hx0def, hAdef]; decide
    have k2 : CV_11 = -3 * x₀ := by rw [hx0def]; decide
    have k1 : CV_12 = 3 * x₀^2 := by rw [hx0def]; decide
    have k0 : CV_13 = -x₀^3 := by rw [hx0def]; decide
    rw [show (x^3 + CV_11 * x^2 + CV_12 * x + CV_13 : VestaBaseField) = (x - x₀)^3
        from by linear_combination x^2 * k2 + x * k1 + k0,
      show (CV_7 * x^3 + CV_8 * x^2 + CV_9 * x + CV_10 : VestaBaseField)
          = s^3 * ((x - x₀)^3 - 2 * (3 * x₀^2 + A) * (x - x₀)
            - 2 * (4 * (x₀^3 + A * x₀ + 1265)))
        from by linear_combination x^3 * g3 + x^2 * g2 + x * g1 + g0]
    ring

/-- Points of iso-Vesta land on Vesta under the specified map. -/
theorem onCurve_iso_map {x y : VestaBaseField}
    (h : OnCurve isoCurve.A isoCurve.B (x, y)) : OnCurve a b (iso_map x y) := by
  rw [iso_map_eq]
  exact iso.onCurve_mapXY h

end Vesta

end CompElliptic.Curves.Pasta
