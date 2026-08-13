/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Hashing.SignedLift
import CompElliptic.Fields.Sqrt
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The simplified SWU mapping

This file defines the deployed hash-to-curve mapping of the Zcash protocol
specification, mirrored from §5.4.9.8 ("Group Hash into Pallas and Vesta"). The
spec's presentation takes precedence over RFC 9380 by its own declaration; the
two agree on every step used here. The concrete Pasta instantiation and its
reference fixtures live in `Hashing/PastaSSWU.lean`, whose module documentation
records how the construction is checked against the reference implementations.

## `sqrt_ratio`

The subroutine `sqrt_ratio` (spec notation `sqrt_ratio_{GF(q)}(num, div)`):
divide, take a square root if one exists, and otherwise take a square root of
the ratio multiplied by a fixed nonsquare `lam` — which always exists, because a
nonsquare times a nonsquare is a square in a finite field
(`isSquare_mul_of_not_isSquare`, by multiplicativity of the quadratic
character). The `Bool` component reports which case occurred; the spec notes the
result is never `⊥`, which here is the fact that the `.getD 0` default is dead
code (`sqrtRatio_false_sq` proves the false branch still returns a genuine
root). The spec allows an arbitrary square root and an arbitrary nonsquare
`lam`; this implementation fixes the Tonelli–Shanks root of `Fields/Sqrt.lean`
and takes `lam` as a parameter, which matches the spec's note that neither
choice affects the mapping's output.

## The mapping

`mapXYUpToSign` computes the spec's steps with the spec's own intermediate
names (`Zuu`, `ta`, `x1num`, `xdiv`, `U`, `x2num`, `y1`, `y2`, `xnum`, `y'`),
stopping just before the sign-matching step; `mapXY` applies that final step,
so their composition is step-for-step the spec's list. `onCurve_mapXY` proves
the result lies on the curve —never the identity— and `map` packages both as
an `SWPoint`. The signed-lift section factors the mapping through `signedLift`
(`candidateMap`, `map_eq_signedLift`) and derives oddness away from `0`
(`map_neg`). The on-curve proof has three strands. The final
sign-matching step squares away. In the square branch, the curve equation at
`x1num/xdiv` is the definition of `U`. In the nonsquare branch the root `y1`
squares to `lam·U/xdiv³`, and the algebra rests on two facts. First,
`θ²·lam = Z` turns the extra factors of `y2 = θ·Zuu·u·y1` into exactly `Zuu³`.
Second, the identity `Zuu³·U = g(x2num/xdiv)·xdiv³` closes the generic case; it
is special to the SSWU choice of `x1num` and `xdiv`, and false in the
exceptional `ta = 0` case. The `ta = 0` case is unreachable in this branch:
RFC 9380's criterion 4 on `Z` makes `g(B/(Z·A))` a square there, so
`sqrt_ratio` took the square branch.

## The `Z` criteria

RFC 9380 §6.6.2 puts four criteria on `Z`. Two have mathematical content, and
the proofs here consume exactly those two: criterion 1 (`Z` nonsquare) makes
the two-candidate trick work, and criterion 4 (`g(B/(Z·A))` square) makes the
exceptional case land in the square branch. Criterion 2 (`Z ≠ -1`) and
criterion 3 (`g(X) - Z` irreducible over `F`) entered in draft 5 of the RFC
to avoid two patents on deterministic hashing to elliptic curves,
US 8,718,276 and US 8,712,038 (Icart et al., filed 2010, expiring June 2030;
see <https://github.com/cfrg/draft-irtf-cfrg-hash-to-curve/pull/172> and
<https://mailarchive.ietf.org/arch/msg/cfrg/jV4Wr4fbMKkd4vzsbEhKbous16Y>).

The former patent claims constructions built on Skałba equalities. A Skałba
equality is an identity `g(X₁(t))·g(X₂(t))·g(X₃(t)) = U(t)²` between rational
functions: it forces some `g(Xᵢ(t))` to be square at every `t`, hence some
`Xᵢ(t)` to be an abscissa on the curve. Simplified SWU satisfies
`g(X₁(t))·g(X₂(t)) = Z·U(t)²`, so a third polynomial completing a Skałba
equality would need `g(X₃(t)) = Z` identically; criterion 3 makes `Z` miss
the image of `g` on `F`, so no such `X₃` exists and the mapping stays outside
the claimed three-polynomial form. Criterion 2 avoids the second patent's
`q ≡ 3 (mod 4)` variant, which fixes `Z = -1`. The criteria exclude the
original parameters of the literature —the simplified SWU of Brier et al.
(<https://eprint.iacr.org/2009/340>) is the `Z = -1` case, and Wahby–Boneh
(<https://eprint.iacr.org/2019/403>) choose `ξ = -1` for BLS12-381— so they
are strictly narrower than what is mathematically necessary, and no proof in
this development depends on them.
-/

namespace CompElliptic.Hashing

open CompElliptic.Fields

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- In a finite field, a nonsquare times a nonsquare is a square: the quadratic
character is multiplicative and takes the value `-1` on exactly the nonsquares,
so the product's character is `(-1)·(-1) = 1`. (In characteristic 2 the
hypothesis `¬ IsSquare a` is vacuous —every element is a square— so no
characteristic assumption is needed.) -/
theorem isSquare_mul_of_not_isSquare {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, (mul_zero 0).symm⟩)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ ⟨0, (mul_zero 0).symm⟩)
  have hχa : quadraticChar F a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have hχb : quadraticChar F b = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  refine (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).mp ?_
  rw [map_mul, hχa, hχb]
  ring

/-- `sqrt_ratio` of protocol spec §5.4.9.8: `(√(num/div), 1)` when `num/div` is
square, else `(√(lam·num/div), 0)` for the fixed nonsquare `lam`. The square
root is the Tonelli–Shanks root; the spec permits any root and any nonsquare
`lam`, and its output-independence note is what licenses fixing them. -/
def sqrtRatio (d : TonelliShanks F) (lam num div : F) : F × Bool :=
  match d.sqrt? (num / div) with
  | some r => (r, true)
  | none => ((d.sqrt? (lam * (num / div))).getD 0, false)

/-- The `Bool` component of `sqrt_ratio` reports squareness of the ratio. -/
theorem sqrtRatio_true_iff (d : TonelliShanks F) (lam num div : F) :
    (sqrtRatio d lam num div).2 = true ↔ IsSquare (num / div) := by
  rcases hs : d.sqrt? (num / div) with _ | r
  · simp only [sqrtRatio, hs]
    exact iff_of_false (by simp) fun hsq => by
      obtain ⟨r, hr⟩ := TonelliShanks.sqrt?_isSome_of_isSquare d hsq
      rw [hs] at hr
      cases hr
  · simp only [sqrtRatio, hs]
    exact iff_of_true trivial ⟨r, (TonelliShanks.sqrt?_mul_self d hs).symm⟩

/-- In the square case, `sqrt_ratio` returns a square root of the ratio. -/
theorem sqrtRatio_true_sq (d : TonelliShanks F) {lam num div : F}
    (h : (sqrtRatio d lam num div).2 = true) :
    (sqrtRatio d lam num div).1 * (sqrtRatio d lam num div).1 = num / div := by
  rcases hs : d.sqrt? (num / div) with _ | r
  · rw [sqrtRatio, hs] at h ⊢
    cases h
  · rw [sqrtRatio, hs]
    exact TonelliShanks.sqrt?_mul_self d hs

/-- In the nonsquare case, `sqrt_ratio` returns a square root of `lam` times the
ratio — never `⊥`, as the spec notes: the ratio is a nonzero nonsquare there, so
multiplying by the nonsquare `lam` makes it a square. -/
theorem sqrtRatio_false_sq (d : TonelliShanks F)
    {lam : F} (hlam : ¬ IsSquare lam) {num div : F}
    (h : (sqrtRatio d lam num div).2 = false) :
    (sqrtRatio d lam num div).1 * (sqrtRatio d lam num div).1
      = lam * (num / div) := by
  rcases hs : d.sqrt? (num / div) with _ | r
  · have hns : ¬ IsSquare (num / div) := fun hsq => by
      obtain ⟨r, hr⟩ := TonelliShanks.sqrt?_isSome_of_isSquare d hsq
      rw [hs] at hr
      cases hr
    obtain ⟨r, hr⟩ := TonelliShanks.sqrt?_isSome_of_isSquare d
      (isSquare_mul_of_not_isSquare hlam hns)
    rw [sqrtRatio, hs]
    simp only [hr, Option.getD_some]
    exact TonelliShanks.sqrt?_mul_self d hr
  · rw [sqrtRatio, hs] at h
    cases h

open CompElliptic.CurveForms.ShortWeierstrass in
/-- Parameters for `map_to_curve_simple_swu` onto a curve `E` with `A·B ≠ 0`
(protocol spec §5.4.9.8): the mapping's nonsquare `Z`; the `sqrt_ratio` data
—Tonelli–Shanks square-root data `d` and the arbitrary nonsquare `lam`—; the
precomputed `θ` with `θ²·lam = Z`; and the sign function used by the final
parity-matching step (`sgn0` for the deployed prime fields).

The record also certifies RFC 9380's four criteria on `Z`
(<https://www.rfc-editor.org/rfc/rfc9380.html#section-6.6.2>): criterion 1 is
`Z_nonsquare`, and criteria 2–4 are `crit2`–`crit4`, with `crit3` stated as
root-freeness of `g(X) - Z` (for a cubic, the RFC's irreducibility). The
module documentation records the criteria's roles and the patent-avoidance
provenance of criteria 2 and 3, which no proof consumes. -/
structure SSWUParams (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  E : SWCurve F
  A_nonzero : E.A ≠ 0
  Z : F
  Z_nonsquare : ¬ IsSquare Z
  d : TonelliShanks F
  lam : F
  lam_nonsquare : ¬ IsSquare lam
  θ : F
  θ_spec : θ * θ * lam = Z
  sgn : F → Bool
  crit2 : Z ≠ -1
  crit3 : ∀ x : F, x ^ 3 + E.A * x + E.B ≠ Z
  crit4 : IsSquare ((E.B / (Z * E.A))^3 + E.A * (E.B / (Z * E.A)) + E.B)

namespace SSWUParams

open CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The nonsquare `Z` is in particular nonzero (zero is a square). -/
theorem Z_nonzero (G : SSWUParams F) : G.Z ≠ 0 :=
  fun h => G.Z_nonsquare (h ▸ ⟨0, (mul_zero 0).symm⟩)

/-- The coordinates of `map_to_curve_simple_swu` before its final step: the
spec's steps with the spec's intermediate names, keeping the candidate ordinate
`y'` that the sign-matching step would overwrite. Splitting the definition here
diverges slightly from the spec's single list, but the composition `mapXY` is
step-for-step the spec's, and the split is what lets the mapping be analysed as
a signed lift (`map_eq_signedLift`). -/
def mapXYUpToSign (G : SSWUParams F) (u : F) : F × F :=
  let Zuu := G.Z * u^2
  let ta := Zuu^2 + Zuu
  let x1num := G.E.B * (ta + 1)
  let xdiv := G.E.A * (if ta = 0 then G.Z else -ta)
  let U := (x1num^2 + G.E.A * xdiv^2) * x1num + G.E.B * xdiv^3
  let x2num := Zuu * x1num
  let sr := sqrtRatio G.d G.lam U (xdiv^3)
  let y1 := sr.1
  let y2 := G.θ * Zuu * u * y1
  let xnum := if sr.2 then x1num else x2num
  let y' := if sr.2 then y1 else y2
  (xnum / xdiv, y')

/-- The coordinates of `map_to_curve_simple_swu` (spec §5.4.9.8): `mapXYUpToSign`,
then the sign-matching step on the candidate ordinate. -/
def mapXY (G : SSWUParams F) (u : F) : F × F :=
  let p := G.mapXYUpToSign u
  (p.1, if G.sgn p.2 = G.sgn u then p.2 else -p.2)

/-- **`map_to_curve_simple_swu` lands on the curve** — moreover always on an
affine point, never the identity. See the module docstring for the shape of the
argument. -/
theorem onCurve_mapXY (G : SSWUParams F) (u : F) :
    OnCurve G.E.A G.E.B (G.mapXY u) := by
  simp only [mapXY, mapXYUpToSign]
  set Zuu := G.Z * u^2 with hZuu
  set ta := Zuu^2 + Zuu with hta
  set x1num := G.E.B * (ta + 1) with hx1num
  set xdiv := G.E.A * (if ta = 0 then G.Z else -ta) with hxdiv
  set U := (x1num^2 + G.E.A * xdiv^2) * x1num + G.E.B * xdiv^3 with hU
  set x2num := Zuu * x1num with hx2num
  set sr := sqrtRatio G.d G.lam U (xdiv^3) with hsr
  have hxdiv0 : xdiv ≠ 0 := by
    rw [hxdiv]
    split_ifs with h
    · exact mul_ne_zero G.A_nonzero G.Z_nonzero
    · exact mul_ne_zero G.A_nonzero (neg_ne_zero.mpr h)
  -- The sign-matching step does not change the square of the ordinate.
  have hsign : ∀ y' : F, (if G.sgn y' = G.sgn u then y' else -y')^2 = y'^2 := by
    intro y'
    split_ifs <;> ring
  -- Reduce the curve equation at `xnum/xdiv` to its cleared form.
  have hcleared : ∀ xnum y : F,
      y^2 * xdiv^3 = xnum^3 + G.E.A * xnum * xdiv^2 + G.E.B * xdiv^3 →
      OnCurve G.E.A G.E.B (xnum / xdiv, y) := by
    intro xnum y h
    unfold OnCurve
    field_simp
    linear_combination h
  by_cases hb : sr.2
  · -- Square branch: the curve equation at `x1num/xdiv` is the definition of `U`.
    have h1 : sr.1 * sr.1 = U / xdiv^3 := sqrtRatio_true_sq G.d hb
    have h1c : sr.1^2 * xdiv^3 = U := by
      rw [sq, h1, div_mul_cancel₀ _ (pow_ne_zero 3 hxdiv0)]
    have hx : (if sr.2 then x1num else x2num) = x1num := by simp [hb]
    have hy : (if sr.2 then sr.1 else G.θ * Zuu * u * sr.1) = sr.1 := by simp [hb]
    rw [hx, hy]
    refine hcleared x1num _ ?_
    rw [hsign sr.1, h1c, hU]
    ring
  · -- Nonsquare branch.
    have hbf : sr.2 = false := Bool.eq_false_iff.mpr hb
    have h2 : sr.1 * sr.1 = G.lam * (U / xdiv^3) :=
      sqrtRatio_false_sq G.d G.lam_nonsquare hbf
    have h2c : sr.1^2 * xdiv^3 = G.lam * U := by
      rw [sq, h2, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 3 hxdiv0)]
    by_cases hta0 : ta = 0
    · -- Exceptional case: criterion 4 makes the ratio a square, contradiction.
      exfalso
      have hxd : xdiv = G.E.A * G.Z := by rw [hxdiv, if_pos hta0]
      have hx1 : x1num = G.E.B := by rw [hx1num, hta0]; ring
      have hA : G.E.A ≠ 0 := G.A_nonzero
      have hZ : G.Z ≠ 0 := G.Z_nonzero
      have hratio : U / xdiv^3
          = (G.E.B / (G.Z * G.E.A))^3 + G.E.A * (G.E.B / (G.Z * G.E.A)) + G.E.B := by
        rw [hU, hxd, hx1]
        field_simp
      have := (sqrtRatio_true_iff G.d G.lam U (xdiv^3)).mpr
        (by rw [hratio]; exact G.crit4)
      rw [← hsr] at this
      exact hb this
    · -- Generic case: the `Zuu³` identity closes the algebra.
      have hxd : xdiv = G.E.A * -ta := by rw [hxdiv, if_neg hta0]
      -- The SSWU identity: special to the choice of `x1num` and `xdiv`.
      have hkey : Zuu^3 * U = x2num^3 + G.E.A * x2num * xdiv^2 + G.E.B * xdiv^3 := by
        rw [hU, hx2num, hx1num, hxd, hta]
        ring
      have hx : (if sr.2 then x1num else x2num) = x2num := by simp [hbf]
      have hy : (if sr.2 then sr.1 else G.θ * Zuu * u * sr.1)
          = G.θ * Zuu * u * sr.1 := by simp [hbf]
      rw [hx, hy]
      refine hcleared x2num _ ?_
      rw [hsign (G.θ * Zuu * u * sr.1)]
      calc (G.θ * Zuu * u * sr.1)^2 * xdiv^3
          = G.θ * G.θ * (Zuu^2 * u^2) * (sr.1^2 * xdiv^3) := by ring
        _ = G.θ * G.θ * (Zuu^2 * u^2) * (G.lam * U) := by rw [h2c]
        _ = (G.θ * G.θ * G.lam) * (u^2 * Zuu^2 * U) := by ring
        _ = G.Z * (u^2 * Zuu^2 * U) := by rw [G.θ_spec]
        _ = Zuu^3 * U := by rw [hZuu]; ring
        _ = x2num^3 + G.E.A * x2num * xdiv^2 + G.E.B * xdiv^3 := hkey

/-- `map_to_curve_simple_swu` as a curve point: the coordinates of `mapXY`,
which are on the curve by `onCurve_mapXY`. -/
def map (G : SSWUParams F) (u : F) : SWPoint G.E :=
  ⟨(G.mapXY u).1, (G.mapXY u).2, Or.inl (G.onCurve_mapXY u)⟩

/-! ## The signed-lift structure of the mapping

The last step of `mapXY` is RFC 9380's sign matching, which `signedLift`
isolates. Packaging the earlier steps as the candidate point `candidateMap`
exhibits `map` as a signed lift (`map_eq_signedLift`), and oddness away from
`0` follows from `signedLift_neg`: the candidate is even up to the sign
carried by the nonsquare branch's bare factor of `u`. -/

/-- The candidate coordinates are representable: `mapXY u` is on the curve,
and its ordinate is the candidate's up to sign, so the squares agree. -/
theorem valid_pre (G : SSWUParams F) (u : F) :
    Valid G.E.A G.E.B (G.mapXYUpToSign u) := by
  left
  have h : OnCurve G.E.A G.E.B (G.mapXY u) := G.onCurve_mapXY u
  have heq : G.mapXY u = ((G.mapXYUpToSign u).1,
      if G.sgn (G.mapXYUpToSign u).2 = G.sgn u
      then (G.mapXYUpToSign u).2 else -(G.mapXYUpToSign u).2) := rfl
  rw [heq] at h
  simp only [OnCurve] at h ⊢
  split_ifs at h
  · exact h
  · rwa [neg_sq] at h

/-- `mapXYUpToSign`, packaged as a curve point: the candidate that the sign-matching
step corrects. -/
def candidateMap (G : SSWUParams F) (u : F) : SWPoint G.E :=
  ⟨(G.mapXYUpToSign u).1, (G.mapXYUpToSign u).2, G.valid_pre u⟩

/-- `map` is the signed lift of the candidate `candidateMap`. -/
theorem map_eq_signedLift (G : SSWUParams F) (u : F) :
    G.map u = signedLift G.candidateMap G.sgn u := by
  apply SWPoint.ext_pair
  rw [show ((G.map u).x, (G.map u).y) = G.mapXY u from rfl]
  simp only [signedLift, candidateMap, mapXY]
  split_ifs <;> rfl

/-- The candidate map is even up to sign: the square branch is even in the
input, and the nonsquare branch is odd — its candidate root carries a bare
factor of `u`. -/
theorem candidateMap_neg (G : SSWUParams F) (u : F) :
    G.candidateMap (-u) = G.candidateMap u ∨ G.candidateMap (-u) = -(G.candidateMap u) := by
  have hx : (G.candidateMap (-u)).x = (G.candidateMap u).x := by
    simp only [candidateMap, mapXYUpToSign, neg_sq]
  have hy : (G.candidateMap (-u)).y = (G.candidateMap u).y
      ∨ (G.candidateMap (-u)).y = -(G.candidateMap u).y := by
    simp only [candidateMap, mapXYUpToSign, neg_sq]
    split_ifs <;> first
      | exact Or.inl rfl
      | exact Or.inr (by ring)
  rcases hy with h | h
  · exact Or.inl (SWPoint.ext_pair (by rw [hx, h]))
  · exact Or.inr (SWPoint.ext_pair
      (by rw [SWPoint.neg_x, SWPoint.neg_y, hx, h]))

/-- The mapping is odd away from `0`, by `signedLift_neg`. -/
theorem map_neg (G : SSWUParams F) (hsgn : IsSignFunction G.sgn) {u : F}
    (hu : u ≠ 0) : G.map (-u) = -(G.map u) := by
  rw [map_eq_signedLift, map_eq_signedLift]
  exact signedLift_neg G.candidateMap_neg hsgn hu

end SSWUParams

end CompElliptic.Hashing
