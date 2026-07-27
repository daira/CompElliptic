/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs

/-!
# Vesta projective point arithmetic over Montgomery limbs: runtime definitions (core-only)

The projective Vesta arithmetic of `CompElliptic.Curves.Pasta.Fast.Projective` and the Pippenger
schedules of `CompElliptic.Curves.Pasta.Fast.MsmProj`, transcribed operation for operation onto
eight-limb Montgomery residues so that they can be native-compiled (the `FastFieldNative` lane in
the lakefile — hence no imports beyond Lean core, and no proofs here). Every operation is proven
to compute its `𝔽_q`-valued counterpart in `CompElliptic.Curves.Pasta.Fast.ProjectiveMontEquiv`.

The `Fast` interfaces are provisional: they are not guaranteed to remain public, and
may be folded into the existing API or otherwise changed incompatibly.
-/

namespace CompElliptic.Curves.Pasta.Fast.ProjectiveMont

open Montgomery.Native64x8 (Limbs8)
open Montgomery.Native64x8.VestaFq

/-- A projective point in `(X : Y : Z)` coordinates, each coordinate an eight-limb Montgomery
residue of the Vesta base field. -/
structure PM where
  /-- The `X` coordinate. -/
  X : Limbs8
  /-- The `Y` coordinate. -/
  Y : Limbs8
  /-- The `Z` coordinate. -/
  Z : Limbs8
deriving DecidableEq

namespace PM

/-- `Array.get!`/`set!` need a default; the projective identity is the right one. -/
instance : Inhabited PM := ⟨⟨zero, one, zero⟩⟩

/-- The Montgomery residue of `3`. -/
def c3 : Limbs8 := ofNat 3
/-- The Montgomery residue of `15` (`b3 = 3b` for Vesta). -/
def c15 : Limbs8 := ofNat 15
/-- The Montgomery residue of `30`. -/
def c30 : Limbs8 := ofNat 30
/-- The Montgomery residue of `45`. -/
def c45 : Limbs8 := ofNat 45
/-- The Montgomery residue of `225`. -/
def c225 : Limbs8 := ofNat 225

/-- Renes–Costello–Batina complete addition (`add-2015-rcb`, `a = 0`, `b3 = 15`), on
Montgomery limbs. -/
@[inline] def padd (P Q : PM) : PM where
  X :=
    sub (sub (add (sub (sub (mul (mul (P.X) (P.Y)) (square (Q.Y))) (mul (mul (mul (c15) (P.X))
      (P.Y)) (square (Q.Z)))) (mul (mul (mul (mul (c30) (P.X)) (P.Z)) (Q.Y)) (Q.Z))) (mul (mul
      (square (P.Y)) (Q.X)) (Q.Y))) (mul (mul (mul (c15) (square (P.Z))) (Q.X)) (Q.Y))) (mul
      (mul (mul (mul (c30) (P.Y)) (P.Z)) (Q.X)) (Q.Z))
  Y :=
    sub (add (add (mul (square (P.Y)) (square (Q.Y))) (mul (mul (mul (c45) (square (P.X)))
      (Q.X)) (Q.Z))) (mul (mul (mul (c45) (P.X)) (P.Z)) (square (Q.X)))) (mul (mul (c225)
      (square (P.Z))) (square (Q.Z)))
  Z :=
    add (add (add (add (add (mul (mul (square (P.Y)) (Q.Y)) (Q.Z)) (mul (mul (P.Y) (P.Z))
      (square (Q.Y)))) (mul (mul (mul (c3) (square (P.X))) (Q.X)) (Q.Y))) (mul (mul (mul (c3)
      (P.X)) (P.Y)) (square (Q.X)))) (mul (mul (mul (c15) (P.Y)) (P.Z)) (square (Q.Z)))) (mul
      (mul (mul (c15) (square (P.Z))) (Q.Y)) (Q.Z))

/-- The projective identity `𝒪 = (0 : 1 : 0)`. -/
def pid : PM := ⟨zero, one, zero⟩

/-! ## Group kernels

Mirroring `MsmProj`'s schedules step for step: only the interpretation of a coordinate changes,
never the schedule, so the correctness proofs stay structural inductions. -/

/-- Fixed 256-step LSB-first double-and-add ladder. -/
def pnsmul (n : Nat) (p : PM) : PM :=
  (List.range 256).foldl
    (fun (st : PM × PM) i =>
      let acc := if (n >>> i) &&& 1 = 1 then padd st.1 st.2 else st.1
      (acc, padd st.2 st.2))
    (pid, p) |>.1

/-- One Array-scatter step (mirrors `MsmProj.pscatterStep`). -/
def scatterStep (a : Array PM) (p : Nat × PM) : Array PM :=
  if p.1 = 0 then a else a.modify (p.1 - 1) (fun v => padd v p.2)

/-- Scatter a digit-tagged point list into its `base − 1` buckets in ONE pass. -/
def bucketScatter (base : Nat) (dp : List (Nat × PM)) : Array PM :=
  dp.foldl scatterStep (Array.replicate (base - 1) pid)

/-- One step of the bucket downsweep (mirrors `MsmProj.paccStep`). -/
def accStep (a : PM) (p : PM × PM) : PM × PM := (padd p.1 a, padd p.2 (padd p.1 a))

/-- The window-`i` value in base `base` (mirrors `MsmProj.pwindowValueFast`). -/
def windowValue (base i : Nat) (terms : List (Nat × PM)) : PM :=
  let scale := base ^ i
  (List.foldr accStep (pid, pid)
    (bucketScatter base (terms.map fun t => (t.1 / scale % base, t.2))).toList).2

/-- `c`-fold doubling — the `base •` Horner step between adjacent windows. -/
def pdoublings (c : Nat) (p : PM) : PM := (List.range c).foldl (fun a _ => padd a a) p

/-- Windowed Pippenger MSM, window `c` (mirrors `MsmProj.pippengerProjScatter`, with the window
count fixed at `⌈256 / c⌉` and the `base •` step spelled as `c` doublings). -/
def msm (c : Nat) (terms : List (Nat × PM)) : PM :=
  let numWindows := (256 + c - 1) / c
  let base := 2 ^ c
  ((List.range numWindows).map fun i => windowValue base i terms).foldr
    (fun v acc => padd (pdoublings c acc) v) pid

/-- Projective negation: `-(X : Y : Z) = (X : −Y : Z)`. -/
@[inline] def pneg (p : PM) : PM := ⟨p.X, sub zero p.Y, p.Z⟩

end PM

end CompElliptic.Curves.Pasta.Fast.ProjectiveMont
