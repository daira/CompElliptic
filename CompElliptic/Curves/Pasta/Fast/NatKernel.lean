/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
/-!
# Core-only `Nat` kernel for Vesta group arithmetic

Zero-import transplant of the proven `paddFast` arithmetic
(`CompElliptic/Curves/Pasta/Fast/Projective.lean`, RCB complete addition over raw canonical
`ℕ` representatives, Vesta `a = 0, b = 5`), plus the ladder, scatter Pippenger MSM,
and radix-2 DIT FFT built from it. `CompElliptic.Curves.Pasta.Fast.NatKernelEquiv` proves every
operation here computes the corresponding statement-surface function.

This module imports nothing beyond Lean core, so it sits in the `FastFieldNative`
`precompileModules` lane (see the lakefile); all proofs about it live in the sibling
`NatKernelEquiv.lean`, which is mathlib-side and therefore *not* in that lane.

It is also the PROOF INTERMEDIARY for the faster Montgomery tier: the kernels of
`CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs` mirror these schedules operation for
operation, and their correctness (`CompElliptic.Curves.Pasta.Fast.ProjectiveMontEquiv`) is
proven by transport against this kernel rather than from scratch. So it is load-bearing even
where nothing evaluates it — do not delete it as dead code.
-/

namespace CompElliptic.Curves.Pasta.Fast.NatKernel

/-- The Vesta base-field prime (= `CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD`),
as a literal so this module needs no imports. -/
def qv : Nat := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

@[inline] def fadd (a b : Nat) : Nat := (a + b) % qv
@[inline] def fmul (a b : Nat) : Nat := (a * b) % qv
@[inline] def fsub (a b : Nat) : Nat := (a + (qv - b % qv)) % qv

/-- Projective Vesta point over canonical `Nat` representatives. -/
structure P3 where
  x : Nat
  y : Nat
  z : Nat

/-- `Array.get!`/`Array.set!` need a default; the projective identity is the right one, so a
bucket that is never hit reads back as `pid` and contributes nothing. -/
instance : Inhabited P3 := ⟨⟨0, 1, 0⟩⟩

/-- Projective identity `(0 : 1 : 0)`. -/
def pid : P3 := ⟨0, 1, 0⟩

/-- RCB complete addition, transplanted verbatim from `paddFast`. -/
def padd (P Q : P3) : P3 :=
  let x1 := P.x; let y1 := P.y; let z1 := P.z
  let x2 := Q.x; let y2 := Q.y; let z2 := Q.z
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
  ⟨X3, Y3, Z3⟩

/-- Binary double-and-add over a fixed 256-bit window (Pasta scalars fit). -/
def pnsmul (n : Nat) (p : P3) : P3 :=
  (List.range 256).foldl
    (fun (st : P3 × P3) i =>
      let acc := if (n >>> i) &&& 1 = 1 then padd st.1 st.2 else st.1
      (acc, padd st.2 st.2))
    (pid, p) |>.1

/-- One Array-scatter step: digit-`0` terms contribute nothing, any other digit `d` `padd`s the
point into bucket slot `d − 1` (slot `k` holds bucket `k + 1`). -/
def scatterStep (a : Array P3) (p : Nat × P3) : Array P3 :=
  if p.1 = 0 then a else a.modify (p.1 - 1) (fun v => padd v p.2)

/-- Scatter a digit-tagged point list into its `base − 1` buckets in ONE pass. -/
def bucketScatter (base : Nat) (dp : List (Nat × P3)) : Array P3 :=
  dp.foldl scatterStep (Array.replicate (base - 1) pid)

/-- One step of the bucket downsweep: carry `(running, total)`, `padd` the next bucket into
`running`, then `padd` `running` into `total`.  Folded from the top bucket down this computes
`Σ_{k=1..base-1} k • bucket_k` in `2 · (base − 1)` additions. -/
def accStep (a : P3) (p : P3 × P3) : P3 × P3 := (padd p.1 a, padd p.2 (padd p.1 a))

/-- The window-`i` value in base `base`: scatter the base-`base` digit-`i` tagged terms into the
`base − 1` buckets in one pass, then run the suffix-sum downsweep. -/
def windowValue (base i : Nat) (terms : List (Nat × P3)) : P3 :=
  let scale := base ^ i
  (List.foldr accStep (pid, pid)
    (bucketScatter base (terms.map fun t => (t.1 / scale % base, t.2))).toList).2

/-- `c`-fold doubling — the `base •` Horner step between adjacent windows. -/
def pdoublings (c : Nat) (p : P3) : P3 := (List.range c).foldl (fun a _ => padd a a) p

/-- Windowed Pippenger MSM, window `c`: per-window Array-scatter buckets, bucket
downsweep, Horner recombination (`c` doublings between adjacent windows). -/
def msm (c : Nat) (terms : List (Nat × P3)) : P3 :=
  let numWindows := (256 + c - 1) / c
  let base := 2 ^ c
  ((List.range numWindows).map fun i => windowValue base i terms).foldr
    (fun v acc => padd (pdoublings c acc) v) pid

/-! ## Projective negation and the radix-2 DIT FFT

The butterfly `(a, b) ↦ (a + tw·b, a − tw·b)` of `bestFftG`
(`Zcash/Arithmetic/Fft.lean`), transplanted onto `P3`: the group addition is `padd`,
the scalar action is `pnsmul`, and the subtraction is `padd` against `pneg`.  Twiddles arrive
as canonical `Nat` scalars (`Fp.val`), computed by the caller, so this module still needs no
imports. -/

/-- Projective negation: `-(x : y : z) = (x : −y : z)` on a short-Weierstrass curve. -/
@[inline] def pneg (p : P3) : P3 := ⟨p.x, fsub 0 p.y, p.z⟩

/-- Bit-reversal permutation index, transplanted from `Zcash.Snark.Keygen.bitreverse`. -/
def bitreverse (n l : Nat) : Nat := Id.run do
  let mut r := 0
  let mut m := n
  for _ in [0:l] do
    r := (r <<< 1) ||| (m &&& 1)
    m := m >>> 1
  return r

/-- In-place radix-2 DIT FFT over `P3`, mirroring `bestFftG`: bit-reversal permutation, then
`logN` rounds of decimation-in-time butterflies against the precomputed twiddle scalars `tw`
(`tw[i] = (omega ^ i).val`, `i < n / 2`). -/
def fft (a0 : Array P3) (tw : Array Nat) (logN : Nat) : Array P3 := Id.run do
  let n := a0.size
  let mut a := a0
  -- bit-reversal permutation
  for k in [0:n] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  -- `logN` rounds of butterflies
  let mut half := 1
  for _ in [0:logN] do
    let chunk := 2 * half
    let twiddleChunk := n / chunk
    for c in [0:n / chunk] do
      let s := c * chunk
      for j in [0:half] do
        let twdl := tw[j * twiddleChunk]!
        let aIdx := s + j
        let bIdx := s + half + j
        let aOld := a[aIdx]!
        let t := pnsmul twdl a[bIdx]!
        a := a.set! aIdx (padd aOld t)
        a := a.set! bIdx (padd aOld (pneg t))
    half := chunk
  return a

end CompElliptic.Curves.Pasta.Fast.NatKernel
