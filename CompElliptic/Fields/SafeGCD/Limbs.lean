/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Fields.SafeGCD.Divsteps62

/-!
# The signed-radix-`2 ^ 62` limb layer, ported and checked

The remaining kernels of the Rust module: the multi-limb arithmetic that `divsteps_62_var`
feeds, and the driver that ties it together. Where
`CompElliptic.Fields.SafeGCD.Reference` applies a batch's transition to `(f, g)` and `(d, e)`
as single integers, these apply it limb by limb, in signed radix `2 ^ 62` over five limbs,
exactly as the Rust does.

## How the Rust types are modelled

* `[i64; 5]` becomes `Signed62`, five `Int` limbs. Every value the Rust holds in an `i64` or an
  `i128` is in range there, so plain `Int` arithmetic is faithful; the places where the Rust
  genuinely relies on wrapping are the ones that go through `UInt64` below.
* `(x as u64 & MASK62) as i64` becomes `low62`, and the arithmetic shift `x >>= 62` becomes
  `shr62`. Lean's `%` and `/` on `Int` are Euclidean, so for the positive divisor `2 ^ 62` they
  are exactly the non-negative-remainder mask and the floor-division shift, and
  `low62_add_shr62` records the decomposition they satisfy.
* the sign masks `x >> 63` (which yield `0` or `-1`) become the conditionals they stand for, and
  `x & mask` with such a mask becomes the corresponding `if`.
* `pack62`, `unpack62` and the sign-folding in `shrink_len` operate on `u64` bit patterns, so
  they go through `UInt64` and `toI64` / `toU64`.

## Provenance

Ported from `src/fields/modinv62.rs` of
[zcash/pasta_curves#119](https://github.com/zcash/pasta_curves/pull/119), pinned at commit
`9299dfbb19978428ba24229bc13dff25a424dc46` (branch `modinv62`). Every `Rust:` link on a
declaration below points into that commit, so the line numbers stay valid even after the branch
moves; to review against the tip of the branch instead, open the pull request and diff.

## What is checked

Nothing here is proved; it is checked against what is. The end-to-end check is
`limbInvertCounted` against the proved `invertCounted`, on the port's own regression vectors and
on pseudo-random inputs, both the value and the batch count. Beneath that, the Rust test
module's own differential obligations are reproduced: the sparse-modulus kernels against a
generic-modulus reference that multiplies by every limb (`refUpdateDe`), the first-batch and
terminal specializations against the general ones, `normalize62` against a reference reduction,
and the `pack62` / `unpack62` round trip.

That split is deliberate. The limb layer is a *representation* of the integers the proof is
about, so the honest claim for it is agreement with the proved layer, not a second proof.
-/

namespace CompElliptic.Fields.SafeGCD

/-! ## Words and limbs -/

/-- `MASK62`, the low 62 bits of a word.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L50-L51> -/
def mask62 : UInt64 := ((1 : UInt64) <<< (62 : UInt64)) - 1

/-- `(x as u64 & MASK62) as i64`: the low 62 bits of a two's-complement value, as a
non-negative integer. -/
def low62 (x : Int) : Int := x % 2 ^ 62

/-- `x >>= 62` on a signed value: an arithmetic shift, that is, floor division. -/
def shr62 (x : Int) : Int := x / 2 ^ 62

/-- The two agree with the radix decomposition, which is what makes the limb loops exact. -/
theorem low62_add_shr62 (x : Int) : 2 ^ 62 * shr62 x + low62 x = x := by
  unfold low62 shr62; omega

/-- A signed multi-word integer in radix `2 ^ 62`, least-significant limb first: the Rust
`Signed62([i64; 5])`. In canonical form every limb below the active length is in
`[0, 2 ^ 62)` and the top active limb carries the sign.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L107-L112> -/
structure Signed62 where
  /-- The five limbs, least-significant first. -/
  limbs : Array Int
deriving DecidableEq, Repr, Inhabited

namespace Signed62

/-- Limb `i`, or `0` out of range. -/
def get (s : Signed62) (i : Nat) : Int := s.limbs.getD i 0

/-- Replace limb `i`. -/
def set (s : Signed62) (i : Nat) (v : Int) : Signed62 := ⟨s.limbs.set! i v⟩

/-- Build from a list of limbs. -/
def ofList (l : List Int) : Signed62 := ⟨l.toArray⟩

/-- The all-zero value. -/
def zero : Signed62 := ofList [0, 0, 0, 0, 0]

/-- The integer denoted by the limbs. -/
def val (s : Signed62) : Int :=
  s.get 0 + 2 ^ 62 * s.get 1 + 2 ^ 124 * s.get 2 + 2 ^ 186 * s.get 3 + 2 ^ 248 * s.get 4

end Signed62

/-- The per-field constants the kernels need: the Rust `InvParams` trait.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L53-L66> -/
structure LimbParams where
  /-- The modulus in signed radix `2 ^ 62`, least-significant limb first. -/
  modulus : Signed62
  /-- `m⁻¹ mod 2 ^ 62`. -/
  mu : UInt64
  /-- `R ^ 2 mod m` in signed radix `2 ^ 62`: the initial `e`. -/
  r2 : Signed62
deriving Repr, Inhabited

/-! ## `pack62` and `unpack62` -/

/-- Repack a canonical `4 x 64`-bit little-endian representation into signed radix `2 ^ 62`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L233-L248> -/
def pack62 (x : Array UInt64) : Signed62 :=
  let x0 := x.getD 0 0
  let x1 := x.getD 1 0
  let x2 := x.getD 2 0
  let x3 := x.getD 3 0
  Signed62.ofList
    [ (x0 &&& mask62).toNat
    , (((x0 >>> 62) ||| (x1 <<< 2)) &&& mask62).toNat
    , (((x1 >>> 60) ||| (x2 <<< 4)) &&& mask62).toNat
    , (((x2 >>> 58) ||| (x3 <<< 6)) &&& mask62).toNat
    , (x3 >>> 56).toNat ]

/-- Repack a canonical signed-62 value in `[0, m)` back into `4 x 64` bits.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L250-L268> -/
def unpack62 (v : Signed62) : Array UInt64 :=
  let v0 := toU64 (v.get 0)
  let v1 := toU64 (v.get 1)
  let v2 := toU64 (v.get 2)
  let v3 := toU64 (v.get 3)
  let v4 := toU64 (v.get 4)
  #[ v0 ||| (v1 <<< 62)
   , (v1 >>> 2) ||| (v2 <<< 60)
   , (v2 >>> 4) ||| (v3 <<< 58)
   , (v3 >>> 6) ||| (v4 <<< 56) ]

/-! ## Applying the transition to `f` and `g` -/

/-- The limb loop of `update_fg_62_var`, carrying the two `i128` accumulators.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L412-L421> -/
def updateFgLoop (t : Trans) : Nat → Nat → Signed62 → Signed62 → Int → Int →
    Signed62 × Signed62 × Int × Int
  | 0, _, f, g, cf, cg => (f, g, cf, cg)
  | n + 1, j, f, g, cf, cg =>
      let fi := f.get j
      let gi := g.get j
      let cf' := cf + t.u * fi + t.v * gi
      let cg' := cg + t.q * fi + t.r * gi
      updateFgLoop t n (j + 1) (f.set (j - 1) (low62 cf')) (g.set (j - 1) (low62 cg'))
        (shr62 cf') (shr62 cg')

/-- Apply the transition to the full-width `f` and `g` over `len` active limbs, dividing
exactly by `2 ^ 62`: the Rust `update_fg_62_var`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L393-L426> -/
def updateFg62Var (len : Nat) (f g : Signed62) (t : Trans) : Signed62 × Signed62 :=
  let cf := t.u * f.get 0 + t.v * g.get 0
  let cg := t.q * f.get 0 + t.r * g.get 0
  let (f, g, cf, cg) := updateFgLoop t (len - 1) 1 f g (shr62 cf) (shr62 cg)
  (f.set (len - 1) cf, g.set (len - 1) cg)

/-- `update_fg_62_var` specialized to the first batch, where `f` is still the modulus
`[m0, m1, 2, 0, 64]`: the three sparse `f` limbs become shifts of the matrix entries.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L428-L479> -/
def updateFg62First (P : LimbParams) (f g : Signed62) (t : Trans) : Signed62 × Signed62 :=
  let m0 := P.modulus.get 0
  let m1 := P.modulus.get 1
  -- Limb 0.
  let cf := t.u * m0 + t.v * g.get 0
  let cg := t.q * m0 + t.r * g.get 0
  let cf := shr62 cf
  let cg := shr62 cg
  -- Limb 1.
  let cf := cf + t.u * m1 + t.v * g.get 1
  let cg := cg + t.q * m1 + t.r * g.get 1
  let f := f.set 0 (low62 cf)
  let cf := shr62 cf
  let g' := g.set 0 (low62 cg)
  let cg := shr62 cg
  -- Limb 2: `m2 = 2`.
  let cf := cf + t.u * 2 + t.v * g.get 2
  let cg := cg + t.q * 2 + t.r * g.get 2
  let f := f.set 1 (low62 cf)
  let cf := shr62 cf
  let g' := g'.set 1 (low62 cg)
  let cg := shr62 cg
  -- Limb 3: `m3 = 0`.
  let cf := cf + t.v * g.get 3
  let cg := cg + t.r * g.get 3
  let f := f.set 2 (low62 cf)
  let cf := shr62 cf
  let g' := g'.set 2 (low62 cg)
  let cg := shr62 cg
  -- Limb 4: `m4 = 64`.
  let cf := cf + t.u * 64 + t.v * g.get 4
  let cg := cg + t.q * 64 + t.r * g.get 4
  let f := f.set 3 (low62 cf)
  let cf := shr62 cf
  let g' := g'.set 3 (low62 cg)
  let cg := shr62 cg
  (f.set 4 cf, g'.set 4 cg)

/-! ## Applying the transition to the coefficients `d` and `e` -/

/-- The sign mask `x >> 63`, which is `-1` for a negative limb and `0` otherwise. -/
def signMask (x : Int) : Int := if x < 0 then -1 else 0

/-- `x & signMask y`, the Rust `u & sd`. -/
def andMask (x m : Int) : Int := if m = -1 then x else 0

/-- The `mu`-derived correction that makes a coefficient row divisible by `2 ^ 62`:
`md - ((MU * c + md) & MASK62)`, with the `u64` wrapping invisible past the 62-bit mask.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L522-L523> -/
def muCorrect (mu : UInt64) (c md : Int) : Int :=
  md - ((toI64 mu * c + md) % 2 ^ 62)

/-- Apply the transition to `d` and `e` modulo `m`, dividing exactly by `2 ^ 62`: the Rust
`update_de_62`, with the sparse modulus limbs 2 and 4 applied as shifts and limb 3 skipped.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L481-L574> -/
def updateDe62 (P : LimbParams) (d e : Signed62) (t : Trans) : Signed62 × Signed62 :=
  let sd := signMask (d.get 4)
  let se := signMask (e.get 4)
  let md := andMask t.u sd + andMask t.v se
  let me := andMask t.q sd + andMask t.r se
  let cd := t.u * d.get 0 + t.v * e.get 0
  let ce := t.q * d.get 0 + t.r * e.get 0
  let md := muCorrect P.mu cd md
  let me := muCorrect P.mu ce me
  -- Limb 0 of the modulus contribution (general multiplication).
  let cd := cd + P.modulus.get 0 * md
  let ce := ce + P.modulus.get 0 * me
  let cd := shr62 cd
  let ce := shr62 ce
  -- Limb 1 (general multiplication by `m1`).
  let cd := cd + t.u * d.get 1 + t.v * e.get 1 + P.modulus.get 1 * md
  let ce := ce + t.q * d.get 1 + t.r * e.get 1 + P.modulus.get 1 * me
  let d' := d.set 0 (low62 cd)
  let cd := shr62 cd
  let e' := e.set 0 (low62 ce)
  let ce := shr62 ce
  -- Limb 2: `m2 = 2`, so the modulus contribution is a shift.
  let cd := cd + t.u * d.get 2 + t.v * e.get 2 + md * 2
  let ce := ce + t.q * d.get 2 + t.r * e.get 2 + me * 2
  let d' := d'.set 1 (low62 cd)
  let cd := shr62 cd
  let e' := e'.set 1 (low62 ce)
  let ce := shr62 ce
  -- Limb 3: `m3 = 0`, no modulus contribution.
  let cd := cd + t.u * d.get 3 + t.v * e.get 3
  let ce := ce + t.q * d.get 3 + t.r * e.get 3
  let d' := d'.set 2 (low62 cd)
  let cd := shr62 cd
  let e' := e'.set 2 (low62 ce)
  let ce := shr62 ce
  -- Limb 4: `m4 = 64`, so the modulus contribution is a shift.
  let cd := cd + t.u * d.get 4 + t.v * e.get 4 + md * 64
  let ce := ce + t.q * d.get 4 + t.r * e.get 4 + me * 64
  let d' := d'.set 3 (low62 cd)
  let cd := shr62 cd
  let e' := e'.set 3 (low62 ce)
  let ce := shr62 ce
  (d'.set 4 cd, e'.set 4 ce)

/-- `update_de_62` specialized to the first batch, where `d = 0` (so every product against `d`
vanishes and both sign masks are zero, since the initial `e = R ^ 2` is in `[0, m)`).
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L576-L653> -/
def updateDe62First (P : LimbParams) (e : Signed62) (t : Trans) : Signed62 × Signed62 :=
  let cd := t.v * e.get 0
  let ce := t.r * e.get 0
  let md := -((toI64 P.mu * cd) % 2 ^ 62)
  let me := -((toI64 P.mu * ce) % 2 ^ 62)
  let cd := cd + P.modulus.get 0 * md
  let ce := ce + P.modulus.get 0 * me
  let cd := shr62 cd
  let ce := shr62 ce
  -- Limb 1.
  let cd := cd + t.v * e.get 1 + P.modulus.get 1 * md
  let ce := ce + t.r * e.get 1 + P.modulus.get 1 * me
  let dOut := Signed62.zero.set 0 (low62 cd)
  let cd := shr62 cd
  let eOut := Signed62.zero.set 0 (low62 ce)
  let ce := shr62 ce
  -- Limb 2: `m2 = 2`.
  let cd := cd + t.v * e.get 2 + md * 2
  let ce := ce + t.r * e.get 2 + me * 2
  let dOut := dOut.set 1 (low62 cd)
  let cd := shr62 cd
  let eOut := eOut.set 1 (low62 ce)
  let ce := shr62 ce
  -- Limb 3: `m3 = 0`.
  let cd := cd + t.v * e.get 3
  let ce := ce + t.r * e.get 3
  let dOut := dOut.set 2 (low62 cd)
  let cd := shr62 cd
  let eOut := eOut.set 2 (low62 ce)
  let ce := shr62 ce
  -- Limb 4: `m4 = 64`.
  let cd := cd + t.v * e.get 4 + md * 64
  let ce := ce + t.r * e.get 4 + me * 64
  let dOut := dOut.set 3 (low62 cd)
  let cd := shr62 cd
  let eOut := eOut.set 3 (low62 ce)
  let ce := shr62 ce
  (dOut.set 4 cd, eOut.set 4 ce)

/-- The terminal coefficient update: only the top row of the matrix, since after the final
batch only `d` feeds the result and `e` is dead. The Rust `update_d_only_62`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L655-L696> -/
def updateDOnly62 (P : LimbParams) (d e : Signed62) (u v : Int) : Signed62 :=
  let sd := signMask (d.get 4)
  let se := signMask (e.get 4)
  let md := andMask u sd + andMask v se
  let cd := u * d.get 0 + v * e.get 0
  let md := muCorrect P.mu cd md
  let cd := cd + P.modulus.get 0 * md
  let cd := shr62 cd
  let cd := cd + u * d.get 1 + v * e.get 1 + P.modulus.get 1 * md
  let d' := d.set 0 (low62 cd)
  let cd := shr62 cd
  let cd := cd + u * d.get 2 + v * e.get 2 + md * 2
  let d' := d'.set 1 (low62 cd)
  let cd := shr62 cd
  let cd := cd + u * d.get 3 + v * e.get 3
  let d' := d'.set 2 (low62 cd)
  let cd := shr62 cd
  let cd := cd + u * d.get 4 + v * e.get 4 + md * 64
  let d' := d'.set 3 (low62 cd)
  let cd := shr62 cd
  d'.set 4 cd

/-! ## Normalization, termination test, and length shrinking -/

/-- One pass of carry propagation over limbs `0` to `3`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L725-L733> -/
def propagate (r : Signed62) : Signed62 :=
  let r1 := r.get 1 + shr62 (r.get 0)
  let r0 := low62 (r.get 0)
  let r2 := r.get 2 + shr62 r1
  let r1 := low62 r1
  let r3 := r.get 3 + shr62 r2
  let r2 := low62 r2
  let r4 := r.get 4 + shr62 r3
  let r3 := low62 r3
  Signed62.ofList [r0, r1, r2, r3, r4]

/-- Add the modulus to every limb when `cond` holds; the Rust `MODULUS[i] & cond_add`. -/
def condAddModulus (P : LimbParams) (r : Signed62) (cond : Bool) : Signed62 :=
  if cond then
    Signed62.ofList (List.range 5 |>.map fun i => r.get i + P.modulus.get i)
  else r

/-- Negate every limb; the Rust `(r ^ cond_negate) - cond_negate` with `cond_negate = -1`. -/
def negateLimbs (r : Signed62) : Signed62 :=
  Signed62.ofList (List.range 5 |>.map fun i => -r.get i)

/-- Normalize `r` from `(-2m, m)` to `[0, m)`, negating first if `sign` is negative:
the Rust `normalize_62`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L698-L768> -/
def normalize62 (P : LimbParams) (r : Signed62) (sign : Int) : Signed62 :=
  let r := condAddModulus P r (r.get 4 < 0)
  let r := if sign < 0 then negateLimbs r else r
  let r := propagate r
  let r := condAddModulus P r (r.get 4 < 0)
  propagate r

/-- Whether the `len` active limbs of `g` are all zero. The Rust ORs the limbs together and
compares with zero, which is the same test.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L770-L781> -/
def isZero (g : Signed62) (len : Nat) : Bool :=
  (List.range len).all fun i => g.get i == 0

/-- Shrink the active length by one when both top limbs are pure sign extensions of the limb
below, folding their signs down. The Rust `shrink_len`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L783-L797> -/
def shrinkLen (f g : Signed62) (len : Nat) : Signed62 × Signed62 × Nat :=
  let fn := f.get (len - 1)
  let gn := g.get (len - 1)
  if len ≥ 2 && (fn == 0 || fn == -1) && (gn == 0 || gn == -1) then
    let foldDown (s : Signed62) (top : Int) : Signed62 :=
      s.set (len - 2) (toI64 (toU64 (s.get (len - 2)) ||| (toU64 top <<< 62)))
    (foldDown f fn, foldDown g gn, len - 1)
  else (f, g, len)

/-! ## The driver -/

/-- The loop of `invert_counted` over batches `2 ..= 12`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L846-L872> -/
def limbLoop (P : LimbParams) : Nat → Nat → Int → Nat → Signed62 → Signed62 → Signed62 →
    Signed62 → Option (Array UInt64 × Nat)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, batch, eta, len, f, g, d, e =>
      let (t, eta) := divsteps62Var eta (toU64 (f.get 0)) (toU64 (g.get 0))
      let (f, g) := updateFg62Var len f g t
      if isZero g len then
        let d := updateDOnly62 P d e t.u t.v
        let d := normalize62 P d (f.get (len - 1))
        some (unpack62 d, batch)
      else
        let (d, e) := updateDe62 P d e t
        let (f, g, len) := shrinkLen f g len
        limbLoop P n (batch + 1) eta len f g d e

/-- Invert a nonzero field element given by its canonical `4 x 64`-bit little-endian internal
(Montgomery) representation, reporting the batch count: the Rust `invert_counted`. The first
batch is specialized, as there `f` is the sparse modulus, `d` is zero and `0 ≤ e = R ^ 2 < m`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L807-L874> -/
def limbInvertCounted (P : LimbParams) (x : Array UInt64) : Option (Array UInt64 × Nat) :=
  if x.all (· == 0) then none
  else
    let f := P.modulus
    let g := pack62 x
    let e := P.r2
    let (t, eta) := divsteps62Var (-1) (toU64 (f.get 0)) (toU64 (g.get 0))
    let (f, g) := updateFg62First P f g t
    let (d, e) := updateDe62First P e t
    let (f, g, len) := shrinkLen f g 5
    limbLoop P 11 2 eta len f g d e

/-- The Rust `invert`: `limbInvertCounted` without the batch count.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L799-L805> -/
def limbInvert (P : LimbParams) (x : Array UInt64) : Option (Array UInt64) :=
  (limbInvertCounted P x).map Prod.fst

/-! ## A generic-modulus reference for the coefficient update

The Rust test module carries `ref_update_de`: the same coefficient update with no
specialization at all, multiplying by *every* modulus limb including the zero one. It exists so
the sparse kernels can be checked limb-exact against it rather than against themselves. Ported
here for the same purpose. -/

/-- The limb loop of `ref_update_de`, which reads `d` and `e` from captured copies.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1067-L1076> -/
def refUpdateDeLoop (t : Trans) (m : Signed62) (md me : Int) (dIn eIn : Signed62) :
    Nat → Nat → Signed62 → Signed62 → Int → Int → Signed62 × Signed62 × Int × Int
  | 0, _, d, e, cd, ce => (d, e, cd, ce)
  | n + 1, i, d, e, cd, ce =>
      let cd' := cd + t.u * dIn.get i + t.v * eIn.get i + m.get i * md
      let ce' := ce + t.q * dIn.get i + t.r * eIn.get i + m.get i * me
      refUpdateDeLoop t m md me dIn eIn n (i + 1)
        (d.set (i - 1) (low62 cd')) (e.set (i - 1) (low62 ce')) (shr62 cd') (shr62 ce')

/-- The generic-modulus coefficient update: no sparse shifts, no skipped limb, no first-batch
or terminal specialization. The Rust `ref_update_de`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1046-L1080> -/
def refUpdateDe (m : Signed62) (mu : UInt64) (d e : Signed62) (t : Trans) : Signed62 × Signed62 :=
  let sd := signMask (d.get 4)
  let se := signMask (e.get 4)
  let md := andMask t.u sd + andMask t.v se
  let me := andMask t.q sd + andMask t.r se
  let cd := t.u * d.get 0 + t.v * e.get 0
  let ce := t.q * d.get 0 + t.r * e.get 0
  let md := muCorrect mu cd md
  let me := muCorrect mu ce me
  let cd := shr62 (cd + m.get 0 * md)
  let ce := shr62 (ce + m.get 0 * me)
  let (d', e', cd, ce) := refUpdateDeLoop t m md me d e 4 1 d e cd ce
  (d'.set 4 cd, e'.set 4 ce)

/-! ## Value-level specification of `normalize62`

Unlike the kernels above, normalization has a short independent specification (reduce to the
canonical residue, negating first if asked), so it is checked against that rather than against
a second copy of itself. -/

/-- `normalize62` produced the canonical residue of `± r` and left the limbs canonical.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1529-L1568> -/
def normalizeOk (P : LimbParams) (m : Nat) (r : Signed62) (sign : Int) : Bool :=
  let out := normalize62 P r sign
  let expected := (if sign < 0 then -r.val else r.val) % (m : Int)
  out.val == expected && (List.range 5).all fun i => 0 ≤ out.get i && out.get i < 2 ^ 62

/-! ## Walking a real inversion, checking every specialization

Each specialized kernel is checked against the general one at every batch of a real inversion,
which is where the states that actually arise live: `update_fg_62_first` against
`update_fg_62_var`, `update_de_62_first` and `update_de_62` against `refUpdateDe`, and
`update_d_only_62` against the `d` row of `refUpdateDe` at the terminal batch. -/

/-- The batch loop of the specialization check; mirrors `limbLoop`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1412-L1527> -/
def specializationsLoop (P : LimbParams) : Nat → Int → Nat → Signed62 → Signed62 → Signed62 →
    Signed62 → Bool
  | 0, _, _, _, _, _, _ => false
  | n + 1, eta, len, f, g, d, e =>
      let (t, eta) := divsteps62Var eta (toU64 (f.get 0)) (toU64 (g.get 0))
      let (f, g) := updateFg62Var len f g t
      let generic := refUpdateDe P.modulus P.mu d e t
      if isZero g len then
        updateDOnly62 P d e t.u t.v == generic.1
      else if updateDe62 P d e t != generic then false
      else
        let (f, g, len) := shrinkLen f g len
        specializationsLoop P n eta len f g generic.1 generic.2

/-- Every specialized kernel is limb-exact against the general one, at every batch of the
inversion of `x`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1460-L1503> -/
def specializationsAgree (P : LimbParams) (x : Array UInt64) : Bool :=
  let f := P.modulus
  let g := pack62 x
  let (t, eta) := divsteps62Var (-1) (toU64 (f.get 0)) (toU64 (g.get 0))
  let firstFgOk := updateFg62First P f g t == updateFg62Var 5 f g t
  let firstDeOk := updateDe62First P P.r2 t == refUpdateDe P.modulus P.mu Signed62.zero P.r2 t
  let (f, g) := updateFg62First P f g t
  let (d, e) := updateDe62First P P.r2 t
  let (f, g, len) := shrinkLen f g 5
  firstFgOk && firstDeOk && specializationsLoop P 11 eta len f g d e

end CompElliptic.Fields.SafeGCD
