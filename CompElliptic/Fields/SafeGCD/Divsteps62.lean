/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Fields.SafeGCD.Reference

/-!
# The batched 62-divstep kernel, ported and checked against the recurrence

`CompElliptic.Fields.SafeGCD.Divstep` runs divsteps one at a time over `ℤ`, which is what the
correctness proof is about. Implementations do not: they run a *batch* of 62 divsteps on the
bottom words of `f` and `g` alone, in 64-bit wrapping arithmetic, accumulating the transition
matrix, and only then apply that matrix once at full width. That batching kernel is
libsecp256k1's `secp256k1_modinv64_divsteps_62_var`, ported for the Pasta fields in
[zcash/pasta_curves#119](https://github.com/zcash/pasta_curves/pull/119) as
`divsteps_62_var`.

`divsteps62Var` below is a transcription of that function into Lean, with `UInt64` standing for
`u64` (both wrap modulo `2 ^ 64`) and `Int` for `i64` where the Rust value is exact.

It is not proved equal to `run 62`; it is *checked* against it. Three things make that check
sharp:

* the kernel compresses a variable number of divsteps into each inner iteration: a
  trailing-zero count batches the halvings, and a small modular-inverse identity cancels up to
  4 bits of `g` at once when `eta ≥ 0` (`f + (((f + 1) &&& 4) <<< 1)` inverts `f` modulo 16) or
  up to 6 after the swap when `eta < 0` (`f * (f * f - 2)` inverts `-f` modulo 64). Those
  identities are finite facts, so `magic_inverse_mod_16` and `magic_inverse_mod_64` below prove
  them outright by `decide`;
* the kernel reads only the bottom words, so agreement with `run 62` on the *full* integers is
  exactly the claim that 62 divsteps depend on no more than that;
* it returns the updated `eta` too, so a drift in the branch schedule cannot hide.

`CompElliptic.Fields.SafeGCD.Pasta` additionally replays the check along the real trajectories
of the port's own regression vectors, where `f` and `g` are full 255-bit values rather than the
single-word samples used here.

## Provenance

Ported from `src/fields/modinv62.rs` of
[zcash/pasta_curves#119](https://github.com/zcash/pasta_curves/pull/119), pinned at commit
`9299dfbb19978428ba24229bc13dff25a424dc46` (branch `modinv62`). Every `Rust:` link on a
declaration below points into that commit, so the line numbers stay valid even after the branch
moves; to review against the tip of the branch instead, open the pull request and diff.

## Scope

The rest of the Rust module, the signed-radix-`2 ^ 62` limb arithmetic and the driver built on
it, is in `CompElliptic.Fields.SafeGCD.Limbs`.

One thing here is deliberately *not* ported: `negative_eta_multiplier`, an
`#[inline(never)]` helper that exists only to stop the AArch64 backend speculatively
evaluating both cancellation formulas:
<https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L125-L136>
 It computes exactly the expression it replaces, so `divsteps62Step` inlines it; there
is no Lean counterpart to a codegen barrier, and nothing to check.
-/

namespace CompElliptic.Fields.SafeGCD

/-! ## Word helpers -/

/-- `u64::MAX`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L50-L51> -/
def allOnes : UInt64 := 0xffffffffffffffff

/-- Reinterpret a word as a signed 64-bit integer, the Rust `as i64`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L367-L372> -/
def toI64 (x : UInt64) : Int :=
  if x.toNat < 2 ^ 63 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64

/-- Truncate an integer to its bottom 64 bits, the Rust `as u64`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L846-L848> -/
def toU64 (x : Int) : UInt64 := UInt64.ofNat (x % (2 ^ 64)).toNat

/-- The number of trailing zero bits of a word; `64` for zero. The kernel only ever calls it on
a word made nonzero by a sentinel bit. -/
def trailingZeros (x : UInt64) : Nat :=
  let rec go : Nat → UInt64 → Nat
    | 0, _ => 64
    | fuel + 1, y => if y &&& 1 == 1 then 0 else 1 + go fuel (y >>> 1)
  go 64 x

/-! ## The magic modular inverses the kernel uses

Both are finite claims about a word modulo a small power of two, so `decide` settles them for
every residue. They are what licenses cancelling several bits of `g` in one inner iteration
instead of one bit per divstep.
-/

/-- For odd `f`, `f + (((f + 1) &&& 4) <<< 1)` is the inverse of `f` modulo `16`: the identity
behind the `eta ≥ 0` branch, which cancels up to 4 bits of `g` at a time.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L350-L360> -/
theorem magic_inverse_mod_16 :
    ∀ f < 16, f % 2 = 1 → (f + ((f + 1) &&& 4) * 2) * f % 16 = 1 := by decide

/-- For odd `f`, `f * (f * f - 2)` is the inverse of `-f` modulo `64`: the identity behind the
`eta < 0` branch, which cancels up to 6 bits of `g` at a time once `f` and `g` have swapped.
`62` stands for `-2` modulo `64`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L329-L348> -/
theorem magic_inverse_mod_64 :
    ∀ f < 64, f % 2 = 1 → (f * (f * f + 62) % 64) * (64 - f) % 64 = 1 := by decide

/-- The same fact in the form the cancellation actually needs: `g + f * w` with
`w = f * g * (f * f - 2)` is `g * (1 + f ^ 2 * (f ^ 2 - 2)) = g * (1 - (f ^ 2 - 1) ^ 2)`, and
`(f ^ 2 - 1) ^ 2` is divisible by `64` for odd `f` because `f ^ 2 - 1 = (f - 1) * (f + 1)` is
divisible by `8`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L329-L348> -/
theorem cancellation_mod_64 :
    ∀ f < 64, f % 2 = 1 → (f * f * (f * f + 62) + 1) % 64 = 0 := by decide

/-! ## The kernel -/

/-- The mutable state of `divsteps62Var`'s inner loop, mirroring the Rust locals.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L281-L288> -/
structure Divsteps62State where
  /-- The Bernstein-Yang `eta`, exact. -/
  eta : Int
  /-- Top-left matrix accumulator. -/
  u : UInt64
  /-- Top-right matrix accumulator. -/
  v : UInt64
  /-- Bottom-left matrix accumulator. -/
  q : UInt64
  /-- Bottom-right matrix accumulator. -/
  r : UInt64
  /-- The working `f`, bottom word only. -/
  f : UInt64
  /-- The working `g`, bottom word only. -/
  g : UInt64
  /-- Divsteps still to perform in this batch. -/
  i : Nat
deriving Repr, Inhabited

/-- One iteration of the Rust `loop`: batch away the trailing zeros of `g`, then (unless the
batch is complete) swap if `eta < 0` and cancel as many low bits of `g` as the current `eta`
allows.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L289-L365> -/
def divsteps62Step (s : Divsteps62State) : Divsteps62State :=
  let zeros := trailingZeros (s.g ||| (allOnes <<< UInt64.ofNat s.i))
  let g := s.g >>> UInt64.ofNat zeros
  let u := s.u <<< UInt64.ofNat zeros
  let v := s.v <<< UInt64.ofNat zeros
  let eta := s.eta - (zeros : Int)
  let i := s.i - zeros
  if i = 0 then
    { s with eta := eta, u := u, v := v, g := g, i := 0 }
  else
    let etaNeg := eta < 0
    -- On the negative branch, negate `eta` and replace `f, g` by `g, -f` (and the matrix rows
    -- likewise), so the cancellation below always works against an odd `f`.
    let eta' := if etaNeg then -eta else eta
    let f' := if etaNeg then g else s.f
    let g' := if etaNeg then 0 - s.f else g
    let u' := if etaNeg then s.q else u
    let q' := if etaNeg then 0 - u else s.q
    let v' := if etaNeg then s.r else v
    let r' := if etaNeg then 0 - v else s.r
    let limit : Nat := min (eta'.toNat + 1) i
    let w :=
      if etaNeg then
        let m := (allOnes >>> UInt64.ofNat (64 - limit)) &&& 63
        f' * g' * (f' * f' - 2) &&& m
      else
        let m := (allOnes >>> UInt64.ofNat (64 - limit)) &&& 15
        let w0 := f' + ((f' + 1 &&& 4) <<< 1)
        (0 - w0) * g' &&& m
    { eta := eta', u := u', v := v', q := q' + u' * w, r := r' + v' * w,
      f := f', g := g' + f' * w, i := i }

/-- Iterate `divsteps62Step` until the batch is complete. Each iteration after the first
consumes at least one divstep, so `70` is ample fuel for a 62-divstep batch.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L288-L366> -/
def divsteps62Loop : Nat → Divsteps62State → Divsteps62State
  | 0, s => s
  | fuel + 1, s => if s.i = 0 then s else divsteps62Loop fuel (divsteps62Step s)

/-- The port's `divsteps_62_var`: 62 divsteps read off the bottom words `f0` and `g0`, returning
the accumulated transition matrix and the updated `eta`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L270-L391> -/
def divsteps62Var (eta : Int) (f0 g0 : UInt64) : Trans × Int :=
  let s := divsteps62Loop 70 ⟨eta, 1, 0, 0, 1, f0, g0, 62⟩
  (⟨toI64 s.u, toI64 s.v, toI64 s.q, toI64 s.r⟩, s.eta)

/-! ## Differential check against the recurrence -/

/-- The kernel agrees with `run 62` on the integers `f` and `g`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1345-L1377> -/
def batchAgrees (eta f g : Int) : Bool :=
  let p := run 62 ⟨eta, f, g⟩
  divsteps62Var eta (toU64 f) (toU64 g) == (p.2, p.1.eta)

/-- A pseudo-random word stream, for sampling the kernel's input space. -/
def lcg (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

/-- `n` sample triples `(eta, f, g)` with `f` odd, drawn from `lcg` starting at `seed`. -/
def samples : Nat → UInt64 → List (Int × Int × Int)
  | 0, _ => []
  | n + 1, x =>
      let a := lcg x
      let b := lcg a
      let c := lcg b
      ((c.toNat % 61 : Nat) - 30, ((a ||| 1).toNat : Int), (b.toNat : Int)) :: samples n c

-- The kernel reproduces the recurrence (matrix and `eta`) on 512 single-word samples.
#guard (samples 512 0x9e3779b97f4a7c15).all fun t => batchAgrees t.1 t.2.1 t.2.2

-- Boundary `eta` values, where the branch schedule and the `limit` clamp change behaviour.
#guard ([-62, -31, -2, -1, 0, 1, 2, 31, 62] : List Int).all fun e =>
  batchAgrees e 1 0 && batchAgrees e 1 1 && batchAgrees e (2 ^ 62 - 1) (2 ^ 62 - 2)
    && batchAgrees e 0xffffffffffffffff 0

end CompElliptic.Fields.SafeGCD
