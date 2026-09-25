/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Fields.SafeGCD.Limbs
import CompElliptic.Fields.Pasta

/-!
# The Pasta divstep inversion parameters, and the Rust port checked against them

Instantiates the proved driver of `CompElliptic.Fields.SafeGCD.Reference` at the two Pasta base
fields, and checks the Rust port of
[zcash/pasta_curves#119](https://github.com/zcash/pasta_curves/pull/119) against it.

Everything the port hardcodes is *derived* here rather than restated, and then compared:

* `pallasInv` / `vestaInv` take their modulus from `CompElliptic.Fields.Pasta`, their seed as
  `2 ^ 512 mod m` (the Montgomery `R ^ 2`), and their `inv2w` as `((m + 1) / 2) ^ 62 mod m`,
  which is `(2 ^ 62)⁻¹` because `(m + 1) / 2` is `2⁻¹` for odd `m`. No magic constant.
* `fp_modulus_limbs_eq` and friends check the port's radix-`2 ^ 62` `MODULUS`, its `MU`
  (`m⁻¹ mod 2 ^ 62`, the multiplier that makes each coefficient update divisible by `2 ^ 62`)
  and its `R2` against those derivations, by kernel computation.
* the `#guard`s at the end replay the port's own pinned regression vectors: for each, the
  driver must return the Fermat inverse `R ^ 2 * x ^ (m - 2) mod m`, an oracle independent of
  divsteps, *and* consume exactly the number of 62-divstep batches the port pins. A drifting
  batch count means the control flow has diverged, which is the port's own stated rule.

## Provenance

Ported from `src/fields/modinv62.rs` of
[zcash/pasta_curves#119](https://github.com/zcash/pasta_curves/pull/119), pinned at commit
`9299dfbb19978428ba24229bc13dff25a424dc46` (branch `modinv62`). Every `Rust:` link on a
declaration below points into that commit, so the line numbers stay valid even after the branch
moves; to review against the tip of the branch instead, open the pull request and diff.

The batch counts are the sharpest of these: they are a function of the whole divstep trajectory,
so reproducing all twelve of them from an independent implementation of the recurrence pins the
`eta` convention, the branch selection, the batch width, and the termination test at once.
-/

namespace CompElliptic.Fields.SafeGCD

open CompElliptic.Fields.Pasta

-- The closed numeric facts below evaluate 512-bit powers (`R ^ 2 = 2 ^ 512 mod m`) in the
-- kernel, which needs a deeper recursion budget and a raised `norm_num` exponent threshold.
set_option maxRecDepth 8000
set_option exponentiation.threshold 600

/-! ## Helpers -/

/-- Recombine little-endian limbs of `bits` bits each into a natural number. -/
def ofLimbs (bits : Nat) (l : List Nat) : Nat :=
  l.foldr (fun w acc => acc * 2 ^ bits + w) 0

/-- Binary modular exponentiation. `fuel` bounds the number of squarings; `powMod` supplies
`512`, ample for the 255-bit Pasta exponents. -/
def powModAux (n : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
      if e = 0 then acc
      else powModAux n fuel (b * b % n) (e / 2) (if e % 2 = 1 then acc * b % n else acc)

/-- `b ^ e mod n`, by repeated squaring. -/
def powMod (b e n : Nat) : Nat := powModAux n 512 (b % n) e 1

/-- The inverse of `2 ^ w` modulo an odd `m`, as `((m + 1) / 2) ^ w`: for odd `m` the element
`(m + 1) / 2` is `2⁻¹`, since `2 * ((m + 1) / 2) = m + 1 ≡ 1`. -/
def invTwoPow (m w : Nat) : Nat := powMod ((m + 1) / 2) w m

/-- The expected inverse, by Fermat's little theorem: `seed * x ^ (m - 2) mod m`. This is the
oracle the `#guard`s below compare the divstep driver against, and it shares no code with it.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1570-L1583> -/
def fermatInv (P : Params) (x : Nat) : Nat := P.seed * powMod x (P.m - 2) P.m % P.m

/-! ## Parameters -/

/-- Divstep inversion parameters for the Pallas base field `𝔽ₚ` (`pasta_curves`' `Fp`), seeded
with `R ^ 2` so that the result is already in Montgomery form. -/
def pallasInv : Params where
  m := PALLAS_BASE_CARD
  width := 62
  seed := 2 ^ 512 % PALLAS_BASE_CARD
  inv2w := invTwoPow PALLAS_BASE_CARD 62

/-- Divstep inversion parameters for the Vesta base field `𝔽_q` (`pasta_curves`' `Fq`). -/
def vestaInv : Params where
  m := PALLAS_SCALAR_CARD
  width := 62
  seed := 2 ^ 512 % PALLAS_SCALAR_CARD
  inv2w := invTwoPow PALLAS_SCALAR_CARD 62

/-- `pallasInv` is well-formed, so `invert_spec` applies to it. -/
theorem pallasInv_wf : pallasInv.WF where
  odd := by decide
  two_lt := by decide
  inv2w_spec := by decide

/-- `vestaInv` is well-formed, so `invert_spec` applies to it. -/
theorem vestaInv_wf : vestaInv.WF where
  odd := by decide
  two_lt := by decide
  inv2w_spec := by decide

/-! ## The Rust port's hardcoded constants, re-derived

Each `List` below is transcribed from `src/fields/modinv62.rs`; each theorem re-derives the
same number from the field constants of `CompElliptic.Fields.Pasta` and compares.
-/

/-- `FpParams::MODULUS`: `p` in signed radix `2 ^ 62`, least-significant limb first.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L72-L72> -/
def fpModulusLimbs : List Nat := [0x192d30ed00000001, 0x091a63f02533e46e, 2, 0, 0x40]

/-- `FqParams::MODULUS`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L87-L87> -/
def fqModulusLimbs : List Nat := [0x0c46eb2100000001, 0x091a63f02652a376, 2, 0, 0x40]

/-- `FpParams::R2`: `2 ^ 512 mod p` in radix `2 ^ 62`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L74-L82> -/
def fpR2Limbs : List Nat :=
  [0x0c78ecb30000000f, 0x1f4c36f62c37839e, 0x397a99bc3c95d18d, 0x1b506bdee72dc51d, 9]

/-- `FqParams::R2`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L89-L97> -/
def fqR2Limbs : List Nat :=
  [0x3c9678ff0000000f, 0x1eed0cf624685b8f, 0x3ae231004ccf5906, 0x1b506bdf33f6aa5f, 9]

/-- `FpParams::MU`: `p⁻¹ mod 2 ^ 62`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L73-L73> -/
def fpMU : Nat := 0x26d2cf1300000001

/-- `FqParams::MU`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L88-L88> -/
def fqMU : Nat := 0x33b914df00000001

/-- The port's `Fp` modulus limbs recombine to the Pallas base field's order.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1262-L1305> -/
theorem fp_modulus_limbs_eq : ofLimbs 62 fpModulusLimbs = PALLAS_BASE_CARD := by decide

/-- The port's `Fq` modulus limbs recombine to the Vesta base field's order.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1262-L1305> -/
theorem fq_modulus_limbs_eq : ofLimbs 62 fqModulusLimbs = PALLAS_SCALAR_CARD := by decide

/-- The port's `Fp` `R2` limbs recombine to `2 ^ 512 mod p`, the seed `pallasInv` uses.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1262-L1305> -/
theorem fp_r2_limbs_eq : ofLimbs 62 fpR2Limbs = pallasInv.seed := by decide

/-- The port's `Fq` `R2` limbs recombine to `2 ^ 512 mod q`, the seed `vestaInv` uses.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1262-L1305> -/
theorem fq_r2_limbs_eq : ofLimbs 62 fqR2Limbs = vestaInv.seed := by decide

/-- The port's `Fp` `MU` inverts the bottom modulus limb modulo `2 ^ 62`; this is the
`const_assert!` the Rust module pins at compile time.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L98-L106> -/
theorem fp_mu_spec : fpMU * fpModulusLimbs.headI % 2 ^ 62 = 1 := by decide

/-- The port's `Fq` `MU` inverts the bottom modulus limb modulo `2 ^ 62`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L98-L106> -/
theorem fq_mu_spec : fqMU * fqModulusLimbs.headI % 2 ^ 62 = 1 := by decide

/-- The sparse shape of both moduli that the port's kernels hardcode: limbs `2, 3, 4` are
`2, 0, 64`, so the `k * m` corrections need only two general multiplications.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L98-L106> -/
theorem modulus_sparse_shape :
    fpModulusLimbs.drop 2 = [2, 0, 64] ∧ fqModulusLimbs.drop 2 = [2, 0, 64] := by decide

/-! ## The port's pinned regression vectors, replayed

Each entry is `(x, batches)` with `x` the internal (Montgomery) representation as a natural
number and `batches` the 62-divstep batch count the Rust port pins. The check is that the proved
driver returns the Fermat inverse in exactly that many batches.
-/

/-- `PALLAS_VECTORS` from the Rust port, as `(value, pinned batch count)`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L890-L934> -/
def pallasVectors : List (Nat × Nat) :=
  [ (ofLimbs 64 [0x34786d38fffffffd, 0x992c350be41914ad, 0xffffffffffffffff, 0x3fffffffffffffff], 7)
  , (ofLimbs 64 [0x5d1, 0, 0, 0], 8)
  , (ofLimbs 64 [0xe096c0a18679d7ae, 0x2cc4e34bc6b6f06a, 0x20eddc12b5a7661d, 0x0c3c5e66537210ad], 8)
  , (ofLimbs 64 [1, 0, 0, 0], 9)
  , (ofLimbs 64 [0xa162a7d34ad63d62, 0xba71beb748b1fa25, 0x68dc1330fab3847b, 0x2dc205e082f2c197], 10)
  , (ofLimbs 64 [0x7ceb4d8e9534361d, 0x8d7879adc97a8e79, 0x19ed0538ef7b15eb, 0x35fb58b0ee06c5b4], 10) ]

/-- `VESTA_VECTORS` from the Rust port, as `(value, pinned batch count)`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L936-L975> -/
def vestaVectors : List (Nat × Nat) :=
  [ (ofLimbs 64 [0x5b2b3e9cfffffffd, 0x992c350be3420567, 0xffffffffffffffff, 0x3fffffffffffffff], 7)
  , (ofLimbs 64 [0x3ea12df55a259593, 0xd9c58668e724391e, 0xfcf9d370dd78552a, 0x1f7fd517b4f7efeb], 8)
  , (ofLimbs 64 [0x4973c2bd762bc27a, 0x9085d079ecab3a12, 0x9f66128174a6731a, 0x3e7853d1fb18fcca], 8)
  , (ofLimbs 64 [1, 0, 0, 0], 9)
  , (ofLimbs 64 [0xba5f061296c, 0, 0, 0], 10)
  , (ofLimbs 64 [0xc00e79606e554fa8, 0x13f9947f444f41d3, 0xd5a780db63e83468, 0x337e275425a385f3], 10) ]

/-- One vector passes when the driver returns the Fermat inverse in the pinned batch count.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1686-L1696> -/
def vectorOk (P : Params) (v : Nat × Nat) : Bool :=
  invertCounted P 12 v.1 == some ((fermatInv P v.1 : Int), v.2)

-- The Rust port's twelve pinned vectors, replayed against the proved driver.
#guard pallasVectors.all (vectorOk pallasInv)
#guard vestaVectors.all (vectorOk vestaInv)

-- The port's zero case returns nothing.
#guard invert pallasInv 12 0 == none
#guard invert vestaInv 12 0 == none

/-! ## The batching kernel along real trajectories

`CompElliptic.Fields.SafeGCD.Divsteps62` checks the ported `divsteps_62_var` against the
recurrence on single-word samples. Here the same check runs at every batch boundary of a real
inversion, where `f` and `g` are full 255-bit values (and negative for most of the run), so the
claim being tested is that reading only the bottom word is enough. -/

/-- Walk an inversion trajectory, checking at each batch that the ported kernel reproduces the
matrix and `eta` that `run 62` produces. Both Pasta parameter sets have `width = 62`, which is
what `batchAgrees` assumes.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1345-L1377> -/
def trajectoryAgrees (P : Params) : Nat → RState → Bool
  | 0, _ => false
  | n + 1, s =>
      if !batchAgrees s.eta s.f s.g then false
      else
        let s' := s.step P
        if s'.g = 0 then true else trajectoryAgrees P n s'

/-- The initial driver state for inverting `x`. -/
def initialState (P : Params) (x : Nat) : RState :=
  ⟨-1, (P.m : Int), (x : Int), 0, (P.seed : Int)⟩

#guard pallasVectors.all fun v => trajectoryAgrees pallasInv 12 (initialState pallasInv v.1)
#guard vestaVectors.all fun v => trajectoryAgrees vestaInv 12 (initialState vestaInv v.1)

/-! ## The limb layer, checked against the proved driver

`CompElliptic.Fields.SafeGCD.Limbs` ports the radix-`2 ^ 62` kernels and the driver that uses
them. The parameter sets below are built from the Rust literals transcribed above, the very
ones `fp_modulus_limbs_eq`, `fp_r2_limbs_eq` and `fp_mu_spec` pin to the derived values, so
the limb layer runs on the port's own constants, and the checks compare its output with the
proved integer driver's. -/

/-- The Rust `FpParams`, as limb-layer parameters.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L68-L82> -/
def pallasLimbParams : LimbParams where
  modulus := Signed62.ofList (fpModulusLimbs.map Int.ofNat)
  mu := UInt64.ofNat fpMU
  r2 := Signed62.ofList (fpR2Limbs.map Int.ofNat)

/-- The Rust `FqParams`, as limb-layer parameters.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L83-L97> -/
def vestaLimbParams : LimbParams where
  modulus := Signed62.ofList (fqModulusLimbs.map Int.ofNat)
  mu := UInt64.ofNat fqMU
  r2 := Signed62.ofList (fqR2Limbs.map Int.ofNat)

/-- A natural number as four little-endian 64-bit limbs, the Rust internal representation. -/
def toLimbs64 (x : Nat) : Array UInt64 :=
  #[UInt64.ofNat (x % 2 ^ 64), UInt64.ofNat (x / 2 ^ 64 % 2 ^ 64),
    UInt64.ofNat (x / 2 ^ 128 % 2 ^ 64), UInt64.ofNat (x / 2 ^ 192 % 2 ^ 64)]

/-- The natural number four little-endian 64-bit limbs denote. -/
def ofLimbs64Array (a : Array UInt64) : Nat :=
  (a.getD 0 0).toNat + 2 ^ 64 * (a.getD 1 0).toNat + 2 ^ 128 * (a.getD 2 0).toNat
    + 2 ^ 192 * (a.getD 3 0).toNat

/-- The limb driver and the proved integer driver agree on `x`, value and batch count.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1585-L1608> -/
def limbAgrees (LP : LimbParams) (P : Params) (x : Nat) : Bool :=
  match limbInvertCounted LP (toLimbs64 x), invertCounted P 12 x with
  | some (y, k), some (y', k') => (ofLimbs64Array y : Int) == y' && k == k'
  | none, none => true
  | _, _ => false

-- The port's pinned vectors, through the limb layer.
#guard pallasVectors.all fun v => limbAgrees pallasLimbParams pallasInv v.1
#guard vestaVectors.all fun v => limbAgrees vestaLimbParams vestaInv v.1

-- Zero has no inverse in either layer.
#guard limbInvert pallasLimbParams (toLimbs64 0) == none
#guard limbInvert vestaLimbParams (toLimbs64 0) == none

/-- Pseudo-random field elements below `m`, for sampling the limb layer beyond the pinned
vectors. -/
def randomElements (m : Nat) : Nat → UInt64 → List Nat
  | 0, _ => []
  | n + 1, x =>
      let a := lcg x
      let b := lcg a
      let c := lcg b
      let d := lcg c
      let v := (a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat) % m
      (if v == 0 then 1 else v) :: randomElements m n d

#guard (randomElements pallasInv.m 64 0xda39a3ee5e6b4b0d).all
  (limbAgrees pallasLimbParams pallasInv)
#guard (randomElements vestaInv.m 64 0x3f786850e387550f).all
  (limbAgrees vestaLimbParams vestaInv)

-- Small and boundary representations: 1, 2, m - 1, m - 2, and single set bits.
#guard ([1, 2, 3, pallasInv.m - 1, pallasInv.m - 2] ++
    (List.range 63).map (fun k => 2 ^ (4 * k + 1))).all
  (limbAgrees pallasLimbParams pallasInv)
#guard ([1, 2, 3, vestaInv.m - 1, vestaInv.m - 2] ++
    (List.range 63).map (fun k => 2 ^ (4 * k + 1))).all
  (limbAgrees vestaLimbParams vestaInv)

/-! ### The Rust test module's own differential obligations

Reproduced here against the same generic-modulus reference the Rust uses: the sparse-modulus
kernels must be limb-exact against a version that multiplies by every modulus limb, and the
first-batch and terminal specializations against the general ones. -/

/-- `pack62` and `unpack62` round-trip on a canonical representation.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1307-L1343> -/
def packRoundTrips (x : Nat) : Bool := ofLimbs64Array (unpack62 (pack62 (toLimbs64 x))) == x

#guard ([0, 1, 2, pallasInv.m - 1] ++ (List.range 63).map (fun k => 2 ^ (4 * k + 1))).all
  packRoundTrips
#guard (randomElements pallasInv.m 64 0x5ba93c9db0cff93f).all packRoundTrips

-- Every sparse, first-batch and terminal specialization is limb-exact against the
-- generic-modulus reference, at every batch of a real inversion.
#guard pallasVectors.all fun v =>
  specializationsAgree pallasLimbParams (toLimbs64 v.1)
#guard vestaVectors.all fun v =>
  specializationsAgree vestaLimbParams (toLimbs64 v.1)
#guard (randomElements pallasInv.m 32 0x2cf24dba5fb0a30e).all fun x =>
  specializationsAgree pallasLimbParams (toLimbs64 x)
#guard (randomElements vestaInv.m 32 0x18ac3e7343f01690).all fun x =>
  specializationsAgree vestaLimbParams (toLimbs64 x)

/-- Normalization inputs: the canonical residue of a random element, minus zero, one or two
copies of the modulus, which is the range `(-2m, m)` the kernel promises to handle. -/
def normalizeCases (P : Params) (LP : LimbParams) : List Signed62 :=
  let shifted (x : Nat) (k : Nat) : Signed62 :=
    Signed62.ofList <| (List.range 5).map fun i =>
      (pack62 (toLimbs64 x)).get i - (k : Int) * LP.modulus.get i
  (List.range 3).flatMap fun k =>
    (randomElements P.m 8 (0xfcde2b2edba56bf4 + UInt64.ofNat k)).map (shifted · k)

#guard (normalizeCases pallasInv pallasLimbParams).all fun r =>
  normalizeOk pallasLimbParams pallasInv.m r 1 && normalizeOk pallasLimbParams pallasInv.m r (-1)
#guard (normalizeCases vestaInv vestaLimbParams).all fun r =>
  normalizeOk vestaLimbParams vestaInv.m r 1 && normalizeOk vestaLimbParams vestaInv.m r (-1)

end CompElliptic.Fields.SafeGCD
