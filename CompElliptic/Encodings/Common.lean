/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Common encoding primitives (integers, bit sequences, and endianness)

The Zcash Protocol Specification's integer / bit-sequence / octet-string conversion primitives,
shared by the concrete point and field encodings in `CompElliptic/Encodings/`. Following the
*Separate types with explicit conversions* and *Give mistakes nowhere to hide* principles: bit-
and byte-sequence depictions are distinct fixed-length types with their lengths in the types
(so truncation / padding errors are caught), and the endianness is carried *in the name* of each
primitive, never a silent default.

Every primitive in this family takes a *bit* length (never a byte length), so there is no
bit-vs-byte ambiguity to remember at a call site; an octet primitive like `I2LEOSP` produces
`⌈ℓ/8⌉` bytes from a bit length `ℓ`.

So far: `I2LEOSP` (integer → little-endian octet string). The little-endian bit-sequence
conversions (`I2LEBSP`, `LEBS2IP`) and the bit↔byte bridges (`LEBS2OSP`, `LEOS2BSP`) will join
it here as the decode direction (`abst`) is built out.
-/

namespace CompElliptic

/-- `I2LEOSP ℓ n`: the little-endian octet (byte) encoding of the integer `n`, as `⌈ℓ/8⌉ = (ℓ+7)/8`
bytes, least-significant byte first (Zcash spec, "Integers, Bit Sequences, and Endianness").
Byte `i` is `⌊n / 256^i⌋ mod 256`.

`ℓ` is a *bit* length (uniform with the rest of the family), and the domain `Fin (2^ℓ)` ensures
that `n` is in range by construction, so that there can be no silent high-byte truncation
(*Give mistakes nowhere to hide*). -/
def I2LEOSP (ℓ : ℕ) (n : Fin (2^ℓ)) : Vector UInt8 ((ℓ + 7) / 8) :=
  Vector.ofFn (fun i : Fin ((ℓ + 7) / 8) => UInt8.ofNat (n.val / 256^(i : ℕ) % 256))

/-- `LEOS2IP S`: the integer represented in little-endian byte order by the `m`-byte string `S`
(Zcash spec, "Integers, Bit Sequences, and Endianness") — the decode-direction inverse of
`I2LEOSP` on byte-aligned lengths. The byte length `m` is carried by `S`'s type, and the result
lies in `[0, 2^(8*m))`. -/
def LEOS2IP {m : ℕ} (S : Vector UInt8 m) : ℕ :=
  Nat.ofDigits 256 (S.toList.map UInt8.toNat)

/-- The integer `x.val + (y.val % 2)·2^k` of a compressed point encoding (an `x`-coordinate with a
single parity/sign bit at position `k`) is `< 2^(k+1)`, provided the base field modulus fits in `k`
bits (`Fact (n ≤ 2^k)`). This is the field-size precondition that lets such an integer inhabit
`Fin (2^(k+1))`, e.g. for `I2LEOSP (k+1)`. -/
theorem encodedInt_lt {k n : ℕ} [Fact (Nat.Prime n)] [Fact (n ≤ 2^k)] (x y : ZMod n) :
    x.val + (y.val % 2) * 2^k < 2^(k + 1) := by
  haveI : NeZero n := ⟨(Fact.out : Nat.Prime n).pos.ne'⟩
  have hx : x.val < 2^k := lt_of_lt_of_le (ZMod.val_lt x) Fact.out
  have hkk : (2 : ℕ)^(k + 1) = 2^k + 2^k := by rw [pow_succ]; ring
  have hpar : y.val % 2 ≤ 1 := by omega
  have hprod : (y.val % 2) * 2^k ≤ 2^k := by
    calc (y.val % 2) * 2^k ≤ 1 * 2^k := by gcongr
      _ = 2^k := one_mul _
  omega

end CompElliptic
