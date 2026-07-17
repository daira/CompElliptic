/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.Pasta
import CompElliptic.Encodings.Common

/-!
# Encodings of Pasta curve points

The compressed point encoding for Pallas and Vesta, per the
[Zcash Protocol Specification §5.4.9](https://zips.z.cash/protocol/protocol.pdf#concretepairing).
A point `(x, y)` encodes as the 32-byte little-endian octet string of `x` with the free top bit
(bit 255, since each modulus is `< 2^255`) set to the parity of `y`; the identity `𝒪 = (0, 0)`
encodes as 32 zero bytes — which falls out of the same formula. Matches `pasta_curves`' affine
`GroupEncoding::to_bytes`.

This file covers the *encode* direction (`toBytes`). The partial decode (`abst`), the assembly
into named `CanonicalEncoding` values (`PallasEncoding` / `VestaEncoding`), and the spec-named
bit/byte primitives (`I2LEBSP` / `LEBS2OSP`) come next.

Note on naming: the spec's `repr_P` outputs a *bit* sequence (`𝔹^[ℓ]`); our encoding outputs
*bytes* (`Vector UInt8 32`), a different type, so we deliberately do **not** call it `repr`.
-/

namespace CompElliptic

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Fields.Pasta

/-- The compressed encoding of a short-Weierstrass point over a base field `ZMod n` whose modulus
fits in 255 bits (`Fact (n ≤ 2^255)`, as holds for both Pallas and Vesta): the 32-byte
(`I2LEOSP 256`) little-endian encoding of `x` with the free top bit (bit 255) set to the parity of
`y`. The integer is `< 2^256` by `encodedInt_lt` (the field-size precondition). The identity
`(0, 0)` encodes as 32 zero bytes (the same formula). -/
def toBytes {n : ℕ} [Fact (Nat.Prime n)] [Fact (n ≤ 2^255)]
    {E : SWCurve (ZMod n)} (P : SWPoint E) : Vector UInt8 32 :=
  I2LEOSP 256 ⟨P.x.val + (P.y.val % 2) * 2^255, encodedInt_lt P.x P.y⟩

/-- The Pallas base field modulus fits in 255 bits (it is `≈ 2^254`), so the compressed encoding has
a free top bit for the `y`-parity. -/
instance : Fact (PALLAS_BASE_CARD ≤ 2^255) := ⟨by decide⟩

/-- Likewise the Pallas scalar field (= Vesta base field) modulus. -/
instance : Fact (PALLAS_SCALAR_CARD ≤ 2^255) := ⟨by decide⟩

namespace Curves.Pasta.Pallas

/-- The test point `G = (-1, 2)` as an on-curve `SWPoint`, for exercising `toBytes`. -/
def G_point : SWPoint curve := ⟨-1, 2, by decide⟩

#eval (toBytes G_point).toList

end Curves.Pasta.Pallas

namespace Curves.Pasta.Vesta

/-- The test point `G = (-1, 2)` on the Vesta curve as an on-curve `SWPoint`, for exercising
`toBytes` over the Vesta base field (`= PallasScalarField`). -/
def G_point : SWPoint curve := ⟨-1, 2, by decide⟩

#eval (toBytes G_point).toList

end Curves.Pasta.Vesta

end CompElliptic
