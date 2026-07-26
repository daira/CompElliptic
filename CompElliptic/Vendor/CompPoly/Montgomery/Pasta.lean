/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Field
import CompElliptic.Fields.Pasta

/-!
# The Pasta base fields as fast eight-limb Montgomery fields

The per-field data realizing the two Pasta base fields as `Mont64x8Field`s.  Unlike the
upstream CompPoly branch, which is self-contained and therefore carries its own Pratt
certificates, this vendored copy reuses the primes and certificates of
`CompElliptic.Fields.Pasta`, so that there is exactly one
`Field (ZMod PALLAS_SCALAR_CARD)` instance in the repository and the Montgomery carrier
bridges directly into the `Fq` of `CompElliptic.Curves.Pasta.Fast.Projective`.

Note the Pasta naming: `PALLAS_SCALAR_CARD` is the **Vesta base** field size and
`PALLAS_BASE_CARD` is the **Vesta scalar** field size.
-/

namespace Montgomery
namespace Native64x8

open CompElliptic.Fields.Pasta

/-- The Vesta base field (`= PALLAS_SCALAR_CARD`) as a fast eight-limb Montgomery field. -/
instance instVestaBase : Mont64x8Field PALLAS_SCALAR_CARD where
  prime := PALLAS_SCALAR_is_prime
  modulusLimbs := VestaFq.modulusLimbs
  rModModulus := VestaFq.rModModulus
  r2ModModulus := VestaFq.r2ModModulus
  montgomeryNegInv := VestaFq.negInv

/-- The Pallas base field (`= PALLAS_BASE_CARD`) as a fast eight-limb Montgomery field. -/
instance instPallasBase : Mont64x8Field PALLAS_BASE_CARD where
  prime := PALLAS_BASE_is_prime
  modulusLimbs := PallasFq.modulusLimbs
  rModModulus := PallasFq.rModModulus
  r2ModModulus := PallasFq.r2ModModulus
  montgomeryNegInv := PallasFq.negInv

/-- The fast Vesta base field carrier, stored as a Montgomery residue. -/
abbrev VestaBaseFast : Type := FastField PALLAS_SCALAR_CARD

/-- The fast Pallas base field carrier, stored as a Montgomery residue. -/
abbrev PallasBaseFast : Type := FastField PALLAS_BASE_CARD

end Native64x8
end Montgomery
