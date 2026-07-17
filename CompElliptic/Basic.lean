/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompPoly.Fields.Secp256k1

/-!
# CompElliptic

Computable elliptic-curve abstractions, built in the style of (and on top of) CompPoly.

This module is currently only a build smoke test: it confirms that the toolchain, Mathlib
(pulled in transitively via CompPoly), and CompPoly itself all resolve and compile together,
and that CompPoly's computable prime-field machinery — the template we will follow for the
Pasta base/scalar fields — is usable here.
-/

namespace CompElliptic

open Secp256k1 in
/-- Smoke test: CompPoly's `ZMod`-based prime field is available and its `Field` instance works. -/
example : (1 : BaseField) + 0 = 1 := by ring

end CompElliptic
