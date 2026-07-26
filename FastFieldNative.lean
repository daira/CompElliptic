/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs
import CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs

/-!
# The precompiled native lane

Root module of the `FastFieldNative` library (see the lakefile): it exists only so that the
emitted `.so` carries an initializer named after the library. Its import closure — the Montgomery
field definitions and the Vesta kernel — is core-only by construction; the proofs about them live
in sibling modules outside the lane.
-/
