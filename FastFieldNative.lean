/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs
import CompElliptic.Curves.Pasta.Fast.NatKernel
import CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs

/-!
# The precompiled native lane

Root module of the `FastFieldNative` library — the only `precompileModules` target in this
repository (see the lakefile for the full rationale).

It exists so that the shared library Lake emits
(`.lake/build/lib/libCompElliptic_FastFieldNative.so`) carries an initializer whose name matches
the library: Lean's dynlib loader derives the expected `initialize_…` symbol from the `.so`
filename, so a library without a root module of the same name fails at load time with
`error loading plugin, initializer not found` in every module that imports the lane.

Its import closure is **core-only by construction**: the eight-limb Montgomery field definitions
(`CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs`), the `Nat`-carrier Vesta kernel
(`CompElliptic.Curves.Pasta.Fast.NatKernel`) and the Montgomery Vesta kernel
(`CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs`) each import nothing beyond Lean core, so
native compilation stays at four modules instead of a mathlib closure. Every theorem *about*
these definitions lives in sibling modules that are deliberately outside the lane.

`scripts/check_native_lane.sh` re-checks the core-only invariant.
-/
