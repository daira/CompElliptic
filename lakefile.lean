import Lake
open System Lake DSL

package CompElliptic where
  version := v!"0.1.0"

-- Mathlib is pulled in transitively (and version-pinned) by CompPoly, so that the two
-- always agree on the toolchain and Mathlib revision.
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly.git" @ "d458e5cebd364b15660ff8de20ec964dcd52c120"

-- The glob sweeps every module under `CompElliptic/`, so that modules which the root
-- `CompElliptic.lean` deliberately does not import are still in a build target. That applies to
-- `CompElliptic/Curves/Pasta/Fast/` and `CompElliptic/Vendor/`: importing them would put the
-- precompiled native lane below (`FastFieldNative`) in the import closure of every consumer of
-- `import CompElliptic`, which is not wanted -- the fast arithmetic is opt-in.
@[default_target]
lean_lib CompElliptic where
  globs := #[.andSubmodules `CompElliptic]

-- The ONLY library in this repository with `precompileModules`, and the only reason it exists.
--
-- WHY: `CompElliptic/Curves/Pasta/Fast/` is arithmetic that is meant to be *run* -- by `#eval`,
-- by `decide`, and above all by `native_decide` -- not just proven about. Under `precompileModules`
-- Lake compiles these modules to a shared library that the elaborator loads, so evaluation happens
-- at native speed instead of in the interpreter.
--
-- THE CORE-ONLY INVARIANT: every module in this lane must import nothing beyond Lean core.
-- `precompileModules` runs native codegen over the lane's whole import closure; pointing it at
-- anything mathlib-side means natively compiling a mathlib closure, which OOMs a 16 GB machine.
-- That is why the two modules below are pure definition modules, split away from their proofs:
--   * `...Vendor.CompPoly.Montgomery.Native64x8Defs` -- proofs in `Native64x8*.lean` (not in lane)
--   * `...Curves.Pasta.Fast.ProjectiveMontDefs`      -- proofs in `ProjectiveMontEquiv.lean` (ditto)
-- Adding a module here whose imports are not core-only will not fail loudly; it will just make the
-- build enormous. `scripts/check_native_lane.sh` checks the invariant.
--
-- THE ROOT MODULE: `FastFieldNative.lean` exists only to be named after the library. Lean derives
-- the expected `initialize_...` symbol of a dynlib from the `.so` filename
-- (`libCompElliptic_FastFieldNative.so`), so without a module of exactly that name every module
-- importing the lane fails at elaboration with `error loading plugin, initializer not found`.
lean_lib FastFieldNative where
  precompileModules := true
  globs := #[
    .one `FastFieldNative,
    .one `CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs,
    .one `CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs
  ]
