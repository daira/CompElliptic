import Lake
open System Lake DSL

package CompElliptic where
  version := v!"0.1.0"

-- Mathlib is pulled in transitively (and version-pinned) by CompPoly, so that the two
-- always agree on the toolchain and Mathlib revision.
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly.git" @ "d458e5cebd364b15660ff8de20ec964dcd52c120"

-- The glob covers modules the root `CompElliptic.lean` deliberately does not import: the fast
-- arithmetic and its vendored field are opt-in, so that `import CompElliptic` stays free of the
-- precompiled lane below.
@[default_target]
lean_lib CompElliptic where
  globs := #[.andSubmodules `CompElliptic]

-- Native-compiles the Montgomery arithmetic, which is meant to be run (`#eval`, `native_decide`),
-- not only proven about. Every module here must import nothing outside Lean core: codegen runs over
-- the whole import closure, so one mathlib-side import silently makes the build enormous -- hence
-- the definitions/proofs split, and `scripts/check_native_lane.sh`. `FastFieldNative.lean` exists
-- only because Lean derives a dynlib's `initialize_...` symbol from the library name.
lean_lib FastFieldNative where
  precompileModules := true
  globs := #[
    .one `FastFieldNative,
    .one `CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs,
    .one `CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs
  ]
