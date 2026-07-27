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
-- NOTE (observed on Lean/Lake v4.30.0): declaring the `CompElliptic` library first does NOT
-- stop the default build from building and loading this lane's dylib — the lane's proof
-- modules import the definition modules, so the shared facet is built for their elaboration.
-- Ownership under overlapping globs and declaration order is not an opt-in boundary; the
-- opt-in invariant for native-executing checks is enforced by `scripts/check_native_optin.py`
-- (see `design/lean-native-trust-research.md`, Appendix C).
lean_lib FastFieldNative where
  precompileModules := true
  globs := #[
    .one `FastFieldNative,
    .one `CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs,
    .one `CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs
  ]
