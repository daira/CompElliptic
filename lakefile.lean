import Lake
open System Lake DSL

package CompElliptic where
  version := v!"0.1.0"

-- Mathlib is pulled in transitively (and version-pinned) by CompPoly, so that the two
-- always agree on the toolchain and Mathlib revision.
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly.git" @ "d458e5cebd364b15660ff8de20ec964dcd52c120"

@[default_target]
lean_lib CompElliptic
