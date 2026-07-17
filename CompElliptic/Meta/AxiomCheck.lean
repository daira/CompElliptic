/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# `assert_axioms` — a concise, build-checked trust-boundary pin

A sibling of Mathlib's `assert_no_sorry` (same `collectAxioms` machinery) that asserts an *upper
bound* on a declaration's trusted base. Unlike a `#guard_msgs`-pinned `#print axioms`, it does not
hard-code the pretty-printed axiom list, so it stays green across toolchain bumps that rename the
`native_decide` axiom — while still failing the build the moment a declaration reaches beyond its
declared tier (a `sorry`, an unexpected axiom, or `native_decide` where none was permitted).
-/

open Lean Elab Command

namespace CompElliptic.Meta

/-- The standard axioms of Lean's trusted base — the whole budget for a general theorem. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- An axiom introduced by `native_decide`: its name carries a `native_decide` component
(e.g. `…_native.native_decide.ax_1_1`). Matching on the component rather than the full name keeps
the check stable across the toolchain-dependent axiom naming. -/
def isNativeDecideAxiom (n : Name) : Bool :=
  n.components.any (· == `native_decide)

/--
`assert_axioms foo` fails the build unless `foo` depends only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular, no `sorry` and no `native_decide`.

`assert_axioms foo +native` additionally permits `native_decide` compiler-trust axioms, whose exact
names are toolchain-dependent. Any other axiom (including `sorryAx`) is still rejected.
-/
elab "assert_axioms " n:ident native:("+native")? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axs ← collectAxioms name
  let allowNative := native.isSome
  let unexpected := axs.filter fun ax =>
    !standardAxioms.contains ax && !(allowNative && isNativeDecideAxiom ax)
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"

end CompElliptic.Meta
