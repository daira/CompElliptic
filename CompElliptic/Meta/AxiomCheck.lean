/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# `assert_axioms` and `assert_computable` — concise, build-checked trust assertions

Siblings of Mathlib's `assert_no_sorry` (same `collectAxioms` machinery) that assert an *upper
bound* on a declaration's trusted base. Unlike a `#guard_msgs`-pinned `#print axioms`, they do not
hard-code the pretty-printed axiom list, so they stay green across toolchain bumps that rename the
`native_decide` axiom — while still failing the build the moment a declaration reaches beyond its
declared tier (a `sorry`, an unexpected axiom, or `native_decide` where none was permitted).
The `#guard_msgs`-pinned form remains the right tool when the *exact* axiom set is the claim.

These commands are also used in ironwood (`Zcash/Meta/AxiomCheck.lean`); changes here should be
reflected there and vice versa.
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

/--
`assert_computable foo` fails the build unless `foo` is a plain `def` — an actual
definition, not marked `noncomputable` — depending on no axioms beyond `propext` / `Quot.sound`.
This is the breaks-as-computed-data check: the data is genuinely computed, and with
`Classical.choice` excluded it cannot have been conjured from mere propositional existence even
in erased positions.

`assert_computable foo +choice` additionally permits `Classical.choice`. Together with the
plain-`def` check this asserts choice enters only through erased `Prop` fields: had it touched the
data, the definition could not have compiled as a plain `def`. `+native` likewise permits
`native_decide` compiler-trust axioms.

The plain-`def` check guards a gap in "computability is compiler-enforced": marking a reduction
`noncomputable` later would still build, silently voiding the convention; this assertion catches
it.
-/
elab "assert_computable " n:ident choice:("+choice")? native:("+native")? : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let info ← liftCoreM <| getConstInfo name
  unless info matches .defnInfo _ do
    throwError "{n} is not a def"
  if Lean.isNoncomputable env name then
    throwError "{n} is marked noncomputable"
  let axs ← collectAxioms name
  let allowChoice := choice.isSome
  let allowNative := native.isSome
  let unexpected := axs.filter fun ax =>
    !(ax == ``propext || ax == ``Quot.sound
      || (allowChoice && ax == ``Classical.choice)
      || (allowNative && isNativeDecideAxiom ax))
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"

end CompElliptic.Meta
