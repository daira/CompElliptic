/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood, Tal Derei
-/
import CompElliptic.Meta.AxiomCheck

/-!
# Regression tests for `CompElliptic.Meta.AxiomCheck`

Two rejection families. The native-axiom provenance cases deliberately impersonate Lean's
`native_decide` auxiliaries: most declare an axiom named like an auxiliary, and one instead names a
*theorem* so that its own genuine auxiliary imitates the marker path. The `assert_computable` cases
pin the declaration checks that stand behind "the reduction data is genuinely computed". Both live
in this test-only library so the production `CompElliptic` library never imports them.
-/

namespace MetaCheck.AxiomCheck

namespace Genuine

theorem owner : (123456 : Nat) < 123457 := by native_decide

assert_axioms MetaCheck.AxiomCheck.Genuine.owner +native(
  MetaCheck.AxiomCheck.Genuine.owner)

end Genuine

namespace GenuineAutoParam

/-- The certificate lives in an auto-param, so the axiom is emitted while elaborating the
structure instance below rather than a tactic block of its own. Lean then records the auxiliary's
end position at the start of the *next* token — past the end of the owning declaration — which is
why ownership is decided by the auxiliary's start position. The Tonelli–Shanks data of this
repository (`CompElliptic.Fields.Pasta.pallasBase`, `vestaBase`) is the census entry with this
shape. -/
structure Certified where
  value : Nat
  small : value < 123457 := by native_decide

def owner : Certified where
  value := 123456

assert_axioms MetaCheck.AxiomCheck.GenuineAutoParam.owner +native(
  MetaCheck.AxiomCheck.GenuineAutoParam.owner)

end GenuineAutoParam

namespace NonexistentOwner

axiom owner._native.native_decide.ax_1_1 : False
theorem target : False := owner._native.native_decide.ax_1_1

/-- error: Unknown constant `MetaCheck.AxiomCheck.NonexistentOwner.owner` -/
#guard_msgs (whitespace := lax) in
assert_axioms MetaCheck.AxiomCheck.NonexistentOwner.target +native(
  MetaCheck.AxiomCheck.NonexistentOwner.owner)

end NonexistentOwner

namespace UnrelatedOwner

theorem owner : True := True.intro
axiom owner._native.native_decide.ax_1_1 : False
theorem target : False := owner._native.native_decide.ax_1_1

/-- error: MetaCheck.AxiomCheck.UnrelatedOwner.target: '+native' names 'MetaCheck.AxiomCheck.UnrelatedOwner.owner', but that declaration owns no native_decide axiom -/
#guard_msgs (whitespace := lax) in
assert_axioms MetaCheck.AxiomCheck.UnrelatedOwner.target +native(
  MetaCheck.AxiomCheck.UnrelatedOwner.owner)

end UnrelatedOwner

namespace ForgedDependency

axiom owner._native.native_decide.ax_1_1 : False
theorem owner : False := owner._native.native_decide.ax_1_1

/-- error: 'MetaCheck.AxiomCheck.ForgedDependency.owner._native.native_decide.ax_1_1' looks like a native_decide axiom owned by 'MetaCheck.AxiomCheck.ForgedDependency.owner', but it was not emitted inside that declaration -/
#guard_msgs (whitespace := lax) in
assert_axioms MetaCheck.AxiomCheck.ForgedDependency.owner +native(
  MetaCheck.AxiomCheck.ForgedDependency.owner)

end ForgedDependency

namespace MacroForged

/-! The forgery `ForgedDependency` cannot express. A top-level `axiom` command is necessarily its
own command, so its start lands *before* the owner's — which is what makes that case detectable.
Macro expansion removes exactly that tell: every declaration a macro emits inherits the macro
*invocation site* as its declaration range, so the axiom and the theorem using it share one
identical range. A non-strict start comparison accepts that automatically, and the census would
then certify an arbitrary axiom — here `False` — as a `native_decide` compiler-trust certificate.
`rangeStartsInside` therefore requires the auxiliary to start *strictly* after the owner, which no
macro-emitted sibling can do while both genuine shapes (`Genuine`, `GenuineAutoParam`) still can. -/

macro "forge " n:ident " : " t:term : command =>
  `(axiom $(Lean.mkIdent (n.getId ++ `_native ++ `native_decide ++ `ax_1_1)) : $t
    theorem $n : $t := $(Lean.mkIdent (n.getId ++ `_native ++ `native_decide ++ `ax_1_1)))

forge owner : False

/-- error: 'MetaCheck.AxiomCheck.MacroForged.owner._native.native_decide.ax_1_1' looks like a native_decide axiom owned by 'MetaCheck.AxiomCheck.MacroForged.owner', but it was not emitted inside that declaration -/
#guard_msgs (whitespace := lax) in
assert_axioms MetaCheck.AxiomCheck.MacroForged.owner +native(
  MetaCheck.AxiomCheck.MacroForged.owner)

end MacroForged

namespace SecondCertificate

/-! Two genuine certificates in one cone. The allowance compares the exact *set* of native axioms
reached against the set the named owners actually own, so an annotation that names only the first
owner goes stale the moment a second certificate enters the cone. Comparing owner sets alone would
not suffice: distinct axioms can share an owner name (see `AliasedOwner`). -/

theorem first : (234567 : Nat) < 234568 := by native_decide

theorem second : (345678 : Nat) < 345679 := by native_decide

theorem target : (234567 : Nat) < 234568 ∧ (345678 : Nat) < 345679 := ⟨first, second⟩

/-- error: MetaCheck.AxiomCheck.SecondCertificate.target: '+native' names [MetaCheck.AxiomCheck.SecondCertificate.first] but the native_decide axiom(s) present are owned by [MetaCheck.AxiomCheck.SecondCertificate.first, MetaCheck.AxiomCheck.SecondCertificate.second]; write '+native(MetaCheck.AxiomCheck.SecondCertificate.first, MetaCheck.AxiomCheck.SecondCertificate.second)' -/
#guard_msgs (whitespace := lax) in
assert_axioms MetaCheck.AxiomCheck.SecondCertificate.target +native(
  MetaCheck.AxiomCheck.SecondCertificate.first)

assert_axioms MetaCheck.AxiomCheck.SecondCertificate.target +native(
  MetaCheck.AxiomCheck.SecondCertificate.first,
  MetaCheck.AxiomCheck.SecondCertificate.second)

end SecondCertificate

namespace AliasedOwner

/-! A certifying declaration whose *own* name contains the marker components. Its auxiliary is
`owner.native_decide.smuggled._native.native_decide.ax_1_1`, so reading ownership off the prefix
before the *first* `_native`/`native_decide` component would credit it to `owner` — collapsing it
onto the legitimate certificate, where a pre-existing `+native(owner)` would cover both and admit
an undisclosed compiler-trust dependency. Ownership is decided by the *last* marker instead, so the
smuggled certificate keeps its own owner and the stale annotation fails the build. -/

theorem owner : (456789 : Nat) < 456790 := by native_decide

namespace owner.native_decide

theorem smuggled : (567890 : Nat) < 567891 := by native_decide

end owner.native_decide

theorem target : (456789 : Nat) < 456790 ∧ (567890 : Nat) < 567891 :=
  ⟨owner, owner.native_decide.smuggled⟩

/-- error: MetaCheck.AxiomCheck.AliasedOwner.target: '+native' names [MetaCheck.AxiomCheck.AliasedOwner.owner] but the native_decide axiom(s) present are owned by [MetaCheck.AxiomCheck.AliasedOwner.owner, MetaCheck.AxiomCheck.AliasedOwner.owner.native_decide.smuggled]; write '+native(MetaCheck.AxiomCheck.AliasedOwner.owner, MetaCheck.AxiomCheck.AliasedOwner.owner.native_decide.smuggled)' -/
#guard_msgs (whitespace := lax) in
assert_axioms MetaCheck.AxiomCheck.AliasedOwner.target +native(
  MetaCheck.AxiomCheck.AliasedOwner.owner)

/-! The disclosure the census demands: the smuggled certificate is attributed to its own
declaration, not aliased onto `owner`. -/
assert_axioms MetaCheck.AxiomCheck.AliasedOwner.target +native(
  MetaCheck.AxiomCheck.AliasedOwner.owner,
  MetaCheck.AxiomCheck.AliasedOwner.owner.native_decide.smuggled)

end AliasedOwner

namespace ComputableSafety

/-! The `assert_computable` declaration checks. `unsafe` lifts the termination check, so the
reduction below inhabits `False` by bare self-reference while computing nothing — and it is a
`.defnInfo` that is not `noncomputable`, so the kind and computability checks both pass it. Only
the definition-safety check rejects it. The kernel independently refuses to let a safe declaration
depend on an unsafe one, so what the check has to catch is a reduction no safe proof consumes:
precisely a deliverable endpoint, which the census pins directly for that same reason. -/

unsafe def unsafeReduction : False := unsafeReduction

/-- error: MetaCheck.AxiomCheck.ComputableSafety.unsafeReduction is marked unsafe -/
#guard_msgs (whitespace := lax) in
assert_computable MetaCheck.AxiomCheck.ComputableSafety.unsafeReduction

/-! `partial def` elaborates to an `opaque` constant carrying an unsafe implementation, so it is
rejected one check earlier — as not a `def` at all. Pinned so a toolchain that instead emits a
`.defnInfo` with `partial` safety is caught by the safety check rather than passing silently. -/

partial def partialReduction (n : Nat) : Nat :=
  if n = 0 then 0 else partialReduction (n - 1)

/-- error: MetaCheck.AxiomCheck.ComputableSafety.partialReduction is not a def -/
#guard_msgs (whitespace := lax) in
assert_computable MetaCheck.AxiomCheck.ComputableSafety.partialReduction

/-! The positive case, so the rejections above are not passing vacuously. -/

def safeReduction (n : Nat) : Nat := n + 1

assert_computable MetaCheck.AxiomCheck.ComputableSafety.safeReduction

end ComputableSafety

namespace UnneededChoice

/-! An over-broad `+choice` is rejected: the flag on a reduction that never reaches
`Classical.choice` would silently over-state the trusted base, mirroring how a stale
`+native` owner list is rejected. The choice-free reduction is the positive case's shape. -/

def choiceFreeReduction (n : Nat) : Nat := n + 1

/-- error: MetaCheck.AxiomCheck.UnneededChoice.choiceFreeReduction does not depend on Classical.choice; drop the '+choice' flag -/
#guard_msgs (whitespace := lax) in
assert_computable MetaCheck.AxiomCheck.UnneededChoice.choiceFreeReduction +choice

/-! The genuine-`+choice` positive case: choice entering through an erased `Prop` field. -/

def choiceUsingReduction (n : Nat) : { m : Nat // ∃ k, m = n + k } :=
  ⟨n + 1, Classical.choice ⟨⟨1, rfl⟩⟩⟩

assert_computable MetaCheck.AxiomCheck.UnneededChoice.choiceUsingReduction +choice

end UnneededChoice

end MetaCheck.AxiomCheck
