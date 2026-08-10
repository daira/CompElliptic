/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood, Tal Derei
-/
import CompElliptic.Meta.AxiomCheck

/-!
# Regression tests for the compiled-body-override checks

`@[implemented_by]` and `@[extern]` swap the body the compiler runs while the kernel keeps
reducing the original, and Lean checks no relation between the two. A declaration carrying either
is still a `.safe` `.defnInfo`, is not `noncomputable`, and introduces no axiom, so every other
check in `CompElliptic.Meta.AxiomCheck` passes it — which is what makes this the one census bypass
that reaches a *value*: a `native_decide` certificate over doctored data reports a match against
data the kernel refutes.

The declarations here are deliberately doctored, so they live in this test-only library, out of the
production `CompElliptic` import graph, alongside the forged axioms of `MetaCheck.AxiomCheck` —
and in a module of their own, because `checkCompiledBodyDisclosure` is a property of the whole
import closure: once an override exists here, every later census entry in this module fails, which
is exactly the third case below but would swamp the unrelated entries of the sibling file.

The order of this file is therefore load-bearing: the clean entries come first, while the module
still has nothing to report.
-/

namespace MetaCheck.CompiledOverride

/-! ## Clean module

Both commands pass while nothing in the closure substitutes a compiled body — so the rejections
below are not passing vacuously, and the disclosure check is not simply always-on. -/

def cleanReduction (n : Nat) : Nat := n + 1

assert_computable MetaCheck.CompiledOverride.cleanReduction

theorem cleanTheorem : (2 : Nat) + 2 = 4 := rfl

assert_axioms MetaCheck.CompiledOverride.cleanTheorem

/-! ## An ambient-package target

The disclosure sweep exempts the ambient roots — the toolchain and the pinned dependency stack, not
the toolchain alone. `Nat.add` is `@[extern]`, as are most of the arithmetic and container
primitives whose compiled code every `native_decide` runs regardless. Censusing one *directly* is a
different claim, though: there the substitution is the entry's own subject rather than background
compiler trust, and `assert_computable`'s "genuinely computed" would be asserted of a body that
never runs. The per-declaration check therefore applies to any target. -/

/-- error: Nat.add carries '@[extern]', so its compiled body is not the body the kernel reduces and Lean checks no relation between the two. Nothing this census verifies about the kernel term constrains what compiled code — a `native_decide` over it in particular — computes. -/
#guard_msgs (whitespace := lax) in
assert_computable Nat.add

/-! ## The bypass

`capturedData` stands in for natively-certified data: `assert_computable` sees a plain safe `def`
whose axioms are empty, `native_decide` evaluates the *compiled* body and certifies the match, and
the kernel disagrees — `refutesAtKernel` proves the negation of what `fingerprintMatch` proves,
both about the same constant. Every check that predates this file accepts the pair. -/

def honestCaptured : List Nat := [1, 2, 3]

unsafe def doctoredImpl : List Nat := [9, 9, 9]

@[implemented_by doctoredImpl] def capturedData : List Nat := honestCaptured

def target : List Nat := [9, 9, 9]

theorem fingerprintMatch : capturedData = target := by native_decide

theorem refutesAtKernel : capturedData ≠ target := by decide

/-- error: MetaCheck.CompiledOverride.capturedData carries '@[implemented_by]', so its compiled body is not the body the kernel reduces and Lean checks no relation between the two. Nothing this census verifies about the kernel term constrains what compiled code — a `native_decide` over it in particular — computes. -/
#guard_msgs (whitespace := lax) in
assert_computable MetaCheck.CompiledOverride.capturedData

/-! ## The certificate that consumes it

Pinning the doctored data is only half the bypass: the entry that actually launders it is the
`assert_axioms` on the `native_decide` certificate, whose own declaration is clean. What that entry
reaches is a compiled body, which no axiom footprint records — so it is caught by the closure-wide
disclosure check, naming the declaration responsible. -/

/-- error: MetaCheck.CompiledOverride.fingerprintMatch cannot be censused: MetaCheck.CompiledOverride.capturedData (@[implemented_by]) substitute(s) a compiled body Lean never checks against the kernel body, so the value the compiler runs is unconstrained by anything proved about it. If you must, use `@[csimp]` instead, but be aware that `@[csimp]` still substantially increases the trust surface. -/
#guard_msgs (whitespace := lax) in
assert_axioms MetaCheck.CompiledOverride.fingerprintMatch +native(
  MetaCheck.CompiledOverride.fingerprintMatch)

/-! An entry with no connection at all to the doctored declaration fails too. The census states the
artifact's trusted base, and an unchecked compiled body inside it is undisclosed compiler trust
wherever it sits; scoping the check to each entry's dependency cone would let the same commit that
adds the override keep every unrelated entry green. -/

/-- error: MetaCheck.CompiledOverride.honestCaptured cannot be censused: MetaCheck.CompiledOverride.capturedData (@[implemented_by]) substitute(s) a compiled body Lean never checks against the kernel body, so the value the compiler runs is unconstrained by anything proved about it. If you must, use `@[csimp]` instead, but be aware that `@[csimp]` still substantially increases the trust surface. -/
#guard_msgs (whitespace := lax) in
assert_computable MetaCheck.CompiledOverride.honestCaptured

/-! ## `@[extern]`

The same swap without an `unsafe` helper: the compiled body becomes a foreign symbol, about which
nothing at all is known. Both checks report it exactly as they report `@[implemented_by]`. -/

@[extern "compelliptic_metacheck_doctored_symbol"] def externData : List Nat := honestCaptured

/-- error: MetaCheck.CompiledOverride.externData carries '@[extern]', so its compiled body is not the body the kernel reduces and Lean checks no relation between the two. Nothing this census verifies about the kernel term constrains what compiled code — a `native_decide` over it in particular — computes. -/
#guard_msgs (whitespace := lax) in
assert_computable MetaCheck.CompiledOverride.externData

/-- error: MetaCheck.CompiledOverride.cleanTheorem cannot be censused: MetaCheck.CompiledOverride.capturedData (@[implemented_by]), MetaCheck.CompiledOverride.externData (@[extern]) substitute(s) a compiled body Lean never checks against the kernel body, so the value the compiler runs is unconstrained by anything proved about it. If you must, use `@[csimp]` instead, but be aware that `@[csimp]` still substantially increases the trust surface. -/
#guard_msgs (whitespace := lax) in
assert_axioms MetaCheck.CompiledOverride.cleanTheorem

end MetaCheck.CompiledOverride
