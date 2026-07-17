/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.Curves.PastaOrder
import CompElliptic.Fields.Sqrt
import CompElliptic.Meta.AxiomCheck

/-!
# Trust boundary, build-checked

The library-wide census that makes the *independently re-checkable trust* principle (see the
README) a build-time check rather than a prose claim. Each `assert_axioms` below pins an *upper
bound* on a declaration's trusted base, so a change that widens it — a `sorry`, a new axiom in a
general theorem, or `native_decide` creeping into a quantified result — fails this file rather than
passing silently. The declarations are grouped by trust tier:

* **General theorems** rest only on `propext` / `Classical.choice` / `Quot.sound`. A quantified
  result has no independent spot-check, so it must not reach beyond Lean's standard axioms.
* **Concrete closed facts checked by the kernel** (Pratt primality certificates) add nothing beyond
  those same axioms: the kernel evaluates them directly, trusting only its GMP bignum arithmetic
  (which even ordinary `decide` relies on and which axiom collection does not surface).
* **Concrete closed facts trusting the compiler** (`native_decide`, marked `+native`) each add a
  per-declaration compiler-trust axiom. This is the whole compiler-trust surface, confined to
  falsifiable numeric facts about the Pasta fields and curves — chiefly the order of the
  Tonelli–Shanks roots of unity (`pallasBase`/`vestaBase`) and the two prime-order witnesses behind
  the group orders. Each such fact is reproducible by an independent tool, so a miscompiled oracle
  could in principle be caught by disagreement (the catch requires someone actually performing the
  independent check).

`assert_axioms` matches on the axiom *tier*, not the exact `native_decide` axiom name (which is
toolchain-dependent), so this census stays green across toolchain bumps while still catching any
tier violation.
-/

open CompElliptic.Meta

/-! ## General theorems — standard axioms only -/

assert_axioms CompElliptic.CurveOrder.card_fibre_le_two
assert_axioms CompElliptic.CurveOrder.card_eq_of_prime_witness_of_card_lt_two_mul
assert_axioms CompElliptic.CurveOrder.card_eq_of_prime_witness_of_card_lt_three_mul
assert_axioms CompElliptic.Fields.TonelliShanks.sqrt?_mul_self
assert_axioms CompElliptic.Fields.TonelliShanks.sqrt?_isSome_of_isSquare

/-! ## Concrete closed facts checked by the kernel (Pratt certificates) — standard axioms only -/

assert_axioms CompElliptic.Fields.Pasta.PALLAS_BASE_is_prime
assert_axioms CompElliptic.Fields.Pasta.PALLAS_SCALAR_is_prime

/-! ## Concrete closed facts trusting the compiler (`native_decide`) -/

assert_axioms CompElliptic.Fields.Pasta.pallasBase +native
assert_axioms CompElliptic.Fields.Pasta.vestaBase +native
assert_axioms CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt +native
assert_axioms CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt +native
assert_axioms CompElliptic.Curves.Pasta.Pallas.card_eq +native
assert_axioms CompElliptic.Curves.Pasta.Vesta.card_eq +native
