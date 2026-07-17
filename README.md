# CompElliptic

Computable elliptic-curve abstractions for Lean 4, built in the style of (and on top of)
[CompPoly](https://github.com/Verified-zkEVM/CompPoly).

The aim is a *computable* development of elliptic curves and eventually pairings —across
multiple curve forms and coordinate systems, with correct-by-construction types— suitable for
reasoning about elliptic-curve arithmetic in formally verified settings, such as zero-knowledge
circuits. The first form is short Weierstrass over the Pasta (Pallas/Vesta) cycle.

## Design principles

CompElliptic follows a few named principles, chosen so that the type structure mirrors the
cryptography, mistakes are visible rather than silent, and the trusted base stays small and
auditable. They are referred to by name (rather than number) throughout the codebase, so the
references stay stable as the list evolves:

### Separate types with explicit conversions

Each abstraction level has its own Lean types, kept distinct:

* *group elements* — the mathematical notion;
* *internal representations* of group elements — valid coordinate representatives modulo
  an equivalence;
* *coordinates* — field elements tagged with which kind of coordinate they are;
* *depictions* — rich encoded values tagged with their encoding and what has been checked
  about them, to support local reasoning.

Conversions between these types are always explicit. There are no hidden coercions that
silently cross abstraction levels; every conversion is a named function. Each form bundles
its validity conditions into the type, taking full advantage of Lean's dependent type
system, so that illegal states are unrepresentable.

### Give mistakes nowhere to hide

No class of mistake you can make in a cryptographic protocol is hidden by the API. The type
discipline exists to turn potential errors —treating a non-canonical encoding as canonical;
getting an encoding's bit ordering wrong; using raw coordinates as a group element without
the on-curve check; using circuit cells that are not anchored to their intended source; etc.—
into a visible, type-level obligation.

### Independently re-checkable trust

Any reliance beyond the kernel and the standard axioms is confined to *concrete, closed facts*
about specific fields and curves — each a falsifiable claim that any independent implementation
could reproduce or refute. General theorems, which have no such spot-check, must only depend
on this core of Lean's trusted base. See [trust discipline](#trust-discipline) below for more
detail.

### Consistent terminology

Terminology is [carefully considered](design/naming-survey.md), and consistent with common
cryptographic usage and with the Zcash Protocol Specification.

### Efficiency without abstraction leaks

Although the focus of the library is not on performance, the types a specification writer
reaches for (especially for curve points / group elements) should not be horribly inefficient
for general computation. But implementation choices (such as the use of projective/Jacobian
coordinates) made to improve computational efficiency must not leak into CompElliptic's APIs.
The available API should precisely reflect only what is intended to be modelled.

## Trust discipline

The *independently re-checkable trust* principle rests on a few specifics. The trust extensions
that arise in practice in Lean are `native_decide` —which discharges a goal by running compiled
native code, adding a per-declaration compiler-trust axiom— and, unavoidably for numbers of this
size, the kernel's own GMP-backed bignum arithmetic, on which even ordinary `decide` depends.

In CompElliptic, we allow these extensions to be used only for concrete, closed facts with no
free variables: a Pratt primality certificate, a field's cardinality, the multiplicative order
of a fixed root of unity, a (non-)residuosity check. These facts are easily reproducible: another
computer-algebra system, proof assistant, bignum library, or hand computation would compute the
same result, so a miscompiled or buggy oracle could in principle be caught by disagreement rather
than silently believed — the catch requires someone actually performing the independent check.

A general, quantified theorem ranging over many objects (for example, the correctness of a
square-root algorithm for all finite fields it supports) has no analogous independent spot-check,
so it must rest only on `propext` / `Classical.choice` / `Quot.sound`. Two corollaries guide the
implementation:

* prefer kernel `decide` to `native_decide` wherever the computation is feasible for the kernel,
  since that removes the compiler and any `@[extern]` / `@[implemented_by]` overrides (although
  not GMP) from the trusted base;
* state each computational fact in a form an independent tool could re-verify.

This split is not just documented but checked at build time: `CompElliptic/TrustBoundary.lean` is a
census of representative declarations, each pinned with `assert_axioms` (a sibling of
`assert_no_sorry`) to the tier it is allowed to sit in. A general theorem that reaches for
`native_decide`, or a concrete fact that acquires an unexpected axiom, fails that file. The *Status*
section below summarizes how the split appears in the actual axiom dependencies.

## Status

Early work in progress. Present so far:

- the Pasta (Pallas/Vesta) base and scalar prime fields, with machine-verified Pratt primality
  certificates (`CompElliptic/Fields/Pasta.lean`);
- a computable short-Weierstrass affine group law with correct-by-construction `SWCurve` /
  `SWPoint` types — closure, commutativity, associativity, and the full `AddCommGroup (SWPoint E)`
  instance (including scalar multiplication), with associativity by transport to Mathlib's
  `WeierstrassCurve.Affine.Point` group (`CompElliptic/CurveForms/ShortWeierstrass.lean`);
- Pallas and Vesta as concrete `SWCurve` instances (`CompElliptic/Curves/Pasta.lean`);
- a curve-form-agnostic `CoordinateSystem` abstraction — a carrier with a validity predicate, an
  equivalence on representatives, and computable operations — yielding a derived `AddCommGroup` on
  the quotient, with affine as the `Rel = Eq` instance (`CompElliptic/CoordinateSystem.lean`);
- an `Encoding` abstraction distinguishing `CanonicalEncoding` from `LenientEncoding` over a shared
  `EncodingClass` interface, with encoded values ("depictions") tagged `Raw` / `Decodable` /
  `Canonical`, the bijection `G ≃ Canonical e`, and the canonical-versus-decodable distinction
  (`CompElliptic/Encoding.lean`);
- a computable Tonelli–Shanks square root for prime fields, soundness and completeness proved, with
  `pallasBase` / `vestaBase` instances (`CompElliptic/Fields/Sqrt.lean`);
- the compressed Pasta point encoding (`toBytes`) for Pallas and Vesta (`CompElliptic/Encodings/`).

Uses of `sorry` are kept minimal and limited to work-in-progress. The library's general theorems
depend only on the standard `propext` / `Classical.choice` / `Quot.sound` axioms. Facts specific to
concrete fields and curves additionally depend on `native_decide`'s per-declaration compiler-trust
axiom, confined (per the *Independently re-checkable trust* principle) to checks the kernel cannot
feasibly run, chiefly the order of the Tonelli–Shanks roots of unity. The tier of each is pinned in
`CompElliptic/TrustBoundary.lean`. Further coordinate systems (projective and Jacobian), curve
forms, the represented-group bridge, and the circuit model are tracked in [TODO.md](TODO.md).

## License

Dual-licensed under your choice of the Apache License, Version 2.0 or the MIT license.

## Acknowledgements

Claude Opus 4.8 was used in the development of this project.
