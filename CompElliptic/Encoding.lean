/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.Logic.Denumerable

/-!
# Encodings

An *encoding* maps an element type `G` into a type `D` of *depictions* — possible encoded forms
of elements that may or may not be decodable. `D` will typically be `BitVec ℓ`, a byte vector, etc.
We coin the term "depiction" to avoid confusion between encodings (the mappings) and depictions
(the encoded forms). `encode : G → D` is total and injective; `decode : D → Option G` is *partial*.

There are two encoding types, explicitly-named siblings so the choice between them is always
deliberate:

- `CanonicalEncoding G D` — the everyday type. `decode` is *canonical*: it accepts only canonical
  depictions (`IsCanonical`).
- `LenientEncoding G D` — `encode` / `decode` / `encodek` with *no* canonicity requirement, so
  `decode` may accept non-canonical depictions.

`EncodingClass` is the shared interface (`encode` / `decode` / `encodek`); both structures are
instances, so the tagged-depiction types below apply to either with prefix syntax.

In Zcash, for example, the encodings (see
[Zcash Protocol Specification §5.4.9](https://zips.z.cash/protocol/protocol.pdf#concretepairing))
of Pallas and Vesta curve points are canonical; the encodings of Jubjub curve points were
originally lenient, but additional canonicity checks were specified in [ZIP 216](https://zips.z.cash/zip-0216)
(actually the history is more complicated). To faithfully model situations like this, we
need both kinds of encoding.

## Two notions of validity

For any encoding `e`, a depiction can be:

- **decodable** — `(decode e r).isSome` (`decodableSet`); decoding yields some element.
- **canonical** — `r ∈ Set.range (encode e)` (`canonicalSet`); `r` is `encode g`, i.e. it decodes
  *and* round-trips.

`canonical ⊆ decodable` always holds; the notions coincide when `e` is a canonical encoding
(`CanonicalEncoding.canonicalSet_eq_decodableSet`). For lenient encodings they differ, and
—since conflating them is a common class of mistake— the API never says "valid": you must
name `Canonical` or `Decodable`.

## Tagged-depiction types

These types support local reasoning by allowing a depiction to be *tagged* with its intended
encoding, and whether it has been checked as decodable or canonical:

- `Raw e` — an unchecked depiction of `G` under `e`. This is type-distinct from a bare `D`,
  or a depiction for a different encoding.
- `Decodable e` — a depiction of `G` that is guaranteed to be decodable under `e`.
- `Canonical e` — a depiction of `G` that is guaranteed to be canonical under `e`.

`Canonical.decoded` and `Decodable.decoded` are total: they always return an element.

`encodingEquiv e : G ≃ Canonical e` gives the bijection between elements and their canonical
depictions.

A raw depiction can be validated using `checkCanonical : Raw e → Option (Canonical e)` or
`checkDecodable : Raw e → Option (Decodable e)`. A decodable depiction can be checked to be
already canonical (`Decodable.checkCanonical`) or canonicalized (`Decodable.canonicalize`).
`Canonical.toDecodable` is the obvious inclusion.

With `D = ℕ`, `toEncodable` witnesses that a `LenientEncoding` refines `Encodable G`. (There
is no `Denumerable` analogue: that needs `G` infinite, whereas cryptographic objects are
almost always finite.)
-/

namespace CompElliptic

/-- `IsCanonical encode decode` holds when `decode` accepts only canonical depictions:
anything it decodes re-encodes to itself. This is stated on the bare maps so that it can
be proved/refuted about a candidate decoder implementation. -/
def IsCanonical {G D : Type*} (encode : G → D) (decode : D → Option G) : Prop :=
  ∀ {r g}, decode r = some g → encode g = r

/-- The interface shared by the encoding variants: the `encode` / `decode` / `encodek` maps.
The tagged-depiction types are defined over this class, so they apply to either variant as
`Raw e` etc. -/
class EncodingClass (E : Type*) (G D : outParam Type*) where
  /-- Encode an element. -/
  encode : E → G → D
  /-- Decode a depiction. -/
  decode : E → D → Option G
  /-- Decoding undoes encoding. -/
  encodek : ∀ (e : E) (g : G), decode e (encode e g) = some g

/-- A lenient encoding: `encode` / `decode` / `encodek`, with *no* canonicity requirement. -/
structure LenientEncoding (G D : Type*) where
  /-- Encode an element. -/
  encode : G → D
  /-- Decode a depiction. -/
  decode : D → Option G
  /-- Decoding undoes encoding. -/
  encodek : ∀ g, decode (encode g) = some g

/-- A canonical encoding: a `LenientEncoding` whose `decode` is additionally `IsCanonical`. -/
structure CanonicalEncoding (G D : Type*) extends LenientEncoding G D where
  /-- `decode` accepts only canonical depictions (anything it decodes re-encodes to itself). -/
  canonical : IsCanonical encode decode

instance {G D : Type*} : EncodingClass (LenientEncoding G D) G D where
  encode e := e.encode
  decode e := e.decode
  encodek e := e.encodek

instance {G D : Type*} : EncodingClass (CanonicalEncoding G D) G D where
  encode e := e.encode
  decode e := e.decode
  encodek e := e.encodek

variable {E G D : Type*} [inst : EncodingClass E G D]

/-- The decodable depictions of `e`: those on which `decode` succeeds. -/
def decodableSet (e : E) : Set D := {r | (EncodingClass.decode e r).isSome}

/-- The canonical depictions of `e`: the image of `encode`. -/
def canonicalSet (e : E) : Set D := Set.range (EncodingClass.encode e)

/-- `encode e g` is a canonical depiction. -/
theorem encode_mem_canonicalSet (e : E) (g : G) : EncodingClass.encode e g ∈ canonicalSet e :=
  ⟨g, rfl⟩

/-- A canonical depiction is decodable. -/
theorem isSome_decode_of_mem_canonicalSet {e : E} {r : D} (h : r ∈ canonicalSet e) :
    (EncodingClass.decode e r).isSome := by
  obtain ⟨g, rfl⟩ := h
  rw [EncodingClass.encodek]
  rfl

/-- `canonical ⊆ decodable`, for any encoding. -/
theorem canonicalSet_subset_decodableSet (e : E) : canonicalSet e ⊆ decodableSet e :=
  fun _ h => isSome_decode_of_mem_canonicalSet h

/-- `encode` is injective. -/
theorem encode_injective (e : E) : Function.Injective (EncodingClass.encode e) := fun a b h => by
  have hk := EncodingClass.encodek e a
  rw [h, EncodingClass.encodek e b] at hk
  exact (Option.some.inj hk).symm

/-- An unchecked depiction of a `G` element under `e`. Phantom-tagged by `e`, so type-distinct from
a bare `D` and from a depiction under a different encoding. (The `EncodingClass` binder is explicit
so that `Raw e` can infer `D` from `e`'s instance; the sole field `depiction : D` would not pin it.) -/
@[ext] structure Raw {E G D : Type*} [EncodingClass E G D] (e : E) where
  /-- The underlying (unchecked) depiction. -/
  depiction : D

/-- A decodable depiction under `e`: one on which `decode` succeeds. -/
@[ext] structure Decodable (e : E) where
  /-- The underlying depiction, with a proof that it is decodable. -/
  depiction : decodableSet e

/-- A canonical depiction under `e`: one in the image of `encode`. -/
@[ext] structure Canonical (e : E) where
  /-- The underlying depiction, with a proof that it is canonical. -/
  depiction : canonicalSet e

namespace Decodable

variable {e : E}

/-- Forget decodability, yielding a `Raw e`. -/
def toRaw (v : Decodable e) : Raw e := ⟨v.depiction.1⟩

/-- Decode a decodable depiction (total). -/
def decoded (v : Decodable e) : G := (EncodingClass.decode e v.depiction.1).get v.depiction.2

end Decodable

namespace Canonical

variable {e : E}

/-- Forget canonicity, yielding a `Raw e`. -/
def toRaw (v : Canonical e) : Raw e := ⟨v.depiction.1⟩

/-- A canonical depiction is decodable. -/
def toDecodable (v : Canonical e) : Decodable e :=
  ⟨⟨v.depiction.1, isSome_decode_of_mem_canonicalSet v.depiction.2⟩⟩

/-- Decode a canonical depiction (total). -/
def decoded (v : Canonical e) : G :=
  (EncodingClass.decode e v.depiction.1).get (isSome_decode_of_mem_canonicalSet v.depiction.2)

end Canonical

/-- Decode an unchecked depiction (partial). -/
def decodedRaw {e : E} (r : Raw e) : Option G := EncodingClass.decode e r.depiction

/-- Encode an element as a canonical depiction. -/
def encodeCanonical (e : E) (g : G) : Canonical e :=
  ⟨⟨EncodingClass.encode e g, encode_mem_canonicalSet e g⟩⟩

/-- Canonicalize a decodable depiction: decode it and re-encode to the canonical form. -/
def Decodable.canonicalize {e : E} (v : Decodable e) : Canonical e := encodeCanonical e v.decoded

/-- Check whether a decodable depiction is *already* canonical, returning it unchanged as a
`Canonical e` if so (`none` if non-canonical). Contrast `canonicalize`, which re-encodes. -/
def Decodable.checkCanonical [DecidableEq D] {e : E} (v : Decodable e) : Option (Canonical e) :=
  if h : EncodingClass.encode e v.decoded = v.depiction.1 then
    some ⟨⟨v.depiction.1, ⟨v.decoded, h⟩⟩⟩
  else none

/-- `encode` as the bijection `G ≃ Canonical e`. -/
def encodingEquiv (e : E) : G ≃ Canonical e where
  toFun := encodeCanonical e
  invFun := Canonical.decoded
  left_inv g := by
    simp only [encodeCanonical, Canonical.decoded]
    apply Option.some.inj
    rw [Option.some_get]
    exact EncodingClass.encodek e g
  right_inv v := by
    obtain ⟨⟨r, g, rfl⟩⟩ := v
    apply Canonical.ext
    apply Subtype.ext
    show EncodingClass.encode e (Canonical.decoded _) = EncodingClass.encode e g
    congr 1
    simp only [Canonical.decoded]
    apply Option.some.inj
    rw [Option.some_get]
    exact EncodingClass.encodek e g

/-- Check whether a raw depiction is decodable. -/
def checkDecodable {e : E} (r : Raw e) : Option (Decodable e) :=
  match h : EncodingClass.decode e r.depiction with
  | some _ => some ⟨⟨r.depiction, by simp only [decodableSet, Set.mem_setOf_eq, h, Option.isSome_some]⟩⟩
  | none => none

/-- Check whether a raw depiction is canonical (decodes *and* re-encodes to itself). -/
def checkCanonical [DecidableEq D] {e : E} (r : Raw e) : Option (Canonical e) :=
  match EncodingClass.decode e r.depiction with
  | some g => if h : EncodingClass.encode e g = r.depiction then some ⟨⟨r.depiction, ⟨g, h⟩⟩⟩ else none
  | none => none

/-- With `D = ℕ`, a lenient encoding gives an `Encodable` (whose `decode` is partial). -/
@[reducible] def toEncodable (e : LenientEncoding G ℕ) : Encodable G where
  encode := e.encode
  decode := e.decode
  encodek := e.encodek

namespace CanonicalEncoding

variable {G D : Type*} (e : CanonicalEncoding G D)

/-- The usable form of the `canonical` field: anything `decode` accepts re-encodes to itself. -/
theorem decode_canonical {r : D} {g : G} (h : e.decode r = some g) : e.encode g = r := e.canonical h

/-- For a canonical encoding, the two notions of validity coincide. -/
theorem canonicalSet_eq_decodableSet : canonicalSet e = decodableSet e := by
  ext r
  constructor
  · intro h
    exact isSome_decode_of_mem_canonicalSet h
  · intro h
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h
    exact ⟨g, e.decode_canonical hg⟩

end CanonicalEncoding

end CompElliptic
