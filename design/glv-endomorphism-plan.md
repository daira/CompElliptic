# GLV endomorphism: implementation plan

Status as of 2026-07-13: nothing GLV-related exists in the repo. A grep for
`glv|endomorph|lambda|cube root` returns one unrelated TODO line about windowed
scalar multiplication. This document is the design for the first step.

Every Lean fragment below was compiled against this repo's pinned Mathlib
(`lake env lean`) before being written down. The prototypes lived in a scratch
directory, not in the repo, so nothing here is committed code yet.

## Context

The goal is the GLV endomorphism on the Pasta curves: the map
`phi(x, y) = (zeta * x, y)`, where `zeta` is a primitive cube root of unity in
the base field, which acts on the prime-order group as multiplication by a
scalar `lambda` (a primitive cube root of unity in the scalar field). The first
step is the endomorphism itself plus the field and curve properties it rests
on, verified both by proof and by property-based tests. Scalar decomposition
(`k = k1 + k2 * lambda`) is deliberately deferred to a follow-on.

### What already exists to build on

| Piece | File |
| --- | --- |
| Pasta base/scalar fields `ZMod p` / `ZMod q`, Pratt certificates | `CompElliptic/Fields/Pasta.lean` |
| Short-Weierstrass kernel (`OnCurve`, `add`, `neg`, `Valid`), `SWCurve` / `SWPoint`, `AddCommGroup` | `CompElliptic/CurveForms/ShortWeierstrass.lean` |
| Fast `n` smul `P` (binary double-and-add, `native_decide`-friendly at 2^254) | `CompElliptic/ScalarMul.lean` |
| Pallas/Vesta as `SWCurve`, test point `G = (-1, 2)` | `CompElliptic/Curves/Pasta.lean` |
| Group order `= q` (Pallas) / `= p` (Vesta), given the `HasseBound` hypothesis | `CompElliptic/CurveOrder.lean`, `CompElliptic/Curves/PastaOrder.lean` |

Plausible is already available transitively via Mathlib and is listed in
`lake-manifest.json`, so the property-based tests need no new dependency.

## Findings

### 1. phi is an additive endomorphism, and it needs no hypotheses at all

The slope scales by `zeta^2` in *both* branches of `add`, so a single algebraic
core covers doubling and the generic case:

- distinct x: `(y2 - y1) / (zeta*x2 - zeta*x1) = zeta^-1 * s = zeta^2 * s`,
  since `zeta^-1 = zeta^2` when `zeta^3 = 1`;
- doubling (with `A = 0`): `3*(zeta*x)^2 / (2*y) = zeta^2 * (3*x^2 / (2*y))`.

Then in both branches `x3 |-> zeta^4 * s^2 - zeta*x1 - zeta*x2 = zeta * x3`
(using `zeta^4 = zeta`) and `y3 |-> zeta^3 * s * (x1 - x3) - y1 = y3`.

The branch guards are preserved exactly: `zeta != 0` gives
`(zeta*x, y) = (0,0) <-> (x,y) = (0,0)`, and `zeta*x1 = zeta*x2 <-> x1 = x2`,
while `y` is untouched. The two junk-division cases (`y = 0`, `x1 = x2`) are
also consistent, because both sides produce `0/0 = 0`.

Consequently `phi_add` requires no `Valid` hypothesis, no `IsElliptic`, and no
`b != 0`. Only `A = 0` and `zeta^3 = 1`.

(Correction, from implementing it: the plan originally claimed `phi_add` would
depend on *no axioms whatsoever*. It does not. As implemented, every declaration
in the module reports `[propext, Classical.choice, Quot.sound]`, pulled in
through Mathlib's `Field` and division machinery. That is the same footprint the
existing group-law lemmas have, so nothing is lost, but the stronger claim was
wrong.)

The one real constraint is that **`A = 0` is required**: for `A != 0`,
`y^2 = (zeta*x)^3 + A*(zeta*x) + B` fails.

The slope-scaling step is a clean, hypothesis-free lemma:

```lean
theorem zeta_inv {z : F} (hz : z ^ 3 = 1) : z⁻¹ = z ^ 2 :=
  inv_eq_of_mul_eq_one_right (by linear_combination hz)

theorem div_zeta_mul {z : F} (hz : z ^ 3 = 1) (a b : F) :
    a / (z * b) = z ^ 2 * (a / b) := by
  rw [div_mul_eq_div_div_swap, div_eq_mul_inv _ z, zeta_inv hz]; ring
```

### 2. phi = [lambda] needs no cyclic-group machinery

`IsCyclic`, `zpowers`, `Finite` and `Fintype` are all unnecessary. Mathlib has a
direct additive lemma that derives `Finite` internally from `Nat.card G = p`
plus primality.

| Lemma | File | Signature |
| --- | --- | --- |
| `mem_multiples_of_prime_card` | `Mathlib/GroupTheory/SpecificGroups/Cyclic/Basic.lean:155` (`to_additive` of `mem_powers_of_prime_card`) | `{G} [AddGroup G] {p} [Fact p.Prime] (h : Nat.card G = p) {g g' : G} (hg : g != 0) : g' in AddSubmonoid.multiples g` |
| `AddSubmonoid.mem_multiples_iff` | `Mathlib/Algebra/Group/Submonoid/Membership.lean` | `x in AddSubmonoid.multiples z <-> exists n : Nat, n smul z = x` |
| `map_nsmul` | `Mathlib/Algebra/Group/Hom/Defs.lean` | `[AddMonoidHomClass F G H] (f : F) (n : Nat) (a : G) : f (n smul a) = n smul f a` |
| `nsmul_left_comm` | Mathlib (`Algebra/Group/Defs` area) | `(a : M) (m n : Nat) : n smul m smul a = m smul n smul a` |

That yields a five-line capstone (compiled; `#print axioms` reports
`[propext, Classical.choice, Quot.sound]`):

```lean
theorem endo_eq_nsmul_of_prime_card {G : Type*} [AddGroup G] {r : ℕ} [Fact r.Prime]
    (hcard : Nat.card G = r) (f : G →+ G) {g : G} (hg : g ≠ 0) {lam : ℕ}
    (hspot : f g = lam • g) (x : G) : f x = lam • x := by
  obtain ⟨n, rfl⟩ := (AddSubmonoid.mem_multiples_iff x g).mp (mem_multiples_of_prime_card hcard hg)
  rw [map_nsmul, hspot, nsmul_left_comm]
```

Using `mem_multiples` (over `Nat`) rather than `mem_zmultiples` (over `Int`) is
what keeps `lam : Nat`, which is what `binNsmul` and `native_decide` want.

Also verified as existing but **not needed**: `isAddCyclic_of_prime_card`,
`zmultiples_eq_top_of_prime_card`, `mem_zmultiples_of_prime_card`,
`AddMonoidHom.map_addCyclic`, `IsAddCyclic.exists_generator`.

Threading `hHasse`: the `SWPoint` capstone takes `hcard : Nat.card (SWPoint E) = r`
as an ordinary argument, so the per-curve theorem just takes `hHasse` and feeds
it to `Pallas.card_eq hHasse`. No new machinery.

### 3. The numeric obligations are mostly kernel `decide`

Verified with `#print axioms` (all `[propext, Classical.choice, Quot.sound]`,
about 0.4s total with `set_option maxRecDepth 10000`):

- `ZETA ^ 3 = 1`, `ZETA != 1`, `ZETA ^ 2 + ZETA + 1 = 0` (in `PallasBaseField` /
  `VestaBaseField`): plain `by decide`.
- `LAMBDA < PALLAS_SCALAR_CARD`, `(LAMBDA : PallasScalarField) ^ 3 = 1`,
  `(LAMBDA : PallasScalarField) ^ 2 + LAMBDA + 1 = 0`: plain `by decide`.

This matters: because `zeta^3 = 1` is kernel-proved, the *definition* of `phiPt`
carries no `native_decide` axiom.

The point spot-check `phiPt Gpt = LAMBDA smul Gpt` **must** be `native_decide`.
Kernel `decide` gets genuinely stuck (not merely slow): `binNsmul` is
well-founded recursion, so its equations do not reduce definitionally, and
`decide` bails at `instDecidableEqSWPoint`. This is the same reason the existing
`scalarCard_nsmul_Gpt` uses `native_decide`. Both the Pallas and Vesta
spot-checks pass by `native_decide`.

Final axiom footprint of `Pallas.phi_eq_lambda_nsmul` (measured): the three
standard axioms, plus the pre-existing `PastaOrder` `native_decide` axioms, plus
one new one for the spot-check. No new *kind* of trust.

### 4. Plausible for crypto-size fields

Current API (plausible rev `86210d4`, Lean 4.30 era), confirmed by reading the
source:

- `Plausible.Arbitrary a` (`Plausible/Arbitrary.lean`): just `arbitrary : Gen a`.
- `Plausible.Shrinkable a` (`Plausible/Shrinkable.lean`): `shrink : a -> List a`,
  with a `{}` default of `fun _ => []`.
- `Plausible.SampleableExt a` (`Plausible/Sampleable.lean`): there is a
  `@[default_instance] selfContained` built from `[Repr a] [Shrinkable a]
  [Arbitrary a]`. So you write only `Arbitrary` and `Shrinkable`; `SampleableExt`
  comes free.
- `Testable`'s forall-instance is `varTestable [SampleableExt a] ...`; the base
  case is `decidableTestable [PrintableProp p] [Decidable p]`. The body
  proposition **must be `Decidable`**. `PrintableProp` has a low-priority
  catch-all instance, so it is never an obligation.

**The size problem.** `Fin.Arbitrary`, `Nat.Arbitrary` and `BitVec.Arbitrary` all
clamp with `min (<- getSize) n`, and `getSize <= maxSize = 100`, so they produce
values in `[0, 100]`. Useless for a 254-bit field. There is no
`Arbitrary (ZMod n)` anywhere; Mathlib's `Mathlib/Testing/Plausible/Sampleable.lean`
adds only `Rat` and `PNat`.

**But `Gen.choose Nat 0 (n-1)` is genuinely uniform for a 254-bit `n`.** Traced:
`BoundedRandom Nat -> rand (Fin _) -> randFin -> randNat` (`Init/Data/Random.lean:102`),
and `randNat` uses the Haskell `randomIvalInteger` algorithm: `randNatAux`
accumulates about nine successive 31-bit `StdGen` draws into a `k * 1000`
magnitude value before reducing mod `k`, giving under 1/1000 bias. It is not
limited to a single 31-bit draw, so no manual 64-bit composition is needed.

The generator (compiled and tested; sampled values measured at `log2` = 253, 252,
250, 246, i.e. full width and independent of the `size` parameter):

```lean
open Plausible

instance instArbitraryZMod (n : ℕ) [NeZero n] : Arbitrary (ZMod n) where
  arbitrary := do
    let ⟨v, _⟩ ← Gen.choose Nat 0 (n - 1) (Nat.zero_le _)
    return (v : ZMod n)

instance instShrinkableZMod (n : ℕ) : Shrinkable (ZMod n) := {}   -- no shrinking
```

`Repr (ZMod n)` already exists (`ZMod.repr`, `Mathlib/Data/ZMod/Defs.lean:157`),
so `SampleableExt` is inferred. Give the trivial `Shrinkable` deliberately:
halving the `ZMod.val` representative of a field element is algebraically
meaningless (it produces an unrelated element, not a simpler one) and just burns
time. Counterexamples then report as `(0 shrinks)` with the raw 254-bit witness.

**`#test` versus the `plausible` tactic.**

- `#test` is `macro tk:"#test " e:term : command => `(command| #eval%$tk Testable.check $e)`
  (`Plausible/Testable.lean:620`). It is an `#eval`, so `lake build` runs it, and a
  counterexample is a `Lean.throwError`, hence a build failure. That is the
  behaviour we want.
- `#test` takes no `Configuration`. To set `numInst` or `randomSeed`, write
  `#eval Plausible.Testable.check p { numInst := 25, randomSeed := some 42 }`.
- **Do not use the `plausible` tactic in library code.** It closes the goal with
  `sorry` when it finds no counterexample (confirmed: `declaration uses 'sorry'`).
  It is a disproof search, not a proof. Only `#test` and `#eval Testable.check`
  are safe under the no-`sorry` policy.

**Performance (measured, baseline import cost subtracted).**

| Workload | Time |
| --- | --- |
| 200 interpreted 254-bit `SWPoint` scalar mults (`#eval`) | 10.3s, about 51ms each |
| `Testable.check`, 200 instances x 2 scalar mults | 24s (about 0.12s/instance) |
| The real GLV `#test`s, 25 instances each, 4-8 mults | 6.5s |
| All the `decide` field-level numeric facts | 0.4s |

So roughly 50ms per interpreted 254-bit scalar multiplication. At the default
`numInst = 100`, a property with two scalar mults costs about 10s; three or four
such properties would add about a minute to every build of that module. Hence the
separate, non-default test library below.

## Implementation plan

### 1. `CompElliptic/CurveForms/Endomorphism.lean` (new, about 140 lines)

Imports `CompElliptic.CurveForms.ShortWeierstrass` and
`Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic`. Reopens the namespace
`CompElliptic.CurveForms.ShortWeierstrass`: this is a *layer* on the short
Weierstrass form, not a new form, which is why it is not a new `CurveForms/`
form module. It must not go in `CurveOrder.lean`, which would be circular
(`CurveOrder` imports `ShortWeierstrass`).

Three layers, mirroring `CurveOrder.lean`'s own structure. Every proof here is a
real proof: no `decide`, no `native_decide`.

```lean
-- Section 1: pure finite-group theory (no curves)
theorem endo_eq_nsmul_of_prime_card {G : Type*} [AddGroup G] {r : ℕ} [Fact r.Prime]
    (hcard : Nat.card G = r) (f : G →+ G) {g : G} (hg : g ≠ 0) {lam : ℕ}
    (hspot : f g = lam • g) (x : G) : f x = lam • x
-- mem_multiples_of_prime_card + AddSubmonoid.mem_multiples_iff + map_nsmul + nsmul_left_comm

-- Section 2: raw computable kernel (A = 0)
def phi (z : F) (p : F × F) : F × F := (z * p.1, p.2)
theorem zeta_ne_zero  {z : F} (hz : z ^ 3 = 1) : z ≠ 0
theorem zeta_inv      {z : F} (hz : z ^ 3 = 1) : z⁻¹ = z ^ 2
theorem div_zeta_mul  {z : F} (hz : z ^ 3 = 1) (a b : F) : a / (z * b) = z ^ 2 * (a / b)
@[simp] theorem phi_origin (z : F) : phi z ((0, 0) : F × F) = (0, 0)
theorem phi_eq_origin_iff {z : F} (hz : z ^ 3 = 1) (p : F × F) : phi z p = (0, 0) ↔ p = (0, 0)
theorem onCurve_phi {b z : F} (hz : z ^ 3 = 1) {p} (h : OnCurve 0 b p) : OnCurve 0 b (phi z p)
                                             -- linear_combination h - p.1 ^ 3 * hz
theorem valid_phi   {b z : F} (hz : z ^ 3 = 1) {p} (h : Valid 0 b p) : Valid 0 b (phi z p)
theorem phi_addXY   {z : F} (hz : z ^ 3 = 1) (lam x1 y1 x2 : F) : ...  -- shared chord/tangent core
theorem phi_add     {z : F} (hz : z ^ 3 = 1) (p q : F × F) :
    phi z (add 0 p q) = add 0 (phi z p) (phi z q)          -- no Valid hyps; zero axioms

-- Section 3: SWPoint level
def SWPoint.phiPt {E : SWCurve F} (hA : E.A = 0) {z : F} (hz : z ^ 3 = 1) : SWPoint E → SWPoint E
theorem SWPoint.phiPt_add ...
def SWPoint.phiHom ... : SWPoint E →+ SWPoint E
theorem SWPoint.phiPt_eq_nsmul {E : SWCurve F} (hA : E.A = 0) {z : F} (hz : z ^ 3 = 1)
    {r : ℕ} [Fact r.Prime] (hcard : Nat.card (SWPoint E) = r)
    {G : SWPoint E} (hG : G ≠ 0) {lam : ℕ} (hspot : SWPoint.phiPt hA hz G = lam • G)
    (P : SWPoint E) : SWPoint.phiPt hA hz P = lam • P
  := endo_eq_nsmul_of_prime_card hcard (SWPoint.phiHom hA hz) hG hspot P
```

`phiPt` takes the two proofs as arguments; they are `Prop`s, hence erased, so
`native_decide` on `phiPt ... Gpt = LAMBDA smul Gpt` works (verified).

The `phi_addXY` core needs exactly two `linear_combination`s (both verified):

```lean
⟨by linear_combination (-(z * lam ^ 2)) * hz,
 by linear_combination (lam ^ 3 * (1 + z ^ 3) - 2 * lam * x1 - lam * x2) * hz⟩
```

Write `phi_add`'s branch walk with explicit `by_cases` plus `rw [if_pos/if_neg ...]`
(as `add_eq_addXY` does), **not** `split_ifs <;> simp_all`: the nested `ite`s blow
the recursion limit, exactly as the `add_neg` docstring already warns.

### 2. `CompElliptic/Curves/PastaEndo.lean` (new, about 70 lines)

Imports `CompElliptic.Curves.PastaOrder` and `CompElliptic.CurveForms.Endomorphism`.
Needs `set_option maxRecDepth 10000` for the `decide`s.

```lean
namespace CompElliptic.Curves.Pasta.Pallas

def ZETA   : PallasBaseField := 0x2d33357cb532458ed3552a23a8554e5005270d29d19fc7d27b7fd22f0201b547
def LAMBDA : ℕ               := 0x397e65a7d7c1ad71aee24b27e308f0a61259527ec1d4752e619d1840af55f1b1

theorem A_zero      : curve.A = 0 := rfl                       -- real proof
theorem ZETA_cube   : ZETA ^ 3 = 1 := by decide                -- kernel, axiom-clean
theorem ZETA_ne_one : ZETA ≠ 1 := by decide
theorem ZETA_quad   : ZETA ^ 2 + ZETA + 1 = 0 := by decide     -- primitivity
theorem LAMBDA_lt   : LAMBDA < PALLAS_SCALAR_CARD := by decide
theorem LAMBDA_cube : (LAMBDA : PallasScalarField) ^ 3 = 1 := by decide
theorem LAMBDA_quad : (LAMBDA : PallasScalarField) ^ 2 + LAMBDA + 1 = 0 := by decide

/-- The GLV endomorphism `φ(x, y) = (ζ·x, y)` on the Pallas group. -/
def phi (P : SWPoint curve) : SWPoint curve := SWPoint.phiPt A_zero ZETA_cube P

theorem phi_Gpt : phi Gpt = LAMBDA • Gpt := by native_decide   -- the ONE new native_decide

/-- **φ = [λ] on the whole Pallas group** (assuming Hasse's bound). -/
theorem phi_eq_lambda_nsmul (hHasse : HasseBound curve) (P : SWPoint curve) :
    phi P = LAMBDA • P :=
  SWPoint.phiPt_eq_nsmul A_zero ZETA_cube (card_eq hHasse) Gpt_ne_zero phi_Gpt P

end CompElliptic.Curves.Pasta.Pallas
```

Vesta is identical with the *crossed* pair (the two fields swap roles):

```
Vesta.ZETA   : VestaBaseField := 0x06819a58283e528e511db4d81cf70f5a0fed467d47c033af2aa9d2e050aa0e4f
Vesta.LAMBDA : ℕ              := 0x12ccca834acdba712caad5dc57aab1b01d1f8bd237ad31491dad5ebdfdfe4ab9
```

plus `Vesta.card_eq hHasse : Nat.card (SWPoint curve) = PALLAS_BASE_CARD` and the
existing `Fact (Nat.Prime PALLAS_BASE_CARD)`.

Each `zeta` pairs with exactly ONE of the two `lambda`s, so the wrong pairing is
a live hazard. That is precisely why `phi_Gpt` is a checked fact rather than a
comment. (The constants above were computed and cross-checked numerically
against the group law before being written down; the Pallas pair matches the
`pasta_curves` `ENDO_BASE` / `ENDO_SCALAR` convention.)

Optional corollaries, cheap (from `phi_eq_lambda_nsmul` + `LAMBDA_quad` +
`card_nsmul_eq_zero'`), and worth having because they are what GLV decomposition
actually consumes:

- `phi (phi (phi P)) = P` (`φ³ = id`)
- `phi (phi P) + phi P + P = 0` (the `φ² + φ + 1 = 0` relation)

If `lambda` should later live in `PallasScalarField` rather than `Nat`, the route
is `AddCommGroup.zmodModule : (∀ x : G, n • x = 0) → Module (ZMod n) G`, with the
hypothesis discharged by `card_nsmul_eq_zero'` plus `card_eq hHasse`. Deferring
that is fine: `lam : Nat` is what keeps `binNsmul` and `native_decide` fast.

### 3. `CompElliptic.lean` (edit)

Add `import CompElliptic.CurveForms.Endomorphism` and
`import CompElliptic.Curves.PastaEndo`.

### 4. `CompEllipticTests/` (new test library)

- `CompEllipticTests/Arbitrary.lean`: the `Arbitrary (ZMod n)` and
  `Shrinkable (ZMod n)` instances from finding 4. Keep them inside the test
  library so the global instance cannot leak into library elaboration.
- `CompEllipticTests/PastaEndo.lean`: the properties.
  - Cheap (default `numInst`, microseconds):
    `#test ∀ x : PallasBaseField, ZETA * (ZETA * (ZETA * x)) = x` and
    `#test ∀ x : PallasBaseField, ZETA^2 * x + ZETA * x + x = 0`.
  - Expensive (`numInst := 25`, fixed `randomSeed`): `phi` additive on random
    group elements (`j.val • Gpt`, `k.val • Gpt`), and
    `phi (k.val • Gpt) = LAMBDA • (k.val • Gpt)`. Both pass (6.5s combined).
  - Uniform random group elements come free: `k : PallasScalarField` mapped to
    `k.val • Gpt` is uniform over the whole prime-order group, at the cost of one
    scalar mult. No point-decompression or sqrt generator is needed.
- `CompEllipticTests.lean`: root module importing both.

Prefer field-level properties wherever possible (they are free) and reserve the
group-level ones for low `numInst`.

### 5. `lakefile.lean` (edit)

```lean
lean_lib CompEllipticTests   -- deliberately NOT @[default_target]
```

No `require plausible` is needed: it is already a transitive dependency via
Mathlib and `import Plausible` resolves (verified). Leaving the test library off
the default target keeps plain `lake build`, and hence the existing `lean-action`
CI job, unaffected by the roughly 50ms-per-scalar-mult interpreted cost.

### 6. `.github/workflows/ci.yml` (edit)

Add a third job, "Property tests (plausible)", running `lake build CompEllipticTests`
after the Mathlib cache fetch, so the fast "Build (lake)" job stays fast and can
remain the required branch-protection check.

### 7. `TODO.md` (edit)

Add a GLV endomorphism entry under the short-Weierstrass form section, plus a
follow-on entry for **GLV scalar decomposition**: `k = k1 + k2 * lambda (mod r)`
with `|k1|, |k2| ~ sqrt(r)`, via the short lattice basis of
`{(a, b) : a + b*lambda = 0 (mod r)}`. That is a separate, mostly arithmetic job.
The balanced-basis constants are `native_decide`-checkable closed facts, and the
correctness statement `k • P = k1 • P + k2 • (phi P)` follows immediately from
`phi_eq_lambda_nsmul`. The bound on `|k1|, |k2|` is the only genuinely new work.

## Dependency order

1. `CurveForms/Endomorphism.lean` section 1 (group theory): independent, 5 lines.
2. Section 2, the raw kernel: independent of section 1.
3. Section 3, the `SWPoint` layer: needs sections 1 and 2.
4. `Curves/PastaEndo.lean`, Pallas: needs section 3 and the existing `PastaOrder`.
5. Vesta: a copy of step 4.
6. Test library, lakefile, CI: independent of steps 1-5 except for the constants.

## Verification

- `lake build` must stay green and `sorry`-free, and must keep its current speed
  (the test library is not a default target).
- `lake build CompEllipticTests` runs the `#test`s; a counterexample throws and
  fails the build.
- `#print axioms` on each new declaration:
  - `phi_add` and the section-1 group-theory lemma: no new axioms.
  - `ZETA_cube` and friends: the three standard axioms only.
  - `Pallas.phi_eq_lambda_nsmul` / `Vesta.phi_eq_lambda_nsmul`: the three standard
    axioms, the pre-existing `PastaOrder` `native_decide` axioms, and exactly one
    new `native_decide` axiom (the `phi_Gpt` spot-check).

## Risks and open items

- **`precompileModules := true`** on the test library was not tested. It should let
  the interpreter call native code for CompElliptic's own definitions, but the
  inner loop is Mathlib's `ZMod` and `Field` instance dictionaries, which stay
  interpreted, so expect only a modest gain. Measure before relying on it.
- `maxRecDepth 10000` sufficed for every `decide` tried. If a future `decide` on a
  bigger literal chokes, `native_decide` is the fallback; it remains a per-curve
  closed numeric fact, so it stays within the trust discipline.
- The placement of `endo_eq_nsmul_of_prime_card` is a style call. It is
  form-agnostic, so it could live in `CurveOrder.lean`, but `CurveOrder` imports
  `ShortWeierstrass`, so splitting the feature across two files would buy nothing.
