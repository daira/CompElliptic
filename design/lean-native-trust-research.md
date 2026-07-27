# `native_decide`, the IR interpreter, and precompiled dylibs: mechanism and trust base (Lean v4.30.0)

Research informing CompElliptic's trust enforcement: what `native_decide` and
`#eval` actually execute, when locally compiled native code (Lake
`precompileModules` dylibs) enters the evaluation path, and which attributes
(`@[extern]`, `@[implemented_by]`, `@[csimp]`) widen the trusted code base. It
motivates the design rule below and grounds the trust analysis of the
fast-arithmetic PRs (CompElliptic#13, ironwood#111).

Produced 2026-07-27 by a Claude Fable 5 agent, against the `v4.30.0` tag of
leanprover/lean4 (commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, release
published 2026-05-26), plus Zulip and documentation searches.

All file citations are at the `v4.30.0` tag of `leanprover/lean4` unless otherwise
noted.

## Design rule: `@[csimp]` justification theorems require an axiom check

Every theorem used to justify an `@[csimp]` replacement in CompElliptic (or in
any dependency under our control) must be covered by an explicit axiom check
confirming that its proof depends on nothing beyond the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — in particular, not on
`sorryAx` or any project-local axiom. Concretely: a guarded test file with
`#print axioms thm` output under `.expected`, or a CI assertion built on
`Lean.collectAxioms`, for each such theorem.

Rationale: the csimp obligation is an ordinary kernel-checked theorem, so its
axiom dependencies are well-defined and queryable — but possibly only indirect,
via lemmas its proof uses, and so not visible at its own source. Per open
[lean4#7463](https://github.com/leanprover/lean4/issues/7463) those axioms are
**not** propagated into `#print axioms` of the downstream `native_decide` proofs
that execute the substituted code, so a csimp lemma whose axioms go unchecked is
an axiom-smuggling channel. Background: Appendix A (consequence 3) and Q4 below.

---

## Q1. What, officially, does `native_decide` add to the trusted code base?

**Answer.** The canonical enumeration is: the Lean **compiler**, the Lean
**interpreter**, and all **`@[implemented_by]`** and **`@[extern]`** annotations
(including the foreign implementations behind extern symbols).

Citations (verbatim):

- `src/Init/Core.lean`, lines 2375-2379 — docstring of the (now-deprecated)
  `Lean.trustCompiler` axiom:
  > Depends on the correctness of the Lean compiler, interpreter, and all
  > `[implemented_by ...]` and `[extern ...]` annotations.
- `src/Init/Core.lean`, lines 2382-2399 — docstring of `Lean.reduceBool`:
  > Warning: by using this feature, the Lean compiler and interpreter become part
  > of your trusted code base. [...] Recall that the compiler trusts the
  > correctness of all `[implemented_by ...]` and `[extern ...]` annotations.
  > If an extern function is executed, then the trusted code base will also
  > include the implementation of the associated foreign function.
- `src/Init/Core.lean`, lines 2423-2437 — docstring of `Lean.ofReduceBool`
  (repeats the compiler/interpreter warning).
- `src/Init/Tactics.lean`, lines 1405-1420 — `native_decide` docstring:
  > This should be used with care because it adds the entire lean compiler to the
  > trusted part, and a new axiom will show up in `#print axioms` ...
- `src/Init/Tactics.lean`, lines 1320-1325 and 1350-1354 — `DecideConfig.native`
  / `decide +native` docs:
  > ...at the cost of increasing the trusted code base, namely the Lean compiler
  > and all definitions with an `@[implemented_by]` attribute.

`@[csimp]` is deliberately absent from the enumeration because it requires a
kernel-checked proof of `@f = @g` (`src/Lean/Compiler/CSimpAttr.lean`, lines
57-69) — but see the #7463 caveat under Q4, and Appendix A for the full attribute
comparison.

**Confidence: high** (verbatim from v4.30.0 sources).

## Q2. Does `native_decide` invoke C compilation at proof time, or does it evaluate through the IR interpreter?

**Answer.** Neither the C compiler nor any machine-code generation is invoked at
proof time; evaluation goes through the **IR interpreter**. The v4.30.0 tactic
path:

1. `evalNativeDecide` → `evalDecideCore` → `elabNativeDecideCore`
   (`src/Lean/Elab/Tactic/Decide.lean`, lines 55-66, 184-187);
2. → `Lean.Meta.nativeEqTrue` (`src/Lean/Meta/Native.lean`, lines 37-87), which
   creates an auxiliary `Bool` definition, runs `addAndCompile` (the Lean-side
   compiler pipeline down to λRC IR stored in the environment — no `.c`
   emission), then runs `unsafe evalConst Bool auxDeclName`;
3. `evalConst` lands in `lean_eval_const` → `run_boxed` → `interpreter::call_boxed`
   in `src/library/ir_interpreter.cpp` (lines 1157-1190, 1065-1094);
4. if the value is `true`, `nativeEqTrue` **asserts a fresh per-proof axiom
   `e = true`** (`Native.lean`, lines 75-87) — the kernel never re-runs the
   computation.

The legacy kernel path still exists at v4.30.0 for the deprecated `reduceBool`
route: `reduce_native` in `src/kernel/type_checker.cpp` (lines 546-567) calls
`ir::run_boxed_kernel`, which is the same IR interpreter (`ir_interpreter.cpp`,
line 1170) — again no C compilation. The interpreter's header comment (lines 7-26)
is explicit that it exists to avoid runtime code generation.

**Confidence: high** (full call chain read in source). Minor unverified link: the
`evalConst` → `lean_eval_const` `@[extern]` binding was inferred from the
`Native.lean` usage and symbol name, not read directly in
`src/Lean/Environment.lean`.

## Q3. Does the IR interpreter dispatch calls to native symbols when they are available?

That is, does it dispatch calls to `@[extern]` primitives, toolchain-shipped
core, and Lake `precompileModules` dylibs — so that any evaluation (`#eval` or
`native_decide`) in an importing module executes locally compiled code?

**Answer.** Yes to all three, with per-function granularity.

Mechanism (`src/library/ir_interpreter.cpp`):

- `lookup_symbol` (lines 826-869) mangles each called function's name and — when
  `m_prefer_native || decl_tag(...) == decl_kind::Extern || has_init_attribute(...)`
  (line 848) — resolves the "boxed" symbol via `lookup_symbol_in_cur_exe`, which
  is `dlsym(RTLD_DEFAULT, sym)` on POSIX / `EnumProcessModules` +
  `GetProcAddress` on Windows (lines 341-363), i.e. it searches the **entire
  process image**.
- (a) `@[extern]` declarations are always dispatched natively (the `Extern`
  disjunct); runtime primitives live in the toolchain shared libraries.
- (b) Toolchain-compiled core (`libleanshared` / `libInit_shared`) resolves
  because those libraries are part of the `lean` process, and `m_prefer_native`
  defaults to `true`: `LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE true` (lines
  54-55), option `interpreter.prefer_native` — "whether to use precompiled code
  where available" (lines 1047, 1217-1219).
- (c) Plugin/dynlib symbols resolve because dynlibs are loaded with
  `dlopen(path, RTLD_LAZY | RTLD_GLOBAL)`; `src/library/dynlib.cpp`, lines 79-90:
  > Both dynlibs and plugins are loaded with RTLD_GLOBAL. This ensures the
  > interpreter has access to plugin definitions that are also imported ...

Lake side:

- `precompileModules` docstring, `src/lake/Lake/Config/LeanLibConfig.lean`,
  lines 75-82:
  > Whether to compile each of the library's modules into a native shared
  > library that is loaded whenever the module is imported. This speeds up
  > evaluation of metaprograms and enables the interpreter to run functions
  > marked `@[extern]`. Defaults to `false`.
- Lake passes these libraries to downstream `lean` invocations via
  `--load-dynlib` / `--plugin` (`src/lake/Lake/Build/Module.lean`, lines
  519-573, 1169).

**Load-bearing conclusion:** a `native_decide` (or `#eval`) elaborating in a
module that imports a `precompileModules` library **will execute the locally
compiled dylib code** for every imported function whose mangled symbol resolves.
The freshly declared auxiliary `Bool` definition itself is interpreted at top
level, but its calls into the precompiled library dispatch to native code.

Official documentation corroboration —
[Elaboration and Compilation (Lean reference manual)](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/):
> If the `precompileModules` option is set in the build configuration, then this
> native code can be dynamically loaded and invoked by Lean; otherwise, an
> interpreter is used.

Note: the global native-symbol cache assumes no libraries are loaded/unloaded
after first interpreter use (`ir_interpreter.cpp`, lines 375-378).

**Confidence: high** (mechanism verified end-to-end in source, corroborated by
official docs).

## Q4. What has changed recently (2024-2026) in the code generator, `native_decide`, and their trust story?

Four load-bearing developments, plus history:

1. **One axiom per native computation** —
   [PR #12217](https://github.com/leanprover/lean4/pull/12217) implementing
   [RFC #12216](https://github.com/leanprover/lean4/issues/12216)
   (Joachim Breitner), merged 2026-02-03. `native_decide` / `bv_decide` now
   assert one named axiom per computation (e.g. `thm._native.native_decide.ax...`)
   instead of going through `ofReduceBool`; goals include external-checker
   checkability "up to the native calculation" and removing the kernel→compiler
   hook. `reduceBool` / `reduceNat` / `ofReduceBool` / `trustCompiler` are all
   `@[deprecated ... "in-kernel native reduction is deprecated; assert native
   evaluations with axioms instead" (since := "2026-02-01")]`
   (`src/Init/Core.lean`, lines 2375-2437), though the kernel hook still exists
   at v4.30.0. Ship vehicle (verified by tag containment): the merge commit is
   contained in `v4.29.0-rc1` (2026-02-17) but not `v4.28.0-rc1`, so it first
   shipped in the v4.29.0 release candidates, and is in stable
   v4.29.0/v4.30.0.
2. **Stricter meta checks** —
   [PR #13005](https://github.com/leanprover/lean4/pull/13005), merged
   2026-03-20; first in v4.30.0-rc1 (2026-04-01). Modules used in compile-time
   execution must be `meta` imported; `nativeEqTrue` correspondingly sets
   `Compiler.compiler.relaxedMetaCheck` (`Native.lean`, lines 58-60). A proposed
   kernel-side `@[allow_native_decide]` restriction
   ([PR #11790](https://github.com/leanprover/lean4/pull/11790)) is **unmerged**.
3. **New code generator** — the old compiler was replaced by the new
   (LCNF-based) code generator in
   [Lean 4.22.0, 2025-08-14](https://lean-lang.org/doc/reference/latest/releases/v4.22.0/);
   "the compiler" in the trust enumeration now denotes this pipeline
   (`src/Lean/Compiler/IR/ToIR.lean` etc.); the IR interpreter's role is
   unchanged.
4. **Trust-story discussions** —
   - Zulip, Oct 2023: ["soundness bug: native_decide leakage"](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/soundness.20bug.3A.20native_decide.20leakage.html)
     (Mario Carneiro): nondeterministic IO under `reduceBool` proved `False`
     with empty `#print axioms`; fixed by threading the `trustCompiler` axiom
     through `reduceBool`/`reduceNat`
     ([PR #2654](https://github.com/leanprover/lean4/pull/2654)).
   - Still **open**: [issue #7463](https://github.com/leanprover/lean4/issues/7463)
     — `@[csimp]` proofs using `sorry`/axioms are not propagated through
     `native_decide`'s axiom tracking (Zulip:
     ["Axioms used by csimp are not reported"](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Axioms.20used.20by.20csimp.20are.20not.20reported/near/505140945)).
     v4.30.0's csimp docstring carries a corresponding warning
     (`CSimpAttr.lean`, lines 68-69).
   - `decide +native` / `DecideConfig` unification:
     [PR #5999](https://github.com/leanprover/lean4/pull/5999) (Nov 2024).

**Confidence: high** on each enumerated item (verified via source, PR metadata,
and tag-containment checks); **medium** on Zulip *completeness* (searches were
targeted, not an exhaustive 2024-2026 sweep).

### Flagged as unverified

- The exact v4.29.0 official release-notes wording for PR #12217 (the GitHub
  release body is empty; notes live on the docs site).
- The `evalConst` → `lean_eval_const` extern binding (inferred, not read).
- Whether any caller overrides the `interpreter.prefer_native` default (only the
  interpreter constructor was checked).

---

## Appendix A: `@[extern]` vs `@[implemented_by]` vs `@[csimp]`

Common frame: the kernel (proof checker) sees one definition; the compiler can
be told to emit different code. All three are code-substitution directives that
proofs, `decide`, and kernel reduction never see; `#eval`, compiled binaries,
and `native_decide` do see them.

| Attribute | Replacement | Proof obligation | Trusted? |
|---|---|---|---|
| `@[extern "sym"]` | foreign (C) symbol | none | yes |
| `@[implemented_by g]` | another Lean definition `g` (may be `unsafe`/`partial`) | none | yes |
| `@[csimp] theorem : @f = @g` | constant `g` for constant `f` | kernel-checked equality | no (modulo the compiler itself, and #7463) |

### The exact shape of `@[csimp]`

The attribute requires a proof that the two functions are **equal as whole
values** — the statement must be literally `@f = @g`, where both sides are bare
constants (the unapplied functions themselves), and nothing else.

From the attribute's validation code at v4.30.0, `src/Lean/Compiler/CSimpAttr.lean`:

- Lines 40-49 (`isConstantReplacement?`): the theorem's type must match `Eq` with
  both sides being `Expr.const` — i.e. plain constants, not applications, not
  lambdas. The universe levels must be distinct parameters and identical on both
  sides (so `f` and `g` are equated at exactly the same, fully general
  universes).
- Line 55: anything else is rejected with `invalid 'csimp' theorem, only constant
  replacement theorems (e.g., `@f = @g`) are currently supported.`
- Docstring, lines 63-66: *"A compiler simplification theorem cannot take any
  parameters and must prove a statement `@f = @g` where `f` and `g` may be
  arbitrary constants. In functions defined after the theorem tagged `@[csimp]`,
  any occurrence of `f` is replaced with `g` in compiled code, but not in the
  type theory."*

Three practical consequences:

1. **It's function-level equality, not pointwise.** You cannot tag
   `theorem : ∀ xs, List.set xs i a = List.setTR xs i a`. You state
   `@List.set = @List.setTR` (the `@` just means the constant with no arguments
   applied, implicits and all) and typically prove it by `funext` followed by
   induction. That's exactly what core does, e.g. `src/Init/Data/List/Impl.lean`,
   line 78: `@[csimp] theorem set_eq_setTR : @set = @setTR := by ...`. Since the
   equation is between the constants as a whole, the compiler's job is trivial:
   wherever compiled code mentions the constant `f`, substitute the constant `g`
   (`replaceConstant?`, lines 83-90 — note it only fires when the expression *is*
   that constant).
2. **No hypotheses, no parameters.** The equality must hold unconditionally,
   because the compiler will apply the replacement everywhere, in every context.
3. **The proof is an ordinary kernel-checked theorem** — that's the whole point
   versus `@[implemented_by]`, which asserts the substitution with no proof at
   all. But "requires a proof" is only as strong as what the proof depends on:
   the v4.30.0 docstring itself now carries the caveat added in response to
   lean4#7463, lines 68-69: *"However it is still possible to register unsound
   `@[csimp]` lemmas by using `unsafe` or unsound axioms (like `sorryAx`)."* If
   you discharge the `@f = @g` obligation with `sorry` or a bogus axiom, the
   substitution still happens in compiled code, and (per that issue, still open)
   `#print axioms` on a downstream `native_decide` proof won't show the smuggled
   axiom.

So the mental model: `@[extern]`/`@[implemented_by]` say "trust me, run this
other code instead"; `@[csimp]` says the same thing but demands you first prove
`@f = @g` in the logic — one theorem, exactly that shape.

`@[implemented_by]` example in core (`src/Init/Util.lean`, lines 127-140):
`withPtrEq` / `withPtrAddr` are given `unsafe` pointer-based implementations —
the key capability `csimp` cannot provide, since `unsafe` definitions cannot
appear in proofs.

---

## Appendix B: what λRC IR is, and why the mechanism hinges on it

**IR** = intermediate representation. **λRC** (lambda-RC, where **RC** =
reference counting) is the name of the compiler IR Lean 4 uses for code
generation and interpretation. The name comes from the paper *Counting Immutable
Beans: Reference Counting Optimized for Purely Functional Programming*
(Sebastian Ullrich and Leonardo de Moura), which defines two calculi:

- **λPure** — a small, first-order, pure functional language: functions,
  full/partial applications, constructor allocation, field projection, `case`,
  join points. No memory management visible.
- **λRC** — λPure extended with *explicit* memory-management instructions:
  `inc` / `dec` (reference-count increment/decrement) and `reset` / `reuse`
  (destructive reuse of a uniquely-referenced heap cell, the basis of **FBIP**,
  "functional but in-place", updates).

Lean's implementation says this verbatim — `src/Lean/Compiler/IR/Basic.lean`
(v4.30.0), module docstring: *"Implements (extended) λPure and λRc proposed in
the article 'Counting Immutable Beans', Sebastian Ullrich and Leonardo de
Moura."* The datatype `Lean.IR.FnBody` contains the paper's instructions
directly: `vdecl`, `jdecl` (join points), `case`, plus `inc`/`dec` (lines
234-239), `reset`/`reuse` (lines 182-184), unboxed-field ops
`uset`/`sset`/`uproj`/`sproj`, and `box`/`unbox`.

### Where it sits in the pipeline (v4.30.0, new code generator)

```
surface syntax
  --elaborator-->  kernel terms (Expr, dependently typed)        [checked by kernel]
  --new compiler-->  LCNF                                        [Lean Compiler Normal Form]
  --ToIR-->  λPure IR
  --RC-insertion passes-->  λRC IR   (stored per-declaration in an
                                      environment extension, serialized to .olean)
       ├--EmitC--> .c file --bundled clang--> .o --> executable / shared lib
       ├--EmitLLVM--> LLVM bitcode                       (optional backend)
       └--IR interpreter--> direct evaluation            (#eval, native_decide, initializers)
```

**LCNF** = **Lean Compiler Normal Form** — the typed, ANF-style (**ANF** =
administrative normal form: every intermediate value bound to a variable)
representation the new code generator (default since
[Lean 4.22.0](https://lean-lang.org/doc/reference/latest/releases/v4.22.0/))
uses for its optimization passes (inlining, specialization, erasure of
proofs/types). After the mono phase, `Lean.Compiler.IR.ToIR`
(`src/Lean/Compiler/IR/ToIR.lean` at v4.30.0) lowers LCNF into the IR; the
RC-insertion and borrow-inference passes from the paper then turn λPure into
λRC.

### Its role — why everything in the report hinges on it

1. **Single semantic contract for both execution modes.** The C backend and the
   interpreter consume the *same* λRC program. Because reference counting is
   explicit in the IR (an `inc` is an instruction, not a runtime policy),
   interpreted code and compiled code perform identical heap operations on the
   same `lean_object` heap. This is what makes the per-function mixing in Q3
   sound: an interpreted frame can call a native frame and vice versa
   mid-computation.
2. **The ABI boundary.** IR-level signatures (**ABI** = application binary
   interface) plus the generated `_boxed` wrappers — which take and return
   uniform `lean_object*` values — give every compiled function a homogeneous
   calling convention. That is exactly what `ir_interpreter.cpp` exploits: *"We
   always call the 'boxed' versions of native functions, which have a
   (relatively) homogeneous ABI that we can use without runtime code
   generation"* (header comment, lines 19-26). Without this, the
   `dlsym`-per-function dispatch to `precompileModules` dylibs couldn't exist.
3. **Distribution unit.** λRC IR is serialized into `.olean` files, so a
   downstream module can interpret an imported function without ever having
   compiled it to machine code — *"The interpreted IR is taken directly from the
   elab_environment"* (same comment). Native code is a strictly optional
   accelerant discovered at runtime by symbol lookup.
4. **Trust-base framing for `native_decide`.** "Trusting the Lean compiler"
   concretely means trusting `Expr → LCNF → λPure → λRC` (all passes shared by
   both paths), *plus* either the IR interpreter (always) or `EmitC` + the
   bundled C compiler (only for code that was precompiled). A bug in an LCNF or
   IR pass affects every `native_decide`; a bug in `EmitC`/clang only affects
   evaluations that dispatched into precompiled dylibs.

### Documentation links (λRC-specific)

- API docs for the IR itself:
  [Lean.Compiler.IR.Basic](https://lean-lang.org/doc/api/Lean/Compiler/IR/Basic.html)
  (verified — carries the λPure/λRC module description and documents `FnBody`,
  `inc`, `dec`, `reset`, `reuse`)
- The paper:
  [Counting Immutable Beans: Reference Counting Optimized for Purely Functional Programming](https://arxiv.org/abs/1908.05647)
  (arXiv 1908.05647)
- Pipeline overview in the reference manual:
  [Elaboration and Compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
  — *"the compiler is invoked to translate the intermediate representation of
  functions stored in its environment extension into C code. A C file is
  produced for each Lean module; these are then compiled to native code using a
  bundled C compiler."*
- New code generator becoming default:
  [Lean 4.22.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.22.0/)
- Interpreter design notes: header comment of `src/library/ir_interpreter.cpp`
  at v4.30.0 (lines 7-28)

One flag: the `IR/Basic.lean` docstring's remark that the Lean-to-IR
transformation "is implemented in C++" is stale wording from the old code
generator; at v4.30.0 the lowering is `ToIR.lean`, written in Lean.

---

## Appendix C: Lake and the precompiled lane in practice (observed, this repository)

Empirical findings on Lean/Lake v4.30.0, from experiments in this repository:

- **The default build emits and loads the lane dylib.** Plain `lake build` (default
  targets only) builds `FastFieldNative:shared`. The cause is not target membership
  but imports: the lane's own proof modules (`ProjectiveMontEquiv`, the vendored
  Montgomery theorem files, `TrustBoundary`) legitimately import the lane's
  definition modules, and Lake builds and loads the owning library's shared facet
  for their elaboration.
- **Declaration order and glob overlap are not an opt-in boundary.** The hypothesis
  that listing the `CompElliptic` library (whose `andSubmodules` glob covers the
  lane modules) before `FastFieldNative` would make the default build interpret
  them was tested and refuted: the shared facet is built regardless. Module-to-
  library ownership under overlapping globs is not a mechanism one should rely on
  for trust boundaries.
- **Consequence: the enforceable opt-in boundary is at checks, not loading.**
  Since dylib loading is inseparable from elaborating the lane's kernel-verified
  proofs, the invariant this repository enforces (`scripts/check_native_optin.py`)
  is: no module whose import closure reaches a lane module may contain an
  evaluation-based check (`#eval`, `#guard`, `native_decide`) unless explicitly
  opted in with a rationale. Loading is capability; executing a check through the
  loaded code is the trust event.
- **Related hazard: silent dylib-name collision.** Lean module names are global
  across a build, and a downstream repository declaring its own precompiled
  library with the same root module name as a dependency's collides silently —
  the build stays green, one shared object is never emitted, and the affected
  modules quietly run interpreted. Dotted library names avoid this.

## Sources

Documentation:

- [Elaboration and Compilation — Lean reference manual](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- [Lean 4.22.0 release notes (new code generator)](https://lean-lang.org/doc/reference/latest/releases/v4.22.0/)
- [Release notes index](https://lean-lang.org/doc/reference/latest/releases/)
- [Lean.Compiler.IR.Basic — API docs](https://lean-lang.org/doc/api/Lean/Compiler/IR/Basic.html)
- [Counting Immutable Beans (arXiv:1908.05647)](https://arxiv.org/abs/1908.05647)

Issues / PRs (leanprover/lean4):

- [#12216 RFC: one axiom per native computation](https://github.com/leanprover/lean4/issues/12216)
- [#12217 feat: one axiom per native computation](https://github.com/leanprover/lean4/pull/12217)
- [#13005 feat: stricter meta check for temporary programs in native_decide etc](https://github.com/leanprover/lean4/pull/13005)
- [#11790 feat: @[allow_native_decide] kernel check (unmerged)](https://github.com/leanprover/lean4/pull/11790)
- [#7463 @[csimp] can be used to smuggle axioms and unsafe into a proof (open)](https://github.com/leanprover/lean4/issues/7463)
- [#2654 chore: add axiom for tracing use of reduceBool / reduceNat](https://github.com/leanprover/lean4/pull/2654)
- [#5999 feat: decide +revert and improvements to native_decide](https://github.com/leanprover/lean4/pull/5999)

Zulip:

- [soundness bug: native_decide leakage (archive)](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/soundness.20bug.3A.20native_decide.20leakage.html)
- [Axioms used by csimp are not reported](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Axioms.20used.20by.20csimp.20are.20not.20reported/near/505140945)
