/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import CompElliptic.Fields.SafeGCD.Divstep
import Mathlib.Data.Int.ModEq

/-!
# Modular inversion by divsteps: the reference driver, proved correct

The safegcd inversion of libsecp256k1's `secp256k1_modinv64_var`, and of the Pasta port in
[zcash/pasta_curves#119](https://github.com/zcash/pasta_curves/pull/119), specified and proved
at the level of integers: `f` and `g` run the divstep recurrence of
`CompElliptic.Fields.SafeGCD.Divstep` while a pair of *coefficients* `d` and `e` tracks, modulo
`m`, how the current `f` and `g` were built from the input.

The scaled invariants carried across batches are

```text
  X * d ≡ seed * f   (mod m)        X * e ≡ seed * g   (mod m)
```

where `X` is the value being inverted and `seed` is the initial `e`. They hold at the start for
trivial reasons (`d = 0`, `f = m`, `e = seed`, `g = X`), and `step_good` shows a batch preserves
them. At termination `g = 0` and, by `run_eq_one_or_neg_one` (since `gcd (m, X) = 1`), `f = ±1`,
so the sign-corrected `d` satisfies `X * d ≡ seed (mod m)`. That is `invert_spec`, the headline
result.

The `seed` is a genuine parameter of the algorithm, and choosing it is what the Rust PR's
"no Montgomery conversion" trick amounts to:

* `seed = 1` gives the classical inverse `X⁻¹ mod m`;
* `seed = R²  mod m` gives `R² / X mod m`, which for a Montgomery representative `X = aR` is
  exactly `a⁻¹R`, the Montgomery representative of the inverse. No conversion into or out of
  Montgomery form is needed anywhere.

Nothing here is specific to a radix, a limb count, or a word size: `Params.width` is the number
of divsteps per batch (62 in the port) and `batches` the cap on the number of batches (12).

## Scope

This is *partial* correctness: an answer, when produced, is right. Totality, that `g` reaches
`0` within `batches` batches, is the Bernstein-Yang iteration bound
(`⌊(49 · b + 57) / 17⌋` divsteps suffice for `b`-bit inputs, so `738 ≤ 12 · 62` for the Pasta
fields), which is not proved here; the driver returns `none` instead of looping, so the theorem
is unconditional on it.

## Provenance

Ported from `src/fields/modinv62.rs` of
[zcash/pasta_curves#119](https://github.com/zcash/pasta_curves/pull/119), pinned at commit
`9299dfbb19978428ba24229bc13dff25a424dc46` (branch `modinv62`). Every `Rust:` link on a
declaration below points into that commit, so the line numbers stay valid even after the branch
moves; to review against the tip of the branch instead, open the pull request and diff.
-/

namespace CompElliptic.Fields.SafeGCD

/-- The parameters of a divstep inversion: the modulus, the number of divsteps per batch, the
seed for the coefficient `e`, and the modular inverse of `2 ^ width` used to undo each batch's
scaling. -/
structure Params where
  /-- The modulus, which must be odd and greater than `2`. -/
  m : Nat
  /-- The number of divsteps per batch (`62` in the 64-bit ports). -/
  width : Nat
  /-- The initial value of the coefficient `e`; `R ^ 2 mod m` for a Montgomery-native inverse,
  `1` for the classical one. -/
  seed : Nat
  /-- The inverse of `2 ^ width` modulo `m`, used to divide each batch's coefficient update. -/
  inv2w : Nat
deriving DecidableEq, Repr, Inhabited

namespace Params

/-- The modulus as an integer. -/
def M (P : Params) : Int := (P.m : Int)

/-- Well-formedness of a parameter set: an odd modulus above `2`, and `inv2w` really inverting
`2 ^ width`. Both are decidable, so a concrete instantiation discharges them by computation. -/
structure WF (P : Params) : Prop where
  /-- The modulus is odd, so every power of two is invertible modulo it. -/
  odd : P.m % 2 = 1
  /-- The modulus exceeds `2`; in particular `1` is its own canonical residue. -/
  two_lt : 2 < P.m
  /-- `inv2w` is the inverse of `2 ^ width` modulo `m`. -/
  inv2w_spec : P.inv2w * 2 ^ P.width % P.m = 1

end Params

/-- The state of the inversion driver: the divstep state `(eta, f, g)` together with the
coefficients `d` and `e`, kept reduced modulo `m`. -/
structure RState where
  /-- The divstep `eta`. -/
  eta : Int
  /-- The divstep `f`; starts at the modulus. -/
  f : Int
  /-- The divstep `g`; starts at the value being inverted and is driven to zero. -/
  g : Int
  /-- The coefficient tracking `f`: `X * d ≡ seed * f (mod m)`. -/
  d : Int
  /-- The coefficient tracking `g`: `X * e ≡ seed * g (mod m)`. -/
  e : Int
deriving DecidableEq, Repr, Inhabited

/-- The divstep part of a driver state. -/
def RState.toDState (s : RState) : DState := ⟨s.eta, s.f, s.g⟩

/-- One batch: `width` divsteps applied to `(f, g)`, and the same transition applied to the
coefficients `(d, e)` modulo `m`, undoing the batch's factor of `2 ^ width`.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L807-L874> -/
def RState.step (P : Params) (s : RState) : RState :=
  let p := run P.width s.toDState
  { eta := p.1.eta
    f := p.1.f
    g := p.1.g
    d := (p.2.u * s.d + p.2.v * s.e) * (P.inv2w : Int) % P.M
    e := (p.2.q * s.d + p.2.r * s.e) * (P.inv2w : Int) % P.M }

/-- The driver loop: run batches until `g` reaches zero, then read off the sign-corrected `d`,
paired with the number of batches consumed. Returns `none` if the batch budget is exhausted,
which is how the Bernstein-Yang iteration bound is kept out of the trusted statement.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L807-L874> -/
def loop (P : Params) : Nat → RState → Option (Int × Nat)
  | 0, _ => none
  | n + 1, s =>
      let s' := s.step P
      if s'.g = 0 then
        some ((if s'.f < 0 then (-s'.d) % P.M else s'.d % P.M), 1)
      else (loop P n s').map fun z => (z.1, z.2 + 1)

/-- Modular inversion by divsteps, reporting the number of batches consumed alongside the
answer. The count is what the Rust port pins in its regression-vector table.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L807-L874> -/
def invertCounted (P : Params) (batches : Nat) (x : Nat) : Option (Int × Nat) :=
  if x = 0 then none
  else loop P batches ⟨-1, (P.m : Int), (x : Int), 0, (P.seed : Int)⟩

/-- Modular inversion by divsteps: returns `y` with `x * y ≡ seed (mod m)`, given at most
`batches` batches of `P.width` divsteps.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L799-L805> -/
def invert (P : Params) (batches : Nat) (x : Nat) : Option Int :=
  (invertCounted P batches x).map Prod.fst

/-! ## The invariant -/

/-- The invariant carried across batches: `f` odd, the pair coprime, and the two scaled
congruences relating the coefficients to the divstep state.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L24-L27> -/
structure Good (P : Params) (x : Int) (s : RState) : Prop where
  /-- `f` is odd, the standing precondition of the divstep recurrence. -/
  odd : s.f % 2 = 1
  /-- The pair stays coprime, so the terminal `f` is a unit. -/
  cop : Int.gcd s.f s.g = 1
  /-- `X * d ≡ seed * f (mod m)`. -/
  dInv : x * s.d ≡ (P.seed : Int) * s.f [ZMOD P.M]
  /-- `X * e ≡ seed * g (mod m)`. -/
  eInv : x * s.e ≡ (P.seed : Int) * s.g [ZMOD P.M]

/-- Reducing modulo `n` does not change the residue class. -/
theorem emod_modEq (a n : Int) : a % n ≡ a [ZMOD n] := Int.emod_emod_of_dvd _ dvd_rfl

/-- `2 ^ width * inv2w ≡ 1 (mod m)`, the fact that makes each batch's division exact modulo the
modulus. -/
theorem two_pow_mul_inv2w (P : Params) (hP : P.WF) :
    (2 : Int) ^ P.width * (P.inv2w : Int) ≡ 1 [ZMOD P.M] := by
  have h : ((P.inv2w * 2 ^ P.width % P.m : Nat) : Int) = ((1 : Nat) : Int) := by
    exact_mod_cast congrArg (Nat.cast : Nat → Int) hP.inv2w_spec
  have hcast : ((P.inv2w : Int) * 2 ^ P.width) % P.M = 1 := by
    push_cast at h ⊢
    simpa [Params.M] using h
  calc (2 : Int) ^ P.width * (P.inv2w : Int)
      = (P.inv2w : Int) * 2 ^ P.width := by ring
    _ ≡ ((P.inv2w : Int) * 2 ^ P.width) % P.M [ZMOD P.M] := (emod_modEq _ _).symm
    _ = 1 := hcast

/-- A batch preserves the invariant. The two congruences are pushed through the batch's matrix
and then rescaled by `inv2w`; `Divstep.run_two_pow_mul_f` is what makes the rescaling land back
on the new `f`. -/
theorem step_good (P : Params) (hP : P.WF) (x : Int) (s : RState) (h : Good P x s) :
    Good P x (s.step P) := by
  set p := run P.width s.toDState with hp
  have hfodd : s.toDState.f % 2 = 1 := h.odd
  have hcop : Int.gcd s.toDState.f s.toDState.g = 1 := h.cop
  have hfe : 2 ^ P.width * p.1.f = p.2.u * s.f + p.2.v * s.g :=
    run_two_pow_mul_f P.width s.toDState hfodd
  have hge : 2 ^ P.width * p.1.g = p.2.q * s.f + p.2.r * s.g :=
    run_two_pow_mul_g P.width s.toDState hfodd
  have hinv := two_pow_mul_inv2w P hP
  -- One rescaling argument, instantiated at both the `d` row and the `e` row.
  have row : ∀ (cu cv fnew : Int), 2 ^ P.width * fnew = cu * s.f + cv * s.g →
      x * ((cu * s.d + cv * s.e) * (P.inv2w : Int) % P.M) ≡ (P.seed : Int) * fnew [ZMOD P.M] := by
    intro cu cv fnew hnew
    have step1 : x * ((cu * s.d + cv * s.e) * (P.inv2w : Int) % P.M)
        ≡ x * ((cu * s.d + cv * s.e) * (P.inv2w : Int)) [ZMOD P.M] :=
      Int.ModEq.mul_left _ (emod_modEq _ _)
    have step2 : x * ((cu * s.d + cv * s.e) * (P.inv2w : Int))
        ≡ ((P.seed : Int) * (2 ^ P.width * fnew)) * (P.inv2w : Int) [ZMOD P.M] := by
      have hd : cu * (x * s.d) ≡ cu * ((P.seed : Int) * s.f) [ZMOD P.M] :=
        Int.ModEq.mul_left _ h.dInv
      have he : cv * (x * s.e) ≡ cv * ((P.seed : Int) * s.g) [ZMOD P.M] :=
        Int.ModEq.mul_left _ h.eInv
      have hsum : cu * (x * s.d) + cv * (x * s.e)
          ≡ cu * ((P.seed : Int) * s.f) + cv * ((P.seed : Int) * s.g) [ZMOD P.M] := hd.add he
      have hl : x * ((cu * s.d + cv * s.e) * (P.inv2w : Int))
          = (cu * (x * s.d) + cv * (x * s.e)) * (P.inv2w : Int) := by ring
      have hr : cu * ((P.seed : Int) * s.f) + cv * ((P.seed : Int) * s.g)
          = (P.seed : Int) * (cu * s.f + cv * s.g) := by ring
      rw [hl, hnew, ← hr]
      exact hsum.mul_right _
    have step3 : ((P.seed : Int) * (2 ^ P.width * fnew)) * (P.inv2w : Int)
        ≡ (P.seed : Int) * fnew * 1 [ZMOD P.M] := by
      have : ((P.seed : Int) * (2 ^ P.width * fnew)) * (P.inv2w : Int)
          = ((P.seed : Int) * fnew) * (2 ^ P.width * (P.inv2w : Int)) := by ring
      rw [this]
      exact Int.ModEq.mul_left _ hinv
    calc x * ((cu * s.d + cv * s.e) * (P.inv2w : Int) % P.M)
        ≡ x * ((cu * s.d + cv * s.e) * (P.inv2w : Int)) [ZMOD P.M] := step1
      _ ≡ ((P.seed : Int) * (2 ^ P.width * fnew)) * (P.inv2w : Int) [ZMOD P.M] := step2
      _ ≡ (P.seed : Int) * fnew * 1 [ZMOD P.M] := step3
      _ = (P.seed : Int) * fnew := by ring
  exact
    { odd := run_emod_two_f P.width s.toDState hfodd
      cop := run_gcd_eq_one P.width s.toDState hfodd hcop
      dInv := row p.2.u p.2.v p.1.f hfe
      eInv := row p.2.q p.2.r p.1.g hge }

/-! ## Correctness of the driver -/

/-- **Partial correctness of the loop.** Whatever the loop returns is a canonical residue whose
product with `x` is the seed, modulo `m`. -/
theorem loop_spec (P : Params) (hP : P.WF) (x : Int) :
    ∀ (n : Nat) (s : RState) (y : Int) (k : Nat), Good P x s → loop P n s = some (y, k) →
      0 ≤ y ∧ y < P.M ∧ x * y ≡ (P.seed : Int) [ZMOD P.M] := by
  have hMpos : (0 : Int) < P.M := by
    have := hP.two_lt
    simp only [Params.M]
    omega
  intro n
  induction n with
  | zero => intro s y k _ h; simp [loop] at h
  | succ n ih =>
    intro s y k hgood heq
    have hgood' : Good P x (s.step P) := step_good P hP x s hgood
    by_cases hz : (s.step P).g = 0
    · -- Terminal batch: `f` is `±1`, so the sign-corrected `d` is the answer.
      have hy : y = if (s.step P).f < 0 then (-(s.step P).d) % P.M else (s.step P).d % P.M := by
        have := heq
        simp only [loop, hz, if_pos] at this
        exact (congrArg Prod.fst (Option.some.inj this)).symm
      have hpm : (s.step P).f = 1 ∨ (s.step P).f = -1 := by
        have hrun : (run P.width s.toDState).1.g = 0 := hz
        have := run_eq_one_or_neg_one P.width s.toDState hgood.odd hgood.cop hrun
        simpa [RState.step] using this
      refine ⟨?_, ?_, ?_⟩
      · rw [hy]; split <;> exact Int.emod_nonneg _ (ne_of_gt hMpos)
      · rw [hy]; split <;> exact Int.emod_lt_of_pos _ hMpos
      · rcases hpm with h1 | h1
        · have : y = (s.step P).d % P.M := by rw [hy, if_neg (by omega)]
          rw [this]
          calc x * ((s.step P).d % P.M)
              ≡ x * (s.step P).d [ZMOD P.M] := Int.ModEq.mul_left _ (emod_modEq _ _)
            _ ≡ (P.seed : Int) * (s.step P).f [ZMOD P.M] := hgood'.dInv
            _ = (P.seed : Int) := by rw [h1]; ring
        · have : y = (-(s.step P).d) % P.M := by rw [hy, if_pos (by omega)]
          rw [this]
          calc x * ((-(s.step P).d) % P.M)
              ≡ x * (-(s.step P).d) [ZMOD P.M] := Int.ModEq.mul_left _ (emod_modEq _ _)
            _ = -(x * (s.step P).d) := by ring
            _ ≡ -((P.seed : Int) * (s.step P).f) [ZMOD P.M] := hgood'.dInv.neg
            _ = (P.seed : Int) := by rw [h1]; ring
    · have hmap : (loop P n (s.step P)).map (fun z => (z.1, z.2 + 1)) = some (y, k) := by
        simpa [loop, hz] using heq
      cases hL : loop P n (s.step P) with
      | none => rw [hL] at hmap; simp at hmap
      | some z =>
        rw [hL] at hmap
        simp only [Option.map_some] at hmap
        have hz1 : z.1 = y := congrArg Prod.fst (Option.some.inj hmap)
        exact ih (s.step P) z.1 z.2 hgood' (by rw [hL]) |>.imp (fun h => hz1 ▸ h)
          (fun h => ⟨hz1 ▸ h.1, hz1 ▸ h.2⟩)

/-- **Correctness of divstep modular inversion.** For a nonzero `x` below a modulus coprime to
it, any answer the driver produces is the canonical residue `y ∈ [0, m)` with
`x * y ≡ seed (mod m)`.

With `seed = 1` this is the modular inverse; with `seed = R ^ 2 mod m` and `x` a Montgomery
representative `aR`, it is the Montgomery representative `a⁻¹R` of the inverse, which is what
the Pasta port computes, with no Montgomery reduction anywhere.

This is the form that also reports the batch count; `invert_spec` drops it. -/
theorem invertCounted_spec (P : Params) (hP : P.WF) (batches x : Nat) (y : Int) (k : Nat)
    (hcop : Nat.gcd x P.m = 1) (h : invertCounted P batches x = some (y, k)) :
    0 ≤ y ∧ y < P.M ∧ (x : Int) * y ≡ (P.seed : Int) [ZMOD P.M] := by
  rw [invertCounted] at h
  split at h
  · exact absurd h (by simp)
  · refine loop_spec P hP (x : Int) batches _ y k ?_ h
    refine { odd := ?_, cop := ?_, dInv := ?_, eInv := ?_ }
    · have h2 : ((P.m % 2 : Nat) : Int) = 1 := by exact_mod_cast hP.odd
      push_cast at h2
      simpa using h2
    · simpa [Int.gcd, Nat.gcd_comm] using hcop
    · have hz : ((P.seed : Int) * (P.m : Int)) % P.M = 0 := by
        simp [Params.M, Int.mul_emod_left]
      simp [Int.ModEq, hz]
    · simp [Int.ModEq, mul_comm]

/-- **Correctness of divstep modular inversion**, in the form that drops the batch count.
This generality is what the port's `r2_seeding_equivalence` test asserts empirically.
Rust: <https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1741-L1760> -/
theorem invert_spec (P : Params) (hP : P.WF) (batches x : Nat) (y : Int)
    (hcop : Nat.gcd x P.m = 1) (h : invert P batches x = some y) :
    0 ≤ y ∧ y < P.M ∧ (x : Int) * y ≡ (P.seed : Int) [ZMOD P.M] := by
  rw [invert, Option.map_eq_some_iff] at h
  obtain ⟨z, hz, rfl⟩ := h
  exact invertCounted_spec P hP batches x z.1 z.2 hcop hz

end CompElliptic.Fields.SafeGCD
