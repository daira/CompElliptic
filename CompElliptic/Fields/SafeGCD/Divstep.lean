/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Danny Willems
-/
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

/-!
# Bernstein-Yang divsteps over `ℤ`

The mathematical core of *safegcd*: the divstep recurrence of Bernstein and Yang,
["Fast constant-time gcd computation and modular inversion"](https://eprint.iacr.org/2019/266),
in the `eta` form used by libsecp256k1's `modinv64`.

A divstep acts on a state `(eta, f, g)` with `f` odd. Written as a matrix it is

```text
  ⌈f'⌉   1 ⌈u  v⌉ ⌈f⌉
  ⌊g'⌋ = ─ ⌊q  r⌋ ⌊g⌋
         2
```

for one of three integer matrices of determinant `2`, selected by the parity of `g` and the sign
of `eta`. Composing `n` of them gives a single `Trans` of determinant `2 ^ n` that turns `n`
halvings into one exact division by `2 ^ n`, which is what makes a *batched* implementation
possible: read the branch decisions off the bottom limbs of `f` and `g`, accumulate the matrix,
then apply it once at full width.

This module proves the properties such an implementation rests on, for the naive step-at-a-time
recurrence:

* `run_det`: the accumulated determinant is exactly `2 ^ n`;
* `run_two_pow_mul_f` / `run_two_pow_mul_g`: the division by `2 ^ n` is exact, so no information
  is lost;
* `run_emod_two_f`: `f` stays odd, the standing precondition of the recurrence;
* `run_inv_f` / `run_inv_g`: the *adjugate* recovers the original pair from the final one, since
  the determinant is a unit after dividing through by `2 ^ n`. Consequently
  `run_eq_one_or_neg_one`: once `g` reaches `0` and the inputs are coprime, the terminal `f` is
  `±1`, because it divides both inputs.

That last consequence is the usual "`gcd` is invariant along a divstep run", obtained here
without an invariance induction: invertibility of the transition over `ℤ` gives it directly.

`CompElliptic.Fields.SafeGCD.Reference` turns these into the correctness of modular inversion.

## Implementation notes

Oddness of `f` is carried as `f % 2 = 1` rather than as `Odd f`, so that `omega` (which knows
`Int.emod` and `Int.ediv` by numerals) discharges the parity and exact-division side conditions
of all three branches directly.

## Provenance

Ported from `src/fields/modinv62.rs` of
[zcash/pasta_curves#119](https://github.com/zcash/pasta_curves/pull/119), pinned at commit
`9299dfbb19978428ba24229bc13dff25a424dc46` (branch `modinv62`). Every `Rust:` link on a
declaration below points into that commit, so the line numbers stay valid even after the branch
moves; to review against the tip of the branch instead, open the pull request and diff.

The recurrence here is the one the port's batching kernel compresses; the kernel itself is
`divsteps_62_var`:
<https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L270-L391>

The module header stating the scaled invariants the driver maintains is:
<https://github.com/zcash/pasta_curves/blob/9299dfbb1997/src/fields/modinv62.rs#L1-L48>

## References

* Daniel J. Bernstein, Bo-Yin Yang, *Fast constant-time gcd computation and modular inversion*,
  IACR TCHES 2019(3). <https://eprint.iacr.org/2019/266>
* libsecp256k1, `src/modinv64_impl.h` and `doc/safegcd_implementation.md`.
  <https://github.com/bitcoin-core/secp256k1>
-/

namespace CompElliptic.Fields.SafeGCD

/-- A 2×2 integer matrix, the transition of a run of divsteps: it is applied to the column
`(f, g)` and the result divided by the corresponding power of two. -/
structure Trans where
  /-- Top-left entry: the coefficient of `f` in the new `f`. -/
  u : Int
  /-- Top-right entry: the coefficient of `g` in the new `f`. -/
  v : Int
  /-- Bottom-left entry: the coefficient of `f` in the new `g`. -/
  q : Int
  /-- Bottom-right entry: the coefficient of `g` in the new `g`. -/
  r : Int
deriving DecidableEq, Repr, Inhabited

namespace Trans

/-- The identity transition: the transition of zero divsteps. -/
def id : Trans := ⟨1, 0, 0, 1⟩

/-- The determinant `u * r - v * q`. Every divstep matrix has determinant `2`, so a run of `n`
divsteps has determinant `2 ^ n`. -/
def det (t : Trans) : Int := t.u * t.r - t.v * t.q

/-- Matrix product: `a.comp b` applies `b` first, then `a`. -/
def comp (a b : Trans) : Trans :=
  ⟨a.u * b.u + a.v * b.q, a.u * b.v + a.v * b.r,
   a.q * b.u + a.r * b.q, a.q * b.v + a.r * b.r⟩

@[simp] theorem det_id : Trans.id.det = 1 := by simp [det, Trans.id]

/-- Determinants are multiplicative, so a composed run's determinant is the product of the
determinants of its steps. -/
theorem det_comp (a b : Trans) : (a.comp b).det = a.det * b.det := by
  simp only [det, comp]; ring

end Trans

/-- The state of the divstep recurrence. -/
structure DState where
  /-- The Bernstein-Yang `eta` (the negation of their `delta`), driving the branch choice. -/
  eta : Int
  /-- The first element of the pair, maintained odd. -/
  f : Int
  /-- The second element of the pair, driven to zero. -/
  g : Int
deriving DecidableEq, Repr, Inhabited

/-- The transition matrix of a single divstep, determined by `eta` and the parity of `g`:

* `g` even: `(f, g) ↦ (f, g / 2)`;
* `g` odd and `eta < 0`: `(f, g) ↦ (g, (g - f) / 2)`, the swapping branch;
* `g` odd and `eta ≥ 0`: `(f, g) ↦ (f, (g + f) / 2)`.

Each matrix has determinant `2`, and each division is exact whenever `f` is odd. -/
def stepTrans (eta g : Int) : Trans :=
  if g % 2 = 0 then ⟨2, 0, 0, 1⟩
  else if eta < 0 then ⟨0, 2, -1, 1⟩
  else ⟨2, 0, 1, 1⟩

/-- The `eta` after a single divstep: it decreases by one, except on the swapping branch, where
it is reflected to `-eta - 1`. -/
def stepEta (eta g : Int) : Int :=
  if g % 2 = 0 then eta - 1
  else if eta < 0 then -eta - 1
  else eta - 1

/-- The `f` after a single divstep. -/
def stepF (eta f g : Int) : Int := ((stepTrans eta g).u * f + (stepTrans eta g).v * g) / 2

/-- The `g` after a single divstep. -/
def stepG (eta f g : Int) : Int := ((stepTrans eta g).q * f + (stepTrans eta g).r * g) / 2

/-- One divstep on a whole state. -/
def step (s : DState) : DState :=
  ⟨stepEta s.eta s.g, stepF s.eta s.f s.g, stepG s.eta s.f s.g⟩

/-- `n` divsteps from `s`, returning the final state together with the accumulated transition
`t`, which satisfies `2 ^ n * f' = t.u * f + t.v * g` and likewise for `g` (`run_two_pow_mul_f`,
`run_two_pow_mul_g`). -/
def run : Nat → DState → DState × Trans
  | 0, s => (s, Trans.id)
  | n + 1, s =>
      let p := run n (step s)
      (p.1, p.2.comp (stepTrans s.eta s.g))

@[simp] theorem run_zero (s : DState) : run 0 s = (s, Trans.id) := rfl

theorem run_succ (n : Nat) (s : DState) :
    run (n + 1) s = ((run n (step s)).1, (run n (step s)).2.comp (stepTrans s.eta s.g)) := rfl

/-! ## Single-step lemmas

Each is proved by splitting into the three branches of `stepTrans` and handing the resulting
concrete linear-arithmetic goal to `omega`, which knows `Int.ediv` and `Int.emod` by numerals.
-/

/-- Every divstep matrix has determinant `2`. -/
theorem det_stepTrans (eta g : Int) : (stepTrans eta g).det = 2 := by
  unfold stepTrans Trans.det
  split_ifs <;> norm_num

/-- The division defining the new `f` is exact. -/
theorem two_mul_stepF (eta f g : Int) (hf : f % 2 = 1) :
    2 * stepF eta f g = (stepTrans eta g).u * f + (stepTrans eta g).v * g := by
  unfold stepF stepTrans
  split_ifs <;> dsimp only <;> omega

/-- The division defining the new `g` is exact. -/
theorem two_mul_stepG (eta f g : Int) (hf : f % 2 = 1) :
    2 * stepG eta f g = (stepTrans eta g).q * f + (stepTrans eta g).r * g := by
  unfold stepG stepTrans
  split_ifs <;> dsimp only <;> omega

/-- A divstep preserves oddness of `f`: on the swapping branch the new `f` is the old `g`, which
that branch requires to be odd; otherwise `f` is unchanged. -/
theorem stepF_emod_two (eta f g : Int) (hf : f % 2 = 1) : stepF eta f g % 2 = 1 := by
  unfold stepF stepTrans
  split_ifs <;> dsimp only <;> omega

/-! ## The `n`-step specification -/

/-- The contract of a run of `n` divsteps, proved by induction on `n`: the accumulated
determinant is `2 ^ n`, both divisions by `2 ^ n` are exact, and `f` stays odd. -/
theorem run_spec (n : Nat) (s : DState) (hf : s.f % 2 = 1) :
    (run n s).2.det = 2 ^ n ∧
      2 ^ n * (run n s).1.f = (run n s).2.u * s.f + (run n s).2.v * s.g ∧
      2 ^ n * (run n s).1.g = (run n s).2.q * s.f + (run n s).2.r * s.g ∧
      (run n s).1.f % 2 = 1 := by
  induction n generalizing s with
  | zero => refine ⟨by simp, by simp [Trans.id], by simp [Trans.id], hf⟩
  | succ n ih =>
    have hstep : (step s).f % 2 = 1 := stepF_emod_two s.eta s.f s.g hf
    obtain ⟨hdet, hfeq, hgeq, hodd⟩ := ih (step s) hstep
    have hFf : 2 * (step s).f = (stepTrans s.eta s.g).u * s.f + (stepTrans s.eta s.g).v * s.g :=
      two_mul_stepF s.eta s.f s.g hf
    have hFg : 2 * (step s).g = (stepTrans s.eta s.g).q * s.f + (stepTrans s.eta s.g).r * s.g :=
      two_mul_stepG s.eta s.f s.g hf
    rw [run_succ]
    refine ⟨?_, ?_, ?_, hodd⟩
    · simp only [Trans.det_comp, hdet, det_stepTrans]; ring
    · simp only [Trans.comp]
      calc (2 : Int) ^ (n + 1) * (run n (step s)).1.f
          = 2 * (2 ^ n * (run n (step s)).1.f) := by ring
        _ = 2 * ((run n (step s)).2.u * (step s).f + (run n (step s)).2.v * (step s).g) := by
              rw [hfeq]
        _ = (run n (step s)).2.u * (2 * (step s).f)
              + (run n (step s)).2.v * (2 * (step s).g) := by ring
        _ = _ := by rw [hFf, hFg]; ring
    · simp only [Trans.comp]
      calc (2 : Int) ^ (n + 1) * (run n (step s)).1.g
          = 2 * (2 ^ n * (run n (step s)).1.g) := by ring
        _ = 2 * ((run n (step s)).2.q * (step s).f + (run n (step s)).2.r * (step s).g) := by
              rw [hgeq]
        _ = (run n (step s)).2.q * (2 * (step s).f)
              + (run n (step s)).2.r * (2 * (step s).g) := by ring
        _ = _ := by rw [hFf, hFg]; ring

/-- The accumulated determinant of `n` divsteps is `2 ^ n`. -/
theorem run_det (n : Nat) (s : DState) (hf : s.f % 2 = 1) : (run n s).2.det = 2 ^ n :=
  (run_spec n s hf).1

/-- The division by `2 ^ n` producing the new `f` is exact. -/
theorem run_two_pow_mul_f (n : Nat) (s : DState) (hf : s.f % 2 = 1) :
    2 ^ n * (run n s).1.f = (run n s).2.u * s.f + (run n s).2.v * s.g :=
  (run_spec n s hf).2.1

/-- The division by `2 ^ n` producing the new `g` is exact. -/
theorem run_two_pow_mul_g (n : Nat) (s : DState) (hf : s.f % 2 = 1) :
    2 ^ n * (run n s).1.g = (run n s).2.q * s.f + (run n s).2.r * s.g :=
  (run_spec n s hf).2.2.1

/-- `f` stays odd across a run of divsteps. -/
theorem run_emod_two_f (n : Nat) (s : DState) (hf : s.f % 2 = 1) : (run n s).1.f % 2 = 1 :=
  (run_spec n s hf).2.2.2

/-! ## Invertibility, and the terminal `f`

The transition has determinant `2 ^ n` and scales the pair by `1 / 2 ^ n`, so the composite map
`(f, g) ↦ (f', g')` is an *integral* automorphism: its inverse is the adjugate, with the `2 ^ n`
cancelling. The original pair is therefore an integer combination of the final one, which is
what pins the terminal `f` to `± gcd (f, g)`.
-/

/-- The original `f` is recovered from the final pair by the adjugate row `(r, -v)`. -/
theorem run_inv_f (n : Nat) (s : DState) (hf : s.f % 2 = 1) :
    s.f = (run n s).2.r * (run n s).1.f - (run n s).2.v * (run n s).1.g := by
  have hpow : (2 : Int) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  refine mul_left_cancel₀ hpow ?_
  have hdet := run_det n s hf
  have hfe := run_two_pow_mul_f n s hf
  have hge := run_two_pow_mul_g n s hf
  have expand :
      (2 : Int) ^ n * ((run n s).2.r * (run n s).1.f - (run n s).2.v * (run n s).1.g)
        = (run n s).2.r * (2 ^ n * (run n s).1.f) - (run n s).2.v * (2 ^ n * (run n s).1.g) := by
    ring
  rw [expand, hfe, hge]
  have : (run n s).2.r * ((run n s).2.u * s.f + (run n s).2.v * s.g)
      - (run n s).2.v * ((run n s).2.q * s.f + (run n s).2.r * s.g)
      = (run n s).2.det * s.f := by simp only [Trans.det]; ring
  rw [this, hdet]

/-- The original `g` is recovered from the final pair by the adjugate row `(-q, u)`. -/
theorem run_inv_g (n : Nat) (s : DState) (hf : s.f % 2 = 1) :
    s.g = (run n s).2.u * (run n s).1.g - (run n s).2.q * (run n s).1.f := by
  have hpow : (2 : Int) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  refine mul_left_cancel₀ hpow ?_
  have hdet := run_det n s hf
  have hfe := run_two_pow_mul_f n s hf
  have hge := run_two_pow_mul_g n s hf
  have expand :
      (2 : Int) ^ n * ((run n s).2.u * (run n s).1.g - (run n s).2.q * (run n s).1.f)
        = (run n s).2.u * (2 ^ n * (run n s).1.g) - (run n s).2.q * (2 ^ n * (run n s).1.f) := by
    ring
  rw [expand, hfe, hge]
  have : (run n s).2.u * ((run n s).2.q * s.f + (run n s).2.r * s.g)
      - (run n s).2.q * ((run n s).2.u * s.f + (run n s).2.v * s.g)
      = (run n s).2.det * s.g := by simp only [Trans.det]; ring
  rw [this, hdet]

/-- **Invertibility.** Any common divisor of the final pair divides the original pair: the
adjugate rows express `f` and `g` as integer combinations of `f'` and `g'`. -/
theorem run_dvd_of_dvd (n : Nat) (s : DState) (hf : s.f % 2 = 1) {k : Int}
    (hkf : k ∣ (run n s).1.f) (hkg : k ∣ (run n s).1.g) : k ∣ s.f ∧ k ∣ s.g := by
  obtain ⟨a, ha⟩ := hkf
  obtain ⟨b, hb⟩ := hkg
  refine ⟨⟨(run n s).2.r * a - (run n s).2.v * b, ?_⟩,
    ⟨(run n s).2.u * b - (run n s).2.q * a, ?_⟩⟩
  · rw [run_inv_f n s hf, ha, hb]; ring
  · rw [run_inv_g n s hf, ha, hb]; ring

/-- Once `g` has reached `0`, the terminal `f` divides both original entries. -/
theorem run_dvd_of_g_eq_zero (n : Nat) (s : DState) (hf : s.f % 2 = 1)
    (hg : (run n s).1.g = 0) :
    (run n s).1.f ∣ s.f ∧ (run n s).1.f ∣ s.g :=
  run_dvd_of_dvd n s hf dvd_rfl (hg ▸ dvd_zero _)

/-- The gcd of the pair cannot grow along a run, and by invertibility it cannot shrink either. -/
theorem run_gcd_dvd (n : Nat) (s : DState) (hf : s.f % 2 = 1) :
    Int.gcd (run n s).1.f (run n s).1.g ∣ Int.gcd s.f s.g := by
  obtain ⟨h1, h2⟩ :=
    run_dvd_of_dvd n s hf (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  exact_mod_cast Int.dvd_coe_gcd h1 h2

/-- Coprimality of the pair is preserved along a run: this is what lets the inversion driver
carry the hypothesis of `run_eq_one_or_neg_one` from one batch to the next. -/
theorem run_gcd_eq_one (n : Nat) (s : DState) (hf : s.f % 2 = 1) (hcop : Int.gcd s.f s.g = 1) :
    Int.gcd (run n s).1.f (run n s).1.g = 1 :=
  Nat.dvd_one.mp (hcop ▸ run_gcd_dvd n s hf)

/-- **Termination value.** If the inputs are coprime and the run drives `g` to `0`, the terminal
`f` is a unit, that is `1` or `-1`. This is the fact the inversion driver reads the sign of `f`
for. -/
theorem run_eq_one_or_neg_one (n : Nat) (s : DState) (hf : s.f % 2 = 1)
    (hcop : Int.gcd s.f s.g = 1) (hg : (run n s).1.g = 0) :
    (run n s).1.f = 1 ∨ (run n s).1.f = -1 := by
  obtain ⟨hdf, hdg⟩ := run_dvd_of_g_eq_zero n s hf hg
  have hdvd : (run n s).1.f ∣ ((Int.gcd s.f s.g : Nat) : Int) := Int.dvd_coe_gcd hdf hdg
  rw [hcop] at hdvd
  have habs : (run n s).1.f.natAbs ∣ 1 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have := Nat.dvd_one.mp habs
  omega

end CompElliptic.Fields.SafeGCD
