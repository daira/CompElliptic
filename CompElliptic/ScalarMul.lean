/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.Data.Nat.Init

/-!
# Scalar multiplication by binary double-and-add

`binNsmul add zero n x` computes `[n] x` (`n`-fold `add` from `zero`) by binary double-and-add:
`O(log n)` applications of `add`, via a single shared recursive call. It is stated over a *raw*
binary operation `add : M → M → M` and identity `zero : M` —not an `AddMonoid`— precisely so it
can supply the `nsmul` field *of* an `AddMonoid` / `AddCommGroup` instance (a field cannot refer to
the structure it is defining).

It is proven equal (`binNsmul_eq_linNsmul`) to the linear fold `linNsmul`, giving the `nsmul_zero` /
`nsmul_succ` obligations (`binNsmul_zero`, `binNsmul_succ`) any such instance needs. The only
algebraic facts required are associativity of `add` and right-identity of `zero`.
-/

namespace CompElliptic

variable {M : Type*}

/-- Linear scalar multiplication: the left fold `add (... add (add zero x) x ...) x` of `n` copies. -/
def linNsmul (add : M → M → M) (zero : M) : ℕ → M → M
  | 0, _ => zero
  | n + 1, x => add (linNsmul add zero n x) x

/-- Binary double-and-add scalar multiplication: `O(log n)` applications of `add` (the recursive
value is shared via `let`, so there is exactly one recursive call), hence evaluable by
`native_decide` for large `n`. Proven equal to `linNsmul` by `binNsmul_eq_linNsmul`. -/
def binNsmul (add : M → M → M) (zero : M) (n : ℕ) (x : M) : M :=
  if h : n = 0 then zero
  else
    let q := binNsmul add zero (n / 2) x
    let d := add q q
    if n % 2 = 1 then add d x else d
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

theorem binNsmul_zero (add : M → M → M) (zero : M) (x : M) : binNsmul add zero 0 x = zero := by
  rw [binNsmul]; rfl

variable {add : M → M → M} {zero : M}
  (hassoc : ∀ a b c : M, add (add a b) c = add a (add b c)) (hzero : ∀ a : M, add a zero = a)

include hassoc hzero

/-- Additivity of `linNsmul` in the scalar: `[m + n] x = [m] x + [n] x`. -/
theorem linNsmul_add (m n : ℕ) (x : M) :
    linNsmul add zero (m + n) x = add (linNsmul add zero m x) (linNsmul add zero n x) := by
  induction n with
  | zero =>
      show linNsmul add zero m x = add (linNsmul add zero m x) zero
      rw [hzero]
  | succ k ih =>
      show add (linNsmul add zero (m + k) x) x
          = add (linNsmul add zero m x) (add (linNsmul add zero k x) x)
      rw [ih, hassoc]

/-- The binary form computes the same value as the linear fold. -/
theorem binNsmul_eq_linNsmul (n : ℕ) (x : M) :
    binNsmul add zero n x = linNsmul add zero n x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [binNsmul]
    split
    · rename_i h; subst h; rfl
    · rename_i h
      have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      simp only [ih (n / 2) hlt]
      split
      · rename_i hodd
        rw [(linNsmul_add hassoc hzero (n / 2) (n / 2) x).symm]
        have hn : n / 2 + n / 2 + 1 = n := by omega
        have hstep : add (linNsmul add zero (n / 2 + n / 2) x) x
            = linNsmul add zero (n / 2 + n / 2 + 1) x := rfl
        rw [hstep, hn]
      · rename_i heven
        rw [(linNsmul_add hassoc hzero (n / 2) (n / 2) x).symm]
        have hn : n / 2 + n / 2 = n := by omega
        rw [hn]

/-- The double-and-add recurrence: `[n+1] x = [n] x + x`. Supplies the `nsmul_succ` instance field. -/
theorem binNsmul_succ (n : ℕ) (x : M) :
    binNsmul add zero (n + 1) x = add (binNsmul add zero n x) x := by
  rw [binNsmul_eq_linNsmul hassoc hzero (n + 1) x, binNsmul_eq_linNsmul hassoc hzero n x]
  rfl

end CompElliptic
