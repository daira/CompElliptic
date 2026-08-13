/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# Computable square roots in prime fields (Tonelli–Shanks)

A *computable* square root for any odd-characteristic prime field, via the **general** Tonelli–Shanks
algorithm, parameterized by the 2-adic factorization `card-1 = 2^twoAdicity * oddPart` (`oddPart`
odd). This is the fully general case — `twoAdicity = 1` (i.e. `p ≡ 3 mod 4`) degenerates to the
closed form `a^((p+1)/4)` with no loop iterations — not a variant specialized to `p ≡ 1 mod 16`. We
are not optimizing for speed or brevity, only for correctness and computability. It is a field-level
primitive (it knows nothing about curves) and a candidate for upstreaming to CompPoly; it lives here
for now so the Pasta point decoder (`abst`) can use it.

`TonelliShanks.sqrt?` is **self-validating**: it returns `some r` only after checking `r*r = a`,
so an incorrect `TonelliShanks` instance (wrong `rootOfUnity` / `oddPart`) yields `none`, never a
wrong root. *Soundness* (`sqrt?_mul_self`: anything it returns squares to `a`) follows unconditionally
from this. *Completeness* (`sqrt?_isSome_of_isSquare`: a genuine square yields `some`) holds for a
valid instance, via Euler's criterion for the residue test and the loop invariant `loop_sound`.

The default `Monoid.npow` (`a^n`) is linear in `n`, so it cannot evaluate the `≈ 2^253`-sized
exponents here. `fpow` is square-and-multiply (logarithmic), fast enough to `#eval`.

## References

The classical algorithm:

- A. Tonelli, "Bemerkung über die Auflösung quadratischer Congruenzen", Nachrichten von der Königl.
  Gesellschaft der Wissenschaften und der Georg-Augusts-Universität zu Göttingen, 1891, pp. 344–346.
  <https://eudml.org/doc/180329>
- D. Shanks, "Five number-theoretic algorithms", Proceedings of the Second Manitoba Conference on
  Numerical Mathematics, 1973, pp. 51–70. (The original is not available online; see Shanks' later
  notes at <https://homes.cerias.purdue.edu/~ssw/shanks.pdf>.)

The specific formulation implemented here is Algorithm 5 (the prime-field Tonelli–Shanks square
root, with the quadratic-residue test folded in) of — and is the algorithm `pallas.py` in
`zcash-test-vectors` cites:

- G. Adj and F. Rodríguez-Henríquez, "Square root computation over even extension fields", IACR
  Cryptology ePrint Archive, Report 2012/685, <https://eprint.iacr.org/2012/685> (later published
  in IEEE Transactions on Computers, 2014).

(Despite the title, this paper covers more cases than even extension fields.)
-/

namespace CompElliptic.Fields

/-- Square-and-multiply exponentiation: `fpow a n = a^n`, but logarithmic in `n` so it is
feasible to evaluate for large exponents (unlike `Monoid.npow`). -/
def fpow {F : Type*} [Monoid F] (a : F) : ℕ → F
  | 0 => 1
  | n + 1 => (if (n+1) % 2 = 1 then a else 1) * fpow (a*a) ((n+1) / 2)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) one_lt_two

theorem fpow_spec {F : Type*} [Monoid F] (a : F) (n : ℕ) : fpow a n = a^n := by
  induction a, n using fpow.induct with
  | case1 a => simp [fpow]
  | case2 a n ih =>
    rw [fpow, ih, ← pow_two, ← pow_mul]
    rcases Nat.mod_two_eq_zero_or_one (n+1) with h | h
    · rw [if_neg (by omega), one_mul]; congr 1; omega
    · rw [if_pos h, ← pow_succ']; congr 1; omega

/-- `iterSq c k = c^(2^k)`, by squaring `k` times. -/
def iterSq {F : Type*} [Monoid F] (c : F) : ℕ → F
  | 0 => c
  | k + 1 => iterSq (c*c) k

theorem iterSq_spec {F : Type*} [Monoid F] (c : F) (k : ℕ) : iterSq c k = c^(2^k) := by
  induction k generalizing c with
  | zero => simp [iterSq]
  | succ k ih => rw [iterSq, ih, ← pow_two, ← pow_mul, ← pow_succ']

/-- The least `k ≥ 1` with `b^(2^k) = 1`, searched up to `fuel` steps (returning the current
`k` if the fuel runs out). Used on `b` known to lie in the 2-power-torsion subgroup. -/
def leastPow2Order {F : Type*} [Monoid F] [DecidableEq F] (b : F) (fuel : ℕ) : ℕ :=
  go 1 (b*b) fuel
where
  go (k : ℕ) (b2k : F) : ℕ → ℕ
    | 0 => k
    | fuel + 1 => if b2k = 1 then k else go (k+1) (b2k*b2k) fuel

/-- Spec of the `go` accumulator: when some `2^j`-th power of `b2k` (with `j ≤ fuel`) is `1`,
`go k b2k fuel = k + j₀` where `j₀` is the *least* such exponent. -/
theorem leastPow2Order.go_spec {F : Type*} [Monoid F] [DecidableEq F] :
    ∀ (fuel k : ℕ) (b2k : F), (∃ j ≤ fuel, b2k^(2^j) = 1) →
      ∃ j ≤ fuel, leastPow2Order.go k b2k fuel = k + j ∧ b2k^(2^j) = 1 ∧
        ∀ i < j, b2k^(2^i) ≠ 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro k b2k hex
    obtain ⟨j, hj, hbj⟩ := hex
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    exact ⟨0, le_refl 0, rfl, hbj, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ fuel ih =>
    intro k b2k hex
    obtain ⟨j, hj, hbj⟩ := hex
    have hconv : ∀ m : ℕ, (b2k * b2k)^(2^m) = b2k^(2^(m+1)) := fun m => by
      rw [← pow_two, ← pow_mul, ← pow_succ']
    by_cases hb1 : b2k = 1
    · exact ⟨0, Nat.zero_le _, by simp [leastPow2Order.go, hb1], by simpa using hb1,
        fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · have hex' : ∃ j' ≤ fuel, (b2k * b2k)^(2^j') = 1 := by
        obtain _ | j := j
        · exact absurd (by simpa using hbj) hb1
        · exact ⟨j, by omega, by rw [hconv]; exact hbj⟩
      obtain ⟨j'', hj'', hgo, hbj'', hmin⟩ := ih (k+1) (b2k * b2k) hex'
      refine ⟨j'' + 1, by omega, ?_, ?_, ?_⟩
      · rw [leastPow2Order.go, if_neg hb1, hgo]; omega
      · rw [← hconv]; exact hbj''
      · intro i hi
        obtain _ | i := i
        · simpa using hb1
        · rw [← hconv]; exact hmin i (by omega)

/-- The exponent `leastPow2Order b y` is the *least* `k ≥ 1` with `b^(2^k) = 1`, given that `b ≠ 1`
and `b^(2^(y-1)) = 1` (so `b` lies in the 2-power torsion, forcing `y ≥ 2` and `k ≤ y-1`). -/
theorem leastPow2Order_spec {F : Type*} [Monoid F] [DecidableEq F] (b : F) (y : ℕ)
    (hb : b ≠ 1) (hy : b^(2^(y-1)) = 1) :
    1 ≤ leastPow2Order b y ∧ leastPow2Order b y ≤ y-1 ∧
      b^(2^(leastPow2Order b y)) = 1 ∧ b^(2^(leastPow2Order b y - 1)) ≠ 1 := by
  have hy2 : 2 ≤ y := by
    rcases Nat.lt_or_ge y 2 with h | h
    · interval_cases y <;> simp_all
    · exact h
  have hconv : ∀ m : ℕ, (b*b)^(2^m) = b^(2^(m+1)) := fun m => by
    rw [← pow_two, ← pow_mul, ← pow_succ']
  have hwit : (b*b)^(2^(y - 2)) = 1 := by rw [hconv, show y - 2 + 1 = y-1 from by omega]; exact hy
  obtain ⟨j, hj, hgo, hbj, hmin⟩ := leastPow2Order.go_spec y 1 (b*b) ⟨y - 2, by omega, hwit⟩
  have hk : leastPow2Order b y = 1 + j := hgo
  have hjle : j ≤ y - 2 := by
    by_contra h; exact hmin (y - 2) (Nat.lt_of_not_le h) hwit
  have hbk1 : b^(2^j) ≠ 1 := by
    obtain _ | j := j
    · simpa using hb
    · rw [← hconv]; exact hmin j (by omega)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hk, show (1:ℕ)+j = j+1 from by omega, ← hconv]; exact hbj
  · rw [hk, show 1 + j - 1 = j from by omega]; exact hbk1

/-- Validity of Tonelli–Shanks data for `F`, as a predicate on the *bare components* (mirroring
`IsCanonical` for encodings): the 2-adic factorization `card - 1 = 2^twoAdicity * oddPart` holds
with `oddPart` odd and `twoAdicity` positive, and `rootOfUnity` is a primitive `2^twoAdicity`-th
root of unity. -/
structure IsValidTonelliShanks {F : Type*} [Field F] [Fintype F]
    (twoAdicity oddPart : ℕ) (rootOfUnity : F) : Prop where
  /-- `card - 1 = 2^twoAdicity * oddPart`. The default discharges it for a `ZMod`-backed field with
  literal parameters; an exotic field can supply its own proof. -/
  card_eq : Fintype.card F = 2^twoAdicity * oddPart + 1 := by rw [ZMod.card]; decide
  /-- The odd part is odd. -/
  oddPart_odd : Odd oddPart := by decide
  /-- There is at least one factor of two (the field is not of characteristic 2). -/
  twoAdicity_pos : 0 < twoAdicity := by decide
  /-- `rootOfUnity` has multiplicative order exactly `2^twoAdicity`. The order is checked via a
  primitivity certificate (`rootOfUnity^(2^(S-1)) ≠ 1 = rootOfUnity^(2^S)`); the exponentiation has
  a field-sized base, so this leg uses `native_decide`. -/
  rootOfUnity_order : orderOf rootOfUnity = 2^twoAdicity := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_pow (p := 2) ?_ ?_ <;> native_decide

/-- The data Tonelli–Shanks needs for a field `F`: the 2-adic factorization
`card-1 = 2^twoAdicity * oddPart`, a primitive `2^twoAdicity`-th root of unity `rootOfUnity`
(equivalently `g^oddPart` for any quadratic non-residue `g`), bundled with a proof of their
validity (`IsValidTonelliShanks`). This ensures that a invalid instance cannot be constructed,
and completeness needs no separate hypothesis. -/
structure TonelliShanks (F : Type*) [Field F] [Fintype F] where
  /-- The 2-adic valuation `S` of `card-1`. -/
  twoAdicity : ℕ
  /-- The odd part `T` of `card-1 = 2^S * T`. -/
  oddPart : ℕ
  /-- A primitive `2^twoAdicity`-th root of unity (`g^oddPart` for a non-residue `g`). -/
  rootOfUnity : F
  /-- The data is valid for `F`. Defaults to the `IsValidTonelliShanks` field defaults, so an
  instance over a `ZMod`-backed field with literal parameters needs only the three data fields. -/
  valid : IsValidTonelliShanks twoAdicity oddPart rootOfUnity := by exact {}

namespace TonelliShanks

/-- The Tonelli–Shanks main loop (the `while` of Algorithm 5 in Adj–Rodríguez-Henríquez; see the
module references): maintains `x` (the running square-root candidate), `b` (driven to `1`), `c`
(the paper's root of unity `z`), and `y` (the paper's `v`, the current 2-power bound). `fuel` bounds
the iteration count (`y` strictly decreases, so `twoAdicity` steps suffice). -/
def loop {F : Type*} [Field F] [DecidableEq F] (x b c : F) (y : ℕ) : ℕ → F
  | 0 => x
  | fuel + 1 =>
    if b = 1 then x
    else
      let k := leastPow2Order b y
      let w := iterSq c (y - k - 1)
      loop (x*w) (b * (w*w)) (w*w) k fuel

/-- The Tonelli–Shanks loop invariant. If `x*x = a*b`, the residue `b` lies in the 2-power torsion
(`b^(2^(y-1)) = 1`), and `c` is a primitive `2^y`-th root of unity, then the loop drives `b` to `1`
and returns an actual square root of `a`. `fuel` need only bound `y`. The key field fact is that the
only element of multiplicative order two is `-1`, applied to both `b^(2^(k-1))` and `c^(2^(y-1))`. -/
theorem loop_sound {F : Type*} [Field F] [DecidableEq F] (a : F) :
    ∀ (fuel : ℕ) (x b c : F) (y : ℕ), y ≤ fuel →
      x*x = a*b → b^(2^(y-1)) = 1 → orderOf c = 2^y →
      loop x b c y fuel * loop x b c y fuel = a := by
  intro fuel
  induction fuel with
  | zero =>
    intro x b c y hyf hx hb _
    obtain rfl : y = 0 := Nat.le_zero.mp hyf
    have hb1 : b = 1 := by simpa using hb
    simp only [loop]
    rw [hx, hb1, mul_one]
  | succ fuel ih =>
    intro x b c y hyf hx hb hc
    by_cases hb1 : b = 1
    · simp only [loop, if_pos hb1]; rw [hx, hb1, mul_one]
    · obtain ⟨hk1, hky, hbk, hbk1⟩ := leastPow2Order_spec b y hb1 hb
      have hy2 : 2 ≤ y := by omega
      set k := leastPow2Order b y with hkdef
      set w := iterSq c (y - k - 1) with hwdef
      have hw2 : w*w = c^(2^(y - k)) := by
        rw [hwdef, iterSq_spec, ← pow_add, ← two_mul, ← pow_succ', show y - k - 1 + 1 = y - k from by omega]
      have hcm1 : c^(2^(y-1)) = -1 := by
        have hne : c^(2^(y-1)) ≠ 1 := by
          intro h
          have hdvd : orderOf c ∣ 2^(y-1) := orderOf_dvd_of_pow_eq_one h
          rw [hc] at hdvd
          have hle : (2:ℕ)^y ≤ 2^(y-1) := Nat.le_of_dvd (by positivity) hdvd
          have he : (2:ℕ)^y = 2 * 2^(y-1) := by rw [← pow_succ', show y-1+1 = y from by omega]
          have : 0 < (2:ℕ)^(y-1) := by positivity
          omega
        have hsq : c^(2^(y-1)) * c^(2^(y-1)) = 1 := by
          rw [← pow_add, ← two_mul, ← pow_succ', show y-1+1 = y from by omega, ← hc,
              pow_orderOf_eq_one]
        rcases mul_self_eq_one_iff.mp hsq with h | h
        · exact absurd h hne
        · exact h
      have hbm1 : b^(2^(k-1)) = -1 := by
        have hsq : b^(2^(k-1)) * b^(2^(k-1)) = 1 := by
          rw [← pow_add, ← two_mul, ← pow_succ', show k-1+1 = k from by omega]; exact hbk
        rcases mul_self_eq_one_iff.mp hsq with h | h
        · exact absurd h hbk1
        · exact h
      have hnewx : (x*w) * (x*w) = a * (b * (w*w)) := by
        rw [show (x*w) * (x*w) = (x*x) * (w*w) from by ring, hx]; ring
      have hnewb : (b * (w*w))^(2^(k-1)) = 1 := by
        rw [hw2, mul_pow, hbm1, ← pow_mul, ← pow_add, show (y - k) + (k-1) = y-1 from by omega, hcm1]
        ring
      have hnewc : orderOf (w*w) = 2^k := by
        rw [hw2, orderOf_pow' c (pow_ne_zero (y - k) (by norm_num)), hc,
            Nat.gcd_eq_right (pow_dvd_pow 2 (by omega : y - k ≤ y)),
            Nat.pow_div (by omega : y - k ≤ y) (by norm_num), show y - (y - k) = k from by omega]
      have hkf : k ≤ fuel := by omega
      simp only [loop, if_neg hb1]
      exact ih (x*w) (b * (w*w)) (w*w) k hkf hnewx hnewb hnewc

/-- Tonelli–Shanks square root. Returns `some r` with `r*r = a` when `a` is a square in `F`, and
`none` when it is not. Self-validating: the result is checked against `r*r = a` before being
returned. -/
def sqrt? {F : Type*} [Field F] [Fintype F] [DecidableEq F] (d : TonelliShanks F) (a : F) : Option F :=
  if a = 0 then some 0
  else
    -- Euler's criterion: `a` is a square iff `a^((card-1) / 2) = 1`, where `(card-1) / 2 = 2^(S-1) * T`.
    let pm1d2 := 2^(d.twoAdicity - 1) * d.oddPart
    if fpow a pm1d2 = 1 then
      let x := loop (fpow a ((d.oddPart + 1) / 2)) (fpow a d.oddPart) d.rootOfUnity d.twoAdicity
                    d.twoAdicity
      if x*x = a then some x else none
    else none

/-- **Soundness** of `sqrt?`: anything it returns squares to `a`. This holds for *any*
`TonelliShanks` data —even an invalid one— because `sqrt?` re-checks `r*r = a` before returning
`some r`. (Completeness —that a genuine square yields `some`— is `sqrt?_isSome_of_isSquare`.) -/
theorem sqrt?_mul_self {F : Type*} [Field F] [Fintype F] [DecidableEq F] (d : TonelliShanks F)
    {a r : F} (h : d.sqrt? a = some r) : r*r = a := by
  simp only [sqrt?] at h
  split_ifs at h with h0 h1 hx <;> simp_all
  subst h
  simp only [mul_zero]

/-- **Completeness** of `sqrt?`: for a valid instance, every square `a` yields `some r`. The
residue test passes by Euler's criterion, and the loop returns an actual root by `loop_sound`. -/
theorem sqrt?_isSome_of_isSquare {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : TonelliShanks F) {a : F} (ha : IsSquare a) :
    ∃ r, d.sqrt? a = some r := by
  -- The residue-test exponent `2^(S-1) * T` is `(card-1) / 2`, and the field has odd order.
  have hodd : Fintype.card F % 2 = 1 := by
    have h2 : 2 ∣ 2^d.twoAdicity * d.oddPart :=
      (dvd_pow_self 2 d.valid.twoAdicity_pos.ne').mul_right d.oddPart
    rw [d.valid.card_eq]; omega
  have hchar : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_of_char_two h; omega
  have hpow : 2^d.twoAdicity = 2 * 2^(d.twoAdicity - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel d.valid.twoAdicity_pos]
  have hexp : Fintype.card F / 2 = 2^(d.twoAdicity - 1) * d.oddPart := by
    rw [d.valid.card_eq, hpow, mul_assoc]; omega
  simp only [sqrt?]
  split_ifs with h0 h1 hx
  · exact ⟨0, rfl⟩
  · exact ⟨_, rfl⟩
  · -- a ≠ 0, residue test passed, but `x*x ≠ a`: contradicted by the loop invariant.
    refine absurd (loop_sound a d.twoAdicity _ _ _ d.twoAdicity (le_refl _) ?_ ?_
      d.valid.rootOfUnity_order) hx
    · -- initial `x*x = a*b`: `(a^((T+1)/2))² = a^(T+1) = a · a^T`, using `T` odd.
      rw [fpow_spec, fpow_spec, ← pow_add, ← two_mul,
          Nat.mul_div_cancel' (d.valid.oddPart_odd.add_one).two_dvd, pow_succ']
    · -- initial residue: `(a^T)^(2^(S-1)) = a^(2^(S-1)·T)`, which the residue test `h1` says is `1`.
      rw [fpow_spec, ← pow_mul, Nat.mul_comm d.oddPart, ← fpow_spec]; exact h1
  · -- a ≠ 0 and the residue test failed: contradicted by Euler's criterion for a square.
    exact absurd (by rw [fpow_spec, ← hexp]; exact (FiniteField.isSquare_iff hchar h0).mp ha) h1

/-- A valid `rootOfUnity` is a quadratic non-residue. It has full 2-power order, so its
Euler power `rootOfUnity^((card-1)/2) = (rootOfUnity^(2^(twoAdicity-1)))^oddPart`
evaluates to `(-1)^oddPart = -1`, whereas Euler's criterion gives `1` for a nonzero
square. This lets a deployment reuse `rootOfUnity` as an auxiliary nonsquare with no
per-field computation. -/
theorem rootOfUnity_not_isSquare {F : Type*} [Field F] [Fintype F]
    (d : TonelliShanks F) : ¬ IsSquare d.rootOfUnity := by
  intro hsq
  have hodd : Fintype.card F % 2 = 1 := by
    have h2 : 2 ∣ 2^d.twoAdicity * d.oddPart :=
      (dvd_pow_self 2 d.valid.twoAdicity_pos.ne').mul_right d.oddPart
    rw [d.valid.card_eq]; omega
  have hchar : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_of_char_two h; omega
  have hpow : 2^d.twoAdicity = 2 * 2^(d.twoAdicity - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel d.valid.twoAdicity_pos]
  have hexp : Fintype.card F / 2 = 2^(d.twoAdicity - 1) * d.oddPart := by
    rw [d.valid.card_eq, hpow, mul_assoc]; omega
  -- `rootOfUnity ≠ 0`, since it has a power equal to `1`.
  have hone : d.rootOfUnity^(2^d.twoAdicity) = 1 := by
    rw [← d.valid.rootOfUnity_order]; exact pow_orderOf_eq_one _
  have hne : d.rootOfUnity ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by positivity : (2:ℕ)^d.twoAdicity ≠ 0)] at hone
    exact zero_ne_one hone
  -- The half power squares to `1` but is not `1` (the order is too big), so it is `-1`.
  have hhalf : d.rootOfUnity^(2^(d.twoAdicity - 1)) = -1 := by
    have hsq1 : d.rootOfUnity^(2^(d.twoAdicity - 1))
        * d.rootOfUnity^(2^(d.twoAdicity - 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← hpow]; exact hone
    refine (mul_self_eq_one_iff.mp hsq1).resolve_left fun h1 => ?_
    have hdvd : orderOf d.rootOfUnity ∣ 2^(d.twoAdicity - 1) :=
      orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [d.valid.rootOfUnity_order] at hdvd
    have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : (1:ℕ) < 2)).mp hdvd
    have := d.valid.twoAdicity_pos
    omega
  -- Euler's power of the square is `1`, but it evaluates to `(-1)^oddPart = -1`.
  have heuler : d.rootOfUnity^(Fintype.card F / 2) = 1 :=
    (FiniteField.isSquare_iff hchar hne).mp hsq
  rw [hexp, pow_mul, hhalf, d.valid.oddPart_odd.neg_one_pow] at heuler
  exact Ring.neg_one_ne_one_of_char_ne_two hchar heuler

end TonelliShanks

end CompElliptic.Fields
