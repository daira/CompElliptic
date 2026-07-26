/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import Mathlib.Data.List.GetD
import CompElliptic.Fields.Pasta

/-!
# Windowed Pippenger multi-scalar multiplication, proven equal to the naive MSM

The naive MSM `(terms.map fun (n, x) => n • x).sum` is the mathematical core of a Pedersen-style
vector commitment, and with 255-bit scalars it dominates a verifying-key derivation.  This module
gives the windowed Pippenger accelerator `pippenger c terms` — per-window bucket sums, the
suffix-sum trick, a Horner pass across windows — and proves it equal to the naive MSM
(`pippenger_eq_msm`).  Measured at `n = 2048`: `242 s` naive against `22.5 s` at the optimal
window `c = 8` (`defaultWindow`); `pippengerFast` replaces the proof-layer per-bucket `filterMap`
by a single-pass `bucketScatter`.

Everything is generic over `[AddCommMonoid M]`: scalars are `ℕ`, so nothing below needs negation.

The equality goes through the base-`2 ^ c` digit decomposition `n • x = ∑ i, digit i n •
(base ^ i • x)` (`smul_eq_sum_digits`), an exchange of the sum over terms with the sum over
windows (`list_sum_finset_sum`), the identification of each window's contribution with its
weighted bucket sum (`naiveWindow_eq_buckets`, `foldr_accStep`), and `hornerList_eq`.
-/

namespace CompElliptic.Curves.Pasta.Fast.Msm

open scoped BigOperators

variable {M : Type*} [AddCommMonoid M]

/-! ## The naive MSM (the object we accelerate) -/

/-- The naive multi-scalar multiplication: `∑ (n, x), n • x`.  This is the shape the VK-commitment
`commitLagrangeWith` reduces to. -/
def naiveMsm (terms : List (ℕ × M)) : M :=
  (terms.map fun t => t.1 • t.2).sum

/-! ## Base-`2 ^ c` digit decomposition of a scalar -/

/-- The `i`-th base-`base` digit of `n`: `⌊n / base ^ i⌋ mod base`. -/
def digit (base i n : ℕ) : ℕ := n / base ^ i % base

/-- Reconstruct `n` from its first `W` base-`base` digits, provided `n < base ^ W`.  A bespoke
windowed decomposition (cleaner here than `Nat.digits`). -/
theorem sum_digit (base : ℕ) (hb : 0 < base) :
    ∀ W n, n < base ^ W → n = ∑ i ∈ Finset.range W, digit base i n * base ^ i := by
  intro W
  induction W with
  | zero => intro n hn; simpa using Nat.lt_one_iff.mp hn
  | succ W ih =>
    intro n hn
    rw [Finset.sum_range_succ']
    have hdiv : n / base < base ^ W := by
      rw [Nat.div_lt_iff_lt_mul hb, ← pow_succ]; exact hn
    have hstep : ∀ i ∈ Finset.range W,
        digit base (i + 1) n * base ^ (i + 1) = base * (digit base i (n / base) * base ^ i) := by
      intro i _
      have hd : digit base (i + 1) n = digit base i (n / base) := by
        simp only [digit, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
      rw [hd, pow_succ]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← ih (n / base) hdiv]
    simp only [digit, pow_zero, Nat.div_one, Nat.mul_one]
    exact (Nat.div_add_mod n base).symm

/-- `n • x = ∑ i, digit i n • (base ^ i • x)` — the per-scalar decomposition that drives the
window exchange. -/
theorem smul_eq_sum_digits (base : ℕ) (hb : 0 < base) (W n : ℕ) (x : M) (h : n < base ^ W) :
    n • x = ∑ i ∈ Finset.range W, digit base i n • (base ^ i • x) := by
  conv_lhs => rw [sum_digit base hb W n h]
  rw [Finset.sum_smul]
  simp_rw [mul_smul]

/-! ## Buckets and the weighted bucket sum -/

/-- The bucket-`b` sum of a digit-tagged point list: `∑ {x | (b, x) ∈ dp}`.  A single `filterMap`
pass, so the group additions across all buckets total the list length. -/
def bucketOf (dp : List (ℕ × M)) (b : ℕ) : M :=
  (dp.filterMap fun p => if p.1 = b then some p.2 else none).sum

/-- The direct window value of a digit-tagged list: `∑ (d, x), d • x`. -/
def naiveWindow (dp : List (ℕ × M)) : M :=
  (dp.map fun p => p.1 • p.2).sum

@[simp] theorem bucketOf_nil (b : ℕ) : bucketOf ([] : List (ℕ × M)) b = 0 := rfl

/-- Prepending `(d, x)` adds `x` to bucket `d` and leaves the others fixed. -/
theorem bucketOf_cons (d : ℕ) (x : M) (dp : List (ℕ × M)) (b : ℕ) :
    bucketOf ((d, x) :: dp) b = (if d = b then x else 0) + bucketOf dp b := by
  unfold bucketOf
  rw [List.filterMap_cons]
  by_cases h : d = b <;> simp [h]

/-- A single spike: the weighted-bucket sum of a one-hot indicator at digit `d` is `d • x`, provided
`d < base`. -/
theorem sum_ite_digit (base d : ℕ) (x : M) (hd : d < base) :
    ∑ k ∈ Finset.range (base - 1), (k + 1) • (if d = k + 1 then x else (0 : M)) = d • x := by
  cases d with
  | zero => simp
  | succ d' =>
    have hcongr : ∀ k ∈ Finset.range (base - 1),
        (k + 1) • (if d' + 1 = k + 1 then x else (0 : M))
          = if d' = k then (d' + 1) • x else 0 := by
      intro k _
      by_cases h : d' = k
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq (Finset.range (base - 1)) d' (fun _ => (d' + 1) • x)]
    have : d' ∈ Finset.range (base - 1) := by
      rw [Finset.mem_range]; omega
    simp [this]

/-- **The bucket identity.**  The direct window value equals the weighted sum of buckets
`∑_{b=1}^{base-1} b • bucketSum b`, provided every digit is `< base`. -/
theorem naiveWindow_eq_buckets (base : ℕ) (dp : List (ℕ × M))
    (hlt : ∀ p ∈ dp, p.1 < base) :
    naiveWindow dp = ∑ k ∈ Finset.range (base - 1), (k + 1) • bucketOf dp (k + 1) := by
  induction dp with
  | nil => simp [naiveWindow]
  | cons p dp ih =>
    obtain ⟨d, x⟩ := p
    have hd : d < base := hlt (d, x) (by simp)
    have ih' := ih (fun q hq => hlt q (by simp [hq]))
    simp only [naiveWindow, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    have hb : ∀ k ∈ Finset.range (base - 1),
        (k + 1) • bucketOf ((d, x) :: dp) (k + 1)
          = (k + 1) • (if d = k + 1 then x else 0) + (k + 1) • bucketOf dp (k + 1) := by
      intro k _
      rw [bucketOf_cons, smul_add]
    rw [Finset.sum_congr rfl hb, Finset.sum_add_distrib, sum_ite_digit base d x hd]

/-! ## The suffix-sum accumulation -/

/-- One step of the suffix-sum accumulator: carry `(running, total)`, add the next bucket to the
running sum, then fold the running sum into the total.  Folding this from the top bucket down
computes `∑ b, b • bucket_b` in `2 · #buckets` adds. -/
def accStep (a : M) (p : M × M) : M × M := (p.1 + a, p.2 + (p.1 + a))

/-- The mathematical spec of the accumulator's total: the position-weighted sum `∑_k (k+1) • vals[k]`
(`vals[0]` weighted `1`, …).  Recursive so the `foldr` invariant is a one-line induction — this is a
*spec*, never executed (it recomputes `vals.sum`); the executable path is `accStep`. -/
def weightedSum : List M → M
  | [] => 0
  | a :: vals => a + vals.sum + weightedSum vals

/-- The `foldr accStep` invariant: running is the plain sum, total is the position-weighted sum
(shifted by the initial carry). -/
theorem foldr_accStep (r0 t0 : M) (vals : List M) :
    List.foldr accStep (r0, t0) vals
      = (r0 + vals.sum, t0 + vals.length • r0 + weightedSum vals) := by
  induction vals with
  | nil => simp [weightedSum]
  | cons a vals ih =>
    rw [List.foldr_cons, ih, accStep]
    simp only [List.sum_cons, List.length_cons, weightedSum, succ_nsmul]
    refine Prod.ext ?_ ?_ <;> simp only <;> abel

/-- Weighted sum of an appended singleton: the new element sits at the end with weight `length + 1`. -/
theorem weightedSum_append (xs : List M) (y : M) :
    weightedSum (xs ++ [y]) = weightedSum xs + (xs.length + 1) • y := by
  induction xs with
  | nil => simp [weightedSum]
  | cons a xs ih =>
    simp only [List.cons_append, weightedSum, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero, ih, List.length_cons, succ_nsmul]
    abel

/-- Weighted sum of a `range`-indexed list is the finite weighted sum. -/
theorem weightedSum_range_map (K : ℕ) (g : ℕ → M) :
    weightedSum ((List.range K).map g) = ∑ k ∈ Finset.range K, (k + 1) • g k := by
  induction K with
  | zero => simp [weightedSum]
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, weightedSum_append,
      List.length_map, List.length_range, ih, Finset.sum_range_succ]

/-! ## The Horner fold across windows -/

/-- Horner across windows, least-significant first: `∑ i, base ^ i • vals[i]` in `#windows`
doublings.  `foldr` processes the most-significant window first (innermost), each step doubles
(`base •`) and adds the window value. -/
def hornerList (base : ℕ) (vals : List M) : M :=
  List.foldr (fun v acc => base • acc + v) 0 vals

theorem hornerList_eq (base : ℕ) (vals : List M) :
    hornerList base vals = ∑ k ∈ Finset.range vals.length, base ^ k • vals.getD k 0 := by
  induction vals with
  | nil => simp [hornerList]
  | cons v vals ih =>
    rw [hornerList, List.foldr_cons]
    show base • hornerList base vals + v = _
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, one_smul, pow_succ']
    rw [Finset.smul_sum]
    simp only [mul_smul]

/-! ## The full Pippenger MSM -/

/-- The digit-tagged term list for window `i`: each scalar replaced by its `i`-th base-`base` digit. -/
def dpOf (base i : ℕ) (terms : List (ℕ × M)) : List (ℕ × M) :=
  terms.map fun t => (digit base i t.1, t.2)

/-- The window `i` value, computed the fast way: build the `base − 1` buckets, then run the
suffix-sum accumulation (`2 · (base − 1)` adds). -/
def windowValue (base i : ℕ) (terms : List (ℕ × M)) : M :=
  (List.foldr accStep (0, 0)
    ((List.range (base - 1)).map fun k => bucketOf (dpOf base i terms) (k + 1))).2

/-- The largest scalar appearing in `terms` (`0` if empty). -/
def maxScalar (terms : List (ℕ × M)) : ℕ := (terms.map Prod.fst).foldr max 0

omit [AddCommMonoid M] in
theorem le_maxScalar (terms : List (ℕ × M)) (t : ℕ × M) (ht : t ∈ terms) :
    t.1 ≤ maxScalar terms := by
  unfold maxScalar
  have : t.1 ∈ terms.map Prod.fst := List.mem_map_of_mem ht
  generalize terms.map Prod.fst = l at this
  clear ht
  induction l with
  | nil => simp at this
  | cons a l ih =>
    rcases List.mem_cons.mp this with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The number of windows: enough base-`2 ^ c` digits to cover the largest scalar. -/
def numWindows (c : ℕ) (terms : List (ℕ × M)) : ℕ :=
  Nat.log (2 ^ c) (maxScalar terms) + 1

/-- **Windowed Pippenger MSM.**  Provably equal to `naiveMsm` (`pippenger_eq_msm`). -/
def pippenger (c : ℕ) (terms : List (ℕ × M)) : M :=
  hornerList (2 ^ c)
    ((List.range (numWindows c terms)).map fun i => windowValue (2 ^ c) i terms)

/-! ## Auxiliary sum-exchange lemmas -/

/-- Push a scalar through a mapped list sum. -/
theorem smul_list_sum (c : ℕ) (l : List M) :
    c • l.sum = (l.map fun a => c • a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [smul_add, ih]

/-- Fubini between a list sum and a finite sum. -/
theorem list_sum_finset_sum {α ι : Type*} (l : List α) (s : Finset ι) (F : α → ι → M) :
    (l.map fun a => ∑ i ∈ s, F a i).sum = ∑ i ∈ s, (l.map fun a => F a i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]

/-- `getD` of a `range`-map at an in-range index. -/
theorem getD_map_range (f : ℕ → M) (W k : ℕ) (h : k < W) :
    ((List.range W).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD]
  simp [h]

/-! ## The main equality -/

/-- The fast window value equals the direct window contribution `∑ (n, x), digit(n) • x`. -/
theorem windowValue_eq (base i : ℕ) (hbase : 0 < base) (terms : List (ℕ × M)) :
    windowValue base i terms = (terms.map fun t => digit base i t.1 • t.2).sum := by
  unfold windowValue
  rw [foldr_accStep]
  simp only [smul_zero, add_zero, zero_add]
  rw [weightedSum_range_map]
  have hdp : ∀ p ∈ dpOf base i terms, p.1 < base := by
    intro p hp
    unfold dpOf at hp
    rw [List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    exact Nat.mod_lt _ hbase
  rw [← naiveWindow_eq_buckets base (dpOf base i terms) hdp]
  unfold naiveWindow dpOf
  rw [List.map_map]
  rfl

/-- **Pippenger equals the naive MSM.**  For any window size `c ≥ 1` and any term list. -/
theorem pippenger_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × M)) :
    pippenger c terms = (terms.map fun t => t.1 • t.2).sum := by
  have hb1 : 1 < 2 ^ c := Nat.one_lt_two_pow_iff.mpr hc.ne'
  have hb0 : 0 < 2 ^ c := by positivity
  set base := 2 ^ c
  set W := numWindows c terms with hW
  -- every scalar fits in `W` base-`base` digits
  have hbound : ∀ t ∈ terms, t.1 < base ^ W := by
    intro t ht
    calc t.1 ≤ maxScalar terms := le_maxScalar terms t ht
      _ < base ^ W := Nat.lt_pow_succ_log_self hb1 _
  -- the Pippenger value is the Horner sum of the true window contributions
  have hpip : pippenger c terms
      = ∑ i ∈ Finset.range W, base ^ i • (terms.map fun t => digit base i t.1 • t.2).sum := by
    unfold pippenger
    rw [hornerList_eq, List.length_map, List.length_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [getD_map_range _ _ _ hk, windowValue_eq base k hb0]
  rw [hpip]
  -- the naive MSM is the same Horner sum, via digit decomposition + sum exchange
  have e1 : (terms.map fun t => t.1 • t.2)
      = terms.map fun t => ∑ i ∈ Finset.range W, digit base i t.1 • (base ^ i • t.2) := by
    apply List.map_congr_left
    intro t ht
    exact smul_eq_sum_digits base hb0 W t.1 t.2 (hbound t ht)
  rw [e1, list_sum_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [Function.comp]
  rw [smul_comm]

/-! ## Single-pass Array bucketing (constant factors)

`windowValue` computes each bucket by its own `filterMap` pass — `(base − 1) · n` list steps per
window, which measurably competes with the group ops at `base = 2 ^ 8` and dominates beyond.
`bucketScatter` builds all buckets in ONE pass (an `Array.modify` per term) and is proven to
produce exactly the `bucketOf` list (`bucketScatter_toList`), so
`pippengerFast = pippenger = naiveMsm`. -/

/-- One scatter step: drop digit-`0` terms, otherwise add the point into bucket slot `d − 1`
(slot `k` holds bucket `k + 1`). -/
def scatterStep (a : Array M) (p : ℕ × M) : Array M :=
  if p.1 = 0 then a else a.modify (p.1 - 1) (· + p.2)

/-- Scatter a digit-tagged point list into its `base − 1` buckets in one pass. -/
def bucketScatter (base : ℕ) (dp : List (ℕ × M)) : Array M :=
  dp.foldl scatterStep (Array.replicate (base - 1) 0)

@[simp] theorem size_scatterStep (a : Array M) (p : ℕ × M) :
    (scatterStep a p).size = a.size := by
  unfold scatterStep; split <;> simp

@[simp] theorem size_foldl_scatterStep (dp : List (ℕ × M)) (a : Array M) :
    (dp.foldl scatterStep a).size = a.size := by
  induction dp generalizing a with
  | nil => rfl
  | cons p dp ih => rw [List.foldl_cons, ih, size_scatterStep]

/-- A single scatter step read back through `getElem?` (proof-free indexing, so the fold invariant
rewrites cleanly): slot `k` gains `x` exactly when the digit is `k + 1`. -/
theorem getElem?_scatterStep (a : Array M) (d : ℕ) (x : M) (k : ℕ) :
    (scatterStep a (d, x))[k]?
      = a[k]?.map fun v => v + (if d = k + 1 then x else 0) := by
  unfold scatterStep
  by_cases h0 : d = 0
  · simp [h0, Option.map_id']
  · simp only [if_neg h0]
    rw [Array.getElem?_modify]
    by_cases hdk : d = k + 1
    · rw [if_pos (by omega), if_pos hdk]
    · rw [if_neg (by omega), if_neg hdk]
      simp [Option.map_id']

/-- The fold invariant: slot `k` accumulates bucket `k + 1` on top of its initial value. -/
theorem getElem?_foldl_scatterStep (dp : List (ℕ × M)) :
    ∀ (a : Array M) (k : ℕ),
      (dp.foldl scatterStep a)[k]? = a[k]?.map fun v => v + bucketOf dp (k + 1) := by
  induction dp with
  | nil => intro a k; simp [Option.map_id']
  | cons p dp ih =>
    intro a k
    obtain ⟨d, x⟩ := p
    rw [List.foldl_cons, ih (scatterStep a (d, x)) k, getElem?_scatterStep a d x k,
      Option.map_map, bucketOf_cons]
    apply congrFun
    apply congrArg
    funext v
    simp only [Function.comp_apply]
    rw [add_assoc]

/-- `bucketScatter` produces exactly the per-bucket list `windowValue` folds over. -/
theorem bucketScatter_toList (base : ℕ) (dp : List (ℕ × M)) :
    (bucketScatter base dp).toList
      = (List.range (base - 1)).map fun k => bucketOf dp (k + 1) := by
  apply List.ext_getElem?
  intro k
  rw [Array.getElem?_toList, bucketScatter, getElem?_foldl_scatterStep dp _ k,
    List.getElem?_map, Array.getElem?_replicate]
  by_cases hk : k < base - 1
  · rw [if_pos hk, List.getElem?_range hk]
    simp
  · rw [if_neg hk, List.getElem?_eq_none (by simp; omega)]
    simp

/-- The window value via the single-pass scatter. -/
def windowValueFast (base i : ℕ) (terms : List (ℕ × M)) : M :=
  (List.foldr accStep (0, 0) (bucketScatter base (dpOf base i terms)).toList).2

theorem windowValueFast_eq (base i : ℕ) (terms : List (ℕ × M)) :
    windowValueFast base i terms = windowValue base i terms := by
  unfold windowValueFast windowValue
  rw [bucketScatter_toList]

/-- **Windowed Pippenger MSM, Array-bucketed** — the executable accelerator.  Equal to `pippenger`
(`pippengerFast_eq`) and hence to the naive MSM (`pippengerFast_eq_msm`). -/
def pippengerFast (c : ℕ) (terms : List (ℕ × M)) : M :=
  hornerList (2 ^ c)
    ((List.range (numWindows c terms)).map fun i => windowValueFast (2 ^ c) i terms)

theorem pippengerFast_eq (c : ℕ) (terms : List (ℕ × M)) :
    pippengerFast c terms = pippenger c terms := by
  unfold pippengerFast pippenger
  congr 1
  apply List.map_congr_left
  intro i _
  exact windowValueFast_eq (2 ^ c) i terms

/-- The Array-bucketed Pippenger equals the naive MSM — the accelerator's end-to-end
correctness. -/
theorem pippengerFast_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × M)) :
    pippengerFast c terms = (terms.map fun t => t.1 • t.2).sum := by
  rw [pippengerFast_eq, pippenger_eq_msm c hc]

/-! ## Windows-parallel Pippenger

The `numWindows c terms ≈ ⌈255/c⌉` window values are mutually independent (each scans the term
list, buckets, and runs its own suffix accumulation); only the final Horner fold consumes them in
order. `pippengerFastPar` evaluates the windows through the proven `parMap` below, so the
equality to the sequential accelerator is purely `parMap_eq_map` — the evaluation strategy is
the only difference. Measured (interpreted, `n = 2048`, `c = 8`, 12 cores):
`11.6 s → 4.3 s` per MSM. -/

/-- Parallel `List.map`: spawn a task per element, then collect the results in order.

This is a *pure* function — `Task` is logically the one-field structure `⟨get : α⟩`,
`Task.spawn fn = ⟨fn ()⟩` and `Task.get ⟨a⟩ = a` are both definitional — so it is provably equal
to `List.map` (`parMap_eq_map`). The only thing it changes is the *evaluation strategy*: under
`native_decide` (compiled to C, run on the real task scheduler) the elementwise work runs on the
thread pool. Because the equality to `List.map` is definitional, swapping `List.map` for `parMap`
in a `native_decide`-backed definition changes nothing about the statement's meaning or trust
base: the compiled `Task` primitives are already inside the `native_decide` trust boundary, and
the kernel's view is literally `List.map`. -/
def parMap {α : Type u} {β : Type v} (f : α → β) (xs : List α) : List β :=
  (xs.map (fun x => Task.spawn (fun _ => f x))).map Task.get

/-- `parMap` is `List.map`: the task round-trip `Task.get (Task.spawn (fun _ => f x))` is `f x`
definitionally, so nothing but the evaluation strategy differs. -/
@[simp] theorem parMap_eq_map {α : Type u} {β : Type v} (f : α → β) (xs : List α) :
    parMap f xs = xs.map f := by
  rw [parMap, List.map_map]; rfl

/-- **Windows-parallel Array-bucketed Pippenger MSM**: `pippengerFast` with the independent
window values evaluated as parallel tasks. Equal to `pippengerFast` (`pippengerFastPar_eq`)
and hence to the naive MSM (`pippengerFastPar_eq_msm`). -/
def pippengerFastPar (c : ℕ) (terms : List (ℕ × M)) : M :=
  hornerList (2 ^ c)
    (parMap (fun i => windowValueFast (2 ^ c) i terms) (List.range (numWindows c terms)))

/-- The windows-parallel Pippenger is the sequential one: `parMap` is `map`. -/
theorem pippengerFastPar_eq (c : ℕ) (terms : List (ℕ × M)) :
    pippengerFastPar c terms = pippengerFast c terms := by
  rw [pippengerFastPar, parMap_eq_map, pippengerFast]

/-- The windows-parallel Pippenger equals the naive MSM. -/
theorem pippengerFastPar_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × M)) :
    pippengerFastPar c terms = (terms.map fun t => t.1 • t.2).sum := by
  rw [pippengerFastPar_eq, pippengerFast_eq_msm c hc]

/-! ## The `commit_lagrange` wrapper -/

/-- The default window size, picked by measurement (see the module docstring's ladder): `c = 8`
is the optimum for the `n = 2048`-term MSMs of an Orchard-sized verifying key — `10.7×` over the
naive MSM. -/
def defaultWindow : ℕ := 8

section Wrapper

variable {G : Type*} [AddCommGroup G] [Inhabited G]

/-- The scalar field the commitment coefficients live in: Vesta's scalar field (`= pallas::Base`),
which is what a Vesta-based Pedersen commitment takes its coefficients from. -/
abbrev Fp := CompElliptic.Fields.Pasta.VestaScalarField

/-- The naive `commit_lagrange` spec — a Pedersen vector commitment against a fixed Lagrange
basis, plus a blinding term:
`(∑ᵢ coeffsᵢ.val • basisᵢ) + blind`. -/
def commitLagrangeSpec (blind : G) (basis : List G) (coeffs : List Fp) : G :=
  ((List.range coeffs.length).map
    (fun i => (coeffs.getD i 0).val • basis.getD i 0)).sum + blind

/-- The fast `commit_lagrange`: Array-bucketed windowed Pippenger over the `(coeffᵢ.val, basisᵢ)`
terms, plus the blind.  The terms are zipped directly (`List.zip`), not indexed through `getD`, to
avoid the quadratic list-indexing of the spec's `range`/`getD` spelling. -/
def commitLagrangeFastWith (c : ℕ) (blind : G) (basis : List G) (coeffs : List Fp) : G :=
  pippengerFast c
    ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
      fun t => (t.1.val, t.2)) + blind

omit [Inhabited G] in
/-- The zipped term list is the spec's `range`/`getD` term list: the padded basis makes the zip
total at length `coeffs.length`, and in-range `getD` is `getElem`. -/
theorem zip_terms_eq (basis : List G) (coeffs : List Fp) :
    ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
        fun t => (t.1.val, t.2))
      = (List.range coeffs.length).map
          fun i => ((coeffs.getD i 0).val, basis.getD i 0) := by
  apply List.ext_getElem
  · simp [List.length_zip]; omega
  · intro i h1 h2
    have hi : i < coeffs.length := by
      simp only [List.length_map, List.length_zip] at h1
      omega
    simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
    have hc : coeffs.getD i 0 = coeffs[i] := List.getD_eq_getElem coeffs 0 hi
    rw [hc]
    rcases Nat.lt_or_ge i basis.length with hib | hib
    · rw [List.getElem_append_left hib, List.getD_eq_getElem basis 0 hib]
    · rw [List.getElem_append_right hib, List.getD_eq_default basis 0 (by omega)]
      simp

omit [Inhabited G] in
/-- **The fast commitment equals the naive spec.** -/
theorem commitLagrangeFastWith_eq (c : ℕ) (hc : 0 < c)
    (blind : G) (basis : List G) (coeffs : List Fp) :
    commitLagrangeFastWith c blind basis coeffs = commitLagrangeSpec blind basis coeffs := by
  unfold commitLagrangeFastWith commitLagrangeSpec
  rw [zip_terms_eq, pippengerFast_eq, pippenger_eq_msm c hc, List.map_map]
  rfl

end Wrapper

end CompElliptic.Curves.Pasta.Fast.Msm
