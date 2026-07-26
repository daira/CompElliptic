/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta.Fast.NatKernel
import CompElliptic.Curves.Pasta.Fast.Projective
import CompElliptic.Curves.Pasta.Fast.MsmProj

/-!
# The `Nat` kernel is the proven projective arithmetic

`CompElliptic.Curves.Pasta.Fast.NatKernel` is a zero-import transplant of the projective Vesta
arithmetic, so that it can be native-compiled (see the `FastFieldNative` lane in the lakefile).
This module — which is mathlib-side, and therefore *not* in that lane — proves that the
transplant computes the statement-surface functions of
`CompElliptic.Curves.Pasta.Fast.Projective`, operation for operation.  These specs are also
load-bearing for the faster Montgomery tier, whose kernels are proven correct by transport
through this one's shared schedules (`CompElliptic.Curves.Pasta.Fast.ProjectiveMontEquiv`).

The bridge is the coordinatewise cast `toPVes : P3 → PVes`, `⟨x, y, z⟩ ↦ (x : 𝔽_q, y, z)`.  It
is a *representation* map, not an isomorphism: many `P3`s denote the same `PVes` (the kernel
keeps canonical representatives, so in fact `toPVes` is injective on canonical triples, but
nothing below needs that).  Each kernel operation is shown to commute with it, exactly as
`padd_eq_paddFast` relates `padd` to its fused raw-`ℕ` spelling.

## Main results

* `toPVes_padd` — the kernel's RCB addition is `PVes.padd`
* `toPVes_pid`, `toPVes_pneg` — identity and negation
* `pnsmul_spec` — the kernel's 256-step ladder is `n • ·` in the affine group, for `n < 2 ^ 256`
* `msm_spec` — the kernel's windowed Pippenger MSM is `Fast.Msm.pippenger`, the accelerator proven
  equal to the naive multi-scalar multiplication
* `valid_pneg`, `toAffine_pneg` — the kernel's negation is the affine group inverse

`msm_spec` goes through the already-proven projective port: `msm` mirrors
`MsmProj.pippengerProjScatter` fold for fold (bucket scatter, suffix-sum downsweep, Horner).

The kernel's radix-2 DIT FFT (`NatKernel.fft`) is deliberately *not* specified here: its
statement needs a reference group DFT to be equal to, and CompElliptic has none yet.  A
downstream consumer that does have one proves the array simulation on its side, out of `toG`,
`toPVes_padd`/`valid_padd`, `pnsmul_spec` and `toAffine_pneg` — which is what the last section
of this module exists to supply.
-/

namespace CompElliptic.Curves.Pasta.Fast.NatKernel

open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.Projective
open CompElliptic.Curves.Pasta.Fast.Projective.PVes

/-- The Vesta base field, the ambient field of the projective statement surface. -/
local notation "Fq" => CompElliptic.Curves.Pasta.Fast.Projective.Fq

/-- The kernel's modulus literal is the Vesta base field order. -/
theorem qv_eq : qv = CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := rfl

theorem qv_pos : 0 < qv := by decide

/-- Coordinatewise interpretation of a kernel triple as a projective point over `𝔽_q`. -/
def toPVes (p : P3) : PVes := ⟨(p.x : Fq), (p.y : Fq), (p.z : Fq)⟩

@[simp] theorem toPVes_X (p : P3) : (toPVes p).X = (p.x : Fq) := rfl
@[simp] theorem toPVes_Y (p : P3) : (toPVes p).Y = (p.y : Fq) := rfl
@[simp] theorem toPVes_Z (p : P3) : (toPVes p).Z = (p.z : Fq) := rfl

/-! ## The field operations -/

theorem cast_fadd (a b : ℕ) : ((fadd a b : ℕ) : Fq) = (a : Fq) + (b : Fq) := by
  rw [fadd, qv_eq, ZMod.natCast_mod, Nat.cast_add]

theorem cast_fmul (a b : ℕ) : ((fmul a b : ℕ) : Fq) = (a : Fq) * (b : Fq) := by
  rw [fmul, qv_eq, ZMod.natCast_mod, Nat.cast_mul]

theorem cast_fsub (a b : ℕ) : ((fsub a b : ℕ) : Fq) = (a : Fq) - (b : Fq) := by
  rw [fsub, qv_eq, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub (Nat.mod_lt _ (qv_eq ▸ qv_pos)).le, ZMod.natCast_mod, ZMod.natCast_self]
  ring

/-! ## The group operations -/

/-- **The kernel's addition is the projective addition.**  Same Renes–Costello–Batina closed
forms, evaluated on canonical representatives with fused mul-mod. -/
theorem toPVes_padd (p q : P3) : toPVes (padd p q) = PVes.padd (toPVes p) (toPVes q) := by
  simp only [padd, PVes.padd, toPVes, PVes.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cast_fadd, cast_fmul, cast_fsub, Nat.cast_ofNat] <;> ring

set_option linter.unusedSimpArgs false in
@[simp] theorem toPVes_pid : toPVes pid = PVes.pid := by
  simp only [pid, toPVes, PVes.pid, PVes.mk.injEq, Nat.cast_zero, Nat.cast_one]

set_option linter.unusedSimpArgs false in
/-- **The kernel's negation is coordinate negation of `Y`**, the short-Weierstrass inverse. -/
theorem toPVes_pneg (p : P3) :
    toPVes (pneg p) = ⟨(toPVes p).X, -(toPVes p).Y, (toPVes p).Z⟩ := by
  simp only [pneg, toPVes, PVes.mk.injEq, cast_fsub, Nat.cast_zero, zero_sub]

/-! ## The scalar ladder

`pnsmul` is a fixed 256-step LSB-first double-and-add, which is a different schedule from the
statement-surface `pnsmulFast` (`binNsmul`, MSB-first recursion).  The equality is therefore
proved where the group law lives: through `toAffine`, using that `padd` is the affine
addition on valid points (`toAffine_padd`) and preserves validity (`valid_padd`). -/

/-- The ladder state after `i` steps: the accumulator holds `(n mod 2 ^ i) • A` and the base
holds `2 ^ i • A`, both valid. -/
private def LadderInv (A : G) (n i : ℕ) (st : P3 × P3) : Prop :=
  Valid (toPVes st.1) ∧ Valid (toPVes st.2) ∧
    toAffine (toPVes st.1) = (n % 2 ^ i) • A ∧ toAffine (toPVes st.2) = (2 ^ i : ℕ) • A

private theorem ladder_step {A : G} {n i : ℕ} {st : P3 × P3} (h : LadderInv A n i st) :
    LadderInv A n (i + 1)
      ((if (n >>> i) &&& 1 = 1 then padd st.1 st.2 else st.1), padd st.2 st.2) := by
  obtain ⟨hv1, hv2, ha1, ha2⟩ := h
  have hbit : (n >>> i) &&& 1 = n / 2 ^ i % 2 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have hmod : n % 2 ^ (i + 1) = n % 2 ^ i + 2 ^ i * (n / 2 ^ i % 2) := by
    rw [pow_succ, Nat.mod_mul]
  have hdouble : toAffine (toPVes (padd st.2 st.2)) = (2 ^ (i + 1) : ℕ) • A := by
    rw [toPVes_padd, toAffine_padd hv2 hv2, ha2, ← two_nsmul, smul_smul, pow_succ]
    ring_nf
  refine ⟨?_, ?_, ?_, hdouble⟩
  · split
    · exact toPVes_padd _ _ ▸ valid_padd hv1 hv2
    · exact hv1
  · exact toPVes_padd _ _ ▸ valid_padd hv2 hv2
  · split
    · rename_i hodd
      rw [toPVes_padd, toAffine_padd hv1 hv2, ha1, ha2, ← add_nsmul]
      congr 1
      rw [hbit] at hodd
      rw [hmod, hodd, Nat.mul_one]
    · rename_i heven
      rw [ha1]
      congr 1
      rw [hbit] at heven
      have h0 : n / 2 ^ i % 2 = 0 := by omega
      rw [hmod, h0, Nat.mul_zero, Nat.add_zero]

/-- **The kernel ladder computes `n • ·`** in the affine group, for scalars below `2 ^ 256`
(all Pasta scalars).  Statement shape mirrors `PVes.pnsmulFast_spec`. -/
theorem pnsmul_spec {p : P3} (hp : Valid (toPVes p)) (n : ℕ) (hn : n < 2 ^ 256) :
    Valid (toPVes (pnsmul n p)) ∧
      toAffine (toPVes (pnsmul n p)) = n • toAffine (toPVes p) := by
  set A := toAffine (toPVes p) with hA
  have base : ∀ m : ℕ, m ≤ 256 →
      LadderInv A n m ((List.range m).foldl
        (fun (st : P3 × P3) i =>
          (if (n >>> i) &&& 1 = 1 then padd st.1 st.2 else st.1, padd st.2 st.2))
        (pid, p)) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp only [List.range_zero, List.foldl_nil]
        refine ⟨?_, hp, ?_, ?_⟩
        · rw [toPVes_pid]; exact valid_pid
        · rw [toPVes_pid, toAffine_pid, pow_zero, Nat.mod_one, zero_nsmul]
        · rw [pow_zero, hA, one_nsmul]
    | succ k ih =>
        intro hk
        rw [List.range_succ, List.foldl_append]
        exact ladder_step (ih (by omega))
  obtain ⟨hv, -, hval, -⟩ := base 256 le_rfl
  refine ⟨hv, ?_⟩
  rw [pnsmul, hval, Nat.mod_eq_of_lt hn]

/-! ## The windowed Pippenger MSM

The kernel's `msm` is spelled to mirror `MsmProj.pippengerProjScatter` fold for fold: the
Array-scatter bucketing (`scatterStep`/`bucketScatter`), the suffix-sum downsweep (`accStep`), and
the Horner recombination across windows.  Each of those is `toPVes`-transported to its `PVes` twin
*structurally* (no validity needed — `toPVes_padd` is unconditional), and the already-proven
`MsmProj.pwindowValueFast_spec` then supplies the affine meaning of a window.

The one place the kernel deliberately differs is the window count: it uses the fixed
`⌈256 / c⌉` windows of a Pasta scalar rather than `Msm.numWindows` (which depends on the term
list). `hornerList_windows_eq_msm` is `Msm.pippenger_eq_msm` with the window count freed, which
reconciles the two. -/

/-- Mapping commutes with `Array.modify` when the modification commutes. -/
private theorem map_modify {α β : Type} (g : α → β) (f : α → α) (f' : β → β)
    (hf : ∀ v, g (f v) = f' (g v)) (a : Array α) (j : ℕ) :
    (a.modify j f).map g = (a.map g).modify j f' := by
  apply Array.ext_getElem?
  intro i
  by_cases h : j = i
  · subst h
    rcases hoi : a[j]? with _ | v <;>
      simp [Array.getElem?_map, Array.getElem?_modify, hoi, hf]
  · simp [Array.getElem?_map, Array.getElem?_modify, h]

/-- One kernel scatter step is `MsmProj.pscatterStep` after `toPVes`. -/
private theorem map_scatterStep (a : Array P3) (p : ℕ × P3) :
    (scatterStep a p).map toPVes = MsmProj.pscatterStep (a.map toPVes) (p.1, toPVes p.2) := by
  unfold scatterStep MsmProj.pscatterStep
  by_cases h : p.1 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact map_modify toPVes _ _ (fun v => toPVes_padd v p.2) a (p.1 - 1)

/-- The kernel's single-pass bucketing is `MsmProj.pbucketScatter` after `toPVes`. -/
private theorem map_bucketScatter (base : ℕ) (dp : List (ℕ × P3)) :
    (bucketScatter base dp).map toPVes
      = MsmProj.pbucketScatter base (dp.map fun t => (t.1, toPVes t.2)) := by
  have hfold : ∀ (l : List (ℕ × P3)) (a : Array P3),
      (l.foldl scatterStep a).map toPVes
        = (l.map fun t => (t.1, toPVes t.2)).foldl MsmProj.pscatterStep (a.map toPVes) := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons p l ih =>
      intro a
      rw [List.foldl_cons, ih, map_scatterStep, List.map_cons, List.foldl_cons]
  rw [bucketScatter, MsmProj.pbucketScatter, hfold, Array.map_replicate, toPVes_pid]

/-- The kernel's bucket downsweep is `MsmProj.paccStep`'s fold after `toPVes`. -/
private theorem foldr_accStep_toPVes (L : List P3) :
    (toPVes (L.foldr accStep (pid, pid)).1, toPVes (L.foldr accStep (pid, pid)).2)
      = List.foldr MsmProj.paccStep (PVes.pid, PVes.pid) (L.map toPVes) := by
  induction L with
  | nil => simp only [List.foldr_nil, List.map_nil, toPVes_pid]
  | cons a L ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, ← ih]
    simp only [accStep, MsmProj.paccStep, toPVes_padd]

/-- **The kernel's window value is the projective scatter-bucketed window value.** -/
theorem toPVes_windowValue (base i : ℕ) (terms : List (ℕ × P3)) :
    toPVes (windowValue base i terms)
      = MsmProj.pwindowValueFast base i (terms.map fun t => (t.1, toPVes t.2)) := by
  have hb : (bucketScatter base (terms.map fun t => (t.1 / base ^ i % base, t.2))).toList.map toPVes
      = (MsmProj.pbucketScatter base
          (MsmProj.pdpOf base i (terms.map fun t => (t.1, toPVes t.2)))).toList := by
    rw [← Array.toList_map, map_bucketScatter]
    congr 2
    simp only [MsmProj.pdpOf, List.map_map, Function.comp_def, Msm.digit]
  show toPVes (List.foldr accStep (pid, pid) _).2 = _
  rw [MsmProj.pwindowValueFast, ← hb, ← foldr_accStep_toPVes]

/-- The `c`-fold doubling is `2 ^ c • ·` in the affine group. -/
private theorem pdoublings_spec {p : P3} (hp : Valid (toPVes p)) (c : ℕ) :
    Valid (toPVes (pdoublings c p)) ∧
      toAffine (toPVes (pdoublings c p)) = (2 ^ c : ℕ) • toAffine (toPVes p) := by
  induction c with
  | zero => exact ⟨hp, by rw [pow_zero, one_nsmul]; rfl⟩
  | succ k ih =>
    obtain ⟨hv, he⟩ := ih
    have hstep : pdoublings (k + 1) p = padd (pdoublings k p) (pdoublings k p) := by
      rw [pdoublings, List.range_succ, List.foldl_append]; rfl
    rw [hstep, toPVes_padd]
    refine ⟨valid_padd hv hv, ?_⟩
    rw [toAffine_padd hv hv, he, ← two_nsmul, smul_smul, pow_succ]
    ring_nf

/-- The kernel's Horner recombination across windows is `Msm.hornerList` after `toAffine`. -/
private theorem hfold_spec (c : ℕ) (vals : List P3) (h : ∀ v ∈ vals, Valid (toPVes v)) :
    Valid (toPVes (vals.foldr (fun v acc => padd (pdoublings c acc) v) pid)) ∧
      toAffine (toPVes (vals.foldr (fun v acc => padd (pdoublings c acc) v) pid))
        = Msm.hornerList (2 ^ c) (vals.map fun v => toAffine (toPVes v)) := by
  induction vals with
  | nil =>
    refine ⟨by rw [List.foldr_nil, toPVes_pid]; exact valid_pid, ?_⟩
    rw [List.foldr_nil, toPVes_pid, toAffine_pid, List.map_nil, Msm.hornerList, List.foldr_nil]
  | cons v xs ih =>
    have hv : Valid (toPVes v) := h v (by simp)
    obtain ⟨hacc, heq⟩ := ih fun w hw => h w (by simp [hw])
    obtain ⟨hdv, hde⟩ := pdoublings_spec hacc c
    rw [List.foldr_cons, toPVes_padd]
    refine ⟨valid_padd hdv hv, ?_⟩
    rw [toAffine_padd hdv hv, hde, heq, List.map_cons]
    simp only [Msm.hornerList, List.foldr_cons]

/-- **Horner recombination of `W` windows is the naive MSM**, whenever `W` base-`2 ^ c` digits
cover every scalar.  This is `Msm.pippenger_eq_msm` with the window count freed from
`Msm.numWindows` (the kernel fixes it at `⌈256 / c⌉`). -/
private theorem hornerList_windows_eq_msm (c W : ℕ) (terms : List (ℕ × G))
    (hW : ∀ t ∈ terms, t.1 < (2 ^ c) ^ W) :
    Msm.hornerList (2 ^ c) ((List.range W).map fun i => Msm.windowValue (2 ^ c) i terms)
      = (terms.map fun t => t.1 • t.2).sum := by
  have hb0 : 0 < 2 ^ c := by positivity
  have hpip : Msm.hornerList (2 ^ c)
        ((List.range W).map fun i => Msm.windowValue (2 ^ c) i terms)
      = ∑ i ∈ Finset.range W,
          (2 ^ c) ^ i • (terms.map fun t => Msm.digit (2 ^ c) i t.1 • t.2).sum := by
    rw [Msm.hornerList_eq, List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [Msm.getD_map_range _ _ _ hk, Msm.windowValue_eq (2 ^ c) k hb0]
  rw [hpip]
  have e1 : (terms.map fun t => t.1 • t.2)
      = terms.map fun t =>
          ∑ i ∈ Finset.range W, Msm.digit (2 ^ c) i t.1 • ((2 ^ c) ^ i • t.2) :=
    List.map_congr_left fun t ht => Msm.smul_eq_sum_digits (2 ^ c) hb0 W t.1 t.2 (hW t ht)
  rw [e1, Msm.list_sum_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Msm.smul_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply]
  rw [smul_comm]

/-- **The kernel's windowed Pippenger MSM is the proven affine Pippenger.**  Structurally the
kernel runs `MsmProj.pippengerProjScatter` over canonical `Nat` representatives; the fixed
`⌈256 / c⌉` window count is reconciled with `Msm.numWindows` through the naive MSM. -/
theorem msm_spec (c : ℕ) (hc : 0 < c) (terms : List (ℕ × P3))
    (hv : ∀ t ∈ terms, Valid (toPVes t.2)) (hn : ∀ t ∈ terms, t.1 < 2 ^ 256) :
    toAffine (toPVes (msm c terms))
      = Msm.pippenger c (terms.map fun t => (t.1, toAffine (toPVes t.2))) := by
  set W := (256 + c - 1) / c with hWdef
  set aterms := terms.map fun t => (t.1, toAffine (toPVes t.2)) with haterms
  have hptv : ∀ p ∈ terms.map (fun t => (t.1, toPVes t.2)), Valid p.2 := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact hv t ht
  have hmapaff : (terms.map fun t => (t.1, toPVes t.2)).map (fun t => (t.1, toAffine t.2))
      = aterms := by
    rw [haterms, List.map_map]
    rfl
  have hwinv : ∀ i, Valid (toPVes (windowValue (2 ^ c) i terms)) := fun i => by
    rw [toPVes_windowValue]
    exact (MsmProj.pwindowValueFast_spec _ i _ hptv).1
  have hwina : ∀ i, toAffine (toPVes (windowValue (2 ^ c) i terms))
      = Msm.windowValue (2 ^ c) i aterms := fun i => by
    rw [toPVes_windowValue, (MsmProj.pwindowValueFast_spec _ i _ hptv).2, hmapaff]
  have hvals : ∀ v ∈ (List.range W).map (fun i => windowValue (2 ^ c) i terms),
      Valid (toPVes v) := by
    intro v hvm
    rw [List.mem_map] at hvm
    obtain ⟨i, -, rfl⟩ := hvm
    exact hwinv i
  have hmsm : msm c terms = ((List.range W).map fun i => windowValue (2 ^ c) i terms).foldr
      (fun v acc => padd (pdoublings c acc) v) pid := rfl
  rw [hmsm, (hfold_spec c _ hvals).2, List.map_map]
  have hmapwin : ((List.range W).map fun i =>
        toAffine (toPVes (windowValue (2 ^ c) i terms)))
      = (List.range W).map fun i => Msm.windowValue (2 ^ c) i aterms :=
    List.map_congr_left fun i _ => hwina i
  rw [show ((fun v => toAffine (toPVes v)) ∘ fun i => windowValue (2 ^ c) i terms)
      = fun i => toAffine (toPVes (windowValue (2 ^ c) i terms)) from rfl, hmapwin]
  have hcW : 256 ≤ c * W := by
    have h1 : c * W + (256 + c - 1) % c = 256 + c - 1 := by
      rw [hWdef]; exact Nat.div_add_mod (256 + c - 1) c
    have h2 : (256 + c - 1) % c < c := Nat.mod_lt _ hc
    obtain ⟨x, hx⟩ : ∃ x, c * W = x := ⟨_, rfl⟩
    rw [hx] at h1 ⊢
    omega
  have hbound : ∀ t ∈ aterms, t.1 < (2 ^ c) ^ W := by
    intro t ht
    rw [haterms, List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    calc s.1 < 2 ^ 256 := hn s hs
      _ ≤ (2 ^ c) ^ W := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) hcW
  rw [hornerList_windows_eq_msm c W aterms hbound, ← Msm.pippenger_eq_msm c hc]

/-! ## The affine reading, and projective negation through it

`toG` is the composite `toAffine ∘ toPVes`, the map an array-level simulation of the kernel
transports along.  `pneg` is the last kernel operation whose affine meaning is needed: unlike
`padd` it is not used by the ladder or the MSM, but any FFT-shaped consumer needs it for the
butterfly's subtraction (`a − t = padd a (pneg t)`). -/

/-- The affine reading of a kernel triple. -/
def toG (p : P3) : G := toAffine (toPVes p)

theorem toG_eq : toG = toAffine ∘ toPVes := rfl

/-! ### Projective negation through `toAffine` -/

/-- Negation preserves validity: `(X : −Y : Z)` is on the curve whenever `(X : Y : Z)` is. -/
theorem valid_pneg {p : P3} (h : Valid (toPVes p)) : Valid (toPVes (pneg p)) := by
  obtain ⟨hoc, hne⟩ := h
  rw [toPVes_pneg]
  refine ⟨?_, ?_⟩
  · simp only [OnCurveP] at hoc ⊢
    linear_combination hoc
  · rcases hne with hx | hy | hz
    · exact Or.inl hx
    · exact Or.inr (Or.inl (neg_ne_zero.mpr hy))
    · exact Or.inr (Or.inr hz)

/-- **The kernel's negation is the affine group inverse.** -/
theorem toAffine_pneg {p : P3} (h : Valid (toPVes p)) :
    toAffine (toPVes (pneg p)) = - toAffine (toPVes p) := by
  rcases eq_or_ne (toPVes p).Z 0 with hz | hz
  · have h1 : toAffine (toPVes (pneg p)) = 0 := by
      rw [toPVes_pneg, toAffine, dif_neg]
      rintro ⟨-, hne⟩
      exact hne hz
    have h2 : toAffine (toPVes p) = 0 := by
      rw [toAffine, dif_neg]
      rintro ⟨-, hne⟩
      exact hne hz
    rw [h1, h2, neg_zero]
  · have e2 : ((toAffine (toPVes p)).x, (toAffine (toPVes p)).y)
        = ((toPVes p).X / (toPVes p).Z, (toPVes p).Y / (toPVes p).Z) := by
      rw [toAffine_coords h, aff, if_neg hz]
    have e1 : ((toAffine (toPVes (pneg p))).x, (toAffine (toPVes (pneg p))).y)
        = ((toPVes p).X / (toPVes p).Z, -(toPVes p).Y / (toPVes p).Z) := by
      rw [toAffine_coords (valid_pneg h), toPVes_pneg, aff, if_neg hz]
    apply CompElliptic.CurveForms.ShortWeierstrass.SWPoint.ext_pair
    rw [e1, CompElliptic.CurveForms.ShortWeierstrass.SWPoint.neg_x,
      CompElliptic.CurveForms.ShortWeierstrass.SWPoint.neg_y]
    rw [Prod.mk.injEq] at e2
    rw [e2.1, e2.2, neg_div]

end CompElliptic.Curves.Pasta.Fast.NatKernel
