/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs
import CompElliptic.Vendor.CompPoly.Montgomery.Pasta
import CompElliptic.Curves.Pasta.Fast.NatKernelEquiv

/-!
# The Montgomery kernel is the proven projective arithmetic

`CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs` is a zero-import transplant of the projective
Vesta arithmetic onto the eight-limb Montgomery representation of `𝔽_q`, so that it can sit in
the `FastFieldNative` `precompileModules` leaf (see the lakefile).  This module — which is
mathlib-side and therefore *not* in that lane — proves that the transplant computes the
statement-surface functions of `CompElliptic.Curves.Pasta.Fast.Projective`.

The bridge is the coordinatewise value map `montVal : Limbs8 → 𝔽_q`, `x ↦ x.toNat / 2 ^ 256`,
which is exactly `Montgomery.Native64x8.FastField.toField` read off a raw limb vector; it is
correct on **well-formed** residues (`WF x := x.Bounded ∧ x.toNat < q`), the carrier property of
the proven `FastField PALLAS_SCALAR_CARD`.  Every field operation of the kernel is the
corresponding `FastField` operation on the nose, so the per-operation cast lemmas
(`montVal_add`, `montVal_sub`, `montVal_neg`, `montVal_mul`) are the vendored field's
`toField_*` homomorphism lemmas, and `WF` preservation is the carrier proof that ships with each
operation.

## Main results

* `toPVesM_padd` — the kernel's RCB addition is `PVes.padd`
* `toPVesM_pid`, `toPVesM_pneg` — identity and negation
* `pnsmulM_spec` — the kernel's 256-step ladder is `n • ·` in the affine group, for `n < 2 ^ 256`
* `msmM_spec` — the kernel's windowed Pippenger MSM is `Fast.Msm.pippenger`

Because `ProjectiveMontDefs` was transcribed from `CompElliptic.Curves.Pasta.Fast.NatKernel`
**operation for operation**, the kernel-level results are obtained by *transporting along the
`Nat` kernel* rather than by redoing its group theory: `RM p n` says a Montgomery triple is
well-formed and denotes the same projective point as a `Nat` triple, `RM` is preserved by
`padd`/`pid`/`pneg`, and therefore — by structural induction over the shared schedules — by the
ladder and the scatter Pippenger.  The affine meaning then comes from `NatKernelEquiv`'s
`pnsmul_spec`/`msm_spec` verbatim.

The transport API itself (`RM`, `RM2`, `RA` and their closure lemmas, plus the fold combinators
`foldl_rel₂`/`foldr_rel₂`) is public rather than private, because the same induction is what a
downstream consumer needs to lift a *further* shared schedule — the kernels' radix-2 DIT FFT in
particular, whose reference group DFT CompElliptic does not have — to the Montgomery tier.
-/

namespace CompElliptic.Curves.Pasta.Fast.ProjectiveMont

open Montgomery.Native64x8
open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.Projective
open CompElliptic.Curves.Pasta.Fast.Projective.PVes
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)
open CompElliptic.Curves.Pasta.Fast.NatKernel (P3)

/-- The Vesta base field, the ambient field of the projective statement surface. -/
local notation "Fq" => CompElliptic.Curves.Pasta.Fast.Projective.Fq

/-! ## The field level

`WF` is the carrier property of `FastField PALLAS_SCALAR_CARD` and every `VestaFq` entry point is
the corresponding `FastField` operation on the nose (both sides reduce to the same
`Native64x8` call at the Vesta constants), so the whole field tier is `rfl`-transport into the
vendored proofs. -/

/-- A well-formed Montgomery residue: bounded limbs holding a value below `q`.  This is exactly
the carrier property of `Montgomery.Native64x8.FastField PALLAS_SCALAR_CARD`. -/
def WF (x : Limbs8) : Prop := x.Bounded ∧ x.toNat < PALLAS_SCALAR_CARD

/-- The field value of a Montgomery residue: the residue divided by the radix `R = 2 ^ 256`. -/
def montVal (x : Limbs8) : Fq := (x.toNat : Fq) * ((2 ^ 256 : ℕ) : Fq)⁻¹

/-- A well-formed residue, packaged as an element of the proven fast field. -/
private def toFF (x : Limbs8) (h : WF x) : FastField PALLAS_SCALAR_CARD := ⟨x, h⟩

theorem montVal_eq_toField {x : Limbs8} (h : WF x) :
    montVal x = FastField.toField (toFF x h) := by
  rw [montVal]
  exact (FastField.toField_eq (toFF x h)).symm

/-! ### Per-operation cast lemmas -/

theorem wf_add {a b : Limbs8} (ha : WF a) (hb : WF b) : WF (VestaFq.add a b) :=
  (FastField.add (toFF a ha) (toFF b hb)).property

theorem montVal_add {a b : Limbs8} (ha : WF a) (hb : WF b) :
    montVal (VestaFq.add a b) = montVal a + montVal b := by
  rw [montVal_eq_toField (wf_add ha hb), montVal_eq_toField ha, montVal_eq_toField hb]
  exact FastField.toField_add (toFF a ha) (toFF b hb)

theorem wf_sub {a b : Limbs8} (ha : WF a) (hb : WF b) : WF (VestaFq.sub a b) :=
  (FastField.sub (toFF a ha) (toFF b hb)).property

theorem montVal_sub {a b : Limbs8} (ha : WF a) (hb : WF b) :
    montVal (VestaFq.sub a b) = montVal a - montVal b := by
  rw [montVal_eq_toField (wf_sub ha hb), montVal_eq_toField ha, montVal_eq_toField hb]
  exact FastField.toField_sub (toFF a ha) (toFF b hb)

theorem wf_neg {a : Limbs8} (ha : WF a) : WF (VestaFq.neg a) :=
  (FastField.neg (toFF a ha)).property

theorem montVal_neg {a : Limbs8} (ha : WF a) : montVal (VestaFq.neg a) = -montVal a := by
  rw [montVal_eq_toField (wf_neg ha), montVal_eq_toField ha]
  exact FastField.toField_neg (toFF a ha)

theorem wf_mul {a b : Limbs8} (ha : WF a) (hb : WF b) : WF (VestaFq.mul a b) :=
  (FastField.mul (toFF a ha) (toFF b hb)).property

theorem montVal_mul {a b : Limbs8} (ha : WF a) (hb : WF b) :
    montVal (VestaFq.mul a b) = montVal a * montVal b := by
  rw [montVal_eq_toField (wf_mul ha hb), montVal_eq_toField ha, montVal_eq_toField hb]
  exact FastField.toField_mul (toFF a ha) (toFF b hb)

theorem wf_square {a : Limbs8} (ha : WF a) : WF (VestaFq.square a) := wf_mul ha ha

theorem montVal_square {a : Limbs8} (ha : WF a) :
    montVal (VestaFq.square a) = montVal a * montVal a := montVal_mul ha ha

theorem wf_zero : WF VestaFq.zero := (FastField.zero PALLAS_SCALAR_CARD).property

theorem montVal_zero : montVal VestaFq.zero = 0 := by
  rw [montVal_eq_toField wf_zero]
  exact FastField.toField_zero

theorem wf_one : WF VestaFq.one := (FastField.one PALLAS_SCALAR_CARD).property

theorem montVal_one : montVal VestaFq.one = 1 := by
  rw [montVal_eq_toField wf_one]
  exact FastField.toField_one

/-- **Entering Montgomery form is the canonical cast**, for canonical naturals.  This is
`FastField.ofCanonicalNat`'s correctness read off raw limbs. -/
theorem wf_ofNat {k : ℕ} (h : k < PALLAS_SCALAR_CARD) : WF (VestaFq.ofNat k) :=
  (FastField.ofCanonicalNat k h).property

theorem montVal_ofNat {k : ℕ} (h : k < PALLAS_SCALAR_CARD) :
    montVal (VestaFq.ofNat k) = (k : Fq) := by
  rw [montVal_eq_toField (wf_ofNat h)]
  exact FastField.toField_ofCanonicalNat h

/-! ### The RCB coefficients -/

theorem wf_c3 : WF PM.c3 := wf_ofNat (by decide)
theorem wf_c15 : WF PM.c15 := wf_ofNat (by decide)
theorem wf_c30 : WF PM.c30 := wf_ofNat (by decide)
theorem wf_c45 : WF PM.c45 := wf_ofNat (by decide)
theorem wf_c225 : WF PM.c225 := wf_ofNat (by decide)

theorem montVal_c3 : montVal PM.c3 = 3 := by
  rw [show PM.c3 = VestaFq.ofNat 3 from rfl, montVal_ofNat (by decide)]; norm_num

theorem montVal_c15 : montVal PM.c15 = 15 := by
  rw [show PM.c15 = VestaFq.ofNat 15 from rfl, montVal_ofNat (by decide)]; norm_num

theorem montVal_c30 : montVal PM.c30 = 30 := by
  rw [show PM.c30 = VestaFq.ofNat 30 from rfl, montVal_ofNat (by decide)]; norm_num

theorem montVal_c45 : montVal PM.c45 = 45 := by
  rw [show PM.c45 = VestaFq.ofNat 45 from rfl, montVal_ofNat (by decide)]; norm_num

theorem montVal_c225 : montVal PM.c225 = 225 := by
  rw [show PM.c225 = VestaFq.ofNat 225 from rfl, montVal_ofNat (by decide)]; norm_num

/-! ## The point level -/

/-- Coordinatewise interpretation of a Montgomery triple as a projective point over `𝔽_q`. -/
def toPVesM (p : PM) : PVes := ⟨montVal p.X, montVal p.Y, montVal p.Z⟩

/-- All three coordinates are well-formed Montgomery residues. -/
def WFP (p : PM) : Prop := WF p.X ∧ WF p.Y ∧ WF p.Z

/-- The affine reading of a Montgomery triple. -/
def toGM (p : PM) : G := toAffine (toPVesM p)

@[simp] theorem toPVesM_X (p : PM) : (toPVesM p).X = montVal p.X := rfl
@[simp] theorem toPVesM_Y (p : PM) : (toPVesM p).Y = montVal p.Y := rfl
@[simp] theorem toPVesM_Z (p : PM) : (toPVesM p).Z = montVal p.Z := rfl

theorem wfp_pid : WFP PM.pid := ⟨wf_zero, wf_one, wf_zero⟩

theorem wfp_pneg {p : PM} (h : WFP p) : WFP (PM.pneg p) :=
  ⟨h.1, wf_sub wf_zero h.2.1, h.2.2⟩

set_option maxRecDepth 8000 in
/-- **Well-formedness is closed under the kernel's RCB addition.**  Every node of the
coordinate expressions is one of the four field entry points, each of which ships its own
carrier proof.  The closure search runs `with_reducible`, so a candidate rule is rejected on
the head symbol instead of unfolding the CIOS rounds underneath it. -/
theorem wfp_padd {p r : PM} (hp : WFP p) (hr : WFP r) : WFP (PM.padd p r) := by
  obtain ⟨hpx, hpy, hpz⟩ := hp
  obtain ⟨hrx, hry, hrz⟩ := hr
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [PM.padd]
    repeat' first
      | (with_reducible assumption)
      | (with_reducible exact wf_c3)
      | (with_reducible exact wf_c15)
      | (with_reducible exact wf_c30)
      | (with_reducible exact wf_c45)
      | (with_reducible exact wf_c225)
      | (with_reducible apply wf_square)
      | (with_reducible apply wf_mul)
      | (with_reducible apply wf_add)
      | (with_reducible apply wf_sub)

set_option maxRecDepth 8000 in
/-- **The kernel's addition is the projective addition.**  Same Renes–Costello–Batina closed
forms, evaluated on Montgomery residues with the vendored field's operations. -/
theorem toPVesM_padd {p r : PM} (hp : WFP p) (hr : WFP r) :
    toPVesM (PM.padd p r) = PVes.padd (toPVesM p) (toPVesM r) := by
  obtain ⟨hpx, hpy, hpz⟩ := hp
  obtain ⟨hrx, hry, hrz⟩ := hr
  simp only [toPVesM, PM.padd, PVes.padd, PVes.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp (maxDischargeDepth := 16) only [montVal_add, montVal_sub, montVal_mul, montVal_square,
      montVal_c3, montVal_c15, montVal_c30, montVal_c45, montVal_c225,
      wf_add, wf_sub, wf_mul, wf_square, wf_c3, wf_c15, wf_c30, wf_c45, wf_c225,
      hpx, hpy, hpz, hrx, hry, hrz] <;>
    ring

@[simp] theorem toPVesM_pid : toPVesM PM.pid = PVes.pid := by
  simp only [toPVesM, PM.pid, PVes.pid, PVes.mk.injEq]
  exact ⟨montVal_zero, montVal_one, montVal_zero⟩

/-- **The kernel's negation is coordinate negation of `Y`**, the short-Weierstrass inverse. -/
theorem toPVesM_pneg {p : PM} (h : WFP p) :
    toPVesM (PM.pneg p) = ⟨(toPVesM p).X, -(toPVesM p).Y, (toPVesM p).Z⟩ := by
  have hy : montVal (VestaFq.sub VestaFq.zero p.Y) = -montVal p.Y := by
    rw [montVal_sub wf_zero h.2.1, montVal_zero, zero_sub]
  simp only [toPVesM, PM.pneg, hy]

/-! ## Transport to the `Nat` kernel

`ProjectiveMontDefs` mirrors `CompElliptic.Curves.Pasta.Fast.NatKernel` operation for operation,
so the group kernels are transported wholesale: `RM p n` relates a well-formed Montgomery triple
to the `Nat` triple denoting the same projective point, and the shared schedules preserve it. -/

/-- The canonical `Nat`-kernel triple denoting the same projective point. -/
def ofPM (p : PM) : P3 :=
  ⟨(montVal p.X).val, (montVal p.Y).val, (montVal p.Z).val⟩

theorem toPVes_ofPM (p : PM) : NatKernel.toPVes (ofPM p) = toPVesM p := by
  simp only [NatKernel.toPVes, ofPM, toPVesM, PVes.mk.injEq]
  exact ⟨ZMod.natCast_rightInverse _, ZMod.natCast_rightInverse _, ZMod.natCast_rightInverse _⟩

/-- The kernel correspondence: a well-formed Montgomery triple denoting the same projective
point as a `Nat` triple. -/
def RM (p : PM) (n : P3) : Prop := WFP p ∧ toPVesM p = NatKernel.toPVes n

/-- The correspondence on ladder/downsweep state pairs. -/
def RM2 (s : PM × PM) (s' : P3 × P3) : Prop := RM s.1 s'.1 ∧ RM s.2 s'.2

theorem RM_self {p : PM} (h : WFP p) : RM p (ofPM p) := ⟨h, (toPVes_ofPM p).symm⟩

theorem RM_toG {p : PM} {n : P3} (h : RM p n) : toGM p = NatKernel.toG n := by
  rw [toGM, NatKernel.toG, h.2]

theorem RM_padd {p r : PM} {n m : P3} (hp : RM p n) (hr : RM r m) :
    RM (PM.padd p r) (NatKernel.padd n m) := by
  refine ⟨wfp_padd hp.1 hr.1, ?_⟩
  rw [toPVesM_padd hp.1 hr.1, NatKernel.toPVes_padd, hp.2, hr.2]

theorem RM_pid : RM PM.pid NatKernel.pid :=
  ⟨wfp_pid, by rw [toPVesM_pid, NatKernel.toPVes_pid]⟩

theorem RM_pneg {p : PM} {n : P3} (h : RM p n) :
    RM (PM.pneg p) (NatKernel.pneg n) := by
  refine ⟨wfp_pneg h.1, ?_⟩
  rw [toPVesM_pneg h.1, NatKernel.toPVes_pneg, h.2]

/-! ### Relation-preserving folds -/

/-- A relation-preserving `foldl` whose step may use a property of the list elements. -/
theorem foldl_rel₂ {σ σ' β : Type} (R : σ → σ' → Prop) (P : β → Prop) :
    ∀ (l : List β) (f : σ → β → σ) (g : σ' → β → σ'),
      (∀ s s' x, P x → R s s' → R (f s x) (g s' x)) → (∀ x ∈ l, P x) →
      ∀ s s', R s s' → R (l.foldl f s) (l.foldl g s') := by
  intro l
  induction l with
  | nil => intro _ _ _ _ s s' h; exact h
  | cons x l ih =>
    intro f g hstep hP s s' h
    exact ih f g hstep (fun y hy => hP y (by simp [hy])) _ _
      (hstep s s' x (hP x (by simp)) h)

/-- A relation-preserving `foldr` whose step may use a property of the list elements. -/
theorem foldr_rel₂ {σ σ' β : Type} (R : σ → σ' → Prop) (P : β → Prop) :
    ∀ (l : List β) (f : β → σ → σ) (g : β → σ' → σ'),
      (∀ x s s', P x → R s s' → R (f x s) (g x s')) → (∀ x ∈ l, P x) →
      ∀ s s', R s s' → R (l.foldr f s) (l.foldr g s') := by
  intro l
  induction l with
  | nil => intro _ _ _ _ s s' h; exact h
  | cons x l ih =>
    intro f g hstep hP s s' h
    exact hstep x _ _ (hP x (by simp))
      (ih f g hstep (fun y hy => hP y (by simp [hy])) s s' h)

/-! ### The scalar ladder -/

theorem RM_pnsmul (k : ℕ) {p : PM} {n : P3} (h : RM p n) :
    RM (PM.pnsmul k p) (NatKernel.pnsmul k n) := by
  have key : RM2
      ((List.range 256).foldl (fun (st : PM × PM) i =>
        (if (k >>> i) &&& 1 = 1 then PM.padd st.1 st.2 else st.1, PM.padd st.2 st.2))
        (PM.pid, p))
      ((List.range 256).foldl (fun (st : P3 × P3) i =>
        (if (k >>> i) &&& 1 = 1 then NatKernel.padd st.1 st.2 else st.1,
          NatKernel.padd st.2 st.2))
        (NatKernel.pid, n)) := by
    refine foldl_rel₂ RM2 (fun _ : ℕ => True) (List.range 256) _ _ ?_ (fun _ _ => trivial) _ _
      ⟨RM_pid, h⟩
    intro s s' i _ hs
    refine ⟨?_, RM_padd hs.2 hs.2⟩
    by_cases hc : (k >>> i) &&& 1 = 1
    · rw [if_pos hc, if_pos hc]; exact RM_padd hs.1 hs.2
    · rw [if_neg hc, if_neg hc]; exact hs.1
  exact key.1

/-- **The kernel ladder computes `n • ·`** in the affine group, for scalars below `2 ^ 256`
(all Pasta scalars).  Statement shape mirrors `NatKernel.pnsmul_spec`. -/
theorem pnsmulM_spec {p : PM} (hwf : WFP p) (hp : Valid (toPVesM p)) (n : ℕ) (hn : n < 2 ^ 256) :
    WFP (PM.pnsmul n p) ∧ Valid (toPVesM (PM.pnsmul n p)) ∧
      toAffine (toPVesM (PM.pnsmul n p)) = n • toAffine (toPVesM p) := by
  have hR := RM_pnsmul n (RM_self hwf)
  have hv : Valid (NatKernel.toPVes (ofPM p)) := by rw [toPVes_ofPM]; exact hp
  obtain ⟨hvalid, heq⟩ := NatKernel.pnsmul_spec hv n hn
  refine ⟨hR.1, ?_, ?_⟩
  · rw [hR.2]; exact hvalid
  · rw [hR.2, heq, toPVes_ofPM]

/-! ### Arrays of kernel points -/

private theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i] := by
  intro l₁ l₂ h
  induction h with
  | nil => intro i h₁ _; simp at h₁
  | cons hab _ ih =>
    intro i h₁ h₂
    cases i with
    | zero => exact hab
    | succ k => exact ih k (by simpa using h₁) (by simpa using h₂)

private theorem forall₂_set {α β : Type} {R : α → β → Prop} {x : α} {y : β} (hxy : R x y) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ i, List.Forall₂ R (l₁.set i x) (l₂.set i y) := by
  intro l₁ l₂ h
  induction h with
  | nil => intro i; cases i <;> exact List.Forall₂.nil
  | cons hab hl ih =>
    intro i
    cases i with
    | zero => exact List.Forall₂.cons hxy hl
    | succ k => exact List.Forall₂.cons hab (ih k)

private theorem forall₂_modify {α β : Type} {R : α → β → Prop} {f : α → α} {g : β → β}
    (hfg : ∀ a b, R a b → R (f a) (g b)) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ i, List.Forall₂ R (l₁.modify i f) (l₂.modify i g) := by
  intro l₁ l₂ h
  induction h with
  | nil => intro i; cases i <;> exact List.Forall₂.nil
  | cons hab hl ih =>
    intro i
    cases i with
    | zero => exact List.Forall₂.cons (hfg _ _ hab) hl
    | succ k => exact List.Forall₂.cons hab (ih k)

private theorem forall₂_replicate {α β : Type} {R : α → β → Prop} {x : α} {y : β} (h : R x y) :
    ∀ n, List.Forall₂ R (List.replicate n x) (List.replicate n y)
  | 0 => List.Forall₂.nil
  | n + 1 => List.Forall₂.cons h (forall₂_replicate h n)

private theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.map f = l₂.map g := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, List.map_cons, hfg _ _ hab, ih]

private theorem forall₂_map_self {α β : Type} {R : α → β → Prop} {P : α → Prop} {f : α → β}
    (hf : ∀ a, P a → R a (f a)) :
    ∀ (l : List α), (∀ a ∈ l, P a) → List.Forall₂ R l (l.map f)
  | [], _ => List.Forall₂.nil
  | a :: l, h =>
    List.Forall₂.cons (hf a (h a (by simp)))
      (forall₂_map_self hf l fun b hb => h b (by simp [hb]))

/-- The array-level correspondence: cellwise `RM`. -/
def RA (a : Array PM) (b : Array P3) : Prop := List.Forall₂ RM a.toList b.toList

theorem RA.size {a : Array PM} {b : Array P3} (h : RA a b) : a.size = b.size := by
  have := List.Forall₂.length_eq h
  rwa [Array.length_toList, Array.length_toList] at this

theorem RA.get {a : Array PM} {b : Array P3} (h : RA a b) (k : ℕ) : RM a[k]! b[k]! := by
  by_cases hk : k < a.size
  · have hk' : k < b.size := h.size ▸ hk
    rw [getElem!_pos a k hk, getElem!_pos b k hk']
    have := forall₂_getElem h k (by rwa [Array.length_toList]) (by rwa [Array.length_toList])
    rwa [Array.getElem_toList, Array.getElem_toList] at this
  · have hk' : ¬ k < b.size := by rw [← h.size]; exact hk
    rw [getElem!_neg a k hk, getElem!_neg b k hk']
    exact RM_pid

theorem RA.set {a : Array PM} {b : Array P3} (h : RA a b) (k : ℕ) {p : PM} {n : P3}
    (hp : RM p n) : RA (a.set! k p) (b.set! k n) := by
  simp only [RA, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  exact forall₂_set hp h k

theorem RA.modify {a : Array PM} {b : Array P3} (h : RA a b) (k : ℕ)
    {f : PM → PM} {g : P3 → P3} (hfg : ∀ p n, RM p n → RM (f p) (g n)) :
    RA (a.modify k f) (b.modify k g) := by
  simp only [RA, Array.toList_modify]
  exact forall₂_modify hfg h k

theorem RA.map_toG {a : Array PM} {b : Array P3} (h : RA a b) :
    a.map toGM = b.map NatKernel.toG := by
  have := forall₂_map_eq (f := toGM) (g := NatKernel.toG) (fun _ _ hr => RM_toG hr) h
  rw [← Array.toList_map, ← Array.toList_map] at this
  exact Array.toList_inj.mp this

theorem RA_self {a : Array PM} (h : ∀ p ∈ a, WFP p) : RA a (a.map ofPM) := by
  simp only [RA, Array.toList_map]
  exact forall₂_map_self (P := WFP) (fun p hp => RM_self hp) a.toList
    (fun p hp => h p (by simpa using hp))

/-! ### The windowed Pippenger MSM -/

private theorem RA_scatterStep {a : Array PM} {b : Array P3} (h : RA a b) {t : ℕ × PM}
    (ht : WFP t.2) : RA (PM.scatterStep a t) (NatKernel.scatterStep b (t.1, ofPM t.2)) := by
  simp only [PM.scatterStep, NatKernel.scatterStep]
  by_cases h0 : t.1 = 0
  · rw [if_pos h0, if_pos h0]
    exact h
  · rw [if_neg h0, if_neg h0]
    exact h.modify _ (fun _ _ hpn => RM_padd hpn (RM_self ht))

private theorem RA_bucketScatter (base : ℕ) (dp : List (ℕ × PM)) (h : ∀ t ∈ dp, WFP t.2) :
    RA (PM.bucketScatter base dp)
      (NatKernel.bucketScatter base (dp.map fun t => (t.1, ofPM t.2))) := by
  simp only [PM.bucketScatter, NatKernel.bucketScatter, List.foldl_map]
  refine foldl_rel₂ RA (fun t : ℕ × PM => WFP t.2) dp _ _
    (fun s s' x hx hs => RA_scatterStep (t := x) hs hx) h _ _ ?_
  simp only [RA, Array.toList_replicate]
  exact forall₂_replicate RM_pid _

private theorem RM2_foldr_accStep :
    ∀ {L : List PM} {L' : List P3}, List.Forall₂ RM L L' →
      RM2 (L.foldr PM.accStep (PM.pid, PM.pid))
        (L'.foldr NatKernel.accStep (NatKernel.pid, NatKernel.pid)) := by
  intro L L' h
  induction h with
  | nil => exact ⟨RM_pid, RM_pid⟩
  | cons hab _ ih =>
    simp only [List.foldr_cons, PM.accStep, NatKernel.accStep]
    exact ⟨RM_padd ih.1 hab, RM_padd ih.2 (RM_padd ih.1 hab)⟩

private theorem RM_windowValue (base i : ℕ) (terms : List (ℕ × PM))
    (h : ∀ t ∈ terms, WFP t.2) :
    RM (PM.windowValue base i terms)
      (NatKernel.windowValue base i (terms.map fun t => (t.1, ofPM t.2))) := by
  have hdp : ∀ t ∈ terms.map (fun t : ℕ × PM => (t.1 / base ^ i % base, t.2)), WFP t.2 := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact h s hs
  have hb := RA_bucketScatter base (terms.map fun t : ℕ × PM => (t.1 / base ^ i % base, t.2)) hdp
  have halign : (terms.map fun t : ℕ × PM => (t.1 / base ^ i % base, t.2)).map
        (fun t : ℕ × PM => (t.1, ofPM t.2))
      = (terms.map fun t : ℕ × PM => (t.1, ofPM t.2)).map
        (fun t : ℕ × P3 => (t.1 / base ^ i % base, t.2)) := by
    simp only [List.map_map, Function.comp_def]
  rw [halign] at hb
  exact (RM2_foldr_accStep hb).2

private theorem RM_pdoublings (c : ℕ) {p : PM} {n : P3} (h : RM p n) :
    RM (PM.pdoublings c p) (NatKernel.pdoublings c n) := by
  simp only [PM.pdoublings, NatKernel.pdoublings]
  exact foldl_rel₂ RM (fun _ : ℕ => True) (List.range c) _ _
    (fun _ _ _ _ hs => RM_padd hs hs) (fun _ _ => trivial) _ _ h

private theorem RM_msm (c : ℕ) (terms : List (ℕ × PM)) (h : ∀ t ∈ terms, WFP t.2) :
    RM (PM.msm c terms) (NatKernel.msm c (terms.map fun t => (t.1, ofPM t.2))) := by
  simp only [PM.msm, NatKernel.msm, List.foldr_map]
  exact foldr_rel₂ RM (fun _ : ℕ => True) (List.range ((256 + c - 1) / c)) _ _
    (fun i _ _ _ hs => RM_padd (RM_pdoublings c hs) (RM_windowValue (2 ^ c) i terms h))
    (fun _ _ => trivial) _ _ RM_pid

/-- **The kernel's windowed Pippenger MSM is the proven affine Pippenger.**  Statement shape
mirrors `NatKernel.msm_spec`. -/
theorem msmM_spec (c : ℕ) (hc : 0 < c) (terms : List (ℕ × PM))
    (hwf : ∀ t ∈ terms, WFP t.2) (hv : ∀ t ∈ terms, Valid (toPVesM t.2))
    (hn : ∀ t ∈ terms, t.1 < 2 ^ 256) :
    toAffine (toPVesM (PM.msm c terms))
      = Msm.pippenger c (terms.map fun t => (t.1, toAffine (toPVesM t.2))) := by
  have hR := RM_msm c terms hwf
  have hv' : ∀ t ∈ terms.map (fun t : ℕ × PM => (t.1, ofPM t.2)),
      Valid (NatKernel.toPVes t.2) := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [toPVes_ofPM]
    exact hv s hs
  have hn' : ∀ t ∈ terms.map (fun t : ℕ × PM => (t.1, ofPM t.2)), t.1 < 2 ^ 256 := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact hn s hs
  rw [hR.2, NatKernel.msm_spec c hc _ hv' hn', List.map_map]
  refine congrArg (Msm.pippenger c) (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, toPVes_ofPM]
end CompElliptic.Curves.Pasta.Fast.ProjectiveMont
