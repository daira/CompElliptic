/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Gregor Mitscha-Baude
-/
import CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs
import CompElliptic.Vendor.CompPoly.Montgomery.Pasta
import CompElliptic.Curves.Pasta.Fast.MsmProj

/-!
# The Montgomery kernel is the proven projective arithmetic

`CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs` transcribes the projective Vesta arithmetic
onto eight-limb Montgomery residues; this module proves that the transcription computes the
statement-surface functions of `Projective.lean` / `MsmProj.lean`.  There are two tiers, not
three: the bridge is the coordinatewise `montVal`, which is the vendored field's ring isomorphism
`FastField.toField` read off raw limbs, correct on well-formed residues (`WF`).

`toPVesM_padd` is the one commuting square of substance — the ~40 field operations of the
Renes–Costello–Batina formulas pushed through the ring homomorphism.  Above it everything is
structural: the schedules mirror `MsmProj`'s, so they transport along
`RM p P := WFP p ∧ toPVesM p = P` (and, where the group law is needed, along `toGM`).

## Main results

* `toPVesM_padd`, `toPVesM_pid`, `toPVesM_pneg` — addition, identity and negation
* `pnsmulM_spec` — the 256-step ladder is `n • ·` in the affine group, for `n < 2 ^ 256`
* `msmM_spec` — the windowed Pippenger MSM is `Fast.Msm.pippenger`

`RM`, `RM2`, `RA` and the fold combinators are public rather than private: lifting a *further*
shared schedule to the Montgomery tier needs the same inductions.
-/

namespace CompElliptic.Curves.Pasta.Fast.ProjectiveMont

open Montgomery.Native64x8
open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.Projective
open CompElliptic.Curves.Pasta.Fast.Projective.PVes
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-- The Vesta base field, the ambient field of the projective statement surface. -/
local notation "Fq" => CompElliptic.Curves.Pasta.Fast.Projective.Fq

/-! ## The field level

Every `VestaFq` entry point is the corresponding `FastField` operation on the nose, so the whole
field tier is `rfl`-transport into the vendored proofs. -/

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

/-! ### The affine reading

`WV` bundles the two invariants every group schedule carries; under it the kernel's `padd` is the
affine group addition, which is all the ladder and the Horner recombination need. -/

/-- A well-formed Montgomery triple denoting a representable projective point. -/
def WV (p : PM) : Prop := WFP p ∧ Valid (toPVesM p)

theorem WV_pid : WV PM.pid := ⟨wfp_pid, by rw [toPVesM_pid]; exact valid_pid⟩

theorem WV_padd {p r : PM} (hp : WV p) (hr : WV r) : WV (PM.padd p r) :=
  ⟨wfp_padd hp.1 hr.1, by rw [toPVesM_padd hp.1 hr.1]; exact valid_padd hp.2 hr.2⟩

@[simp] theorem toGM_pid : toGM PM.pid = 0 := by rw [toGM, toPVesM_pid, toAffine_pid]

/-- **The kernel's addition is the affine group addition** on representable points. -/
theorem toGM_padd {p r : PM} (hp : WV p) (hr : WV r) :
    toGM (PM.padd p r) = toGM p + toGM r := by
  simp only [toGM]
  rw [toPVesM_padd hp.1 hr.1, toAffine_padd hp.2 hr.2]

/-! ## The correspondence with the projective statement surface

`RM p P` says a Montgomery triple is well formed and denotes the projective point `P`; every
shared schedule preserves it. -/

/-- The kernel correspondence: a well-formed Montgomery triple denoting a given projective
point. -/
def RM (p : PM) (P : PVes) : Prop := WFP p ∧ toPVesM p = P

/-- The correspondence on ladder/downsweep state pairs. -/
def RM2 (s : PM × PM) (s' : PVes × PVes) : Prop := RM s.1 s'.1 ∧ RM s.2 s'.2

theorem RM_self {p : PM} (h : WFP p) : RM p (toPVesM p) := ⟨h, rfl⟩

theorem RM_toG {p : PM} {P : PVes} (h : RM p P) : toGM p = toAffine P := by rw [toGM, h.2]

/-- A corresponding pair inherits representability from the projective side. -/
theorem RM_valid {p : PM} {P : PVes} (h : RM p P) (hv : Valid P) : WV p :=
  ⟨h.1, by rw [h.2]; exact hv⟩

theorem RM_padd {p r : PM} {P Q : PVes} (hp : RM p P) (hr : RM r Q) :
    RM (PM.padd p r) (PVes.padd P Q) := by
  refine ⟨wfp_padd hp.1 hr.1, ?_⟩
  rw [toPVesM_padd hp.1 hr.1, hp.2, hr.2]

theorem RM_pid : RM PM.pid PVes.pid := ⟨wfp_pid, toPVesM_pid⟩

theorem RM_pneg {p : PM} {P : PVes} (h : RM p P) :
    RM (PM.pneg p) ⟨P.X, -P.Y, P.Z⟩ := by
  refine ⟨wfp_pneg h.1, ?_⟩
  rw [toPVesM_pneg h.1, h.2]

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

/-! ## The scalar ladder

`PM.pnsmul` is LSB-first, unlike the statement-surface `pnsmulFast`, so it is proved where the
group law lives: through `toGM`, carrying the standard accumulator invariant. -/

/-- The ladder state after `i` steps: the accumulator holds `(n mod 2 ^ i) • A` and the base holds
`2 ^ i • A`, both well formed and representable. -/
private def LadderInvM (A : G) (n i : ℕ) (st : PM × PM) : Prop :=
  WV st.1 ∧ WV st.2 ∧ toGM st.1 = (n % 2 ^ i) • A ∧ toGM st.2 = (2 ^ i : ℕ) • A

private theorem ladderM_step {A : G} {n i : ℕ} {st : PM × PM} (h : LadderInvM A n i st) :
    LadderInvM A n (i + 1)
      ((if (n >>> i) &&& 1 = 1 then PM.padd st.1 st.2 else st.1), PM.padd st.2 st.2) := by
  obtain ⟨hv1, hv2, ha1, ha2⟩ := h
  have hbit : (n >>> i) &&& 1 = n / 2 ^ i % 2 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have hmod : n % 2 ^ (i + 1) = n % 2 ^ i + 2 ^ i * (n / 2 ^ i % 2) := by
    rw [pow_succ, Nat.mod_mul]
  have hdouble : toGM (PM.padd st.2 st.2) = (2 ^ (i + 1) : ℕ) • A := by
    rw [toGM_padd hv2 hv2, ha2, ← two_nsmul, smul_smul, pow_succ]
    ring_nf
  refine ⟨?_, WV_padd hv2 hv2, ?_, hdouble⟩
  · split
    · exact WV_padd hv1 hv2
    · exact hv1
  · split
    · rename_i hodd
      rw [hbit] at hodd
      rw [toGM_padd hv1 hv2, ha1, ha2, ← add_nsmul, hmod, hodd, Nat.mul_one]
    · rename_i heven
      rw [hbit] at heven
      have h0 : n / 2 ^ i % 2 = 0 := by omega
      rw [ha1, hmod, h0, Nat.mul_zero, Nat.add_zero]

/-- **The kernel ladder computes `n • ·`** in the affine group, for scalars below `2 ^ 256`
(all Pasta scalars).  Statement shape mirrors `PVes.pnsmulFast_spec`. -/
theorem pnsmulM_spec {p : PM} (hwf : WFP p) (hp : Valid (toPVesM p)) (n : ℕ) (hn : n < 2 ^ 256) :
    WFP (PM.pnsmul n p) ∧ Valid (toPVesM (PM.pnsmul n p)) ∧
      toAffine (toPVesM (PM.pnsmul n p)) = n • toAffine (toPVesM p) := by
  have base : ∀ m : ℕ, m ≤ 256 →
      LadderInvM (toGM p) n m ((List.range m).foldl
        (fun (st : PM × PM) i =>
          (if (n >>> i) &&& 1 = 1 then PM.padd st.1 st.2 else st.1, PM.padd st.2 st.2))
        (PM.pid, p)) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp only [List.range_zero, List.foldl_nil]
        refine ⟨WV_pid, ⟨hwf, hp⟩, ?_, ?_⟩
        · rw [toGM_pid, pow_zero, Nat.mod_one, zero_nsmul]
        · rw [pow_zero, one_nsmul]
    | succ k ih =>
        intro hk
        rw [List.range_succ, List.foldl_append]
        exact ladderM_step (ih (by omega))
  obtain ⟨⟨hw, hv⟩, -, hval, -⟩ := base 256 le_rfl
  rw [Nat.mod_eq_of_lt hn] at hval
  exact ⟨hw, hv, hval⟩

/-! ## Arrays of kernel points -/

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

/-- `Array.get!`/`set!` need a default on the `PVes` side as well as on `PM`'s; the projective
identity is the right one on both, so an out-of-range read stays a corresponding pair. -/
instance : Inhabited PVes := ⟨PVes.pid⟩

/-- The array-level correspondence: cellwise `RM`. -/
def RA (a : Array PM) (b : Array PVes) : Prop := List.Forall₂ RM a.toList b.toList

theorem RA.size {a : Array PM} {b : Array PVes} (h : RA a b) : a.size = b.size := by
  have := List.Forall₂.length_eq h
  rwa [Array.length_toList, Array.length_toList] at this

theorem RA.get {a : Array PM} {b : Array PVes} (h : RA a b) (k : ℕ) : RM a[k]! b[k]! := by
  by_cases hk : k < a.size
  · have hk' : k < b.size := h.size ▸ hk
    rw [getElem!_pos a k hk, getElem!_pos b k hk']
    have := forall₂_getElem h k (by rwa [Array.length_toList]) (by rwa [Array.length_toList])
    rwa [Array.getElem_toList, Array.getElem_toList] at this
  · have hk' : ¬ k < b.size := by rw [← h.size]; exact hk
    rw [getElem!_neg a k hk, getElem!_neg b k hk']
    exact RM_pid

theorem RA.set {a : Array PM} {b : Array PVes} (h : RA a b) (k : ℕ) {p : PM} {P : PVes}
    (hp : RM p P) : RA (a.set! k p) (b.set! k P) := by
  simp only [RA, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  exact forall₂_set hp h k

theorem RA.modify {a : Array PM} {b : Array PVes} (h : RA a b) (k : ℕ)
    {f : PM → PM} {g : PVes → PVes} (hfg : ∀ p P, RM p P → RM (f p) (g P)) :
    RA (a.modify k f) (b.modify k g) := by
  simp only [RA, Array.toList_modify]
  exact forall₂_modify hfg h k

theorem RA.map_toG {a : Array PM} {b : Array PVes} (h : RA a b) :
    a.map toGM = b.map toAffine := by
  have := forall₂_map_eq (f := toGM) (g := toAffine) (fun _ _ hr => RM_toG hr) h
  rw [← Array.toList_map, ← Array.toList_map] at this
  exact Array.toList_inj.mp this

theorem RA_self {a : Array PM} (h : ∀ p ∈ a, WFP p) : RA a (a.map toPVesM) := by
  simp only [RA, Array.toList_map]
  exact forall₂_map_self (P := WFP) (fun p hp => RM_self hp) a.toList
    (fun p hp => h p (by simpa using hp))

/-! ## The windowed Pippenger MSM

Window values transport by `RM` onto `MsmProj.pwindowValueFast` and get their affine meaning from
its spec.  The Horner recombination is the one part that does not mirror `MsmProj` (`c` doublings
instead of `pnsmulFast (2 ^ c)`), so it goes through `toGM` directly, and
`hornerList_windows_eq_msm` reconciles the kernel's fixed `⌈256 / c⌉` windows with
`Msm.numWindows`. -/

private theorem RA_scatterStep {a : Array PM} {b : Array PVes} (h : RA a b) {t : ℕ × PM}
    (ht : WFP t.2) :
    RA (PM.scatterStep a t) (MsmProj.pscatterStep b (t.1, toPVesM t.2)) := by
  simp only [PM.scatterStep, MsmProj.pscatterStep]
  by_cases h0 : t.1 = 0
  · rw [if_pos h0, if_pos h0]
    exact h
  · rw [if_neg h0, if_neg h0]
    exact h.modify _ (fun _ _ hpn => RM_padd hpn (RM_self ht))

private theorem RA_bucketScatter (base : ℕ) (dp : List (ℕ × PM)) (h : ∀ t ∈ dp, WFP t.2) :
    RA (PM.bucketScatter base dp)
      (MsmProj.pbucketScatter base (dp.map fun t => (t.1, toPVesM t.2))) := by
  simp only [PM.bucketScatter, MsmProj.pbucketScatter, List.foldl_map]
  refine foldl_rel₂ RA (fun t : ℕ × PM => WFP t.2) dp _ _
    (fun s s' x hx hs => RA_scatterStep (t := x) hs hx) h _ _ ?_
  simp only [RA, Array.toList_replicate]
  exact forall₂_replicate RM_pid _

private theorem RM2_foldr_accStep :
    ∀ {L : List PM} {L' : List PVes}, List.Forall₂ RM L L' →
      RM2 (L.foldr PM.accStep (PM.pid, PM.pid))
        (L'.foldr MsmProj.paccStep (PVes.pid, PVes.pid)) := by
  intro L L' h
  induction h with
  | nil => exact ⟨RM_pid, RM_pid⟩
  | cons hab _ ih =>
    simp only [List.foldr_cons, PM.accStep, MsmProj.paccStep]
    exact ⟨RM_padd ih.1 hab, RM_padd ih.2 (RM_padd ih.1 hab)⟩

private theorem RM_windowValue (base i : ℕ) (terms : List (ℕ × PM))
    (h : ∀ t ∈ terms, WFP t.2) :
    RM (PM.windowValue base i terms)
      (MsmProj.pwindowValueFast base i (terms.map fun t => (t.1, toPVesM t.2))) := by
  have hdp : ∀ t ∈ terms.map (fun t : ℕ × PM => (t.1 / base ^ i % base, t.2)), WFP t.2 := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact h s hs
  have hb := RA_bucketScatter base (terms.map fun t : ℕ × PM => (t.1 / base ^ i % base, t.2)) hdp
  have halign : (terms.map fun t : ℕ × PM => (t.1 / base ^ i % base, t.2)).map
        (fun t : ℕ × PM => (t.1, toPVesM t.2))
      = MsmProj.pdpOf base i (terms.map fun t : ℕ × PM => (t.1, toPVesM t.2)) := by
    simp only [MsmProj.pdpOf, Msm.digit, List.map_map, Function.comp_def]
  rw [halign] at hb
  exact (RM2_foldr_accStep hb).2

/-- The `c`-fold doubling is `2 ^ c • ·` in the affine group. -/
private theorem pdoublingsM_spec {p : PM} (hp : WV p) (c : ℕ) :
    WV (PM.pdoublings c p) ∧ toGM (PM.pdoublings c p) = (2 ^ c : ℕ) • toGM p := by
  induction c with
  | zero =>
    rw [show PM.pdoublings 0 p = p from rfl]
    exact ⟨hp, by rw [pow_zero, one_nsmul]⟩
  | succ k ih =>
    obtain ⟨hv, he⟩ := ih
    have hstep : PM.pdoublings (k + 1) p = PM.padd (PM.pdoublings k p) (PM.pdoublings k p) := by
      rw [PM.pdoublings, List.range_succ, List.foldl_append]; rfl
    rw [hstep]
    refine ⟨WV_padd hv hv, ?_⟩
    rw [toGM_padd hv hv, he, ← two_nsmul, smul_smul, pow_succ]
    ring_nf

/-- The kernel's Horner recombination across windows is `Msm.hornerList` after `toGM`. -/
private theorem hfoldM_spec (c : ℕ) (vals : List PM) (h : ∀ v ∈ vals, WV v) :
    WV (vals.foldr (fun v acc => PM.padd (PM.pdoublings c acc) v) PM.pid) ∧
      toGM (vals.foldr (fun v acc => PM.padd (PM.pdoublings c acc) v) PM.pid)
        = Msm.hornerList (2 ^ c) (vals.map toGM) := by
  induction vals with
  | nil =>
    refine ⟨by rw [List.foldr_nil]; exact WV_pid, ?_⟩
    rw [List.foldr_nil, toGM_pid, List.map_nil, Msm.hornerList, List.foldr_nil]
  | cons v xs ih =>
    have hv : WV v := h v (by simp)
    obtain ⟨hacc, heq⟩ := ih fun w hw => h w (by simp [hw])
    obtain ⟨hdv, hde⟩ := pdoublingsM_spec hacc c
    rw [List.foldr_cons]
    refine ⟨WV_padd hdv hv, ?_⟩
    rw [toGM_padd hdv hv, hde, heq, List.map_cons]
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

/-- **The kernel's windowed Pippenger MSM is the proven affine Pippenger.**  Statement shape
mirrors `MsmProj.pippengerProjScatter_eq`. -/
theorem msmM_spec (c : ℕ) (hc : 0 < c) (terms : List (ℕ × PM))
    (hwf : ∀ t ∈ terms, WFP t.2) (hv : ∀ t ∈ terms, Valid (toPVesM t.2))
    (hn : ∀ t ∈ terms, t.1 < 2 ^ 256) :
    toAffine (toPVesM (PM.msm c terms))
      = Msm.pippenger c (terms.map fun t => (t.1, toAffine (toPVesM t.2))) := by
  set W := (256 + c - 1) / c with hWdef
  set pterms := terms.map fun t => (t.1, toPVesM t.2) with hpterms
  set aterms := terms.map fun t => (t.1, toAffine (toPVesM t.2)) with haterms
  have hptv : ∀ p ∈ pterms, Valid p.2 := by
    intro p hp
    rw [hpterms, List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact hv t ht
  have hmapaff : pterms.map (fun t => (t.1, toAffine t.2)) = aterms := by
    rw [hpterms, haterms, List.map_map]
    rfl
  -- each window value: well formed, representable, and affinely the `Msm` window value
  have hwin : ∀ i, WV (PM.windowValue (2 ^ c) i terms) ∧
      toGM (PM.windowValue (2 ^ c) i terms) = Msm.windowValue (2 ^ c) i aterms := by
    intro i
    have hR := RM_windowValue (2 ^ c) i terms hwf
    rw [← hpterms] at hR
    obtain ⟨hvw, hew⟩ := MsmProj.pwindowValueFast_spec (2 ^ c) i pterms hptv
    exact ⟨RM_valid hR hvw, by rw [RM_toG hR, hew, hmapaff]⟩
  have hvals : ∀ v ∈ (List.range W).map (fun i => PM.windowValue (2 ^ c) i terms), WV v := by
    intro v hvm
    rw [List.mem_map] at hvm
    obtain ⟨i, -, rfl⟩ := hvm
    exact (hwin i).1
  have hmsm : PM.msm c terms
      = ((List.range W).map fun i => PM.windowValue (2 ^ c) i terms).foldr
        (fun v acc => PM.padd (PM.pdoublings c acc) v) PM.pid := rfl
  have hmapwin : ((List.range W).map fun i => PM.windowValue (2 ^ c) i terms).map toGM
      = (List.range W).map fun i => Msm.windowValue (2 ^ c) i aterms := by
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left fun i _ => (hwin i).2
  show toGM (PM.msm c terms) = _
  rw [hmsm, (hfoldM_spec c _ hvals).2, hmapwin]
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

end CompElliptic.Curves.Pasta.Fast.ProjectiveMont
