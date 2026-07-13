/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import CompElliptic.CurveForms.ShortWeierstrass
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The GLV endomorphism on a short-Weierstrass curve with `A = 0`

For a curve `y² = x³ + B` (so `A = 0`) over a field containing a primitive cube root of unity `ζ`,
the map `φ (x, y) = (ζ x, y)` is a group endomorphism. On a group of prime order it must act as
multiplication by *some* scalar; a single spot-check on a generator identifies which. This is the
GLV endomorphism, the basis of the GLV scalar decomposition.

Three layers:

1. **Pure finite-group theory** (`endo_eq_nsmul_of_prime_card`) — no elliptic curves at all: an
   endomorphism of a group of prime order `r` that sends one non-identity element `g` to `[lam] g`
   is `[lam]` everywhere.
2. **Raw computable kernel** — `phi` on `F × F`, with `phi_add` proving it commutes with the raw
   `add` (for `A = 0`). Notably this needs *no* hypotheses beyond `ζ³ = 1`: not `Valid`, not
   `IsElliptic`, not `B ≠ 0`. The slope scales by `ζ²` in *both* branches of `add`
   (`3(ζx)²/(2y) = ζ²·s` for doubling, `(y₂-y₁)/(ζx₂-ζx₁) = ζ⁻¹·s = ζ²·s` for distinct `x`), the
   branch guards are preserved exactly (`ζ ≠ 0`), and even the junk-division cases agree because
   both sides produce `0/0 = 0`.
3. **Rich bundled types** — `SWPoint.phiPt` / `SWPoint.phiHom` (`φ` as an `AddMonoidHom`), and
   `SWPoint.phiPt_eq_nsmul`, which combines layers 1 and 2: given the group order (a prime `r`) and
   the spot-check `φ G = [lam] G` on a non-identity `G`, conclude `φ P = [lam] P` for *every* `P`.

`A = 0` is essential: for `A ≠ 0` the equation `y² = (ζx)³ + A(ζx) + B` fails. This covers the
Pasta curves (`y² = x³ + 5`), and every curve GLV is used on in practice.

Everything here is a real proof; the numeric facts (`ζ³ = 1`, and the spot-check) are per-curve
closed facts and live in the concrete-curve modules.
-/

namespace CompElliptic.CurveForms.ShortWeierstrass

/-! ## Layer 1: an endomorphism of a prime-order group is multiplication by a scalar

Pure finite-group theory, with no reference to elliptic curves. In a group of prime order `r`,
every element is a multiple of any non-identity element `g` (`mem_multiples_of_prime_card`, which
derives `Finite` internally from `Nat.card G = r` and primality). An additive hom therefore is
pinned by its value on `g` alone. -/

/-- If `G` has prime order `r`, `f` is an endomorphism of `G`, and `f g = [lam] g` for a single
non-identity `g`, then `f = [lam]` on all of `G`.

This is the general theorem behind `φ = [λ]`: it reduces the claim on the whole group to one
*closed, spot-checkable fact* about a single point — the *Independently re-checkable trust*
principle. -/
theorem endo_eq_nsmul_of_prime_card {G : Type*} [AddGroup G] {r : ℕ} [Fact r.Prime]
    (hcard : Nat.card G = r) (f : G →+ G) {g : G} (hg : g ≠ 0) {lam : ℕ}
    (hspot : f g = lam • g) (x : G) : f x = lam • x := by
  obtain ⟨n, rfl⟩ := (AddSubmonoid.mem_multiples_iff x g).mp (mem_multiples_of_prime_card hcard hg)
  rw [map_nsmul, hspot, nsmul_left_comm]

variable {F : Type*} [Field F]

/-! ## Layer 2: the raw computable kernel

The `φ`-specific facts need only `[Field F]`; `[DecidableEq F]` enters at `phi_add`, where the
branch structure of `add` does. -/

/-- The GLV map `φ (x, y) = (z x, y)` on raw coordinates. For `z` a primitive cube root of unity it
is a nontrivial endomorphism of the curve group (`phi_add`, `onCurve_phi`). -/
def phi (z : F) (p : F × F) : F × F := (z * p.1, p.2)

variable {z : F}

/-- A cube root of unity is nonzero. -/
theorem zeta_ne_zero (hz : z ^ 3 = 1) : z ≠ 0 := by
  intro h
  rw [h] at hz
  simp at hz

/-- `z⁻¹ = z²` for a cube root of unity — the identity behind the slope scaling. -/
theorem zeta_inv (hz : z ^ 3 = 1) : z⁻¹ = z ^ 2 :=
  inv_eq_of_mul_eq_one_right (by linear_combination hz)

/-- Scaling the *denominator* of a slope by `z` scales the slope by `z²`. Holds unconditionally
(no `b ≠ 0` needed): for `b = 0` both sides are `0`, since `x / 0 = 0` in Lean. -/
theorem div_zeta_mul (hz : z ^ 3 = 1) (a b : F) : a / (z * b) = z ^ 2 * (a / b) := by
  rw [div_mul_eq_div_div_swap, div_eq_mul_inv _ z, zeta_inv hz]
  ring

/-- `φ` fixes the `(0, 0)` identity sentinel. -/
@[simp] theorem phi_origin (z : F) : phi z ((0, 0) : F × F) = (0, 0) := by
  simp [phi]

/-- `φ` reflects the identity sentinel: `φ p = 𝒪` exactly when `p = 𝒪`. This is what makes the
`𝒪` branch guards of `add` line up on both sides of `phi_add`. -/
theorem phi_eq_origin_iff (hz : z ^ 3 = 1) (p : F × F) : phi z p = (0, 0) ↔ p = (0, 0) := by
  simp [phi, Prod.ext_iff, zeta_ne_zero hz]

/-- `φ` maps the curve `y² = x³ + b` to itself: `(z x)³ = x³` when `z³ = 1`. (`A = 0` is essential.) -/
theorem onCurve_phi {b : F} (hz : z ^ 3 = 1) {p : F × F} (h : OnCurve 0 b p) :
    OnCurve 0 b (phi z p) := by
  simp only [OnCurve, phi] at h ⊢
  linear_combination h - p.1 ^ 3 * hz

/-- `φ` preserves representability (`on the curve, or 𝒪`). -/
theorem valid_phi {b : F} (hz : z ^ 3 = 1) {p : F × F} (h : Valid 0 b p) :
    Valid 0 b (phi z p) := by
  rcases h with h | h
  · exact Or.inl (onCurve_phi hz h)
  · exact Or.inr (by rw [h, phi_origin])

/-- The shared chord/tangent core of `phi_add`, `x`-coordinate half: with the slope scaled to
`z² · lam`, the new `x` scales by `z`. -/
theorem phi_addX (hz : z ^ 3 = 1) (lam x₁ x₂ : F) :
    (z ^ 2 * lam) ^ 2 - z * x₁ - z * x₂ = z * (lam ^ 2 - x₁ - x₂) := by
  linear_combination (z * lam ^ 2) * hz

/-- The shared chord/tangent core of `phi_add`, `y`-coordinate half: with the slope scaled to
`z² · lam` and `x` scaled by `z`, the new `y` is *unchanged*. -/
theorem phi_addY (hz : z ^ 3 = 1) (lam x₁ x₂ y₁ : F) :
    (z ^ 2 * lam) * (z * x₁ - ((z ^ 2 * lam) ^ 2 - z * x₁ - z * x₂)) - y₁
      = lam * (x₁ - (lam ^ 2 - x₁ - x₂)) - y₁ := by
  linear_combination (lam * (2 * x₁ + x₂) - lam ^ 3 * (z ^ 3 + 1)) * hz

variable [DecidableEq F]

/-- **`φ` commutes with the group law** (for `A = 0`), on raw coordinates.

Strikingly, this needs no hypotheses at all beyond `z³ = 1`: no `Valid`, no `IsElliptic`, no
`B ≠ 0`. Every branch guard of `add` is preserved by `φ` (`z ≠ 0`), and both branches scale the
slope by exactly `z²`, after which `phi_addX` / `phi_addY` finish. The degenerate divisions
(`y = 0` in the doubling branch) need no side condition either, since `x / 0 = 0` on both sides.

The branch walk is explicit (`by_cases` + `rw [if_pos/if_neg]`) rather than
`split_ifs <;> simp_all`, which blows the recursion limit on the nested `ite`s (cf. `add_neg`). -/
theorem phi_add (hz : z ^ 3 = 1) (p q : F × F) :
    phi z (add 0 p q) = add 0 (phi z p) (phi z q) := by
  have hz0 : z ≠ 0 := zeta_ne_zero hz
  by_cases hp0 : p = (0, 0)
  · rw [hp0, zero_add, phi_origin, zero_add]
  by_cases hq0 : q = (0, 0)
  · rw [hq0, add_zero, phi_origin, add_zero]
  have hp0' : phi z p ≠ (0, 0) := fun h => hp0 ((phi_eq_origin_iff hz p).mp h)
  have hq0' : phi z q ≠ (0, 0) := fun h => hq0 ((phi_eq_origin_iff hz q).mp h)
  -- `φ` preserves the two remaining guards: same `x` (as `z ≠ 0`), and `y₁ + y₂ = 0` (`y` is fixed).
  have hxg : (phi z p).1 = (phi z q).1 ↔ p.1 = q.1 := by
    simp [phi, mul_right_inj' hz0]
  have hyg : (phi z p).2 + (phi z q).2 = 0 ↔ p.2 + q.2 = 0 := by simp [phi]
  unfold add
  rw [if_neg hp0, if_neg hq0, if_neg hp0', if_neg hq0']
  by_cases hx : p.1 = q.1
  · rw [if_pos hx, if_pos (hxg.mpr hx)]
    by_cases hy : p.2 + q.2 = 0
    · rw [if_pos hy, if_pos (hyg.mpr hy), phi_origin]
    · rw [if_neg hy, if_neg (fun h => hy (hyg.mp h))]
      -- doubling: the slope `3(z x)²/(2y)` is `z² ·` the original slope.
      have hlam : (3 * (phi z p).1 ^ 2 + 0) / (2 * (phi z p).2)
          = z ^ 2 * ((3 * p.1 ^ 2 + 0) / (2 * p.2)) := by
        simp only [phi]
        rw [← mul_div_assoc]
        ring_nf
      simp only [phi, Prod.mk.injEq]
      simp only [phi] at hlam
      rw [hlam]
      exact ⟨(phi_addX hz _ _ _).symm, (phi_addY hz _ _ _ _).symm⟩
  · rw [if_neg hx, if_neg (fun h => hx (hxg.mp h))]
    -- distinct `x`: the slope `(y₂-y₁)/(z x₂ - z x₁)` is `z⁻¹ = z²` times the original slope.
    have hlam : ((phi z q).2 - (phi z p).2) / ((phi z q).1 - (phi z p).1)
        = z ^ 2 * ((q.2 - p.2) / (q.1 - p.1)) := by
      simp only [phi]
      rw [← mul_sub, div_zeta_mul hz]
    simp only [phi, Prod.mk.injEq]
    simp only [phi] at hlam
    rw [hlam]
    exact ⟨(phi_addX hz _ _ _).symm, (phi_addY hz _ _ _ _).symm⟩

/-! ## Layer 3: `φ` on the rich point type -/

/-- `φ` on `SWPoint E`, for a curve with `A = 0` and a cube root of unity `z`. The two proofs are
`Prop`s, hence erased: `phiPt` computes, and is `native_decide`-friendly. -/
def SWPoint.phiPt {E : SWCurve F} (hA : E.A = 0) (hz : z ^ 3 = 1) (P : SWPoint E) : SWPoint E :=
  ⟨z * P.x, P.y, by
    have h : Valid 0 E.B (P.x, P.y) := hA ▸ P.onCurve
    have h' : Valid 0 E.B (phi z (P.x, P.y)) := valid_phi hz h
    rw [hA]
    exact h'⟩

omit [DecidableEq F] in
@[simp] theorem SWPoint.phiPt_coords {E : SWCurve F} (hA : E.A = 0) (hz : z ^ 3 = 1)
    (P : SWPoint E) :
    ((SWPoint.phiPt hA hz P).x, (SWPoint.phiPt hA hz P).y) = phi z (P.x, P.y) := rfl

/-- `φ` is additive on `SWPoint E` — the group-law commutation of `phi_add`, lifted. -/
theorem SWPoint.phiPt_add {E : SWCurve F} (hA : E.A = 0) (hz : z ^ 3 = 1) (P Q : SWPoint E) :
    SWPoint.phiPt hA hz (P + Q) = SWPoint.phiPt hA hz P + SWPoint.phiPt hA hz Q := by
  refine SWPoint.ext_pair ?_
  show phi z (add E.A (P.x, P.y) (Q.x, Q.y))
      = add E.A (phi z (P.x, P.y)) (phi z (Q.x, Q.y))
  rw [hA]
  exact phi_add hz _ _

/-- `φ` as an `AddMonoidHom` on `SWPoint E` — the input to `endo_eq_nsmul_of_prime_card`. -/
def SWPoint.phiHom {E : SWCurve F} (hA : E.A = 0) (hz : z ^ 3 = 1) : SWPoint E →+ SWPoint E :=
  AddMonoidHom.mk' (SWPoint.phiPt hA hz) (SWPoint.phiPt_add hA hz)

/-- **`φ = [lam]` on the whole group**, from the group order and a single spot-check.

Layers 1 and 2 combined: `φ` is an endomorphism (`phiHom`, proved outright), the group has prime
order `r` (a curve fact), and `φ G = [lam] G` for one non-identity `G` (a closed, `native_decide`-
checkable fact). Hence `φ P = [lam] P` for every `P`. -/
theorem SWPoint.phiPt_eq_nsmul {E : SWCurve F} (hA : E.A = 0) (hz : z ^ 3 = 1)
    {r : ℕ} [Fact r.Prime] (hcard : Nat.card (SWPoint E) = r)
    {G : SWPoint E} (hG : G ≠ 0) {lam : ℕ} (hspot : SWPoint.phiPt hA hz G = lam • G)
    (P : SWPoint E) : SWPoint.phiPt hA hz P = lam • P :=
  endo_eq_nsmul_of_prime_card hcard (SWPoint.phiHom hA hz) hG hspot P

end CompElliptic.CurveForms.ShortWeierstrass
