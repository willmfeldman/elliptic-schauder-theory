/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Basic.HalfSpace
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Interpolation: the gradient is controlled by the oscillation and the Hölder seminorm

Gilbarg–Trudinger (interpolation inequalities). On a convex set `S` containing a closed ball
`closedBall c r` and within distance `D` of `c`, if `u` is differentiable within `S`, its derivative
`Du = fderivWithin ℝ u S` satisfies `‖Du x - Du y‖ ≤ H |x - y|^α` on `S`, and
`‖u x - u y‖ ≤ O` on `S`, then for every `λ ∈ (0, 1]`

  `‖Du x‖ ≤ O / (λ r) + H λ^α (D + r)^{1+α} / r` on `S`

(`norm_fderivWithin_le_of_holder`). Corollaries in scaled form with a free `ε > 0`:

* `norm_fderivWithin_halfBall_le`: on `halfBall ν x₀ R` (`‖ν‖ = 1`, `⟪x₀, ν⟫ ≥ 0`),
  `‖Du‖ ≤ ε R^α H + interpConst ε α · R⁻¹ O`;
* `norm_fderivWithin_closedBall_le`: the same on `closedBall x₀ R`.

## Proof

Fix `x ∈ S` and a unit vector `e`. For a sign `σ = ±1` with `‖Du x (c - x + σ r e)‖ ≥ r ‖Du x e‖`,
the point `w = c + σ r e` lies in the ball, so `y = x + λ (w - x) ∈ S`. The mean value inequality on
the segment `[x, y]`, applied to `u - Du x`, gives
`λ ‖Du x (w - x)‖ ≤ ‖u y - u x‖ + H (λ ‖w - x‖)^α λ ‖w - x‖`; divide by `λ r`.
The argument works for vector-valued `u` because `max_σ ‖a + σ b‖ ≥ ‖b‖`.

## Provenance

Original. The calabi-yau project (`CalabiYau/Schauder/Holder/Interpolation`, different pin) was a
design reference only.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001.
-/

public section

open Metric Set RealInnerProductSpace

namespace BasicElliptic

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Interpolation inequality** on a convex set with an inner ball (GT, interpolation
inequalities). -/
theorem norm_fderivWithin_le_of_holder {S : Set E} (hS : Convex ℝ S) {c : E} {r D : ℝ}
    (hr : 0 < r) (hball : closedBall c r ⊆ S) (hD : ∀ p ∈ S, dist p c ≤ D)
    {u : E → F} (hu : DifferentiableOn ℝ u S) {α H O : ℝ} (hα : 0 ≤ α) (hH0 : 0 ≤ H)
    (hH : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderivWithin ℝ u S x - fderivWithin ℝ u S y‖ ≤ H * dist x y ^ α)
    (hO : ∀ x ∈ S, ∀ y ∈ S, ‖u x - u y‖ ≤ O) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    ∀ x ∈ S, ‖fderivWithin ℝ u S x‖ ≤ O / (l * r) + H * l ^ α * (D + r) ^ (1 + α) / r := by
  intro x hx
  set L := fderivWithin ℝ u S x with hLdef
  have hO0 : 0 ≤ O := (norm_nonneg _).trans (hO x hx x hx)
  have hD0 : 0 ≤ D := dist_nonneg.trans (hD x hx)
  set K := O / (l * r) + H * l ^ α * (D + r) ^ (1 + α) / r with hK
  have hK0 : 0 ≤ K := by
    have := Real.rpow_nonneg hl0.le α
    have := Real.rpow_nonneg (by linarith : 0 ≤ D + r) (1 + α)
    positivity
  -- the bound on unit vectors
  have hunit : ∀ e : E, ‖e‖ = 1 → ‖L e‖ ≤ K := by
    intro e he
    -- choose the sign
    obtain ⟨σ, hσ, hσL⟩ : ∃ σ : ℝ, |σ| = 1 ∧ r * ‖L e‖ ≤ ‖L ((c - x) + (σ * r) • e)‖ := by
      by_contra hcon
      push Not at hcon
      have h1 := hcon 1 (by simp)
      have h2 := hcon (-1) (by simp)
      have : ‖L ((r : ℝ) • e)‖ * 2 ≤
          ‖L ((c - x) + (1 * r) • e)‖ + ‖L ((c - x) + (-1 * r) • e)‖ := by
        have : (2 : ℝ) • L (r • e) =
            L ((c - x) + (1 * r) • e) - L ((c - x) + (-1 * r) • e) := by
          simp only [map_add, map_smul, one_mul, neg_mul, neg_smul, map_neg]
          module
        calc ‖L (r • e)‖ * 2 = ‖(2 : ℝ) • L (r • e)‖ := by
              rw [norm_smul, Real.norm_two, mul_comm]
          _ ≤ _ := by rw [this]; exact norm_sub_le _ _
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at this
      linarith
    set w : E := c + (σ * r) • e with hw
    have hwS : w ∈ S := hball (by
      rw [mem_closedBall, hw, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
        Real.norm_eq_abs, abs_mul, hσ, one_mul, abs_of_pos hr])
    set v : E := w - x with hv
    have hvw : (c - x) + (σ * r) • e = v := by rw [hv, hw]; abel
    rw [hvw] at hσL
    have hvnorm : ‖v‖ ≤ D + r := by
      calc ‖v‖ = ‖(c - x) + (σ * r) • e‖ := by rw [hvw]
        _ ≤ ‖c - x‖ + ‖(σ * r) • e‖ := norm_add_le _ _
        _ = dist x c + r := by
            rw [← dist_eq_norm, dist_comm, norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul,
              hσ, one_mul, abs_of_pos hr]
        _ ≤ D + r := by linarith [hD x hx]
    set y : E := x + l • v with hy
    have hyS : y ∈ S := hS.add_smul_sub_mem hx hwS ⟨hl0.le, hl1⟩
    have hyx : y - x = l • v := by rw [hy]; abel
    -- mean value inequality on the segment `[x, y]`
    have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hyS
    have hmv := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := u) (f' := fun z ↦ fderivWithin ℝ u S z) (φ := L) (C := H * (l * ‖v‖) ^ α)
      (fun z hz ↦ ((hu z (hseg hz)).hasFDerivWithinAt).mono hseg)
      (fun z hz ↦ by
        refine (hH z (hseg hz) x hx).trans (mul_le_mul_of_nonneg_left ?_ hH0)
        refine Real.rpow_le_rpow dist_nonneg ?_ hα
        rw [dist_eq_norm]
        obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
        have ha' : a = 1 - b := by linarith
        have : a • x + b • y - x = b • (y - x) := by rw [ha']; module
        rw [this, hyx, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb,
          abs_of_pos hl0]
        have := mul_nonneg hl0.le (norm_nonneg v)
        nlinarith)
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    rw [hyx] at hmv
    have hlv : l * ‖L v‖ ≤ O + H * (l * ‖v‖) ^ α * (l * ‖v‖) := by
      have h1 : ‖L (l • v)‖ ≤ ‖u y - u x‖ + ‖u y - u x - L (l • v)‖ := by
        calc ‖L (l • v)‖ = ‖(u y - u x) - (u y - u x - L (l • v))‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have e1 : ‖L (l • v)‖ = l * ‖L v‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
      have e2 : ‖l • v‖ = l * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
      rw [e1] at h1
      rw [e2] at hmv
      linarith [hO y hyS x hx]
    -- assemble
    have hlvD : (l * ‖v‖) ^ α * (l * ‖v‖) ≤ l ^ α * (D + r) ^ (1 + α) * l := by
      have hlvle : l * ‖v‖ ≤ l * (D + r) := mul_le_mul_of_nonneg_left hvnorm hl0.le
      calc (l * ‖v‖) ^ α * (l * ‖v‖) ≤ (l * (D + r)) ^ α * (l * (D + r)) := by
            gcongr
        _ = l ^ α * (D + r) ^ (1 + α) * l := by
            rw [Real.mul_rpow hl0.le (by linarith), Real.rpow_add (by linarith), Real.rpow_one]
            ring
    have hfin : l * r * ‖L e‖ ≤ O + H * (l ^ α * (D + r) ^ (1 + α) * l) := by
      calc l * r * ‖L e‖ = l * (r * ‖L e‖) := by ring
        _ ≤ l * ‖L v‖ := mul_le_mul_of_nonneg_left hσL hl0.le
        _ ≤ O + H * (l * ‖v‖) ^ α * (l * ‖v‖) := hlv
        _ ≤ O + H * (l ^ α * (D + r) ^ (1 + α) * l) := by
            rw [mul_assoc H]; gcongr
    have hlr : 0 < l * r := mul_pos hl0 hr
    calc ‖L e‖ ≤ (O + H * (l ^ α * (D + r) ^ (1 + α) * l)) / (l * r) :=
          (le_div_iff₀' hlr).2 hfin
      _ = O / (l * r) + H * l ^ α * (D + r) ^ (1 + α) / r := by
          field_simp
  -- from unit vectors to the operator norm
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun h ↦ ?_
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hn : 0 < ‖h‖ := norm_pos_iff.2 hh
  have he := hunit (‖h‖⁻¹ • h) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hn] at he
  linarith

end General

/-- The constant `C(ε, α) = 4 / min 1 ((4 ε / 49)^{1/α})` of the scaled interpolation
inequalities. -/
noncomputable def interpConst (ε α : ℝ) : ℝ := 4 / min 1 ((4 * ε / 49) ^ α⁻¹)

private theorem interp_l_pos {ε α : ℝ} (hε : 0 < ε) : 0 < min 1 ((4 * ε / 49) ^ α⁻¹) :=
  lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)

private theorem interp_l_rpow_le {ε α : ℝ} (hε : 0 < ε) (hα : 0 < α) :
    min 1 ((4 * ε / 49) ^ α⁻¹) ^ α ≤ 4 * ε / 49 := by
  calc min 1 ((4 * ε / 49) ^ α⁻¹) ^ α ≤ ((4 * ε / 49) ^ α⁻¹) ^ α :=
        Real.rpow_le_rpow (interp_l_pos hε).le (min_le_right _ _) hα.le
    _ = 4 * ε / 49 := Real.rpow_inv_rpow (by positivity) hα.ne'

section InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Interpolation on half balls**: for `ε > 0`, `0 < α ≤ 1`,
`‖Du‖ ≤ ε R^α H + C(ε, α) R⁻¹ O` on `halfBall ν x₀ R`. -/
theorem norm_fderivWithin_halfBall_le {ν x₀ : E} {R : ℝ} (hν : ‖ν‖ = 1) (hR : 0 < R)
    (hx₀ : 0 ≤ ⟪x₀, ν⟫) {u : E → F} (hu : DifferentiableOn ℝ u (halfBall ν x₀ R))
    {α H O ε : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hH0 : 0 ≤ H) (hε : 0 < ε)
    (hH : ∀ x ∈ halfBall ν x₀ R, ∀ y ∈ halfBall ν x₀ R,
      ‖fderivWithin ℝ u (halfBall ν x₀ R) x - fderivWithin ℝ u (halfBall ν x₀ R) y‖ ≤
        H * dist x y ^ α)
    (hO : ∀ x ∈ halfBall ν x₀ R, ∀ y ∈ halfBall ν x₀ R, ‖u x - u y‖ ≤ O) :
    ∀ x ∈ halfBall ν x₀ R,
      ‖fderivWithin ℝ u (halfBall ν x₀ R) x‖ ≤ ε * R ^ α * H + interpConst ε α * R⁻¹ * O := by
  set c : E := x₀ + (R / 2) • ν
  have hxc : dist x₀ c = R / 2 := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_one]
  have hball : closedBall c (R / 4) ⊆ halfBall ν x₀ R := by
    intro y hy
    rw [mem_closedBall] at hy
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall]
      linarith [dist_triangle y c x₀, dist_comm x₀ c]
    · rw [mem_halfSpace]
      have h1 : ⟪y, ν⟫ = ⟪x₀, ν⟫ + R / 2 + ⟪y - c, ν⟫ := by
        simp only [c, inner_sub_left, inner_add_left, real_inner_smul_left,
          real_inner_self_of_norm_eq_one hν]
        ring
      have h2 : |⟪y - c, ν⟫| ≤ R / 4 := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [hν, mul_one, ← dist_eq_norm]
        exact hy
      linarith [neg_abs_le ⟪y - c, ν⟫]
  have hD : ∀ p ∈ halfBall ν x₀ R, dist p c ≤ 3 * R / 2 := fun p hp ↦ by
    linarith [dist_triangle p x₀ c, (mem_halfBall.1 hp).1]
  set l := min 1 ((4 * ε / 49) ^ α⁻¹) with hl
  have hl0 : 0 < l := interp_l_pos hε
  have h := norm_fderivWithin_le_of_holder (convex_halfBall ν x₀ R) (by positivity) hball hD hu
    hα.le hH0 hH hO hl0 (min_le_left _ _)
  intro x hx
  refine (h x hx).trans ?_
  have hO0 : 0 ≤ O := (norm_nonneg _).trans (hO x hx x hx)
  have h1 : O / (l * (R / 4)) = interpConst ε α * R⁻¹ * O := by
    rw [interpConst, ← hl]; field_simp
  have h2 : (3 * R / 2 + R / 4) ^ (1 + α) ≤ 49 / 16 * R ^ (1 + α) := by
    rw [show 3 * R / 2 + R / 4 = 7 / 4 * R by ring, Real.mul_rpow (by norm_num) hR.le]
    gcongr
    calc (7 / 4 : ℝ) ^ (1 + α) ≤ (7 / 4) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 49 / 16 := by norm_num
  have h3 := interp_l_rpow_le hε hα
  have hlα : 0 ≤ l ^ α := Real.rpow_nonneg hl0.le _
  have hRα : R ^ (1 + α) = R * R ^ α := by
    rw [Real.rpow_add hR, Real.rpow_one]
  have h4 : H * l ^ α * (3 * R / 2 + R / 4) ^ (1 + α) / (R / 4) ≤ ε * R ^ α * H := by
    rw [div_le_iff₀ (by positivity)]
    calc H * l ^ α * (3 * R / 2 + R / 4) ^ (1 + α)
        ≤ H * (4 * ε / 49) * (49 / 16 * R ^ (1 + α)) := by gcongr
      _ = ε * R ^ α * H * (R / 4) := by rw [hRα]; ring
  rw [h1]; linarith

/-- **Interpolation on balls**: for `ε > 0`, `0 < α ≤ 1`,
`‖Du‖ ≤ ε R^α H + C(ε, α) R⁻¹ O` on `closedBall x₀ R`. -/
theorem norm_fderivWithin_closedBall_le {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → F} (hu : DifferentiableOn ℝ u (closedBall x₀ R))
    {α H O ε : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hH0 : 0 ≤ H) (hε : 0 < ε)
    (hH : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      ‖fderivWithin ℝ u (closedBall x₀ R) x - fderivWithin ℝ u (closedBall x₀ R) y‖ ≤
        H * dist x y ^ α)
    (hO : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R, ‖u x - u y‖ ≤ O) :
    ∀ x ∈ closedBall x₀ R,
      ‖fderivWithin ℝ u (closedBall x₀ R) x‖ ≤ ε * R ^ α * H + interpConst ε α * R⁻¹ * O := by
  set l := min 1 ((4 * ε / 49) ^ α⁻¹) with hl
  have hl0 : 0 < l := interp_l_pos hε
  have h := norm_fderivWithin_le_of_holder (convex_closedBall x₀ R) (r := R / 4)
    (by positivity) (closedBall_subset_closedBall (by linarith))
    (fun p hp ↦ (mem_closedBall.1 hp).trans (by linarith : R ≤ 3 * R / 2)) hu
    hα.le hH0 hH hO hl0 (min_le_left _ _)
  intro x hx
  refine (h x hx).trans ?_
  have hO0 : 0 ≤ O := (norm_nonneg _).trans (hO x hx x hx)
  have h1 : O / (l * (R / 4)) = interpConst ε α * R⁻¹ * O := by
    rw [interpConst, ← hl]; field_simp
  have h2 : (3 * R / 2 + R / 4) ^ (1 + α) ≤ 49 / 16 * R ^ (1 + α) := by
    rw [show 3 * R / 2 + R / 4 = 7 / 4 * R by ring, Real.mul_rpow (by norm_num) hR.le]
    gcongr
    calc (7 / 4 : ℝ) ^ (1 + α) ≤ (7 / 4) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 49 / 16 := by norm_num
  have h3 := interp_l_rpow_le hε hα
  have hlα : 0 ≤ l ^ α := Real.rpow_nonneg hl0.le _
  have hRα : R ^ (1 + α) = R * R ^ α := by
    rw [Real.rpow_add hR, Real.rpow_one]
  have h4 : H * l ^ α * (3 * R / 2 + R / 4) ^ (1 + α) / (R / 4) ≤ ε * R ^ α * H := by
    rw [div_le_iff₀ (by positivity)]
    calc H * l ^ α * (3 * R / 2 + R / 4) ^ (1 + α)
        ≤ H * (4 * ε / 49) * (49 / 16 * R ^ (1 + α)) := by gcongr
      _ = ε * R ^ α * H * (R / 4) := by rw [hRα]; ring
  rw [h1]; linarith

end InnerProduct

end BasicElliptic
