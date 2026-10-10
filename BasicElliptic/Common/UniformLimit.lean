/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Calculus.FDeriv.Add
import BasicElliptic.Holder.Interpolation

/-!
# Uniform limits of functions with uniformly Hölder derivatives

Let `S` be a convex set containing a closed ball and contained in a
bounded set. If `u n → f` uniformly on `S`, each `u n` is differentiable within `S`, and the
within-derivatives `D u n` are `α`-Hölder on `S` with a constant `H` independent of `n`, then `f`
is differentiable within `S` and its derivative is `α`-Hölder with the same constant `H`
(`exists_hasFDerivWithinAt_of_tendstoUniformlyOn`). No subsequence is extracted.

## Proof

* **Cauchy.** By the interpolation inequality (`norm_fderivWithin_le_of_holder`) applied to
  `u n - u m`, whose derivative is `2H`-Hölder,
  `‖D u n x - D u m x‖ ≤ osc (u n - u m) / (l r) + 2 H l^α (D + r)^{1+α} / r`
  for every `l ∈ (0, 1]`. Take `l` small, then `n, m` large: `D u n x` is Cauchy; call its limit
  `g x`. The Hölder bound passes to the limit.
* **Taylor bound.** For `x, y ∈ S` the mean value inequality on the segment `[x, y]` gives
  `‖u n y - u n x - D u n x (y - x)‖ ≤ H ‖y - x‖^{1+α}`
  (`norm_sub_sub_fderiv_le_of_holder`). Let `n → ∞`: the same bound holds for `f` and `g x`,
  which is `o(‖y - x‖)`.

This replaces Arzelà–Ascoli (the interpolation-Cauchy route).
-/

public section

open Filter Topology Metric Set

namespace BasicElliptic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Taylor bound from a Hölder derivative** on a convex set:
`‖u y - u x - u' x (y - x)‖ ≤ H ‖y - x‖^{1+α}`. -/
theorem norm_sub_sub_fderiv_le_of_holder {S : Set E} (hS : Convex ℝ S) {u : E → F}
    {u' : E → E →L[ℝ] F} (hu : ∀ y ∈ S, HasFDerivWithinAt u (u' y) S y) {H α : ℝ}
    (hα : 0 ≤ α) (hHnn : 0 ≤ H) (hH : ∀ x ∈ S, ∀ y ∈ S, ‖u' x - u' y‖ ≤ H * dist x y ^ α) {x y : E}
    (hx : x ∈ S) (hy : y ∈ S) :
    ‖u y - u x - u' x (y - x)‖ ≤ H * ‖y - x‖ ^ (1 + α) := by
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hder : ∀ z ∈ segment ℝ x y,
      HasFDerivWithinAt (fun z ↦ u z - u' x z) (u' z - u' x) (segment ℝ x y) z := fun z hz ↦
    ((hu z (hseg hz)).mono hseg).sub (u' x).hasFDerivWithinAt
  have hbd : ∀ z ∈ segment ℝ x y, ‖u' z - u' x‖ ≤ H * ‖y - x‖ ^ α := by
    intro z hz
    refine (hH z (hseg hz) x hx).trans ?_
    have hzx : dist z x ≤ ‖y - x‖ := by
      rw [← dist_eq_norm, dist_comm y x, dist_comm z x]
      have := dist_add_dist_of_mem_segment hz
      linarith [dist_nonneg (x := z) (y := y)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hzx hα) hHnn
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbd
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have e1 : u y - u' x y - (u x - u' x x) = u y - u x - u' x (y - x) := by
    rw [map_sub]; abel
  rw [e1] at hmv
  refine hmv.trans (le_of_eq ?_)
  rw [Real.rpow_add' (norm_nonneg _) (by linarith), Real.rpow_one]
  ring

/-- A function with `‖f y - f x - L (y - x)‖ ≤ H ‖y - x‖^{1+α}` on `S` (`α > 0`) has derivative
`L` within `S` at `x`. -/
theorem hasFDerivWithinAt_of_norm_sub_le_rpow {S : Set E} {f : E → F} {L : E →L[ℝ] F} {x : E}
    {H α : ℝ} (hα : 0 < α) (h : ∀ y ∈ S, ‖f y - f x - L (y - x)‖ ≤ H * ‖y - x‖ ^ (1 + α)) :
    HasFDerivWithinAt f L S x := by
  refine HasFDerivWithinAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun c hc ↦ ?_)
  set H' := max H 1 with hH'
  have hH'0 : 0 < H' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set δ : ℝ := (c / H') ^ α⁻¹ with hδ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos (div_pos hc hH'0) _
  filter_upwards [inter_mem_nhdsWithin S (ball_mem_nhds x hδ0), self_mem_nhdsWithin] with y hy hyS
  have hyx : ‖y - x‖ < δ := by rw [← dist_eq_norm]; exact mem_ball.1 hy.2
  have hn : 0 ≤ ‖y - x‖ := norm_nonneg _
  have hpow : ‖y - x‖ ^ α ≤ c / H' := by
    calc ‖y - x‖ ^ α ≤ δ ^ α := Real.rpow_le_rpow hn hyx.le hα.le
      _ = c / H' := by
        rw [hδ, ← Real.rpow_mul (div_pos hc hH'0).le, inv_mul_cancel₀ hα.ne', Real.rpow_one]
  have h1 := h y hyS
  rw [Real.rpow_add' hn (by linarith), Real.rpow_one] at h1
  have hpa : 0 ≤ ‖y - x‖ ^ α := Real.rpow_nonneg hn _
  calc ‖f y - f x - L (y - x)‖ ≤ H * (‖y - x‖ ^ α * ‖y - x‖) := by
        rw [mul_comm (‖y - x‖ ^ α)]; exact h1.trans (le_of_eq (by ring))
    _ ≤ H' * (‖y - x‖ ^ α * ‖y - x‖) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ H' * (c / H' * ‖y - x‖) := by gcongr
    _ = c * ‖y - x‖ := by field_simp

private theorem exists_small_l {K ε α : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) (hα : 0 < α) :
    ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ K * l ^ α < ε := by
  set q : ℝ := ε / (2 * (K + 1)) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨min 1 (q ^ α⁻¹), lt_min one_pos (Real.rpow_pos_of_pos hq0 _), min_le_left _ _, ?_⟩
  have h1 : min 1 (q ^ α⁻¹) ^ α ≤ q := by
    calc min 1 (q ^ α⁻¹) ^ α ≤ (q ^ α⁻¹) ^ α :=
          Real.rpow_le_rpow (lt_min one_pos (Real.rpow_pos_of_pos hq0 _)).le (min_le_right _ _)
            hα.le
      _ = q := Real.rpow_inv_rpow hq0.le hα.ne'
  calc K * min 1 (q ^ α⁻¹) ^ α ≤ K * q := mul_le_mul_of_nonneg_left h1 hK
    _ < ε := by
        rw [hq]
        have : K * (ε / (2 * (K + 1))) = ε * (K / (2 * (K + 1))) := by ring
        rw [this]
        have : K / (2 * (K + 1)) < 1 := by
          rw [div_lt_one (by positivity)]; linarith
        nlinarith

variable [CompleteSpace F]

/-- **Uniform limits with uniformly Hölder derivatives**. Let `S` be convex with
`closedBall c r ⊆ S` and `dist p c ≤ D` on `S`. If `u n → f` uniformly on `S`, each `u n` is
differentiable within `S`, and the within-derivatives are `α`-Hölder on `S` with a constant `H`
independent of `n`, then `f` has an `α`-Hölder within-derivative `g` on `S` (same constant). -/
theorem exists_hasFDerivWithinAt_of_tendstoUniformlyOn {S : Set E} (hS : Convex ℝ S) {c : E}
    {r D : ℝ} (hr : 0 < r) (hball : closedBall c r ⊆ S) (hD : ∀ p ∈ S, dist p c ≤ D)
    {u : ℕ → E → F} {f : E → F} (hu : ∀ n, DifferentiableOn ℝ (u n) S) {α H : ℝ}
    (hα : 0 < α) (hH0 : 0 ≤ H)
    (hH : ∀ n, ∀ x ∈ S, ∀ y ∈ S,
      ‖fderivWithin ℝ (u n) S x - fderivWithin ℝ (u n) S y‖ ≤ H * dist x y ^ α)
    (hlim : TendstoUniformlyOn u f atTop S) :
    ∃ g : E → E →L[ℝ] F, (∀ x ∈ S, HasFDerivWithinAt f (g x) S x) ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖g x - g y‖ ≤ H * dist x y ^ α := by
  have hcS : c ∈ S := hball (mem_closedBall_self hr.le)
  have hint : (interior S).Nonempty :=
    ⟨c, interior_mono (ball_subset_closedBall.trans hball)
      (by rw [isOpen_ball.interior_eq]; exact mem_ball_self hr)⟩
  have hU : UniqueDiffOn ℝ S := uniqueDiffOn_convex hS hint
  have hD0 : 0 ≤ D := dist_nonneg.trans (hD c hcS)
  -- Cauchy property of the derivatives at each point
  have hcauchy : ∀ x ∈ S, CauchySeq fun n ↦ fderivWithin ℝ (u n) S x := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set K0 : ℝ := 2 * H * (D + r) ^ (1 + α) / r with hK0
    have hK00 : 0 ≤ K0 := by
      have := Real.rpow_nonneg (by linarith : 0 ≤ D + r) (1 + α); positivity
    obtain ⟨l, hl0, hl1, hl⟩ := exists_small_l hK00 (half_pos hε) hα
    set δ : ℝ := ε * (l * r) / 16 with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 hlim δ hδ0).exists_forall_of_atTop
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hd : DifferentiableOn ℝ (u m - u n) S := (hu m).sub (hu n)
    have hfd : ∀ y ∈ S, fderivWithin ℝ (u m - u n) S y =
        fderivWithin ℝ (u m) S y - fderivWithin ℝ (u n) S y := fun y hy ↦
      fderivWithin_sub (hU y hy) ((hu m) y hy) ((hu n) y hy)
    have hH2 : ∀ x ∈ S, ∀ y ∈ S, ‖fderivWithin ℝ (u m - u n) S x -
        fderivWithin ℝ (u m - u n) S y‖ ≤ (2 * H) * dist x y ^ α := by
      intro x hx y hy
      rw [hfd x hx, hfd y hy]
      calc ‖fderivWithin ℝ (u m) S x - fderivWithin ℝ (u n) S x -
            (fderivWithin ℝ (u m) S y - fderivWithin ℝ (u n) S y)‖
          = ‖(fderivWithin ℝ (u m) S x - fderivWithin ℝ (u m) S y) -
            (fderivWithin ℝ (u n) S x - fderivWithin ℝ (u n) S y)‖ := by
            congr 1; abel
        _ ≤ ‖fderivWithin ℝ (u m) S x - fderivWithin ℝ (u m) S y‖ +
            ‖fderivWithin ℝ (u n) S x - fderivWithin ℝ (u n) S y‖ := norm_sub_le _ _
        _ ≤ H * dist x y ^ α + H * dist x y ^ α := add_le_add (hH m x hx y hy) (hH n x hx y hy)
        _ = (2 * H) * dist x y ^ α := by ring
    have hO : ∀ x ∈ S, ∀ y ∈ S, ‖(u m - u n) x - (u m - u n) y‖ ≤ 4 * δ := by
      intro x hx y hy
      have h1 := hN m hm x hx; have h2 := hN n hn x hx
      have h3 := hN m hm y hy; have h4 := hN n hn y hy
      rw [dist_eq_norm] at h1 h2 h3 h4
      simp only [Pi.sub_apply]
      calc ‖u m x - u n x - (u m y - u n y)‖
          = ‖(f x - u n x) - (f x - u m x) - ((f y - u n y) - (f y - u m y))‖ := by
            congr 1; abel
        _ ≤ ‖f x - u n x‖ + ‖f x - u m x‖ + (‖f y - u n y‖ + ‖f y - u m y‖) := by
            refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
        _ ≤ 4 * δ := by linarith
    have hip := norm_fderivWithin_le_of_holder hS hr hball hD hd hα.le (by positivity) hH2 hO
      hl0 hl1 x hx
    rw [dist_eq_norm, ← hfd x hx]
    have e1 : 4 * δ / (l * r) = ε / 4 := by rw [hδ]; field_simp; ring
    have e2 : 2 * H * l ^ α * (D + r) ^ (1 + α) / r = K0 * l ^ α := by rw [hK0]; ring
    rw [e1, e2] at hip
    linarith
  choose! g hg using fun x (hx : x ∈ S) ↦ cauchySeq_tendsto_of_complete (hcauchy x hx)
  have hgH : ∀ x ∈ S, ∀ y ∈ S, ‖g x - g y‖ ≤ H * dist x y ^ α := fun x hx y hy ↦
    le_of_tendsto ((hg x hx).sub (hg y hy)).norm (Eventually.of_forall fun n ↦ hH n x hx y hy)
  refine ⟨g, fun x hx ↦ ?_, hgH⟩
  refine hasFDerivWithinAt_of_norm_sub_le_rpow (H := H) hα fun y hy ↦ ?_
  have hT : Tendsto (fun n ↦ u n y - u n x - fderivWithin ℝ (u n) S x (y - x)) atTop
      (𝓝 (f y - f x - g x (y - x))) :=
    ((hlim.tendsto_at hy).sub (hlim.tendsto_at hx)).sub
      (((continuous_id.clm_apply continuous_const).tendsto (g x)).comp (hg x hx))
  refine le_of_tendsto hT.norm (Eventually.of_forall fun n ↦ ?_)
  exact norm_sub_sub_fderiv_le_of_holder hS
    (fun z hz ↦ ((hu n) z hz).hasFDerivWithinAt) hα.le hH0 (hH n) hx hy

end BasicElliptic
