/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Higher.Directional
public import BasicElliptic.Div.Quasilinear.SecondOrder
import Mathlib.Analysis.Calculus.ContDiff.Basic
import BasicElliptic.Holder.Algebra
import BasicElliptic.Div.Boundary.Main
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Linear conormal problem: second derivatives up to the flat part

Standing assumptions (on `B = halfBall ν x r`, `-r < ⟪x, ν⟫`): `a` symmetric, `(lam, Λ)`-elliptic,
`C¹` with `α`-Hölder derivative; `G` `C¹` with `α`-Hölder derivative; `f` continuous on `E` and
`α`-Hölder on `B`; `w` a conormal solution of `-div (a ∇w - G) = f` on `B`.

* `Div.exists_local_gradient_holder`: near each point of `ball x r ∩ halfSpace ν`, `∇w` is
  `α`-Hölder (qualitative, `Div/Boundary/`).
* `Div.exists_directional_of_linear`: directional second derivatives `D(∂_e w)` exist and are
  `α`-Hölder up to the flat part, for `e` tangential or near interior points
  (`Div.IsConormalSolOn.translate_sub` and the uniform conormal boundary estimate,
  `Div.exists_hasFDerivWithinAt_fderivWithin_apply_of_linear`).
* `Div.contDiffOn_two_interior_of_linear`: `w ∈ C²(ball x r ∩ openHalfSpace ν)`.
* `Div.neg_divergence_eq_of_weak`, `Div.sum_hessian_coeff_eq`: in the interior the equation holds
  in nondivergence form,
  `Σ_j D²w(b_j, a b_j) = R := -f - Σ_j ⟪b_j, (Da b_j) ∇w⟫ + Σ_j ⟪b_j, DG b_j⟫`.
* `Div.hessian_apply_normal_of_sum_eq`: the normal–normal derivative from the equation.
* `Div.exists_hessian_halfBall_of_linear`: near each point of `ball x r ∩ halfSpace ν`, the
  within-derivative of `D_B w` exists on a small half ball and is `α`-Hölder there.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology NNReal ContDiff Interval

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A `C¹` function on a closed half ball has a bounded within-derivative and is `α`-Hölder
(`α ≤ 1`). -/
theorem exists_bound_holderOnWith_of_contDiffOn_halfBall {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫)
    {g : E → F} (hg : ContDiffOn ℝ 1 g (halfBall ν x r)) {α : ℝ≥0} (hα1 : α ≤ 1) :
    (∃ M : ℝ, ∀ p ∈ halfBall ν x r, ‖fderivWithin ℝ g (halfBall ν x r) p‖ ≤ M) ∧
      ∃ K : ℝ≥0, HolderOnWith K α g (halfBall ν x r) := by
  have hu := uniqueDiffOn_halfBall hν hr hx
  obtain ⟨M, hM⟩ := (isCompact_halfBall ν x r).exists_bound_of_continuousOn
    (hg.continuousOn_fderivWithin hu le_rfl)
  refine ⟨⟨M, hM⟩, ?_⟩
  have hL := (convex_halfBall ν x r).lipschitzOnWith_of_nnnorm_fderivWithin_le
    (C := Real.toNNReal M) (hg.differentiableOn one_ne_zero) (fun p hp ↦ by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hM p hp).trans (Real.le_coe_toNNReal M))
  refine ⟨_, holderOnWith_of_lipschitzOnWith hL hα1 (D := 2 * r) (by positivity)
    fun p hp q hq ↦ ?_⟩
  linarith [dist_triangle p x q, mem_closedBall.1 hp.1, dist_comm q x, mem_closedBall.1 hq.1]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem dist_lt_of_mem_ball_inter {ν x y : E} {r : ℝ} (hy : y ∈ ball x r ∩ halfSpace ν) :
    dist y x < r := mem_ball.1 hy.1

/-- **Local Hölder continuity of the gradient** (qualitative): near each point of
`ball x r ∩ halfSpace ν`, `∇_B w` is `α`-Hölder and bounded on `halfBall ν y₀ (4ρ)`, with
`ρ ≤ ρ₀` and `halfBall ν y₀ (4ρ) ⊆ B`. -/
theorem exists_local_gradient_holder {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν x : E} {r : ℝ}
    (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) {lam Λ : ℝ} (hlam : 0 < lam)
    {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r)) (hsym : IsSymmetricOn a (halfBall ν x r))
    (ha : ContDiffOn ℝ 1 a (halfBall ν x r)) (hG : ContDiffOn ℝ 1 G (halfBall ν x r))
    (hf : Continuous f) (h : IsConormalSolOn ν a G f x r w) {y₀ : E}
    (hy₀ : y₀ ∈ ball x r ∩ halfSpace ν) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ dist y₀ x + 4 * ρ ≤ r ∧
      ∃ Hw : ℝ≥0, HolderOnWith Hw α (gradientWithin w (halfBall ν x r)) (halfBall ν y₀ (4 * ρ)) ∧
        ∃ M : ℝ, ∀ y ∈ halfBall ν y₀ (4 * ρ), ‖gradientWithin w (halfBall ν x r) y‖ ≤ M := by
  set B := halfBall ν x r with hB
  have hd := dist_lt_of_mem_ball_inter hy₀
  set s : ℝ := min (8 * ρ₀) ((r - dist y₀ x) / 2) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by linarith)
  have hs1 : s ≤ 8 * ρ₀ := min_le_left _ _
  have hs2 : s ≤ (r - dist y₀ x) / 2 := min_le_right _ _
  have hy₀ν : 0 ≤ ⟪y₀, ν⟫ := hy₀.2
  have hy₀s : -s < ⟪y₀, ν⟫ := by linarith
  have hsub : closedBall y₀ s ⊆ closedBall x r := closedBall_subset_closedBall' (by linarith)
  have hsub' : ball y₀ s ⊆ ball x r := ball_subset_ball' (by linarith)
  have hBs : halfBall ν y₀ s ⊆ B := inter_subset_inter_left _ hsub
  obtain ⟨-, Ka, hKa⟩ := exists_bound_holderOnWith_of_contDiffOn_halfBall hν hr hx ha hα1.le
  obtain ⟨-, KG, hKG⟩ := exists_bound_holderOnWith_of_contDiffOn_halfBall hν hr hx hG hα1.le
  obtain ⟨Mf, hMf⟩ := (isCompact_halfBall ν y₀ s).exists_bound_of_continuousOn hf.continuousOn
  have hres := h.restrict_halfBall hν hs0 hy₀s hsub hsub'
  obtain ⟨-, Cq, hCq⟩ := Div.contDiffHolderOn_one_halfBall_of_isConormalSolution E α hα hα1 ν y₀
    s lam Λ Ka KG Mf a G f w hν hs0 hy₀s hlam (hell.mono hBs) (hsym.mono hBs) (hKa.mono hBs)
    (hKG.mono hBs) hf.aestronglyMeasurable.restrict (fun y hy ↦ hMf y hy) hres
  set S' := halfBall ν y₀ (s / 2) with hS'
  have hS'B : S' ⊆ B := (halfBall_mono ν y₀ (by linarith)).trans hBs
  have huS' : UniqueDiffOn ℝ S' := uniqueDiffOn_halfBall hν (by positivity) (by linarith)
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hHol : HolderOnWith Cq α (gradientWithin w B) S' := by
    refine holderOnWith_iff_dist_le.2 fun p hp q hq ↦ ?_
    rw [← dist_fderivWithin_eq_dist_gradientWithin,
      ← fderivWithin_subset hS'B (huS' p hp) (hwB p (hS'B hp)),
      ← fderivWithin_subset hS'B (huS' q hq) (hwB q (hS'B hq)),
      ← dist_iteratedFDerivWithin_one w w (huS' p hp) (huS' q hq)]
    exact hCq.dist_le hp hq
  refine ⟨s / 8, by positivity, by linarith, by linarith, Cq, ?_, ?_⟩
  · rw [show 4 * (s / 8) = s / 2 by ring]; exact hHol
  · rw [show 4 * (s / 8) = s / 2 by ring]
    obtain ⟨M, hM⟩ := (isCompact_halfBall ν y₀ (s / 2)).exists_bound_of_continuousOn
      ((continuousOn_gradientWithin_halfBall hν hr hx h.1).mono hS'B)
    exact ⟨M, hM⟩

/-- **Directional second derivatives for the linear problem** (see the module docstring): for
`‖e‖ ≤ 1`, either tangential or with `closedBall z (3ρ)` inside the half space, `∂_e w` has an
`α`-Hölder within-derivative on `halfBall ν z (ρ/4)`. -/
theorem exists_directional_of_linear {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν x : E} {r : ℝ}
    (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) {lam Λ : ℝ} (hlam : 0 < lam)
    {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r)) (hsym : IsSymmetricOn a (halfBall ν x r))
    (ha : ContDiffOn ℝ 1 a (halfBall ν x r)) {Kda : ℝ≥0}
    (hDa : HolderOnWith Kda α (fderivWithin ℝ a (halfBall ν x r)) (halfBall ν x r))
    (hG : ContDiffOn ℝ 1 G (halfBall ν x r)) {Kdg : ℝ≥0}
    (hDG : HolderOnWith Kdg α (fderivWithin ℝ G (halfBall ν x r)) (halfBall ν x r))
    (hf : Continuous f) {Kf : ℝ≥0} (hfH : HolderOnWith Kf α f (halfBall ν x r))
    (h : IsConormalSolOn ν a G f x r w) {z : E} {ρ : ℝ} (hρ : 0 < ρ) (hz : 0 ≤ ⟪z, ν⟫)
    (hzr : dist z x + 4 * ρ ≤ r) {Hw : ℝ≥0}
    (hHw : HolderOnWith Hw α (gradientWithin w (halfBall ν x r)) (halfBall ν z (4 * ρ)))
    {M : ℝ} (hM : ∀ y ∈ halfBall ν z (4 * ρ), ‖gradientWithin w (halfBall ν x r) y‖ ≤ M)
    {e : E} (he : ‖e‖ ≤ 1) (hHe : ⟪e, ν⟫ = 0 ∨ closedBall z (3 * ρ) ⊆ halfSpace ν) :
    ∃ g : E → E →L[ℝ] ℝ, (∀ y ∈ halfBall ν z (ρ / 4),
      HasFDerivWithinAt (fun y ↦ fderivWithin ℝ w (halfBall ν x r) y e) (g y)
        (halfBall ν z (ρ / 4)) y) ∧
      ∃ H : ℝ, 0 ≤ H ∧ ∀ y ∈ halfBall ν z (ρ / 4), ∀ y' ∈ halfBall ν z (ρ / 4),
        ‖g y - g y'‖ ≤ H * dist y y' ^ (α : ℝ) := by
  set B := halfBall ν x r with hB
  set S4 := halfBall ν z (4 * ρ) with hS4
  set B2 := halfBall ν z (2 * ρ) with hB2
  have hBc := convex_halfBall ν x r
  have hBu := uniqueDiffOn_halfBall hν hr hx
  obtain ⟨⟨MDa, hMDa⟩, Ka, hKa⟩ :=
    exists_bound_holderOnWith_of_contDiffOn_halfBall hν hr hx ha hα1.le
  obtain ⟨⟨MDG, hMDG⟩, -, -⟩ :=
    exists_bound_holderOnWith_of_contDiffOn_halfBall hν hr hx hG hα1.le
  obtain ⟨Mf, hMf⟩ := (isCompact_halfBall ν x r).exists_bound_of_continuousOn hf.continuousOn
  have hzS4 : z ∈ S4 := ⟨mem_closedBall_self (by positivity), hz⟩
  have hball4 : closedBall z (4 * ρ) ⊆ closedBall x r := closedBall_subset_closedBall' (by linarith)
  have hS4B : S4 ⊆ B := inter_subset_inter_left _ hball4
  have hzB : z ∈ B := hS4B hzS4
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hzS4)
  have hMDa0 : 0 ≤ MDa := (norm_nonneg _).trans (hMDa z hzB)
  have hMDG0 : 0 ≤ MDG := (norm_nonneg _).trans (hMDG z hzB)
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf z hzB)
  -- compatibility of translations with the half space
  have hcompat : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ closedBall z (2 * ρ),
      (0 ≤ ⟪t • e + y, ν⟫ ↔ 0 ≤ ⟪y, ν⟫) := by
    intro t ht y hy
    have hdt : dist (t • e + y) y ≤ ρ := by
      rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht.1.le]
      nlinarith [ht.2, norm_nonneg e, ht.1]
    rcases hHe with he0 | hball
    · rw [inner_add_left, real_inner_smul_left, he0, mul_zero, zero_add]
    · have h1 : y ∈ halfSpace ν := hball (closedBall_subset_closedBall (by linarith) hy)
      have h2 : t • e + y ∈ halfSpace ν := hball (by
        rw [mem_closedBall]; linarith [dist_triangle (t • e + y) y z, mem_closedBall.1 hy])
      exact ⟨fun _ ↦ h1, fun _ ↦ h2⟩
  have htr : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ B2, t • e + y ∈ S4 := by
    intro t ht y hy
    refine ⟨?_, (hcompat t ht y hy.1).2 hy.2⟩
    rw [mem_closedBall]
    have : dist (t • e + y) y ≤ ρ := by
      rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht.1.le]
      nlinarith [ht.2, norm_nonneg e, ht.1]
    linarith [dist_triangle (t • e + y) y z, (mem_closedBall.1 hy.1)]
  have hB2S4 : B2 ⊆ S4 := halfBall_mono ν z (by linarith)
  have hσI : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ σ ∈ Ι (0 : ℝ) t, σ ∈ Ioc (0 : ℝ) ρ := fun t ht σ hσ ↦ by
    rw [uIoc_of_le ht.1.le] at hσ; exact ⟨hσ.1, hσ.2.trans ht.2⟩
  have hte : ∀ t ∈ Ioc (0 : ℝ) ρ, ‖t • e‖ ≤ t := fun t ht ↦ by
    rw [norm_smul, Real.norm_of_nonneg ht.1.le]; nlinarith [norm_nonneg e, ht.1]
  -- the flux of the difference-quotient problem
  set P : ℝ → E → ℝ := fun t y ↦ ∫ σ in (0 : ℝ)..t, f (σ • e + y) with hP
  set Gt : ℝ → E → E := fun t y ↦ G (t • e + y) - G y -
    (a (t • e + y) - a y) (gradientWithin w B (t • e + y)) - P t y • e with hGt
  set K₁ : ℝ := Kdg + Kda * M + MDa * Hw + Kf with hK₁
  set K₂ : ℝ := MDG + MDa * M + Mf with hK₂
  have hDGd : ∀ p ∈ B, HasFDerivWithinAt G (fderivWithin ℝ G B p) B p := fun p hp ↦
    (hG.differentiableOn one_ne_zero p hp).hasFDerivWithinAt
  have hDad : ∀ p ∈ B, HasFDerivWithinAt a (fderivWithin ℝ a B p) B p := fun p hp ↦
    (ha.differentiableOn one_ne_zero p hp).hasFDerivWithinAt
  have hGtH : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ B2, ∀ y' ∈ B2,
      ‖Gt t y - Gt t y'‖ ≤ t * K₁ * dist y y' ^ (α : ℝ) := by
    intro t ht y hy y' hy'
    have hyB := hS4B (hB2S4 hy)
    have hy'B := hS4B (hB2S4 hy')
    have htyS := htr t ht y hy
    have hty'S := htr t ht y' hy'
    have hd0 : 0 ≤ dist y y' ^ (α : ℝ) := Real.rpow_nonneg dist_nonneg _
    have hdt : dist (t • e + y) (t • e + y') = dist y y' := dist_add_left _ _ _
    -- the three pieces
    have t1 := norm_translate_sub_sub_le hBc hDGd hDG hyB hy'B (hS4B htyS) (hS4B hty'S)
    have t1' : ‖(G (t • e + y) - G y) - (G (t • e + y') - G y')‖ ≤
        t * Kdg * dist y y' ^ (α : ℝ) := by
      refine t1.trans ?_
      calc (Kdg : ℝ) * dist y y' ^ (α : ℝ) * ‖t • e‖ ≤ Kdg * dist y y' ^ (α : ℝ) * t := by
            gcongr; exact hte t ht
        _ = t * Kdg * dist y y' ^ (α : ℝ) := by ring
    have tA := norm_translate_sub_sub_le hBc hDad hDa hyB hy'B (hS4B htyS) (hS4B hty'S)
    have tA' : ‖(a (t • e + y) - a y) - (a (t • e + y') - a y')‖ ≤
        t * Kda * dist y y' ^ (α : ℝ) := by
      refine tA.trans ?_
      calc (Kda : ℝ) * dist y y' ^ (α : ℝ) * ‖t • e‖ ≤ Kda * dist y y' ^ (α : ℝ) * t := by
            gcongr; exact hte t ht
        _ = t * Kda * dist y y' ^ (α : ℝ) := by ring
    have tAb : ‖a (t • e + y') - a y'‖ ≤ MDa * t :=
      (norm_translate_sub_le hBc hDad hMDa hy'B (hS4B hty'S)).trans
        (mul_le_mul_of_nonneg_left (hte t ht) hMDa0)
    have tV : ‖gradientWithin w B (t • e + y) - gradientWithin w B (t • e + y')‖ ≤
        Hw * dist y y' ^ (α : ℝ) := by
      rw [← dist_eq_norm, ← hdt]; exact hHw.dist_le htyS hty'S
    have tVb : ‖gradientWithin w B (t • e + y)‖ ≤ M := hM _ htyS
    have t2 : ‖(a (t • e + y) - a y) (gradientWithin w B (t • e + y)) -
        (a (t • e + y') - a y') (gradientWithin w B (t • e + y'))‖ ≤
        t * (Kda * M + MDa * Hw) * dist y y' ^ (α : ℝ) := by
      set A := a (t • e + y) - a y
      set A' := a (t • e + y') - a y'
      set V := gradientWithin w B (t • e + y)
      set V' := gradientWithin w B (t • e + y')
      have e2 : A V - A' V' = (A - A') V + A' (V - V') := by
        simp only [sub_apply, map_sub]; abel
      rw [e2]
      calc ‖(A - A') V + A' (V - V')‖ ≤ ‖A - A'‖ * ‖V‖ + ‖A'‖ * ‖V - V'‖ :=
            (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
              (ContinuousLinearMap.le_opNorm _ _))
        _ ≤ (t * Kda * dist y y' ^ (α : ℝ)) * M + (MDa * t) * (Hw * dist y y' ^ (α : ℝ)) :=
            add_le_add (mul_le_mul tA' tVb (norm_nonneg _)
                (mul_nonneg (mul_nonneg ht.1.le Kda.2) (Real.rpow_nonneg dist_nonneg _)))
              (mul_le_mul tAb tV (norm_nonneg _) (mul_nonneg hMDa0 ht.1.le))
        _ = t * (Kda * M + MDa * Hw) * dist y y' ^ (α : ℝ) := by ring
    have t3 := abs_primitive_sub_le hf hfH (e := e) (y := y) (y' := y') (t := t)
      fun σ hσ ↦ ⟨hS4B (htr σ (hσI t ht σ hσ) y hy), hS4B (htr σ (hσI t ht σ hσ) y' hy')⟩
    have t3' : ‖P t y • e - P t y' • e‖ ≤ t * Kf * dist y y' ^ (α : ℝ) := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      calc |P t y - P t y'| * ‖e‖ ≤ |P t y - P t y'| * 1 := by gcongr
        _ ≤ |t| * (Kf * dist y y' ^ (α : ℝ)) := by rw [mul_one]; exact t3
        _ = t * Kf * dist y y' ^ (α : ℝ) := by rw [abs_of_pos ht.1]; ring
    have e3 : Gt t y - Gt t y' =
        ((G (t • e + y) - G y) - (G (t • e + y') - G y')) -
        ((a (t • e + y) - a y) (gradientWithin w B (t • e + y)) -
          (a (t • e + y') - a y') (gradientWithin w B (t • e + y'))) -
        (P t y • e - P t y' • e) := by
      simp only [hGt]; abel
    rw [e3]
    calc _ ≤ ‖(G (t • e + y) - G y) - (G (t • e + y') - G y')‖ +
          ‖(a (t • e + y) - a y) (gradientWithin w B (t • e + y)) -
            (a (t • e + y') - a y') (gradientWithin w B (t • e + y'))‖ +
          ‖P t y • e - P t y' • e‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ t * Kdg * dist y y' ^ (α : ℝ) + t * (Kda * M + MDa * Hw) * dist y y' ^ (α : ℝ) +
          t * Kf * dist y y' ^ (α : ℝ) := add_le_add (add_le_add t1' t2) t3'
      _ = t * K₁ * dist y y' ^ (α : ℝ) := by rw [hK₁]; ring
  have hGtb : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ B2, ‖Gt t y‖ ≤ t * K₂ := by
    intro t ht y hy
    have hyB := hS4B (hB2S4 hy)
    have htyS := htr t ht y hy
    have b1 : ‖G (t • e + y) - G y‖ ≤ MDG * t :=
      (norm_translate_sub_le hBc hDGd hMDG hyB (hS4B htyS)).trans
        (mul_le_mul_of_nonneg_left (hte t ht) hMDG0)
    have b2 : ‖(a (t • e + y) - a y) (gradientWithin w B (t • e + y))‖ ≤ MDa * t * M := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      refine mul_le_mul ((norm_translate_sub_le hBc hDad hMDa hyB (hS4B htyS)).trans
          (mul_le_mul_of_nonneg_left (hte t ht) hMDa0)) (hM _ htyS) (norm_nonneg _)
        (mul_nonneg hMDa0 ht.1.le)
    have b3 : ‖P t y • e‖ ≤ t * Mf := by
      rw [norm_smul, Real.norm_eq_abs]
      have := abs_primitive_le (f := f) (S := B) (Mf := Mf) (fun p hp ↦ hMf p hp) (e := e)
        (y := y) (t := t) fun σ hσ' ↦ hS4B (htr σ (hσI t ht σ hσ') y hy)
      rw [abs_of_pos ht.1] at this
      calc |P t y| * ‖e‖ ≤ |P t y| * 1 := by gcongr
        _ ≤ t * Mf := by rw [mul_one]; exact this
    calc ‖Gt t y‖ ≤ ‖G (t • e + y) - G y‖ +
          ‖(a (t • e + y) - a y) (gradientWithin w B (t • e + y))‖ + ‖P t y • e‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ MDG * t + MDa * t * M + t * Mf := add_le_add (add_le_add b1 b2) b3
      _ = t * K₂ := by rw [hK₂]; ring
  have hlin : ∀ t ∈ Ioc (0 : ℝ) ρ,
      IsConormalSolOn ν a (Gt t) 0 z (2 * ρ) (fun y ↦ w (t • e + y) - w y) := by
    intro t ht
    have hte' : |t| * ‖e‖ ≤ ρ := by
      rw [abs_of_pos ht.1]; nlinarith [norm_nonneg e, ht.1, ht.2]
    refine h.translate_sub hν hr hx ha.continuousOn hG.continuousOn hf (fun _ _ ↦ rfl)
      (hHe.imp id fun hb ↦ (closedBall_subset_closedBall (by linarith)).trans hb)
      (by positivity) hz (by linarith)
  exact exists_hasFDerivWithinAt_fderivWithin_apply_of_linear hα hα1 hν hlam h.1 hρ hz hzr
    (hell.mono (hB2S4.trans hS4B)) (hsym.mono (hB2S4.trans hS4B))
    (hKa.mono (hB2S4.trans hS4B)) hHw hM he hcompat (by positivity) hGtH hGtb hlin

/-- **Interior `C²`** for the linear problem. -/
theorem contDiffOn_two_interior_of_linear {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν x : E}
    {r : ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) {lam Λ : ℝ} (hlam : 0 < lam)
    {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r)) (hsym : IsSymmetricOn a (halfBall ν x r))
    (ha : ContDiffOn ℝ 1 a (halfBall ν x r)) {Kda : ℝ≥0}
    (hDa : HolderOnWith Kda α (fderivWithin ℝ a (halfBall ν x r)) (halfBall ν x r))
    (hG : ContDiffOn ℝ 1 G (halfBall ν x r)) {Kdg : ℝ≥0}
    (hDG : HolderOnWith Kdg α (fderivWithin ℝ G (halfBall ν x r)) (halfBall ν x r))
    (hf : Continuous f) {Kf : ℝ≥0} (hfH : HolderOnWith Kf α f (halfBall ν x r))
    (h : IsConormalSolOn ν a G f x r w) :
    ContDiffOn ℝ 2 w (ball x r ∩ openHalfSpace ν) := by
  intro y₀ hy₀
  have hpos : 0 < ⟪y₀, ν⟫ := hy₀.2
  obtain ⟨ρ, hρ, hρ₀, hdist, Hw, hHw, M, hM⟩ := exists_local_gradient_holder hα hα1 hν hr hx
    hlam hell hsym ha hG hf h ⟨hy₀.1, mem_halfSpace.2 hpos.le⟩ (ρ₀ := ⟪y₀, ν⟫ / 8)
    (by positivity)
  have hinner : ∀ y ∈ closedBall y₀ (4 * ρ), 0 < ⟪y, ν⟫ := by
    intro y hy
    have h1 : |⟪y - y₀, ν⟫| ≤ dist y y₀ := by
      rw [dist_eq_norm]; exact (abs_real_inner_le_norm _ _).trans (by rw [hν, mul_one])
    have h2 : ⟪y - y₀, ν⟫ = ⟪y, ν⟫ - ⟪y₀, ν⟫ := inner_sub_left _ _ _
    linarith [(abs_le.1 h1).1, mem_closedBall.1 hy]
  have hball3 : closedBall y₀ (3 * ρ) ⊆ halfSpace ν := fun y hy ↦
    mem_halfSpace.2 (hinner y (closedBall_subset_closedBall (by linarith) hy)).le
  set b := stdOrthonormalBasis ℝ E
  have hdir : ∀ i, ∃ g : E → E →L[ℝ] ℝ, (∀ y ∈ halfBall ν y₀ (ρ / 4),
      HasFDerivWithinAt (fun y ↦ fderivWithin ℝ w (halfBall ν x r) y (b i)) (g y)
        (halfBall ν y₀ (ρ / 4)) y) ∧
      ∃ H : ℝ, 0 ≤ H ∧ ∀ y ∈ halfBall ν y₀ (ρ / 4), ∀ y' ∈ halfBall ν y₀ (ρ / 4),
        ‖g y - g y'‖ ≤ H * dist y y' ^ (α : ℝ) := fun i ↦
    exists_directional_of_linear hα hα1 hν hr hx hlam hell hsym ha hDa hG hDG hf hfH h hρ
      hpos.le hdist hHw hM (b.orthonormal.1 i).le (Or.inr hball3)
  choose g hg H hH0 hH using hdir
  set S := halfBall ν y₀ (ρ / 4) with hS
  set O := ball y₀ (ρ / 4) with hO
  have hOS : O ⊆ S := fun y hy ↦ ⟨ball_subset_closedBall hy, mem_halfSpace.2
    (hinner y (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy))).le⟩
  have hOB : O ⊆ halfBall ν x r := fun y hy ↦ by
    refine ⟨?_, mem_halfSpace.2
      (hinner y (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy))).le⟩
    rw [mem_closedBall]
    linarith [dist_triangle y y₀ x, mem_ball.1 hy]
  set D := fderivWithin ℝ w (halfBall ν x r) with hD
  set Hs : E → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦ ∑ i, (g i y).smulRight (innerSL ℝ (b i))
  have hc : ContDiffOn ℝ 2 w O := by
    refine contDiffOn_two_of_hasFDerivWithinAt isOpen_ball.uniqueDiffOn (D := D) (Hs := Hs)
      (fun y hy ↦ ((h.1.differentiableOn one_ne_zero y (hOB hy)).hasFDerivWithinAt).mono hOB)
      (fun y hy ↦ hasFDerivWithinAt_of_orthonormalBasis b fun i ↦
        ((hg i y (hOS hy)).mono hOS)) ?_
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    have hgc := continuousOn_of_norm_sub_le (by exact_mod_cast hα) (hH0 i) (hH i)
    exact ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).flip
      (innerSL ℝ (b i))).continuous.comp_continuousOn (hgc.mono hOS)
  exact (hc.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))).contDiffWithinAt

/-! ### The equation in nondivergence form -/

/-- **From the weak form to the pointwise equation**: if `V` is `C¹` on an open `Ω`, `g` is
continuous on `Ω`, and `∫ ⟪V, ∇φ⟫ = ∫ g φ` for all smooth `φ` compactly supported in `Ω`, then
`-div V = g` on `Ω` (integration by parts and the fundamental lemma). -/
theorem neg_divergence_eq_of_weak {Ω : Set E} (hΩo : IsOpen Ω) {V : E → E}
    {V' : E → E →L[ℝ] E} (hV : ∀ z ∈ Ω, HasFDerivAt V (V' z) z)
    (hV'c : ∀ v, ContinuousOn (fun z ↦ V' z v) Ω) {g : E → ℝ} (hg : ContinuousOn g Ω)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ z, ⟪V z, ∇ φ z⟫ = ∫ z, g z * φ z)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {y : E} (hy : y ∈ Ω) :
    -∑ j, ⟪b j, V' y (b j)⟫ = g y := by
  set term : ι → E → ℝ := fun j z ↦ ⟪b j, V' z (b j)⟫ with hterm
  have hVj : ∀ j, ∀ z ∈ Ω, HasFDerivAt (fun z ↦ ⟪b j, V z⟫) (innerSL ℝ (b j) ∘L V' z) z :=
    fun j z hz ↦ (innerSL ℝ (b j)).hasFDerivAt.comp z (hV z hz)
  have hVc : ∀ j, ContinuousOn (fun z ↦ ⟪b j, V z⟫) Ω := fun j z hz ↦
    (hVj j z hz).continuousAt.continuousWithinAt
  have hterm_c : ∀ j, ContinuousOn (term j) Ω := fun j ↦
    continuousOn_const.inner (hV'c (b j))
  set F : E → ℝ := fun z ↦ -(∑ j, term j z) - g z with hF
  have hFc : ContinuousOn F Ω :=
    ((continuousOn_finsetSum _ fun j _ ↦ hterm_c j).neg).sub hg
  have hzero : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ z, φ z • F z = 0 := by
    intro φ hφ hφc hφs
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
    have hw := hweak φ hφ hφc hφs
    have hφ0 : ∀ z, z ∉ tsupport φ → φ z = 0 := fun z hz ↦ image_eq_zero_of_notMem_tsupport hz
    have hpt : ∀ z, ⟪V z, ∇ φ z⟫ = ∑ j, ⟪b j, V z⟫ * fderiv ℝ φ z (b j) := by
      intro z
      rw [← b.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [real_inner_comm (b j) (V z)]
      congr 1
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hfd : ∀ j, Continuous fun z ↦ fderiv ℝ φ z (b j) := fun j ↦
      (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hint1 : ∀ j, Integrable fun z ↦ ⟪b j, V z⟫ * fderiv ℝ φ z (b j) := fun j ↦
      integrable_mul_of_tsupport_subset hΩo (hVc j) (hfd j) (hφc.fderiv_apply (𝕜 := ℝ) (b j))
        ((tsupport_fderiv_apply_subset ℝ (b j)).trans hφs)
    have hint2 : ∀ j, Integrable fun z ↦ term j z * φ z := fun j ↦
      integrable_mul_of_tsupport_subset hΩo (hterm_c j) hφd.continuous hφc hφs
    have hint3 : ∀ j, Integrable fun z ↦ ⟪b j, V z⟫ * φ z := fun j ↦
      integrable_mul_of_tsupport_subset hΩo (hVc j) hφd.continuous hφc hφs
    have hintg : Integrable fun z ↦ g z * φ z :=
      integrable_mul_of_tsupport_subset hΩo hg hφd.continuous hφc hφs
    have hfdV : ∀ j z, fderiv ℝ (fun z ↦ ⟪b j, V z⟫) z (b j) * φ z = term j z * φ z := by
      intro j z
      by_cases hz : z ∈ tsupport φ
      · rw [(hVj j z (hφs hz)).fderiv]
        rfl
      · rw [hφ0 z hz, mul_zero, mul_zero]
    have hibp : ∀ j, ∫ z, ⟪b j, V z⟫ * fderiv ℝ φ z (b j) = -∫ z, term j z * φ z := by
      intro j
      have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
        (f := fun z ↦ ⟪b j, V z⟫) (g := φ) (v := b j)
        ((hint2 j).congr (Eventually.of_forall fun z ↦ (hfdV j z).symm)) (hint1 j) (hint3 j)
        (fun z hz ↦ (hVj j z (hφs hz)).differentiableAt) (fun z _ ↦ hφd z)
      rw [this]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun z ↦ hfdV j z)
    have e1 : ∫ z, ⟪V z, ∇ φ z⟫ = ∑ j, ∫ z, ⟪b j, V z⟫ * fderiv ℝ φ z (b j) := by
      rw [← integral_finsetSum _ fun j _ ↦ hint1 j]
      exact integral_congr_ae (Eventually.of_forall fun z ↦ hpt z)
    simp only [hibp, Finset.sum_neg_distrib] at e1
    rw [← integral_finsetSum _ fun j _ ↦ hint2 j] at e1
    have hsum : Integrable fun z ↦ ∑ j, term j z * φ z := integrable_finsetSum _ fun j _ ↦ hint2 j
    have e2 : ∫ z, φ z • F z = -(∫ z, ∑ j, term j z * φ z) - ∫ z, g z * φ z := by
      have hsumn : Integrable fun z ↦ -∑ j, term j z * φ z := hsum.neg
      rw [← integral_neg, ← integral_sub hsumn hintg]
      refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
      simp only [hF, smul_eq_mul]
      rw [← Finset.sum_mul]
      ring
    rw [e2, ← e1, hw, sub_self]
  have hae := hΩo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hFc.locallyIntegrableOn hΩo.measurableSet) hzero
  have heq := Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hΩo.measurableSet).2 hae) hΩo
    hFc continuousOn_const
  have hy0 : F y = 0 := heq hy
  simp only [hF] at hy0
  linarith

/-- **The linear equation in nondivergence form in the interior**: with
`R = -f - Σ_j ⟪b_j, (Da b_j) ∇w⟫ + Σ_j ⟪b_j, DG b_j⟫` (derivatives within `B`),
`Σ_j D²w(b_j, a b_j) = R` on `ball x r ∩ openHalfSpace ν`. -/
theorem sum_hessian_coeff_eq {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν x : E} {r : ℝ}
    (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) {lam Λ : ℝ} (hlam : 0 < lam)
    {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r)) (hsym : IsSymmetricOn a (halfBall ν x r))
    (ha : ContDiffOn ℝ 1 a (halfBall ν x r)) {Kda : ℝ≥0}
    (hDa : HolderOnWith Kda α (fderivWithin ℝ a (halfBall ν x r)) (halfBall ν x r))
    (hG : ContDiffOn ℝ 1 G (halfBall ν x r)) {Kdg : ℝ≥0}
    (hDG : HolderOnWith Kdg α (fderivWithin ℝ G (halfBall ν x r)) (halfBall ν x r))
    (hf : Continuous f) {Kf : ℝ≥0} (hfH : HolderOnWith Kf α f (halfBall ν x r))
    (h : IsConormalSolOn ν a G f x r w) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {y : E} (hy : y ∈ ball x r ∩ openHalfSpace ν) :
    ∑ j, fderiv ℝ (fderiv ℝ w) y (b j) (a y (b j)) =
      -f y - ∑ j, ⟪b j, fderivWithin ℝ a (halfBall ν x r) y (b j)
          (gradientWithin w (halfBall ν x r) y)⟫ +
        ∑ j, ⟪b j, fderivWithin ℝ G (halfBall ν x r) y (b j)⟫ := by
  set Ω := ball x r ∩ openHalfSpace ν with hΩ
  have hΩo : IsOpen Ω := isOpen_ball.inter (isOpen_openHalfSpace ν)
  set B := halfBall ν x r with hB
  have hΩB : Ω ⊆ B := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, mem_halfSpace.2 (mem_openHalfSpace.1 hz.2).le⟩
  have hBn : ∀ z ∈ Ω, B ∈ 𝓝 z := fun z hz ↦ mem_of_superset (hΩo.mem_nhds hz) hΩB
  have hBu : UniqueDiffOn ℝ B := uniqueDiffOn_halfBall hν hr hx
  have hC2 := contDiffOn_two_interior_of_linear hα hα1 hν hr hx hlam hell hsym ha hDa hG hDG
    hf hfH h
  have hD1 : ContDiffOn ℝ 1 (fun z ↦ fderiv ℝ w z) Ω := hC2.fderiv_of_isOpen hΩo (by norm_num)
  have hD2c : ContinuousOn (fun z ↦ fderiv ℝ (fun z ↦ fderiv ℝ w z) z) Ω :=
    hD1.continuousOn_fderiv_of_isOpen hΩo le_rfl
  have hgr : ∀ z ∈ Ω, ∇ w z = gradientWithin w B z := fun z hz ↦
    (gradientWithin_halfBall_eq hz).symm
  set T : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap with hT
  have hTa : ∀ ℓ, T ℓ = (InnerProductSpace.toDual ℝ E).symm ℓ := fun _ ↦ rfl
  have hgradD : ∀ z ∈ Ω, HasFDerivAt (fun z ↦ ∇ w z)
      (T ∘L fderiv ℝ (fun z ↦ fderiv ℝ w z) z) z := fun z hz ↦
    T.hasFDerivAt.comp z ((hD1.differentiableOn one_ne_zero z hz).differentiableAt
      (hΩo.mem_nhds hz)).hasFDerivAt
  have haD : ∀ z ∈ Ω, HasFDerivAt a (fderivWithin ℝ a B z) z := fun z hz ↦ by
    rw [fderivWithin_of_mem_nhds (hBn z hz)]
    exact ((ha.differentiableOn one_ne_zero z (hΩB hz)).differentiableAt (hBn z hz)).hasFDerivAt
  have hGD : ∀ z ∈ Ω, HasFDerivAt G (fderivWithin ℝ G B z) z := fun z hz ↦ by
    rw [fderivWithin_of_mem_nhds (hBn z hz)]
    exact ((hG.differentiableOn one_ne_zero z (hΩB hz)).differentiableAt (hBn z hz)).hasFDerivAt
  set V : E → E := fun z ↦ a z (∇ w z) - G z with hVdef
  set V' : E → E →L[ℝ] E := fun z ↦
    (a z).comp (T ∘L fderiv ℝ (fun z ↦ fderiv ℝ w z) z) + (fderivWithin ℝ a B z).flip (∇ w z) -
      fderivWithin ℝ G B z with hV'def
  have hV : ∀ z ∈ Ω, HasFDerivAt V (V' z) z := fun z hz ↦
    ((haD z hz).clm_apply (hgradD z hz)).sub (hGD z hz)
  have hgc : ContinuousOn (fun z ↦ ∇ w z) Ω := fun z hz ↦
    (hgradD z hz).continuousAt.continuousWithinAt
  have hV'c : ∀ v, ContinuousOn (fun z ↦ V' z v) Ω := by
    intro v
    have e : (fun z ↦ V' z v) = fun z ↦ a z (T (fderiv ℝ (fun z ↦ fderiv ℝ w z) z v)) +
        fderivWithin ℝ a B z v (∇ w z) - fderivWithin ℝ G B z v := by
      funext z
      simp only [hV'def, sub_apply, add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.flip_apply]
    rw [e]
    refine ((((ha.continuousOn.mono hΩB).clm_apply
      (T.continuous.comp_continuousOn (hD2c.clm_apply continuousOn_const))).add
      ((((ha.continuousOn_fderivWithin hBu le_rfl).mono hΩB).clm_apply
        continuousOn_const).clm_apply hgc)).sub
      (((hG.continuousOn_fderivWithin hBu le_rfl).mono hΩB).clm_apply continuousOn_const))
  have hweak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ z, ⟪V z, ∇ φ z⟫ = ∫ z, f z * φ z := by
    intro φ hφ hφc hφs
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have hφt : IsTestFn (ball x r) φ := ⟨hφ1, hφc, hφs.trans fun z hz ↦ hz.1⟩
    have key := h.2 φ hφt
    have h0 : ∀ z, z ∉ tsupport φ → φ z = 0 ∧ ∇ φ z = 0 := fun z hz ↦
      IsTestFn.eq_zero_and_gradient_eq_zero (U := tsupport φ) ⟨hφ1, hφc, subset_rfl⟩ hz
    have hφc' : Continuous (∇ φ) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ1.continuous_fderiv one_ne_zero)
    have hBc := isCompact_halfBall ν x r
    have hgB := continuousOn_gradientWithin_halfBall hν hr hx h.1
    have i1 : IntegrableOn (fun z ↦ ⟪a z (gradientWithin w B z), ∇ φ z⟫) B :=
      ContinuousOn.integrableOn_compact hBc
        ((ha.continuousOn.clm_apply hgB).inner hφc'.continuousOn)
    have i2 : IntegrableOn (fun z ↦ ⟪G z, ∇ φ z⟫) B :=
      ContinuousOn.integrableOn_compact hBc (hG.continuousOn.inner hφc'.continuousOn)
    have eV : ∫ z, ⟪V z, ∇ φ z⟫ =
        ∫ z in B, (⟪a z (gradientWithin w B z), ∇ φ z⟫ - ⟪G z, ∇ φ z⟫) := by
      have hcompl : ∀ z, z ∉ B → ⟪V z, ∇ φ z⟫ = 0 := fun z hz ↦ by
        have hzt : z ∉ tsupport φ := fun h' ↦ hz (hΩB (hφs h'))
        simp only [(h0 z hzt).2, inner_zero_right]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) hcompl]
      refine setIntegral_congr_fun (measurableSet_halfBall ν x r) fun z hz ↦ ?_
      by_cases hzt : z ∈ tsupport φ
      · simp only [hVdef, hgr z (hφs hzt), inner_sub_left]
      · simp only [(h0 z hzt).2, inner_zero_right, sub_zero]
    have ef : ∫ z, f z * φ z = ∫ z in B, f z * φ z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
        have hzt : z ∉ tsupport φ := fun h' ↦ hz (hΩB (hφs h'))
        simp [(h0 z hzt).1]).symm
    rw [eV, integral_sub i1 i2, ef]
    change ∫ z in B, ⟪a z (gradientWithin w B z), ∇ φ z⟫ =
      (∫ z in B, ⟪G z, ∇ φ z⟫) + ∫ z in B, f z * φ z at key
    rw [key]; ring
  have key := neg_divergence_eq_of_weak hΩo hV hV'c hf.continuousOn hweak b hy
  have hexp : ∀ j, ⟪b j, V' y (b j)⟫ = fderiv ℝ (fderiv ℝ w) y (b j) (a y (b j)) +
      ⟪b j, fderivWithin ℝ a B y (b j) (gradientWithin w B y)⟫ -
      ⟪b j, fderivWithin ℝ G B y (b j)⟫ := by
    intro j
    simp only [hV'def, sub_apply, add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.flip_apply, inner_sub_right, inner_add_right]
    rw [hgr y hy]
    congr 2
    have hs := hsym y (hΩB hy) (b j) (T (fderiv ℝ (fun z ↦ fderiv ℝ w z) y (b j)))
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [← hs, real_inner_comm, hTa, InnerProductSpace.toDual_symm_apply]
  simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib] at key
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The normal–normal derivative from the equation** (algebra): if `H` is symmetric with
tangential rows `g_i = H(·, b_i - ⟪b_i, ν⟫ ν)` and `Σ_j H(b_j, A b_j) = c` with `A` symmetric and
`⟪A ν, ν⟫ ≠ 0`, then `H(ξ, ν) = Σ_i ⟪b_i, ξ⟫ g_i ν + ⟪ν, ξ⟫ (c - T) / ⟪A ν, ν⟫`, where
`T = Σ_j (Σ_i ⟪b_i, A b_j⟫ g_i b_j + ⟪A b_j, ν⟫ Σ_i ⟪b_i, b_j⟫ g_i ν)` only involves the `g_i`. -/
theorem hessian_apply_normal_of_sum_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {ν : E} (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : ∀ u v, H u v = H v u) {A : E →L[ℝ] E}
    (hA : (A : E →ₗ[ℝ] E).IsSymmetric) (hAν : ⟪A ν, ν⟫ ≠ 0) {c : ℝ}
    (heq : ∑ j, H (b j) (A (b j)) = c) {g : ι → E →L[ℝ] ℝ}
    (hg : ∀ i ξ, g i ξ = H ξ (b i - ⟪b i, ν⟫ • ν)) (ξ : E) :
    H ξ ν = ∑ i, ⟪b i, ξ⟫ * g i ν + ⟪ν, ξ⟫ *
      ((c - ∑ j, (∑ i, ⟪b i, A (b j)⟫ * g i (b j) +
        ⟪A (b j), ν⟫ * ∑ i, ⟪b i, b j⟫ * g i ν)) / ⟪A ν, ν⟫) := by
  have L1 : ∀ ξ η, H ξ η = ∑ i, ⟪b i, η⟫ * g i ξ + ⟪η, ν⟫ * H ξ ν := by
    intro ξ η
    have e1 : H ξ η = ∑ i, ⟪b i, η⟫ * H ξ (b i) := by
      conv_lhs => rw [← b.sum_repr' η]
      simp only [map_sum, map_smul, smul_eq_mul]
    have e2 : ∀ i, H ξ (b i) = g i ξ + ⟪b i, ν⟫ * H ξ ν := fun i ↦ by
      rw [hg i ξ, map_sub, map_smul, smul_eq_mul]; ring
    have e3 : ∑ i, ⟪b i, η⟫ * ⟪b i, ν⟫ = ⟪η, ν⟫ := by
      rw [← b.sum_inner_mul_inner η ν]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm (b i) η]
    rw [e1]
    simp only [e2, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [← e3, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have L2 : ∀ ξ, H ξ ν = ∑ i, ⟪b i, ξ⟫ * g i ν + ⟪ξ, ν⟫ * H ν ν := fun ξ ↦ by
    rw [hH ξ ν, L1 ν ξ]
  have L3 : ∀ ξ η, H ξ η = (∑ i, ⟪b i, η⟫ * g i ξ + ⟪η, ν⟫ * ∑ i, ⟪b i, ξ⟫ * g i ν) +
      ⟪ξ, ν⟫ * ⟪η, ν⟫ * H ν ν := by
    intro ξ η
    rw [L1 ξ η, L2 ξ]; ring
  have hsumA : ∑ j, ⟪b j, ν⟫ * ⟪A (b j), ν⟫ = ⟪A ν, ν⟫ := by
    rw [real_inner_comm, ← b.sum_inner_mul_inner ν (A ν)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hs := hA (b j) ν
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [real_inner_comm (b j) ν, hs]
  have hnn : H ν ν = (c - ∑ j, (∑ i, ⟪b i, A (b j)⟫ * g i (b j) +
      ⟪A (b j), ν⟫ * ∑ i, ⟪b i, b j⟫ * g i ν)) / ⟪A ν, ν⟫ := by
    have heq' : ∑ j, ((∑ i, ⟪b i, A (b j)⟫ * g i (b j) +
        ⟪A (b j), ν⟫ * ∑ i, ⟪b i, b j⟫ * g i ν) + ⟪b j, ν⟫ * ⟪A (b j), ν⟫ * H ν ν) = c := by
      rw [← heq]; exact Finset.sum_congr rfl fun j _ ↦ (L3 _ _).symm
    rw [Finset.sum_add_distrib] at heq'
    have : ∑ j, ⟪b j, ν⟫ * ⟪A (b j), ν⟫ * H ν ν = ⟪A ν, ν⟫ * H ν ν := by
      rw [← hsumA, Finset.sum_mul]
    rw [this] at heq'
    rw [eq_div_iff hAν]
    linarith
  rw [L2 ξ, hnn, real_inner_comm]

/-! ### Up to the flat part -/

/-- **Second derivatives near a point of `ball x r ∩ halfSpace ν`, with a Hölder bound**: there
are `ρ > 0` and `Hs` such that `D_B w` has within-derivative `Hs y` on `halfBall ν y₀ ρ`, and `Hs`
is `α`-Hölder there.

Tangential rows `D(∂_{e_i} w)`, `e_i = b_i - ⟪b_i, ν⟫ ν`, come from
`Div.exists_directional_of_linear`; in the interior of the half ball the equation
(`Div.sum_hessian_coeff_eq`, `Div.hessian_apply_normal_of_sum_eq`) expresses `D(∂_ν w)` through
them and the data, and the formula extends continuously to the flat part
(`hasFDerivWithinAt_closure_of_tendsto_fderiv`). The resulting `Hs` is an algebraic expression in
Hölder functions with the denominator `⟪a ν, ν⟫ ≥ lam`. -/
theorem exists_hessian_halfBall_of_linear {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν x : E}
    {r : ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) {lam Λ : ℝ} (hlam : 0 < lam)
    {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r)) (hsym : IsSymmetricOn a (halfBall ν x r))
    (ha : ContDiffOn ℝ 1 a (halfBall ν x r)) {Kda : ℝ≥0}
    (hDa : HolderOnWith Kda α (fderivWithin ℝ a (halfBall ν x r)) (halfBall ν x r))
    (hG : ContDiffOn ℝ 1 G (halfBall ν x r)) {Kdg : ℝ≥0}
    (hDG : HolderOnWith Kdg α (fderivWithin ℝ G (halfBall ν x r)) (halfBall ν x r))
    (hf : Continuous f) {Kf : ℝ≥0} (hfH : HolderOnWith Kf α f (halfBall ν x r))
    (h : IsConormalSolOn ν a G f x r w) {y₀ : E} (hy₀ : y₀ ∈ ball x r ∩ halfSpace ν) :
    ∃ ρ > 0, ∃ Hs : E → E →L[ℝ] E →L[ℝ] ℝ,
      (∀ y ∈ halfBall ν y₀ ρ, HasFDerivWithinAt (fderivWithin ℝ w (halfBall ν x r)) (Hs y)
        (halfBall ν y₀ ρ) y) ∧
      ∃ C : ℝ≥0, HolderOnWith C α Hs (halfBall ν y₀ ρ) := by
  obtain ⟨ρ, hρ, -, hdist, Hw, hHw, M, hM⟩ := exists_local_gradient_holder hα hα1 hν hr hx
    hlam hell hsym ha hG hf h hy₀ one_pos
  set B := halfBall ν x r with hB
  set S := halfBall ν y₀ (ρ / 4) with hS
  have hy₀ν : 0 ≤ ⟪y₀, ν⟫ := hy₀.2
  have hSB : S ⊆ B := inter_subset_inter_left _ (closedBall_subset_closedBall' (by linarith))
  have huS : UniqueDiffOn ℝ S := uniqueDiffOn_halfBall hν (by positivity) (by linarith)
  have hBu : UniqueDiffOn ℝ B := uniqueDiffOn_halfBall hν hr hx
  have hSc : IsCompact S := isCompact_halfBall ν y₀ (ρ / 4)
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  set b := stdOrthonormalBasis ℝ E with hbdef
  set e : Fin (Module.finrank ℝ E) → E := fun i ↦ b i - ⟪b i, ν⟫ • ν with he
  have hetan : ∀ i, ⟪e i, ν⟫ = 0 := fun i ↦ by
    simp only [he, inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν]
    ring
  have he1 : ∀ i, ‖e i‖ ≤ 1 := fun i ↦ by
    have h1 : ‖e i‖ ^ 2 + ⟪b i, ν⟫ ^ 2 = 1 := by
      have : b i = e i + ⟪b i, ν⟫ • ν := by simp [he]
      have hb1 : ‖b i‖ = 1 := b.orthonormal.1 i
      have h2 : ‖e i + ⟪b i, ν⟫ • ν‖ ^ 2 = ‖e i‖ ^ 2 + ⟪b i, ν⟫ ^ 2 := by
        rw [norm_add_sq_real, norm_smul, hν, real_inner_smul_right, hetan, Real.norm_eq_abs,
          mul_one, sq_abs]
        ring
      rw [← this, hb1] at h2
      linarith
    nlinarith [norm_nonneg (e i), sq_nonneg ⟪b i, ν⟫]
  have hdir : ∀ i, ∃ g : E → E →L[ℝ] ℝ, (∀ y ∈ S,
      HasFDerivWithinAt (fun y ↦ fderivWithin ℝ w B y (e i)) (g y) S y) ∧
      ∃ H : ℝ, 0 ≤ H ∧ ∀ y ∈ S, ∀ y' ∈ S, ‖g y - g y'‖ ≤ H * dist y y' ^ (α : ℝ) := fun i ↦
    exists_directional_of_linear hα hα1 hν hr hx hlam hell hsym ha hDa hG hDG hf hfH h hρ hy₀ν
      hdist hHw hM (he1 i) (Or.inl (hetan i))
  choose g hg H hH0 hH using hdir
  have hgc : ∀ i, ContinuousOn (g i) S := fun i ↦
    continuousOn_of_norm_sub_le hα' (hH0 i) (hH i)
  have hgH : ∀ i, ∃ C, HolderOnWith C α (g i) S := fun i ↦
    ⟨_, holderOnWith_of_dist_le (hH0 i) fun y hy y' hy' ↦ by
      rw [dist_eq_norm]; exact hH i y hy y' hy'⟩
  -- the interior of `S`
  set Ω' := interior S with hΩ'
  have hΩ'o : IsOpen Ω' := isOpen_interior
  have hΩ'c : Convex ℝ Ω' := (convex_halfBall ν y₀ (ρ / 4)).interior
  have hΩ'S : Ω' ⊆ S := interior_subset
  have hΩ'Ω : Ω' ⊆ ball x r ∩ openHalfSpace ν := by
    intro z hz
    refine ⟨?_, subset_openHalfSpace_of_isOpen hν hΩ'o (hΩ'S.trans fun _ h ↦ h.2) hz⟩
    have := (hΩ'S hz).1
    rw [mem_ball]; rw [mem_closedBall] at this
    linarith [dist_triangle z y₀ x]
  have hclS : closure Ω' = S := by
    rw [hΩ', (convex_halfBall ν y₀ (ρ / 4)).closure_interior_eq_closure_of_nonempty_interior
      (interior_halfBall_nonempty hν (by positivity) (by linarith)),
      (isClosed_halfBall ν y₀ (ρ / 4)).closure_eq]
  have hC2 := contDiffOn_two_interior_of_linear hα hα1 hν hr hx hlam hell hsym ha hDa hG hDG
    hf hfH h
  have hΩo : IsOpen (ball x r ∩ openHalfSpace ν) := isOpen_ball.inter (isOpen_openHalfSpace ν)
  -- the data of the normal–normal derivative
  set Da := fderivWithin ℝ a B with hDadef
  set DG := fderivWithin ℝ G B with hDGdef
  set gw := gradientWithin w B with hgwdef
  set R : E → ℝ := fun y ↦ -f y - ∑ j, ⟪b j, Da y (b j) (gw y)⟫ + ∑ j, ⟪b j, DG y (b j)⟫
    with hR
  set Ts : E → ℝ := fun y ↦ ∑ j, (∑ i, ⟪b i, a y (b j)⟫ * g i y (b j) +
    ⟪a y (b j), ν⟫ * ∑ i, ⟪b i, b j⟫ * g i y ν) with hTs
  set nH : E → ℝ := fun y ↦ (R y - Ts y) / ⟪a y ν, ν⟫ with hnH
  have hApos : ∀ y ∈ S, lam ≤ ⟪a y ν, ν⟫ := fun y hy ↦ by
    have := (hell y (hSB hy)).1 ν
    rw [hν] at this
    linarith
  -- Hölder continuity of the pieces on `S`
  have hBc : IsCompact B := isCompact_halfBall ν x r
  obtain ⟨-, Ka, hKa⟩ := exists_bound_holderOnWith_of_contDiffOn_halfBall hν hr hx ha hα1.le
  have haH : ∃ C, HolderOnWith C α a S := ⟨Ka, hKa.mono hSB⟩
  have hDaH : ∃ C, HolderOnWith C α Da S := ⟨Kda, hDa.mono hSB⟩
  have hDGH : ∃ C, HolderOnWith C α DG S := ⟨Kdg, hDG.mono hSB⟩
  have hgwH : ∃ C, HolderOnWith C α gw S :=
    ⟨Hw, hHw.mono (halfBall_mono ν y₀ (by linarith))⟩
  have hfS : ∃ C, HolderOnWith C α f S := ⟨Kf, hfH.mono hSB⟩
  have hinner : ∀ (v : E) {V : E → E}, (∃ C, HolderOnWith C α V S) →
      ∃ C, HolderOnWith C α (fun y ↦ ⟪v, V y⟫) S := fun v V hV ↦ by
    simpa only [innerSL_apply_apply] using exists_holderOnWith_clm (innerSL ℝ v) hV
  have happ : ∀ (v : E) {L : E → E →L[ℝ] E}, (∃ C, HolderOnWith C α L S) →
      ∃ C, HolderOnWith C α (fun y ↦ L y v) S := fun v L hL ↦ by
    simpa only [ContinuousLinearMap.apply_apply] using
      exists_holderOnWith_clm (ContinuousLinearMap.apply ℝ E v) hL
  have happR : ∀ (v : E) {L : E → E →L[ℝ] ℝ}, (∃ C, HolderOnWith C α L S) →
      ∃ C, HolderOnWith C α (fun y ↦ L y v) S := fun v L hL ↦ by
    simpa only [ContinuousLinearMap.apply_apply] using
      exists_holderOnWith_clm (ContinuousLinearMap.apply ℝ ℝ v) hL
  have hmul : ∀ {u v : E → ℝ}, (∃ C, HolderOnWith C α u S) → (∃ C, HolderOnWith C α v S) →
      ∃ C, HolderOnWith C α (fun y ↦ u y * v y) S := fun hu hv ↦ by
    simpa only [ContinuousLinearMap.mul_apply'] using
      exists_holderOnWith_bilinear hSc hα (ContinuousLinearMap.mul ℝ ℝ) hu hv
  have hsmulc : ∀ {u : E → ℝ} (ℓ : E →L[ℝ] ℝ), (∃ C, HolderOnWith C α u S) →
      ∃ C, HolderOnWith C α (fun y ↦ u y • ℓ) S := fun ℓ hu ↦ by
    simpa only [ContinuousLinearMap.lsmul_apply] using
      exists_holderOnWith_bilinear hSc hα (ContinuousLinearMap.lsmul ℝ ℝ) hu
        (exists_holderOnWith_const ℓ)
  have hRH : ∃ C, HolderOnWith C α R S := by
    refine exists_holderOnWith_add (exists_holderOnWith_sub (exists_holderOnWith_neg hfS)
      (exists_holderOnWith_sum _ fun j _ ↦ hinner (b j) ?_))
      (exists_holderOnWith_sum _ fun j _ ↦ hinner (b j) (happ (b j) hDGH))
    have h1 : ∃ C, HolderOnWith C α (fun y ↦ Da y (b j)) S := by
      simpa only [ContinuousLinearMap.apply_apply] using
        exists_holderOnWith_clm (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) (b j)) hDaH
    simpa only [ContinuousLinearMap.id_apply] using
      exists_holderOnWith_bilinear hSc hα (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) h1 hgwH
  have hTsH : ∃ C, HolderOnWith C α Ts S := by
    refine exists_holderOnWith_sum _ fun j _ ↦ exists_holderOnWith_add
      (exists_holderOnWith_sum _ fun i _ ↦ hmul (hinner (b i) (happ (b j) haH))
        (happR (b j) (hgH i)))
      (hmul ?_ (exists_holderOnWith_sum _ fun i _ ↦ hmul (exists_holderOnWith_const _)
        (happR ν (hgH i))))
    have : (fun y ↦ ⟪a y (b j), ν⟫) = fun y ↦ ⟪ν, a y (b j)⟫ := funext fun y ↦ real_inner_comm _ _
    rw [this]
    exact hinner ν (happ (b j) haH)
  have hdenH : ∃ C, HolderOnWith C α (fun y ↦ ⟪a y ν, ν⟫) S := by
    have : (fun y ↦ ⟪a y ν, ν⟫) = fun y ↦ ⟪ν, a y ν⟫ := funext fun y ↦ real_inner_comm _ _
    rw [this]
    exact hinner ν (happ ν haH)
  have hnHH : ∃ C, HolderOnWith C α nH S := by
    have e : nH = fun y ↦ (R y - Ts y) * (⟪a y ν, ν⟫)⁻¹ := funext fun y ↦ div_eq_mul_inv _ _
    rw [e]
    exact hmul (exists_holderOnWith_sub hRH hTsH) (exists_holderOnWith_inv hlam hdenH hApos)
  -- the candidate derivative of `∂_ν w`
  set gν : E → E →L[ℝ] ℝ := fun y ↦ ∑ i, (g i y ν) • innerSL ℝ (b i) +
    nH y • innerSL ℝ ν with hgν
  have hgνH : ∃ C, HolderOnWith C α gν S :=
    exists_holderOnWith_add (exists_holderOnWith_sum _ fun i _ ↦ hsmulc _ (happR ν (hgH i)))
      (hsmulc _ hnHH)
  have hgνc : ContinuousOn gν S := by
    obtain ⟨C, hC⟩ := hgνH; exact hC.continuousOn hα
  -- at interior points, `D(∂_ν w) = gν`
  have hint : ∀ y ∈ Ω', HasFDerivAt (fun z ↦ fderivWithin ℝ w B z ν) (gν y) y := by
    intro y hy
    have hyΩ := hΩ'Ω hy
    have hcd : ContDiffAt ℝ 2 w y := hC2.contDiffAt (hΩo.mem_nhds hyΩ)
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ w) y := hcd.fderiv_right (m := 1) (by norm_num)
    set H2 := fderiv ℝ (fderiv ℝ w) y with hH2
    have hD2 : HasFDerivAt (fderiv ℝ w) H2 y := (hfd.differentiableAt one_ne_zero).hasFDerivAt
    have hev : (fun z ↦ fderivWithin ℝ w B z) =ᶠ[𝓝 y] fderiv ℝ w := by
      filter_upwards [hΩo.mem_nhds hyΩ] with z hz
      refine fderivWithin_of_mem_nhds ?_
      exact mem_of_superset (hΩo.mem_nhds hz) fun u hu ↦
        ⟨ball_subset_closedBall hu.1, mem_halfSpace.2 (mem_openHalfSpace.1 hu.2).le⟩
    have happ' : ∀ v : E, HasFDerivAt (fun z ↦ fderivWithin ℝ w B z v)
        ((ContinuousLinearMap.apply ℝ ℝ v) ∘L H2) y := fun v ↦
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hD2).congr_of_eventuallyEq
        (hev.mono fun z hz ↦ by simp only [Function.comp_apply, hz,
          ContinuousLinearMap.apply_apply])
    have hSn : S ∈ 𝓝 y := mem_interior_iff_mem_nhds.1 hy
    have hgi : ∀ i ξ, g i y ξ = H2 ξ (b i - ⟪b i, ν⟫ • ν) := fun i ξ ↦ by
      have := ((hg i y (hΩ'S hy)).hasFDerivAt hSn).unique (happ' (e i))
      rw [this]; rfl
    have hsymm : ∀ u v, H2 u v = H2 v u := fun u v ↦
      hcd.isSymmSndFDerivAt (by simp) u v
    have heq := sum_hessian_coeff_eq hα hα1 hν hr hx hlam hell hsym ha hDa hG hDG hf hfH h b hyΩ
    have hAs : (a y : E →ₗ[ℝ] E).IsSymmetric := hsym y (hSB (hΩ'S hy))
    have hAν : ⟪a y ν, ν⟫ ≠ 0 := (hlam.trans_le (hApos y (hΩ'S hy))).ne'
    convert happ' ν using 1
    ext ξ
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.apply_apply]
    rw [hessian_apply_normal_of_sum_eq b H2 hsymm hAs hAν heq hgi ξ]
    simp only [hgν, hnH, hR, hTs, add_apply, FunLike.coe_sum,
      Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply,
      smul_eq_mul]
    have hc : ∑ i, g i y ν * ⟪b i, ξ⟫ = ∑ i, ⟪b i, ξ⟫ * g i y ν :=
      Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    rw [hc]; ring
  -- `∂_ν w` up to the flat part
  have hDc : ContinuousOn (fun z ↦ fderivWithin ℝ w B z ν) B :=
    (h.1.continuousOn_fderivWithin hBu le_rfl).clm_apply continuousOn_const
  have hν' : ∀ y ∈ S, HasFDerivWithinAt (fun z ↦ fderivWithin ℝ w B z ν) (gν y) S y := by
    intro y hy
    rw [← hclS]
    refine hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun z hz ↦ (hint z hz).differentiableAt.differentiableWithinAt) hΩ'c hΩ'o
      (fun z hz ↦ ?_) ?_
    · rw [hclS] at hz
      exact ((hDc z (hSB hz)).mono (hΩ'S.trans hSB))
    · have h1 : Tendsto gν (𝓝[Ω'] y) (𝓝 (gν y)) := (hgνc y hy).mono hΩ'S
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hint z hz).fderiv.symm
  -- assembly
  set Hs : E → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    ∑ i, (g i y + ⟪b i, ν⟫ • gν y).smulRight (innerSL ℝ (b i)) with hHs
  have hsplit : ∀ i, (fun z ↦ fderivWithin ℝ w B z (b i)) =
      fun z ↦ fderivWithin ℝ w B z (e i) + ⟪b i, ν⟫ * fderivWithin ℝ w B z ν := fun i ↦ by
    funext z
    have : b i = e i + ⟪b i, ν⟫ • ν := by simp [he]
    conv_lhs => rw [this]
    rw [map_add, map_smul, smul_eq_mul]
  have hHd : ∀ y ∈ S, HasFDerivWithinAt (fderivWithin ℝ w B) (Hs y) S y := fun y hy ↦
    hasFDerivWithinAt_of_orthonormalBasis b fun i ↦ by
      rw [hsplit i]
      exact (hg i y hy).add ((hν' y hy).const_mul _)
  have hHsH : ∃ C, HolderOnWith C α Hs S := by
    refine exists_holderOnWith_sum _ fun i _ ↦ ?_
    exact exists_holderOnWith_clm ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).flip
      (innerSL ℝ (b i))) (exists_holderOnWith_add (hgH i) (by
        simpa only [ContinuousLinearMap.lsmul_apply] using
          exists_holderOnWith_bilinear hSc hα (ContinuousLinearMap.lsmul ℝ ℝ)
            (exists_holderOnWith_const ⟪b i, ν⟫) hgνH))
  exact ⟨ρ / 4, by positivity, Hs, hHd, hHsH⟩

end BasicElliptic.Div
