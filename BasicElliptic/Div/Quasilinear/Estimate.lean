/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.SecondOrder
public import BasicElliptic.Div.Quasilinear.FrozenStep
import BasicElliptic.Div.Boundary.Main
import BasicElliptic.Holder.Algebra
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The scaled quasilinear conormal estimate

`Div.quasilinear_conormal_estimate_aux` proves
`Div.QuasilinearConormalEstimateStatement`: for `Φ ∈ C²(U)`, `0 ∈ U`, `DΦ` symmetric and
uniformly elliptic, there are `η > 0` and `C` such that every quasilinear conormal solution on
`halfBall ν x r` with `‖∇w‖ ≤ η` satisfies `r ‖Dw(x)‖ ≤ C osc w` and `r² ‖D²w(x)‖ ≤ C osc w`.

## Proof

* If `⟪x, ν⟫ < 0`, `x` is not in the closed half ball and both within-derivatives vanish.
* **The constant flux drops out.** Linearizing at `0`, `w` solves the linear conormal problem
  with coefficient `a(y) = chordCoeff Φ (∇w y) 0` and constant flux `G = -Φ(0)`. A constant
  tangential flux has no weak divergence on a half ball (translation invariance,
  `setIntegral_fderiv_apply_eq_zero_of_invariant`), nor does any constant flux on a ball in the
  open half space. If `g₀ = ⟪Φ(0), ν⟫ ≠ 0` and the half ball meets the flat part, the flux bound
  (`sq_inner_mul_pow_le_of_flux`) at the foot point gives `g₀² ≤ C (Λ η)²`, impossible for `η`
  small: no such solutions exist (so the hypothesis `⟪Φ 0, ν⟫ = 0` is not needed).
* **First derivatives.** The quantitative small-oscillation lemma
  (`exists_holderOnWith_gradientWithin_near`, at `q = 0`) bounds `[∇w]_{1/2}` on a half ball of
  radius `c₁ r / 2` by `C₁ / √r`, so `a` is `1/2`-Hölder with a scale-invariant constant, and
  the linear conormal estimate (`Div.c1Holder_halfBall_estimate`) gives
  `r ‖Dw(x)‖ + r^{3/2} [Dw]_{1/2} ≤ C osc w`.
* **Second derivatives.** For tangential `e`, `u_h = w(h e + ·) - w` solves a linear conormal
  problem with the chord coefficient (Hölder by the previous step); that estimate at `x` and the
  mean value inequality give `‖Dw(x + h e) - Dw(x)‖ ≤ C h osc w / r²`, hence
  `‖D²w(x) e‖ ≤ C osc w / r²`
  (`w ∈ C²` by `Div.contDiffOn_two_halfBall_of_quasilinear_conormal`). The normal–normal entry
  comes from the equation `tr (DΦ(∇w) D²w) = 0` (by continuity up to the flat part) and
  `⟪DΦ ν, ν⟫ ≥ lam`.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient Topology NNReal ContDiff

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Constant fluxes -/

/-- If `S` is invariant under the translations `y ↦ y + t c`, then `∫_S ∂_c φ = 0` for
`φ ∈ C¹_c`. -/
theorem setIntegral_fderiv_apply_eq_zero_of_invariant {S : Set E} {c : E}
    (hinv : ∀ (t : ℝ) (y : E), y + t • c ∈ S ↔ y ∈ S) {φ : E → ℝ} {x : E} {r : ℝ}
    (hφ : IsTestFn (ball x r) φ) : ∫ y in S, fderiv ℝ φ y c = 0 := by
  have hφd : Differentiable ℝ φ := hφ.1.differentiable one_ne_zero
  have hφc : Continuous φ := hφ.1.continuous
  have hdc : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv one_ne_zero
  obtain ⟨K, hK⟩ := (hφ.2.1.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hdc
  -- translation invariance
  have hconst : ∀ t : ℝ, ∫ y in S, φ (y + t • c) = ∫ y in S, φ y := fun t ↦ by
    have := (measurePreserving_add_right volume (t • c)).setIntegral_preimage_emb
      (measurableEmbedding_addRight _) φ S
    have hpre : (fun y ↦ y + t • c) ⁻¹' S = S := by ext y; exact hinv t y
    rwa [hpre] at this
  -- differentiation under the integral sign
  have hzero : ∀ y t, y ∉ ball x (r + ‖c‖) → t ∈ ball (0 : ℝ) 1 →
      fderiv ℝ φ (y + t • c) = 0 := fun y t hy ht ↦ by
    refine fderiv_of_notMem_tsupport ℝ fun hmem ↦ hy ?_
    have h1 := hφ.2.2 hmem
    rw [mem_ball] at h1 ⊢
    have h2 : ‖t • c‖ ≤ ‖c‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        rw [mem_ball, dist_zero_right] at ht; exact ht.le)
    have h3 : dist y (y + t • c) = ‖t • c‖ := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
    linarith [dist_triangle y (y + t • c) x]
  have hint : Integrable (fun y ↦ (ball x (r + ‖c‖)).indicator (fun _ ↦ K * ‖c‖) y)
      (volume.restrict S) :=
    ((integrable_indicator_iff measurableSet_ball).2
      (integrableOn_const measure_ball_lt_top.ne)).restrict
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun (t : ℝ) y ↦ φ (y + t • c)) (F' := fun (t : ℝ) y ↦ fderiv ℝ φ (y + t • c) c)
    (x₀ := 0) (s := ball 0 1)
    (bound := fun y ↦ (ball x (r + ‖c‖)).indicator (fun _ ↦ K * ‖c‖) y) (ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun t ↦
      (hφc.comp (continuous_id.add continuous_const) : Continuous fun y ↦ φ (y + t • c))
        |>.aestronglyMeasurable)
    (by simpa using (hφc.integrable_of_hasCompactSupport hφ.2.1).restrict)
    ((hdc.comp (continuous_id.add continuous_const)).clm_apply continuous_const
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun y t ht ↦ by
      by_cases hy : y ∈ ball x (r + ‖c‖)
      · rw [indicator_of_mem hy]
        exact ((fderiv ℝ φ _).le_opNorm c).trans
          (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _))
      · rw [indicator_of_notMem hy]
        simp [hzero y t hy ht])
    hint
    (Eventually.of_forall fun y t _ ↦ by
      have h1 : HasDerivAt (fun t : ℝ ↦ y + t • c) c t := by
        simpa using ((hasDerivAt_id t).smul_const c).const_add y
      exact (hφd _).hasFDerivAt.comp_hasDerivAt t h1)
  have h0 : HasDerivAt (fun t : ℝ ↦ ∫ y in S, φ (y + t • c)) 0 0 := by
    simp_rw [hconst]; exact hasDerivAt_const _ _
  have := hd.2.unique h0
  simpa using this

/-- A constant tangential flux has no weak divergence on a half ball. -/
theorem setIntegral_halfBall_inner_const_eq_zero {ν x c : E} {r : ℝ} (hc : ⟪c, ν⟫ = 0)
    {φ : E → ℝ} (hφ : IsTestFn (ball x r) φ) :
    ∫ y in halfBall ν x r, ⟪c, ∇ φ y⟫ = 0 := by
  have h0 : ∀ y ∉ ball x r, ⟪c, ∇ φ y⟫ = 0 := fun y hy ↦ by
    rw [(hφ.eq_zero_and_gradient_eq_zero hy).2, inner_zero_right]
  rw [← setIntegral_eq_of_inter_subset (measurableSet_halfSpace ν)
    (halfBall_subset_halfSpace ν x r) (fun y hy ↦ ⟨ball_subset_closedBall hy.2, hy.1⟩) h0]
  simp_rw [inner_gradient_right]
  refine setIntegral_fderiv_apply_eq_zero_of_invariant (fun t y ↦ ?_) hφ
  simp [mem_halfSpace, inner_add_left, real_inner_smul_left, hc]

/-- Any constant flux has no weak divergence on a half ball lying in the closed half space. -/
theorem setIntegral_halfBall_inner_const_eq_zero_of_le {ν x c : E} {r : ℝ} (hν : ‖ν‖ = 1)
    (hx : r ≤ ⟪x, ν⟫) {φ : E → ℝ} (hφ : IsTestFn (ball x r) φ) :
    ∫ y in halfBall ν x r, ⟪c, ∇ φ y⟫ = 0 := by
  have h0 : ∀ y ∉ ball x r, ⟪c, ∇ φ y⟫ = 0 := fun y hy ↦ by
    rw [(hφ.eq_zero_and_gradient_eq_zero hy).2, inner_zero_right]
  have hsub : ball x r ⊆ halfBall ν x r := fun y hy ↦ by
    refine ⟨ball_subset_closedBall hy, mem_halfSpace.2 ?_⟩
    have h1 : |⟪y - x, ν⟫| ≤ ‖y - x‖ := by
      simpa [hν] using abs_real_inner_le_norm (y - x) ν
    have h2 : ‖y - x‖ < r := by rw [← dist_eq_norm]; exact hy
    rw [inner_sub_left] at h1
    linarith [neg_abs_le (⟪y, ν⟫ - ⟪x, ν⟫)]
  rw [← setIntegral_eq_of_inter_subset MeasurableSet.univ (subset_univ _)
    (fun y hy ↦ hsub hy.2) h0, setIntegral_univ]
  simp_rw [inner_gradient_right]
  have := setIntegral_fderiv_apply_eq_zero_of_invariant (S := univ) (c := c)
    (fun t y ↦ by simp) hφ
  rwa [setIntegral_univ] at this

/-- Removing a constant flux with no weak divergence. -/
theorem IsConormalSolOn.of_const_flux {ν x : E} {r : ℝ} {a : E → E →L[ℝ] E} {c : E}
    {u : E → ℝ} (h : IsConormalSolOn ν a (fun _ ↦ c) 0 x r u)
    (hc : ∀ φ, IsTestFn (ball x r) φ → ∫ y in halfBall ν x r, ⟪c, ∇ φ y⟫ = 0) :
    IsConormalSolOn ν a 0 0 x r u := by
  refine ⟨h.1, fun φ hφ ↦ ?_⟩
  rw [h.2 φ hφ, hc φ hφ]
  simp

/-! ### Oscillation -/

theorem regionOsc_mono {X : Type*} {f : X → ℝ} {s t : Set X} (hst : s ⊆ t) (hs : s.Nonempty)
    (ha : BddAbove (f '' t)) (hb : BddBelow (f '' t)) : regionOsc f s ≤ regionOsc f t := by
  rw [regionOsc_def, regionOsc_def]
  have h1 := csSup_le_csSup ha (hs.image f) (image_mono hst)
  have h2 := csInf_le_csInf hb (hs.image f) (image_mono hst)
  linarith

/-! ### The scaled linear estimate without data -/

variable (E) in
/-- The scaled conormal estimate (`Div.c1Holder_halfBall_estimate`) for problems without
data: `ρ ‖Du(p)‖ + ρ^{1+α} [Du]_{α, halfBall ν p (ρ/2)} ≤ C osc u`. -/
theorem c1_estimate_of_isConormalSolOn {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {lam Λ Kc : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν p : E) (ρ : ℝ) (Ka : ℝ≥0) (a : E → E →L[ℝ] E) (u : E → ℝ),
      ‖ν‖ = 1 → 0 < ρ → -ρ < ⟪p, ν⟫ → IsUniformlyElliptic lam Λ a (halfBall ν p ρ) →
      IsSymmetricOn a (halfBall ν p ρ) → HolderOnWith Ka α a (halfBall ν p ρ) →
      (Ka : ℝ) * ρ ^ (α : ℝ) ≤ Kc → IsConormalSolOn ν a 0 0 p ρ u →
      ρ * ‖fderivWithin ℝ u (halfBall ν p ρ) p‖ + ρ ^ (1 + (α : ℝ)) *
          holderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≤
        C * regionOsc u (halfBall ν p ρ) := by
  obtain ⟨C, hC⟩ := Div.c1Holder_halfBall_estimate E α hα hα1 lam Λ Kc hlam
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ν p ρ Ka a u hν hρ hp hell hsym ha hKa hu
  have hG : HolderOnWith 0 α (0 : E → E) (halfBall ν p ρ) := holderOnWith_const 0 0 α _
  have h := hC ν p ρ Ka 0 0 0 a 0 0 u hν hρ hp hell hsym ha hKa hG (fun y _ ↦ by simp)
    aestronglyMeasurable_const (fun y _ ↦ by simp) hu
  simp only [NNReal.coe_zero, mul_zero, add_zero] at h
  have hpB : (halfBall ν p ρ).Nonempty := by
    obtain ⟨z, hz⟩ := interior_halfBall_nonempty hν hρ hp
    exact ⟨z, interior_subset hz⟩
  obtain ⟨c, hc⟩ := (isCompact_halfBall ν p ρ).exists_bound_of_continuousOn hu.1.continuousOn
  have hosc := regionOsc_nonneg_of_abs_le hpB (fun y hy ↦ (Real.norm_eq_abs _).symm.le.trans
    (hc y hy))
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hosc)

/-! ### Hessian bound from the tangential rows and the equation -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `H` is symmetric, `Σ_j H(b_j, A b_j) = 0` with `A` symmetric, `lam`-elliptic and
`‖A‖ ≤ Λ`, and `‖H e‖ ≤ T ‖e‖` for tangential `e`, then `‖H‖ ≤ 2 T (1 + d Λ / lam)`. -/
theorem norm_le_of_tangential {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {ν : E}
    (hν : ‖ν‖ = 1) (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : ∀ u v, H u v = H v u) {A : E →L[ℝ] E}
    (hA : (A : E →ₗ[ℝ] E).IsSymmetric) {lam Λ : ℝ} (hlam : 0 < lam)
    (hell : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫) (hAΛ : ‖A‖ ≤ Λ)
    (heq : ∑ j, H (b j) (A (b j)) = 0) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ e : E, ⟪e, ν⟫ = 0 → ‖H e‖ ≤ T * ‖e‖) :
    ‖H‖ ≤ 2 * T * (1 + Fintype.card ι * Λ / lam) := by
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hAΛ
  set P : E → E := fun ξ ↦ ξ - ⟪ξ, ν⟫ • ν with hP
  have hPν : ∀ ξ, ⟪P ξ, ν⟫ = 0 := fun ξ ↦ by
    rw [hP, inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]
  have hPn : ∀ ξ, ‖P ξ‖ ≤ ‖ξ‖ := fun ξ ↦ by
    have h1 : ‖P ξ‖ ^ 2 = ‖ξ‖ ^ 2 - ⟪ξ, ν⟫ ^ 2 := by
      rw [hP, @norm_sub_sq_real, norm_smul, hν, real_inner_smul_right, Real.norm_eq_abs,
        mul_one, sq_abs]
      ring
    have h2 : ‖P ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by rw [h1]; nlinarith [sq_nonneg ⟪ξ, ν⟫]
    nlinarith [norm_nonneg (P ξ), norm_nonneg ξ]
  have hdec : ∀ ξ, ξ = P ξ + ⟪ξ, ν⟫ • ν := fun ξ ↦ by simp [hP]
  set h := H ν ν with hh
  -- the tangential part
  set HT : E → E → ℝ := fun ξ η ↦ H ξ (P η) + ⟪η, ν⟫ * H (P ξ) ν with hHT
  have hsplit : ∀ ξ η, H ξ η = HT ξ η + ⟪ξ, ν⟫ * ⟪η, ν⟫ * h := fun ξ η ↦ by
    have e1 : H ξ η = H ξ (P η) + ⟪η, ν⟫ * H ξ ν := by
      conv_lhs => rw [hdec η]
      rw [map_add, map_smul, smul_eq_mul]
    have e2 : H ξ ν = H (P ξ) ν + ⟪ξ, ν⟫ * h := by
      conv_lhs => rw [hdec ξ]
      rw [map_add, map_smul, add_apply, FunLike.coe_smul,
        Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, hHT]; ring
  have hHTb : ∀ ξ η, |HT ξ η| ≤ 2 * T * ‖ξ‖ * ‖η‖ := fun ξ η ↦ by
    have h1 : |H ξ (P η)| ≤ T * ‖ξ‖ * ‖η‖ := by
      rw [hH, ← Real.norm_eq_abs]
      calc ‖H (P η) ξ‖ ≤ ‖H (P η)‖ * ‖ξ‖ := (H (P η)).le_opNorm ξ
        _ ≤ T * ‖P η‖ * ‖ξ‖ := by gcongr; exact hT _ (hPν η)
        _ ≤ T * ‖η‖ * ‖ξ‖ := by gcongr; exact hPn η
        _ = T * ‖ξ‖ * ‖η‖ := by ring
    have h2 : |⟪η, ν⟫ * H (P ξ) ν| ≤ T * ‖ξ‖ * ‖η‖ := by
      rw [abs_mul]
      have h3 : |⟪η, ν⟫| ≤ ‖η‖ := by simpa [hν] using abs_real_inner_le_norm η ν
      have h4 : |H (P ξ) ν| ≤ T * ‖ξ‖ := by
        rw [← Real.norm_eq_abs]
        calc ‖H (P ξ) ν‖ ≤ ‖H (P ξ)‖ * ‖ν‖ := (H (P ξ)).le_opNorm ν
          _ ≤ T * ‖P ξ‖ * 1 := by rw [hν]; gcongr; exact hT _ (hPν ξ)
          _ ≤ T * ‖ξ‖ := by rw [mul_one]; gcongr; exact hPn ξ
      calc |⟪η, ν⟫| * |H (P ξ) ν| ≤ ‖η‖ * (T * ‖ξ‖) :=
            mul_le_mul h3 h4 (abs_nonneg _) (norm_nonneg _)
        _ = T * ‖ξ‖ * ‖η‖ := by ring
    calc |HT ξ η| ≤ |H ξ (P η)| + |⟪η, ν⟫ * H (P ξ) ν| := abs_add_le _ _
      _ ≤ 2 * T * ‖ξ‖ * ‖η‖ := by linarith
  -- the normal–normal entry from the equation
  have hsumA : ∑ j, ⟪b j, ν⟫ * ⟪A (b j), ν⟫ = ⟪A ν, ν⟫ := by
    rw [real_inner_comm, ← b.sum_inner_mul_inner ν (A ν)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hs := hA (b j) ν
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [real_inner_comm (b j) ν, hs]
  have hAν : lam ≤ ⟪A ν, ν⟫ := by simpa [hν] using hell ν
  have hheq : ⟪A ν, ν⟫ * h = -∑ j, HT (b j) (A (b j)) := by
    have : ∑ j, (HT (b j) (A (b j)) + ⟪b j, ν⟫ * ⟪A (b j), ν⟫ * h) = 0 := by
      rw [← heq]; exact Finset.sum_congr rfl fun j _ ↦ (hsplit _ _).symm
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsumA] at this
    linarith
  have hsumb : |∑ j, HT (b j) (A (b j))| ≤ 2 * T * (Fintype.card ι * Λ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |HT (b j) (A (b j))| ≤ ∑ _j : ι, 2 * T * Λ := Finset.sum_le_sum fun j _ ↦ by
          refine (hHTb _ _).trans ?_
          rw [(b.orthonormal.1 j), mul_one]
          gcongr
          exact ((A.le_opNorm _).trans (by rw [b.orthonormal.1 j, mul_one])).trans hAΛ
      _ = 2 * T * (Fintype.card ι * Λ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hhb : |h| ≤ 2 * T * (Fintype.card ι * Λ) / lam := by
    rw [le_div_iff₀ hlam]
    have : |⟪A ν, ν⟫ * h| ≤ 2 * T * (Fintype.card ι * Λ) := by rw [hheq, abs_neg]; exact hsumb
    rw [abs_mul, abs_of_pos (hlam.trans_le hAν)] at this
    nlinarith [abs_nonneg h]
  -- the operator norm
  have hK0 : 0 ≤ 2 * T * (1 + Fintype.card ι * Λ / lam) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun ξ ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun η ↦ ?_
  rw [Real.norm_eq_abs, hsplit]
  have h3 : |⟪ξ, ν⟫ * ⟪η, ν⟫ * h| ≤ ‖ξ‖ * ‖η‖ * (2 * T * (Fintype.card ι * Λ) / lam) := by
    rw [abs_mul, abs_mul]
    have hξ : |⟪ξ, ν⟫| ≤ ‖ξ‖ := by simpa [hν] using abs_real_inner_le_norm ξ ν
    have hη : |⟪η, ν⟫| ≤ ‖η‖ := by simpa [hν] using abs_real_inner_le_norm η ν
    gcongr
  calc |HT ξ η + ⟪ξ, ν⟫ * ⟪η, ν⟫ * h| ≤ |HT ξ η| + |⟪ξ, ν⟫ * ⟪η, ν⟫ * h| := abs_add_le _ _
    _ ≤ 2 * T * ‖ξ‖ * ‖η‖ + ‖ξ‖ * ‖η‖ * (2 * T * (Fintype.card ι * Λ) / lam) :=
        add_le_add (hHTb ξ η) h3
    _ = 2 * T * (1 + Fintype.card ι * Λ / lam) * ‖ξ‖ * ‖η‖ := by ring

/-! ### Tangential difference quotients of the gradient -/

/-- **Tangential differences of `∇w` at the centre.** Let `w` be a quasilinear conormal solution
on `B = halfBall ν x r`, `⟪x, ν⟫ ≥ 0`, with `∇w` in a convex `K₀ ⊆ U₀` on which `DΦ` is bounded by
`Λ` and `L`-Lipschitz; let `∇w` be `1/2`-Hölder on `halfBall ν x r₂` (`r₂ ≤ r`) with constant
`Hg`, `Hg √r₂ ≤ C₁`, and `‖∇w‖ ≤ M₁` on `halfBall ν x (r₂/2)`. If `CT` is the constant of that
estimate for `(lam, Λ, 2 L C₁)`, then for tangential `e`, `‖e‖ ≤ 1`, and `0 < h ≤ r₂/4`,
`‖∇w(x + h e) - ∇w(x)‖ ≤ 8 CT M₁ h / r₂`. -/
theorem norm_gradientWithin_add_smul_sub_le {ν x : E} {r r₂ : ℝ} {Φ : E → E} {U₀ K₀ : Set E}
    {lam Λ L C₁ CT M₁ : ℝ} {Hg : ℝ≥0} {w : E → ℝ} (hCT0 : 0 ≤ CT) (hν : ‖ν‖ = 1)
    (hr₂ : 0 < r₂) (hr₂r : r₂ ≤ r)
    (hx : 0 ≤ ⟪x, ν⟫) (hU₀ : IsOpen U₀) (hU₀c : Convex ℝ U₀) (hΦ : ContDiffOn ℝ 1 Φ U₀)
    (hell : ∀ p ∈ U₀, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U₀, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hK₀c : Convex ℝ K₀) (hK₀U : K₀ ⊆ U₀) (hΛ : ∀ p ∈ K₀, ‖fderiv ℝ Φ p‖ ≤ Λ) (hL0 : 0 ≤ L)
    (hL : ∀ a ∈ K₀, ∀ b ∈ K₀, ‖fderiv ℝ Φ a - fderiv ℝ Φ b‖ ≤ L * ‖a - b‖)
    (h : IsQuasilinearConormalSolOn ν Φ x r w)
    (hK : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ K₀)
    (hHg : HolderOnWith Hg (1 / 2) (gradientWithin w (halfBall ν x r)) (halfBall ν x r₂))
    (hHgC : (Hg : ℝ) * √r₂ ≤ C₁)
    (hM₁ : ∀ p ∈ halfBall ν x (r₂ / 2), ‖gradientWithin w (halfBall ν x r) p‖ ≤ M₁)
    (hCT : ∀ (ν p : E) (ρ : ℝ) (Ka : ℝ≥0) (a : E → E →L[ℝ] E) (u : E → ℝ),
      ‖ν‖ = 1 → 0 < ρ → -ρ < ⟪p, ν⟫ → IsUniformlyElliptic lam Λ a (halfBall ν p ρ) →
      IsSymmetricOn a (halfBall ν p ρ) → HolderOnWith Ka (1 / 2) a (halfBall ν p ρ) →
      (Ka : ℝ) * ρ ^ ((1 / 2 : ℝ≥0) : ℝ) ≤ 2 * L * C₁ → IsConormalSolOn ν a 0 0 p ρ u →
      ρ * ‖fderivWithin ℝ u (halfBall ν p ρ) p‖ + ρ ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) *
          holderSeminormOn (1 / 2) (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≤
        CT * regionOsc u (halfBall ν p ρ))
    {e : E} (he : ⟪e, ν⟫ = 0) (he1 : ‖e‖ ≤ 1) {t : ℝ} (ht : 0 < t) (htr : t ≤ r₂ / 4) :
    ‖gradientWithin w (halfBall ν x r) (t • e + x) - gradientWithin w (halfBall ν x r) x‖ ≤
      8 * CT * M₁ * t / r₂ := by
  have hr : 0 < r := hr₂.trans_le hr₂r
  have hxr : -r < ⟪x, ν⟫ := by linarith
  set B := halfBall ν x r with hBdef
  set g := gradientWithin w B with hg
  set ρ₃ := r₂ / 4 with hρ₃
  have hρ₃0 : 0 < ρ₃ := by positivity
  have hxρ : -ρ₃ < ⟪x, ν⟫ := by linarith
  have hu₃ := uniqueDiffOn_halfBall hν hρ₃0 hxρ
  have hB2 : halfBall ν x (r₂ / 2) ⊆ B := halfBall_mono ν x (by linarith)
  have h3B : halfBall ν x ρ₃ ⊆ B := halfBall_mono ν x (by linarith)
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hinner : ∀ y, ⟪t • e + y, ν⟫ = ⟪y, ν⟫ := fun y ↦ by
    rw [inner_add_left, real_inner_smul_left, he, mul_zero, zero_add]
  have hte : ‖t • e‖ ≤ t := by
    rw [norm_smul, Real.norm_of_nonneg ht.le]; exact mul_le_of_le_one_right ht.le he1
  have hshift : ∀ y ∈ halfBall ν x ρ₃, t • e + y ∈ halfBall ν x (r₂ / 2) := fun y hy ↦ by
    refine ⟨?_, by rw [mem_halfSpace, hinner]; exact hy.2⟩
    rw [mem_closedBall]
    have h1 : dist (t • e + y) y = ‖t • e‖ := by rw [dist_eq_norm, add_sub_cancel_right]
    linarith [dist_triangle (t • e + y) y x, mem_closedBall.1 hy.1]
  -- the two solutions on `halfBall ν x ρ₃`
  have hcl : ∀ {z : E} {s : ℝ}, dist z x + s ≤ r → closedBall z s ⊆ closedBall x r :=
    fun hzs ↦ closedBall_subset_closedBall' (by rw [dist_comm] at *; linarith)
  have hbl : ∀ {z : E} {s : ℝ}, dist z x + s ≤ r → ball z s ⊆ ball x r :=
    fun hzs ↦ ball_subset_ball' (by rw [dist_comm] at *; linarith)
  have hdx : dist (t • e + x) x ≤ t := by rw [dist_eq_norm, add_sub_cancel_right]; exact hte
  have htr' := h.translate hν hρ₃0 hxρ (by rw [hinner]; linarith) (hcl (by linarith))
    (hbl (by linarith)) fun y _ ↦ by rw [hinner]
  have hres := h.restrict hν hρ₃0 hxρ (hcl (by rw [dist_self]; linarith))
    (hbl (by rw [dist_self]; linarith))
  have hg₁ : ∀ y ∈ halfBall ν x ρ₃, gradientWithin (fun y ↦ w (t • e + y))
      (halfBall ν x ρ₃) y = g (t • e + y) := fun y hy ↦
    gradientWithin_translate hν hρ₃0 hxρ (fun y hy ↦ hB2 (hshift y hy)) hwB
      (by rintro _ ⟨y, hy, rfl⟩; exact hB2 (hshift y hy)) hy
  have hg₂ : ∀ y ∈ halfBall ν x ρ₃, gradientWithin w (halfBall ν x ρ₃) y = g y := fun y hy ↦
    gradientWithin_eq_of_subset h3B (hu₃ y hy) (hwB y (h3B hy))
  have hlin := IsQuasilinearConormalSolOn.sub hν hρ₃0 hxρ hU₀ hU₀c hΦ htr' hres
    (fun y hy ↦ by rw [hg₁ y hy]; exact hK₀U (hK _ (hB2 (hshift y hy))))
    (fun y hy ↦ by rw [hg₂ y hy]; exact hK₀U (hK _ (h3B hy)))
  set a : E → E →L[ℝ] E := fun y ↦ chordCoeff Φ (gradientWithin (fun y ↦ w (t • e + y))
    (halfBall ν x ρ₃) y) (gradientWithin w (halfBall ν x ρ₃) y) with ha
  have haK : ∀ y ∈ halfBall ν x ρ₃, a y = chordCoeff Φ (g (t • e + y)) (g y) := fun y hy ↦ by
    rw [ha]; simp only; rw [hg₁ y hy, hg₂ y hy]
  have hK1 : ∀ y ∈ halfBall ν x ρ₃, g (t • e + y) ∈ K₀ := fun y hy ↦ hK _ (hB2 (hshift y hy))
  have hK2 : ∀ y ∈ halfBall ν x ρ₃, g y ∈ K₀ := fun y hy ↦ hK _ (h3B hy)
  -- the coefficient
  have hell' : IsUniformlyElliptic lam Λ a (halfBall ν x ρ₃) := fun y hy ↦ by
    rw [haK y hy]
    exact ⟨le_inner_chordCoeff hU₀ hU₀c hΦ hell (hK₀U (hK1 y hy)) (hK₀U (hK2 y hy)),
      norm_chordCoeff_le hK₀c hΛ (hK1 y hy) (hK2 y hy)⟩
  have hsym' : IsSymmetricOn a (halfBall ν x ρ₃) := fun y hy ↦ by
    rw [haK y hy]
    exact isSymmetric_chordCoeff hU₀ hU₀c hΦ hsym (hK₀U (hK1 y hy)) (hK₀U (hK2 y hy))
  have hHg' : ∀ y ∈ halfBall ν x r₂, ∀ y' ∈ halfBall ν x r₂,
      ‖g y - g y'‖ ≤ Hg * dist y y' ^ (1 / 2 : ℝ) := fun y hy y' hy' ↦ by
    have := (holderOnWith_iff_dist_le.1 hHg) y hy y' hy'
    rwa [dist_eq_norm, show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num] at this
  have h2r : halfBall ν x (r₂ / 2) ⊆ halfBall ν x r₂ := halfBall_mono ν x (by linarith)
  have h3r : halfBall ν x ρ₃ ⊆ halfBall ν x r₂ := halfBall_mono ν x (by linarith)
  have hKa : HolderOnWith (Real.toNNReal (2 * L * Hg)) (1 / 2) a (halfBall ν x ρ₃) := by
    refine holderOnWith_iff_dist_le.2 fun y hy y' hy' ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, haK y hy, haK y' hy',
      show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num]
    refine (norm_chordCoeff_sub_le hU₀ hU₀c hΦ hK₀c hK₀U hL0 hL (hK1 y hy) (hK2 y hy)
      (hK1 y' hy') (hK2 y' hy')).trans ?_
    have h1 := hHg' _ (h2r (hshift y hy)) _ (h2r (hshift y' hy'))
    have h2 := hHg' _ (h3r hy) _ (h3r hy')
    rw [dist_add_left] at h1
    calc L * (‖g (t • e + y) - g (t • e + y')‖ + ‖g y - g y'‖)
        ≤ L * (Hg * dist y y' ^ (1 / 2 : ℝ) + Hg * dist y y' ^ (1 / 2 : ℝ)) := by gcongr
      _ = 2 * L * Hg * dist y y' ^ (1 / 2 : ℝ) := by ring
  have hKaC : (Real.toNNReal (2 * L * Hg) : ℝ) * ρ₃ ^ ((1 / 2 : ℝ≥0) : ℝ) ≤ 2 * L * C₁ := by
    rw [Real.coe_toNNReal _ (by positivity), show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]
    have : √ρ₃ ≤ √r₂ := Real.sqrt_le_sqrt (by linarith)
    calc 2 * L * Hg * √ρ₃ ≤ 2 * L * (Hg * √r₂) := by
          rw [mul_assoc (2 * L)]; gcongr
      _ ≤ 2 * L * C₁ := by gcongr
  have hT := hCT ν x ρ₃ _ a _ hν hρ₃0 hxρ hell' hsym' hKa hKaC hlin
  have hT' : ρ₃ * ‖fderivWithin ℝ (fun y ↦ w (t • e + y) - w y) (halfBall ν x ρ₃) x‖ ≤
      CT * regionOsc (fun y ↦ w (t • e + y) - w y) (halfBall ν x ρ₃) := by
    have := holderSeminormOn_nonneg (1 / 2) (fderivWithin ℝ (fun y ↦ w (t • e + y) - w y)
      (halfBall ν x ρ₃)) (halfBall ν x (ρ₃ / 2))
    have : 0 ≤ ρ₃ ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) := by positivity
    nlinarith
  -- the oscillation of the difference
  have hxS : x ∈ halfBall ν x ρ₃ := ⟨mem_closedBall_self hρ₃0.le, hx⟩
  have hmv : ∀ y ∈ halfBall ν x ρ₃, |w (t • e + y) - w y| ≤ M₁ * t := fun y hy ↦ by
    have hs2 := (convex_halfBall ν x (r₂ / 2))
    have hd : DifferentiableOn ℝ w (halfBall ν x (r₂ / 2)) := hwB.mono hB2
    have hx2 : -(r₂ / 2) < ⟪x, ν⟫ := by linarith
    have hu2 := uniqueDiffOn_halfBall hν (by positivity : 0 < r₂ / 2) hx2
    have hb : ∀ z ∈ halfBall ν x (r₂ / 2), ‖fderivWithin ℝ w (halfBall ν x (r₂ / 2)) z‖ ≤ M₁ :=
      fun z hz ↦ by
        rw [fderivWithin_subset hB2 (hu2 z hz) (hwB z (hB2 hz)),
          norm_fderivWithin_eq_norm_gradientWithin]
        exact hM₁ z hz
    have := hs2.norm_image_sub_le_of_norm_fderivWithin_le hd hb
      (halfBall_mono ν x (by linarith) hy) (hshift y hy)
    rw [add_sub_cancel_right, Real.norm_eq_abs] at this
    refine this.trans ?_
    have hM0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ x ⟨mem_closedBall_self (by positivity), hx⟩)
    exact mul_le_mul_of_nonneg_left hte hM0
  have hosc := regionOsc_le_two_mul_of_abs_le ⟨x, hxS⟩ hmv
  -- the gradient of the difference at the centre
  have hgd : ‖fderivWithin ℝ (fun y ↦ w (t • e + y) - w y) (halfBall ν x ρ₃) x‖ =
      ‖g (t • e + x) - g x‖ := by
    rw [norm_fderivWithin_eq_norm_gradientWithin, gradientWithin,
      fderivWithin_fun_sub (hu₃ x hxS) (htr'.1.differentiableOn one_ne_zero x hxS)
        (hres.1.differentiableOn one_ne_zero x hxS), map_sub, ← gradientWithin,
      ← gradientWithin, hg₁ x hxS, hg₂ x hxS]
  rw [hgd] at hT'
  have hosc' := mul_le_mul_of_nonneg_left hosc hCT0
  have hc := hT'.trans hosc'
  rw [hρ₃] at hc
  rw [le_div_iff₀ hr₂]
  linarith

/-! ### The equation at points of the flat part -/

/-- **The nondivergence equation up to the flat part**: if `w` is `C²` on
`S = halfBall ν y₀ ρ` (`y₀` in the closed half space, `B_ρ(y₀) ⊆ B_r(x)`), then
`Σ_i D²_S w(y₀)(b_i, DΦ(∇w(y₀)) b_i) = 0` (by continuity from the interior,
`trace_hessian_eq_zero`). -/
theorem trace_hessianWithin_eq_zero {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {y₀ : E} (hy₀ : 0 ≤ ⟪y₀, ν⟫) {ρ : ℝ}
    (hρ : 0 < ρ) (hball : closedBall y₀ ρ ⊆ ball x r)
    (hC2 : ContDiffOn ℝ 2 w (halfBall ν y₀ ρ)) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    ∑ i, fderivWithin ℝ (fderivWithin ℝ w (halfBall ν y₀ ρ)) (halfBall ν y₀ ρ) y₀ (b i)
      (fderiv ℝ Φ (gradientWithin w (halfBall ν x r) y₀) (b i)) = 0 := by
  set S := halfBall ν y₀ ρ with hS
  set B := halfBall ν x r with hB
  have huS := uniqueDiffOn_halfBall hν hρ (by linarith : -ρ < ⟪y₀, ν⟫)
  have hSB : S ⊆ B := fun y hy ↦ ⟨ball_subset_closedBall (hball hy.1), hy.2⟩
  have hgc : ContinuousOn (gradientWithin w B) B :=
    continuousOn_gradientWithin_halfBall hν hr hx h.1
  have hHc : ContinuousOn (fderivWithin ℝ (fderivWithin ℝ w S) S) S :=
    (hC2.fderivWithin huS (by norm_num : ((1 : ℕ) : ℕ∞ω) + 1 ≤ 2)).continuousOn_fderivWithin huS
      le_rfl
  have hDΦ : ContinuousOn (fderiv ℝ Φ) U := hΦ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  set F : E → ℝ := fun y ↦ ∑ i, fderivWithin ℝ (fderivWithin ℝ w S) S y (b i)
    (fderiv ℝ Φ (gradientWithin w B y) (b i)) with hF
  have hFc : ContinuousOn F S := by
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    exact (hHc.clm_apply continuousOn_const).clm_apply
      (((hDΦ.comp (hgc.mono hSB) fun y hy ↦ hrange y (hSB hy))).clm_apply continuousOn_const)
  set I := ball y₀ ρ ∩ openHalfSpace ν with hI
  have hIo : IsOpen I := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hIS : I ⊆ S := fun y hy ↦ ⟨ball_subset_closedBall hy.1,
    openHalfSpace_subset_halfSpace ν hy.2⟩
  have hF0 : ∀ y ∈ I, F y = 0 := by
    intro y hy
    have hyx : y ∈ ball x r ∩ openHalfSpace ν := ⟨hball (ball_subset_closedBall hy.1), hy.2⟩
    have heq : fderivWithin ℝ w S =ᶠ[𝓝 y] fderiv ℝ w := by
      filter_upwards [hIo.mem_nhds hy] with z hz
      exact fderivWithin_of_mem_nhds (mem_of_superset (hIo.mem_nhds hz) hIS)
    have h1 : fderivWithin ℝ (fderivWithin ℝ w S) S y = fderiv ℝ (fderiv ℝ w) y := by
      rw [fderivWithin_of_mem_nhds (mem_of_superset (hIo.mem_nhds hy) hIS), heq.fderiv_eq]
    have := trace_hessian_eq_zero hν hr hx hU hUc hlam hΦ hell hsym hrange h b hyx
    have h2 : gradientWithin w B y = ∇ w y := gradientWithin_halfBall_eq hyx
    simp only [hF, h1, h2]
    exact this
  have hy₀S : y₀ ∈ S := ⟨mem_closedBall_self hρ.le, hy₀⟩
  have hcl : y₀ ∈ closure I := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨y₀ + (min ε ρ / 2) • ν, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith [min_le_right ε ρ, lt_min hε hρ]
    · rw [mem_openHalfSpace, inner_add_left, real_inner_smul_left,
        real_inner_self_of_norm_eq_one hν]
      have := lt_min hε hρ
      linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hν, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith [min_le_left ε ρ, lt_min hε hρ]
  have hmem := ((hFc y₀ hy₀S).mono hIS).mem_closure_image hcl
  have hsub : F '' I ⊆ {0} := by rintro _ ⟨y, hy, rfl⟩; exact hF0 y hy
  have := closure_mono hsub hmem
  rwa [closure_singleton, mem_singleton_iff] at this

/-! ### Second derivatives at the centre -/

/-- **The Hessian at the centre** (second half of the estimate). Under the hypotheses of
`norm_gradientWithin_add_smul_sub_le`, with `w ∈ C²` near `x` and the first-order bounds
`r₂ ‖Dw(x)‖ ≤ CT O`, `r₂^{3/2} [Dw]_{1/2, halfBall ν x (r₂/2)} ≤ CT O`, the within Hessian
satisfies `‖D²w(x)‖ ≤ 32 CT² O (1 + d Λ / lam) / r₂²`. -/
theorem norm_hessianWithin_le_aux {ν x : E} {r r₂ : ℝ} {Φ : E → E} {U₀ K₀ : Set E}
    {lam Λ L C₁ CT O : ℝ} {Hg : ℝ≥0} {w : E → ℝ} (hCT0 : 0 ≤ CT) (hO : 0 ≤ O)
    (hν : ‖ν‖ = 1) (hr₂ : 0 < r₂) (hr₂r : r₂ ≤ r) (hx : 0 ≤ ⟪x, ν⟫) (hlam : 0 < lam)
    (hU₀ : IsOpen U₀) (hU₀c : Convex ℝ U₀) (hΦ : ContDiffOn ℝ 2 Φ U₀)
    (hell : ∀ p ∈ U₀, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U₀, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hK₀c : Convex ℝ K₀) (hK₀U : K₀ ⊆ U₀) (hΛ : ∀ p ∈ K₀, ‖fderiv ℝ Φ p‖ ≤ Λ) (hL0 : 0 ≤ L)
    (hL : ∀ a ∈ K₀, ∀ b ∈ K₀, ‖fderiv ℝ Φ a - fderiv ℝ Φ b‖ ≤ L * ‖a - b‖)
    (h : IsQuasilinearConormalSolOn ν Φ x r w)
    (hK : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ K₀)
    (hHg : HolderOnWith Hg (1 / 2) (gradientWithin w (halfBall ν x r)) (halfBall ν x r₂))
    (hHgC : (Hg : ℝ) * √r₂ ≤ C₁)
    (hCT : ∀ (ν p : E) (ρ : ℝ) (Ka : ℝ≥0) (a : E → E →L[ℝ] E) (u : E → ℝ),
      ‖ν‖ = 1 → 0 < ρ → -ρ < ⟪p, ν⟫ → IsUniformlyElliptic lam Λ a (halfBall ν p ρ) →
      IsSymmetricOn a (halfBall ν p ρ) → HolderOnWith Ka (1 / 2) a (halfBall ν p ρ) →
      (Ka : ℝ) * ρ ^ ((1 / 2 : ℝ≥0) : ℝ) ≤ 2 * L * C₁ → IsConormalSolOn ν a 0 0 p ρ u →
      ρ * ‖fderivWithin ℝ u (halfBall ν p ρ) p‖ + ρ ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) *
          holderSeminormOn (1 / 2) (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≤
        CT * regionOsc u (halfBall ν p ρ))
    (hfirst : r₂ * ‖fderivWithin ℝ w (halfBall ν x r) x‖ ≤ CT * O)
    (hsemi : r₂ * √r₂ * holderSeminormOn (1 / 2) (fderivWithin ℝ w (halfBall ν x r₂))
      (halfBall ν x (r₂ / 2)) ≤ CT * O) :
    ‖fderivWithin ℝ (fderivWithin ℝ w (halfBall ν x r)) (halfBall ν x r) x‖ ≤
      2 * (32 * CT ^ 2 * O / r₂ ^ 2) *
        (1 + Fintype.card (Fin (finrank ℝ E)) * Λ / lam) := by
  have hr : 0 < r := hr₂.trans_le hr₂r
  have hxr : -r < ⟪x, ν⟫ := by linarith
  set B := halfBall ν x r with hBdef
  set g := gradientWithin w B with hg
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hr₂B : halfBall ν x r₂ ⊆ B := halfBall_mono ν x hr₂r
  have hxr₂ : -r₂ < ⟪x, ν⟫ := by linarith
  have hu₂ := uniqueDiffOn_halfBall hν hr₂ hxr₂
  have hD₂ : ∀ y ∈ halfBall ν x r₂, fderivWithin ℝ w (halfBall ν x r₂) y =
      fderivWithin ℝ w B y := fun y hy ↦
    fderivWithin_subset hr₂B (hu₂ y hy) (hwB y (hr₂B hy))
  have h2r : halfBall ν x (r₂ / 2) ⊆ halfBall ν x r₂ := halfBall_mono ν x (by linarith)
  have hxS2 : x ∈ halfBall ν x (r₂ / 2) := ⟨mem_closedBall_self (by positivity), hx⟩
  have hxB' : x ∈ B := ⟨mem_closedBall_self hr.le, hx⟩
  -- the sup bound on `halfBall ν x (r₂/2)`
  set Sem := holderSeminormOn (1 / 2) (fderivWithin ℝ w (halfBall ν x r₂))
    (halfBall ν x (r₂ / 2)) with hSem
  have hfin : eHolderSeminormOn (1 / 2) (fderivWithin ℝ w (halfBall ν x r₂))
      (halfBall ν x (r₂ / 2)) ≠ ⊤ := by
    refine (eHolderSeminormOn_lt_top_of_holderOnWith (C := Hg)
      (holderOnWith_iff_dist_le.2 fun p hp q hq ↦ ?_)).ne
    rw [hD₂ p (h2r hp), hD₂ q (h2r hq), dist_fderivWithin_eq_dist_gradientWithin]
    exact (holderOnWith_iff_dist_le.1 hHg) p (h2r hp) q (h2r hq)
  set M₁ := 2 * CT * O / r₂ with hM₁def
  have hsq0 : 0 < √r₂ := Real.sqrt_pos.2 hr₂
  have hM₁ : ∀ p ∈ halfBall ν x (r₂ / 2), ‖g p‖ ≤ M₁ := by
    intro p hp
    have h1 := dist_le_holderSeminormOn_mul hfin hp hxS2
    rw [hD₂ p (h2r hp), hD₂ x (h2r hxS2)] at h1
    have h2 : dist p x ^ ((1 / 2 : ℝ≥0) : ℝ) ≤ √r₂ := by
      rw [show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt ((mem_closedBall.1 hp.1).trans (by linarith))
    have hSem0 : 0 ≤ Sem := holderSeminormOn_nonneg _ _ _
    have h3 : Sem * √r₂ ≤ CT * O / r₂ := by
      rw [le_div_iff₀ hr₂]; linarith only [hsemi]
    have h4 : ‖fderivWithin ℝ w B x‖ ≤ CT * O / r₂ := by
      rw [le_div_iff₀ hr₂]; linarith only [hfirst]
    rw [← norm_fderivWithin_eq_norm_gradientWithin]
    calc ‖fderivWithin ℝ w B p‖ ≤ ‖fderivWithin ℝ w B x‖ +
          dist (fderivWithin ℝ w B p) (fderivWithin ℝ w B x) := by
          rw [dist_eq_norm]; exact norm_le_norm_add_norm_sub' _ _
      _ ≤ CT * O / r₂ + Sem * √r₂ :=
          add_le_add h4 (h1.trans (mul_le_mul_of_nonneg_left h2 hSem0))
      _ ≤ M₁ := by
          have e : 2 * CT * O / r₂ = CT * O / r₂ + CT * O / r₂ := by ring
          rw [hM₁def, e]; linarith only [h3]
  -- `w ∈ C²` near `x`
  have hxb : x ∈ ball x r ∩ halfSpace ν := ⟨mem_ball_self hr, hx⟩
  obtain ⟨ρ₀, hρ₀, hC2⟩ := exists_contDiffOn_two_halfBall hν hr hxr hU₀ hU₀c hlam hΦ hell hsym
    (fun y hy ↦ hK₀U (hK y hy)) h hxb
  set ρ₁ := min ρ₀ (r₂ / 4) with hρ₁
  have hρ₁0 : 0 < ρ₁ := lt_min hρ₀ (by positivity)
  have hρ₁r : ρ₁ ≤ r₂ / 4 := min_le_right _ _
  set S₀ := halfBall ν x ρ₁ with hS₀
  have hC2' : ContDiffOn ℝ 2 w S₀ := hC2.mono (halfBall_mono ν x (min_le_left _ _))
  have hxρ₁ : -ρ₁ < ⟪x, ν⟫ := by linarith
  have huS := uniqueDiffOn_halfBall hν hρ₁0 hxρ₁
  have hxS₀ : x ∈ S₀ := ⟨mem_closedBall_self hρ₁0.le, hx⟩
  have hS₀B : S₀ ⊆ B := halfBall_mono ν x (by linarith)
  set Hs := fderivWithin ℝ (fderivWithin ℝ w S₀) S₀ x with hHs
  -- identification with the Hessian within `B`
  have hid : fderivWithin ℝ (fderivWithin ℝ w B) B x = Hs := by
    have hset : B ∩ ball x ρ₁ = S₀ ∩ ball x ρ₁ := by
      ext y
      simp only [hBdef, hS₀, halfBall, mem_inter_iff, mem_closedBall, mem_ball]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨⟨h3.le, h2⟩, h3⟩
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
    rw [← fderivWithin_inter (ball_mem_nhds x hρ₁0), hset,
      fderivWithin_inter (ball_mem_nhds x hρ₁0)]
    refine fderivWithin_congr (fun y hy ↦ ?_) ?_
    · exact (fderivWithin_subset hS₀B (huS y hy) (hwB y (hS₀B hy))).symm
    · exact (fderivWithin_subset hS₀B (huS x hxS₀) (hwB x hxB')).symm
  rw [hid]
  -- symmetry
  have hcl : x ∈ closure (interior S₀) := by
    refine closure_mono (ball_inter_openHalfSpace_subset_interior_halfBall ν x ρ₁) ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨x + (min ε ρ₁ / 2) • ν, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith [min_le_right ε ρ₁, lt_min hε hρ₁0]
    · rw [mem_openHalfSpace, inner_add_left, real_inner_smul_left,
        real_inner_self_of_norm_eq_one hν]
      have := lt_min hε hρ₁0
      linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hν, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith [min_le_left ε ρ₁, lt_min hε hρ₁0]
  have hsymH : ∀ u v, Hs u v = Hs v u := fun u v ↦
    ((hC2'.contDiffWithinAt hxS₀).isSymmSndFDerivWithinAt (by simp) huS hcl hxS₀) u v
  -- the equation at `x`
  set b := stdOrthonormalBasis ℝ E with hb
  have hsum := trace_hessianWithin_eq_zero hν hr hxr hU₀ hU₀c hlam hΦ hell hsym
    (fun y hy ↦ hK₀U (hK y hy)) h hx hρ₁0
    (fun y hy ↦ mem_ball.2 ((mem_closedBall.1 hy).trans_lt (by linarith))) hC2' b
  -- the tangential rows
  set T₀ := 8 * CT * M₁ / r₂ with hT₀
  have hT₀0 : 0 ≤ T₀ := by positivity
  have hderiv : HasFDerivWithinAt (fderivWithin ℝ w S₀) Hs S₀ x :=
    ((hC2'.fderivWithin huS (by norm_num : ((1 : ℕ) : ℕ∞ω) + 1 ≤ 2)).differentiableOn
      one_ne_zero x hxS₀).hasFDerivWithinAt
  have hunit : ∀ e : E, ⟪e, ν⟫ = 0 → ‖e‖ = 1 → ‖Hs e‖ ≤ T₀ := by
    intro e he he1
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hev := hderiv.isLittleO.def hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhdsWithin_iff.1 hev
    set t := min (δ / 2) ρ₁ with ht
    have ht0 : 0 < t := lt_min (by positivity) hρ₁0
    have htr : t ≤ r₂ / 4 := (min_le_right _ _).trans hρ₁r
    have hte : ‖t • e‖ = t := by rw [norm_smul, he1, mul_one, Real.norm_of_nonneg ht0.le]
    have hz : t • e + x ∈ ball x δ ∩ S₀ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_right, hte]
        linarith [min_le_left (δ / 2) ρ₁]
      · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, hte]; exact min_le_right _ _
      · rw [mem_halfSpace, inner_add_left, real_inner_smul_left, he, mul_zero, zero_add]
        exact hx
    have h1 := hδ' hz
    simp only [mem_ofPred_eq, add_sub_cancel_right, hte] at h1
    have hzS := hz.2
    have h2 : ‖fderivWithin ℝ w S₀ (t • e + x) - fderivWithin ℝ w S₀ x‖ ≤ T₀ * t := by
      rw [fderivWithin_subset hS₀B (huS _ hzS) (hwB _ (hS₀B hzS)),
        fderivWithin_subset hS₀B (huS x hxS₀) (hwB x hxB'), ← dist_eq_norm,
        dist_fderivWithin_eq_dist_gradientWithin, dist_eq_norm]
      have := norm_gradientWithin_add_smul_sub_le hCT0 hν hr₂ hr₂r hx hU₀ hU₀c
        (hΦ.of_le (by norm_num)) hell hsym hK₀c hK₀U hΛ hL0 hL h hK hHg hHgC hM₁ hCT he
        he1.le ht0 htr
      calc _ ≤ 8 * CT * M₁ * t / r₂ := this
        _ = T₀ * t := by rw [hT₀]; ring
    have h3 : ‖Hs (t • e)‖ ≤ (T₀ + ε) * t := by
      have := norm_le_norm_add_norm_sub' (Hs (t • e))
        (fderivWithin ℝ w S₀ (t • e + x) - fderivWithin ℝ w S₀ x)
      rw [norm_sub_rev (Hs (t • e))] at this
      linarith only [this, h1, h2]
    rw [map_smul, norm_smul, Real.norm_of_nonneg ht0.le, mul_comm] at h3
    exact le_of_mul_le_mul_right h3 ht0
  have hTe : ∀ e : E, ⟪e, ν⟫ = 0 → ‖Hs e‖ ≤ T₀ * ‖e‖ := by
    intro e he
    rcases eq_or_ne e 0 with rfl | he0
    · simp
    have hn : 0 < ‖e‖ := norm_pos_iff.2 he0
    set e₁ := ‖e‖⁻¹ • e with he₁
    have h1 : ‖e₁‖ = 1 := by
      rw [he₁, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hn.le), inv_mul_cancel₀ hn.ne']
    have h2 : ⟪e₁, ν⟫ = 0 := by rw [he₁, real_inner_smul_left, he, mul_zero]
    have he' : e = ‖e‖ • e₁ := by rw [he₁, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    calc ‖Hs e‖ = ‖Hs (‖e‖ • e₁)‖ := by rw [← he']
      _ = ‖e‖ * ‖Hs e₁‖ := by rw [map_smul, norm_smul, Real.norm_of_nonneg hn.le]
      _ ≤ ‖e‖ * T₀ := mul_le_mul_of_nonneg_left (hunit e₁ h2 h1) hn.le
      _ = T₀ * ‖e‖ := mul_comm _ _
  set A := fderiv ℝ Φ (g x) with hA
  have hgxK : g x ∈ K₀ := hK x hxB'
  have hH := norm_le_of_tangential b hν Hs hsymH (A := A) (hsym _ (hK₀U hgxK)) hlam
    (hell _ (hK₀U hgxK)) (hΛ _ hgxK) hsum hT₀0 hTe
  have hT₀le : T₀ ≤ 32 * CT ^ 2 * O / r₂ ^ 2 := by
    have e : T₀ = 16 * CT ^ 2 * O / r₂ ^ 2 := by rw [hT₀, hM₁def]; field_simp; ring
    rw [e]
    gcongr
    nlinarith [sq_nonneg CT]
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ _ hgxK)
  calc ‖Hs‖ ≤ 2 * T₀ * (1 + Fintype.card (Fin (finrank ℝ E)) * Λ / lam) := hH
    _ ≤ 2 * (32 * CT ^ 2 * O / r₂ ^ 2) * (1 + Fintype.card (Fin (finrank ℝ E)) * Λ / lam) := by
        gcongr

/-! ### The estimate -/

variable (E) in
/-- **The scaled quasilinear conormal estimate** (see the module docstring). Proves
`Div.QuasilinearConormalEstimateStatement`. -/
theorem quasilinear_conormal_estimate_aux : QuasilinearConormalEstimateStatement E := by
  intro ν Φ U lam hν hU h0 hlam hΦ hell hsym
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have : Nontrivial E := ⟨⟨ν, 0, hν0⟩⟩
  -- a convex neighbourhood of `0`
  obtain ⟨η', hη', hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  set η₀ := η' / 3 with hη₀
  have hη₀0 : 0 < η₀ := by positivity
  set U₀ := ball (0 : E) (2 * η₀) with hU₀
  have hU₀U : U₀ ⊆ U := (ball_subset_ball (by linarith)).trans hball
  have hU₀o : IsOpen U₀ := isOpen_ball
  have hU₀c : Convex ℝ U₀ := convex_ball _ _
  have hΦ₀ : ContDiffOn ℝ 2 Φ U₀ := hΦ.mono hU₀U
  have hΦ₁ : ContDiffOn ℝ 1 Φ U₀ := hΦ₀.of_le (by norm_num)
  have hell₀ : ∀ p ∈ U₀, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫ :=
    fun p hp ↦ hell p (hU₀U hp)
  have hsym₀ : ∀ p ∈ U₀, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric := fun p hp ↦ hsym p (hU₀U hp)
  set K₀ := closedBall (0 : E) η₀ with hK₀
  have hK₀U : K₀ ⊆ U₀ := closedBall_subset_ball (by linarith)
  have hK₀c : Convex ℝ K₀ := convex_closedBall _ _
  have h0U₀ : (0 : E) ∈ U₀ := mem_ball_self (by positivity)
  have h0K₀ : (0 : E) ∈ K₀ := mem_closedBall_self hη₀0.le
  -- `DΦ` is bounded and Lipschitz on `K₀`
  have hD1 : ContDiffOn ℝ 1 (fun p ↦ fderiv ℝ Φ p) U₀ := hΦ₀.fderiv_of_isOpen hU₀o (by norm_num)
  have hKc : IsCompact K₀ := isCompact_closedBall _ _
  obtain ⟨Λ', hΛ'⟩ := hKc.exists_bound_of_continuousOn
    ((hΦ₀.continuousOn_fderiv_of_isOpen hU₀o (by norm_num)).mono hK₀U)
  set Λ := max Λ' 0 with hΛdef
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hΛ : ∀ p ∈ K₀, ‖fderiv ℝ Φ p‖ ≤ Λ := fun p hp ↦ (hΛ' p hp).trans (le_max_left _ _)
  obtain ⟨L₀, hL₀⟩ := hKc.exists_bound_of_continuousOn
    ((hD1.continuousOn_fderiv_of_isOpen hU₀o le_rfl).mono hK₀U)
  set L := max L₀ 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hlip : LipschitzOnWith (Real.toNNReal L) (fun p ↦ fderiv ℝ Φ p) K₀ := by
    refine hK₀c.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun p ↦ fderiv ℝ (fun p ↦ fderiv ℝ Φ p) p) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · exact ((hD1.differentiableOn one_ne_zero p (hK₀U hp)).differentiableAt
        (hU₀o.mem_nhds (hK₀U hp))).hasFDerivAt.hasFDerivWithinAt
    · rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL0]
      exact (hL₀ p hp).trans (le_max_left _ _)
  have hL : ∀ a ∈ K₀, ∀ b ∈ K₀, ‖fderiv ℝ Φ a - fderiv ℝ Φ b‖ ≤ L * ‖a - b‖ :=
    fun a ha b hb ↦ by
      have := hlip.dist_le_mul a ha b hb
      rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0] at this
  -- the quantitative small-oscillation lemma at `q = 0`
  obtain ⟨ηG, hηG, c₁, hc₁, C₁, hC₁, hGL⟩ := exists_holderOnWith_gradientWithin_near E hν
    hU₀o hΦ₁ h0U₀ hlam (hell₀ 0 h0U₀) (hsym₀ 0 h0U₀)
  -- the flux obstruction
  obtain ⟨Cf, hCf, hflux⟩ := sq_inner_mul_pow_le_of_flux E hν
  set vB := unitBallVolume E with hvB
  have hvB0 : 0 < vB := unitBallVolume_pos
  set g₀ := ⟪Φ 0, ν⟫ with hg₀
  obtain ⟨η₃, hη₃, hη₃'⟩ : ∃ η₃ > 0, g₀ ≠ 0 → Cf * vB * (Λ * η₃) ^ 2 < g₀ ^ 2 := by
    by_cases hg : g₀ = 0
    · exact ⟨1, one_pos, fun h ↦ absurd hg h⟩
    refine ⟨|g₀| / (2 * (Λ + 1) * (Cf * vB + 1)), by positivity, fun _ ↦ ?_⟩
    have ha : 0 < |g₀| := abs_pos.2 hg
    have h1 : Λ * (|g₀| / (2 * (Λ + 1) * (Cf * vB + 1))) ≤ |g₀| / (2 * (Cf * vB + 1)) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos ha (show (0 : ℝ) < Cf * vB + 1 by positivity)]
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : Cf * vB * (|g₀| / (2 * (Cf * vB + 1))) ^ 2 < g₀ ^ 2 := by
      rw [div_pow, ← sq_abs g₀]
      have hk : 0 < Cf * vB + 1 := by positivity
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg |g₀|, mul_pos (pow_pos ha 2) hk, sq_nonneg (Cf * vB)]
    calc Cf * vB * (Λ * (|g₀| / (2 * (Λ + 1) * (Cf * vB + 1)))) ^ 2
        ≤ Cf * vB * (|g₀| / (2 * (Cf * vB + 1))) ^ 2 := by gcongr
      _ < g₀ ^ 2 := h3
  set η := min (min η₀ ηG) η₃ with hηdef
  have hη : 0 < η := lt_min (lt_min hη₀0 hηG) hη₃
  have hηη₀ : η ≤ η₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hηG : η ≤ ηG := (min_le_left _ _).trans (min_le_right _ _)
  have hηη₃ : η ≤ η₃ := min_le_right _ _
  set c := min c₁ 1 with hcdef
  have hc0 : 0 < c := lt_min hc₁ one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  -- the constant of the conormal estimate
  obtain ⟨CT, hCT0, hCT⟩ := c1_estimate_of_isConormalSolOn E (α := 1 / 2) (by norm_num)
    (by norm_num) (lam := lam) (Λ := Λ) (Kc := 2 * L * C₁) hlam
  set d := Fintype.card (Fin (finrank ℝ E)) with hd
  set C := max (2 * CT / c) (256 * CT ^ 2 * (1 + d * Λ / lam) / c ^ 2) with hC
  refine ⟨η, hη, C, ?_⟩
  intro x r w hr hx h hgrad
  set B := halfBall ν x r with hBdef
  set g := gradientWithin w B with hgdef
  have hBc : IsCompact B := isCompact_halfBall ν x r
  have hBne : B.Nonempty := (interior_halfBall_nonempty hν hr hx).mono interior_subset
  obtain ⟨cw, hcw⟩ := hBc.exists_bound_of_continuousOn h.1.continuousOn
  have hcw' : ∀ y ∈ B, |w y| ≤ cw := fun y hy ↦ (Real.norm_eq_abs _).symm.le.trans (hcw y hy)
  have hosc0 : 0 ≤ regionOsc w B := regionOsc_nonneg_of_abs_le hBne hcw'
  have hC0 : 0 ≤ C := (by positivity : 0 ≤ 2 * CT / c).trans (le_max_left _ _)
  rcases lt_or_ge ⟪x, ν⟫ 0 with hxneg | hx0
  · have hxB : x ∉ closure B := by
      rw [(isClosed_halfBall ν x r).closure_eq]
      exact fun hxB ↦ (not_le.2 hxneg) hxB.2
    rw [fderivWithin_zero_of_notMem_closure hxB, fderivWithin_zero_of_notMem_closure hxB]
    simp only [norm_zero, mul_zero]
    exact ⟨mul_nonneg hC0 hosc0, mul_nonneg hC0 hosc0⟩
  have hxB : x ∈ B := ⟨mem_closedBall_self hr.le, hx0⟩
  have hgK : ∀ y ∈ B, g y ∈ K₀ := fun y hy ↦
    mem_closedBall_zero_iff.2 ((hgrad y hy).trans hηη₀)
  have hgU : ∀ y ∈ B, g y ∈ U₀ := fun y hy ↦ hK₀U (hgK y hy)
  have hgc : ContinuousOn g B := continuousOn_gradientWithin_halfBall hν hr hx h.1
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have huB := uniqueDiffOn_halfBall hν hr hx
  have hbddA : BddAbove (w '' B) :=
    ⟨cw, by rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (hcw' y hy)⟩
  have hbddB : BddBelow (w '' B) :=
    ⟨-cw, by rintro _ ⟨y, hy, rfl⟩; exact neg_le_of_abs_le (hcw' y hy)⟩
  -- the linear problem, after removing the constant flux
  set a : E → E →L[ℝ] E := fun y ↦ chordCoeff Φ (g y) 0 with ha
  have hΦc : ContinuousOn (fun y ↦ Φ (g y)) B := hΦ₁.continuousOn.comp hgc fun y hy ↦ hgU y hy
  have hlin0 := h.isConormalSolOn_sub_inner hν hr hx hΦc (a := a) (G := fun _ ↦ -Φ 0) 0
    continuousOn_const fun y hy ↦ by
      change chordCoeff Φ (g y) 0 (g y - 0) = _
      rw [← sub_eq_chordCoeff_apply hU₀o hU₀c hΦ₁ (hgU y hy) h0U₀]
      abel
  have hw0 : (fun y ↦ w y - ⟪(0 : E), y⟫) = w := funext fun y ↦ by simp
  rw [hw0] at hlin0
  have hconst : ∀ φ, IsTestFn (ball x r) φ → ∫ y in B, ⟪-Φ 0, ∇ φ y⟫ = 0 := by
    intro φ hφ
    rcases le_or_gt r ⟪x, ν⟫ with hfar | hnear
    · exact setIntegral_halfBall_inner_const_eq_zero_of_le hν hfar hφ
    by_cases hg : g₀ = 0
    · exact setIntegral_halfBall_inner_const_eq_zero
        (by rw [inner_neg_left, ← hg₀, hg, neg_zero]) hφ
    exfalso
    -- the half ball at the foot point
    have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
    set yb := x - ⟪x, ν⟫ • ν with hyb
    set s := r - ⟪x, ν⟫ with hs
    have hs0 : 0 < s := by linarith
    have hybν : ⟪yb, ν⟫ = 0 := by
      rw [hyb, inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]
    have hdyb : dist yb x = ⟪x, ν⟫ := by
      rw [hyb, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
        Real.norm_of_nonneg hx0]
    have hcl : closedBall yb s ⊆ closedBall x r :=
      closedBall_subset_closedBall' (by rw [hdyb]; linarith)
    have hbl : ball yb s ⊆ ball x r := ball_subset_ball' (by rw [hdyb]; linarith)
    have hybs : -s < ⟪yb, ν⟫ := by rw [hybν]; linarith
    have hres := h.restrict hν hs0 hybs hcl hbl
    have hsub : halfBall ν yb s ⊆ B := inter_subset_inter_left _ hcl
    have hus := uniqueDiffOn_halfBall hν hs0 hybs
    have heq : ∀ y ∈ halfBall ν yb s, gradientWithin w (halfBall ν yb s) y = g y :=
      fun y hy ↦ gradientWithin_eq_of_subset hsub (hus y hy) (hwB y (hsub hy))
    have hQc : ContinuousOn (fun y ↦ Φ (gradientWithin w (halfBall ν yb s) y))
        (halfBall ν yb s) :=
      hΦ₁.continuousOn.comp (continuousOn_gradientWithin_halfBall hν hs0 hybs hres.1)
        fun y hy ↦ by rw [heq y hy]; exact hgU y (hsub hy)
    have hfl := hflux yb s _ (Φ 0) hybν hs0 hQc fun φ hφ ↦ hres.2 φ hφ
    -- the right-hand side is at most `(Λ η)² |B_s|`
    have hpt : ∀ y ∈ halfBall ν yb s,
        ‖Φ (gradientWithin w (halfBall ν yb s) y) - Φ 0‖ ^ 2 ≤ (Λ * η) ^ 2 := fun y hy ↦ by
      rw [heq y hy, sub_eq_chordCoeff_apply hU₀o hU₀c hΦ₁ (hgU y (hsub hy)) h0U₀, sub_zero]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine ((chordCoeff Φ (g y) 0).le_opNorm _).trans ?_
      exact mul_le_mul (norm_chordCoeff_le hK₀c hΛ (hgK y (hsub hy)) h0K₀)
        (hgrad y (hsub hy)) (norm_nonneg _) hΛ0
    have hvol : volume.real (halfBall ν yb s) ≤ s ^ finrank ℝ E * vB := by
      rw [← measureReal_ball_eq hs0, measureReal_def, measureReal_def,
        measure_congr (halfBall_ae_eq hν0 yb s)]
      exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono inter_subset_left)
    have hfin : volume (halfBall ν yb s) ≠ ⊤ := (isCompact_halfBall ν yb s).measure_lt_top.ne
    have hint : ∫ y in halfBall ν yb s,
        ‖Φ (gradientWithin w (halfBall ν yb s) y) - Φ 0‖ ^ 2 ≤
          (Λ * η) ^ 2 * (s ^ finrank ℝ E * vB) := by
      calc _ ≤ ∫ _y in halfBall ν yb s, (Λ * η) ^ 2 :=
            setIntegral_mono_on (((hQc.sub continuousOn_const).norm.pow 2).integrableOn_compact
              (isCompact_halfBall ν yb s)) (integrableOn_const hfin)
              (measurableSet_halfBall ν yb s) hpt
        _ = (Λ * η) ^ 2 * volume.real (halfBall ν yb s) := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
        _ ≤ _ := by gcongr
    have hsd : 0 < s ^ finrank ℝ E := pow_pos hs0 _
    have h1 : g₀ ^ 2 * s ^ finrank ℝ E ≤ Cf * vB * (Λ * η) ^ 2 * s ^ finrank ℝ E := by
      calc g₀ ^ 2 * s ^ finrank ℝ E ≤ Cf * _ := hfl
        _ ≤ Cf * ((Λ * η) ^ 2 * (s ^ finrank ℝ E * vB)) := by gcongr
        _ = Cf * vB * (Λ * η) ^ 2 * s ^ finrank ℝ E := by ring
    have h2 : g₀ ^ 2 ≤ Cf * vB * (Λ * η) ^ 2 := le_of_mul_le_mul_right h1 hsd
    have h3 : Cf * vB * (Λ * η) ^ 2 ≤ Cf * vB * (Λ * η₃) ^ 2 := by
      gcongr
    linarith [hη₃' hg]
  have hlin : IsConormalSolOn ν a 0 0 x r w := hlin0.of_const_flux hconst
  -- the a priori Hölder bound for `∇w`
  have hHol := hGL x r w x (r / 2) hr hx h (half_pos hr) hx0
    (closedBall_subset_ball (half_lt_self hr)) fun z hz ↦ by
      rw [sub_zero]; exact (hgrad z (halfBall_mono ν x (by linarith) hz)).trans hηG
  set r₂ := c * (r / 2) with hr₂def
  have hr₂ : 0 < r₂ := by positivity
  have hr₂r : r₂ ≤ r / 2 := mul_le_of_le_one_left (by positivity) hc1
  have hr₂B : halfBall ν x r₂ ⊆ B := halfBall_mono ν x (by linarith)
  set Hg := Real.toNNReal (C₁ / √(r / 2)) with hHgdef
  have hHgv : (Hg : ℝ) = C₁ / √(r / 2) := Real.coe_toNNReal _ (by positivity)
  have hHg : HolderOnWith Hg (1 / 2) g (halfBall ν x r₂) :=
    hHol.mono (halfBall_mono ν x (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (by positivity)))
  have hsqrt : √r₂ ≤ √(r / 2) := Real.sqrt_le_sqrt hr₂r
  have hHgC : (Hg : ℝ) * √r₂ ≤ C₁ := by
    rw [hHgv]
    calc C₁ / √(r / 2) * √r₂ ≤ C₁ / √(r / 2) * √(r / 2) := by gcongr
      _ = C₁ := by field_simp
  have hgr : ∀ y ∈ halfBall ν x r₂, ∀ y' ∈ halfBall ν x r₂,
      ‖g y - g y'‖ ≤ Hg * dist y y' ^ (1 / 2 : ℝ) := fun y hy y' hy' ↦ by
    have := (holderOnWith_iff_dist_le.1 hHg) y hy y' hy'
    rwa [dist_eq_norm, show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num] at this
  -- the coefficient on `halfBall ν x r₂`
  have hell_a : IsUniformlyElliptic lam Λ a (halfBall ν x r₂) := fun y hy ↦
    ⟨le_inner_chordCoeff hU₀o hU₀c hΦ₁ hell₀ (hgU y (hr₂B hy)) h0U₀,
      norm_chordCoeff_le hK₀c hΛ (hgK y (hr₂B hy)) h0K₀⟩
  have hsym_a : IsSymmetricOn a (halfBall ν x r₂) := fun y hy ↦
    isSymmetric_chordCoeff hU₀o hU₀c hΦ₁ hsym₀ (hgU y (hr₂B hy)) h0U₀
  have hKa : HolderOnWith (Real.toNNReal (L * Hg)) (1 / 2) a (halfBall ν x r₂) := by
    refine holderOnWith_iff_dist_le.2 fun y hy y' hy' ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm,
      show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num]
    refine (norm_chordCoeff_sub_le hU₀o hU₀c hΦ₁ hK₀c hK₀U hL0 hL (hgK y (hr₂B hy)) h0K₀
      (hgK y' (hr₂B hy')) h0K₀).trans ?_
    rw [sub_self, norm_zero, add_zero, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hgr y hy y' hy') hL0
  have hKaC : (Real.toNNReal (L * Hg) : ℝ) * r₂ ^ ((1 / 2 : ℝ≥0) : ℝ) ≤ 2 * L * C₁ := by
    rw [Real.coe_toNNReal _ (by positivity), show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, mul_assoc]
    calc L * (Hg * √r₂) ≤ L * C₁ := by gcongr
      _ ≤ 2 * L * C₁ := by nlinarith [mul_nonneg hL0 hC₁]
  have hxr₂ : -r₂ < ⟪x, ν⟫ := by linarith
  have hlin₂ := hlin.restrict_halfBall hν hr₂ hxr₂ (closedBall_subset_closedBall (by linarith))
    (ball_subset_ball (by linarith))
  have hT := hCT ν x r₂ _ a w hν hr₂ hxr₂ hell_a hsym_a hKa hKaC hlin₂
  have hosc₂ : regionOsc w (halfBall ν x r₂) ≤ regionOsc w B :=
    regionOsc_mono hr₂B ⟨x, ⟨mem_closedBall_self hr₂.le, hx0⟩⟩ hbddA hbddB
  have hxr₂B : x ∈ halfBall ν x r₂ := ⟨mem_closedBall_self hr₂.le, hx0⟩
  have hu₂ := uniqueDiffOn_halfBall hν hr₂ hxr₂
  have hD₂ : ∀ y ∈ halfBall ν x r₂, fderivWithin ℝ w (halfBall ν x r₂) y =
      fderivWithin ℝ w B y := fun y hy ↦
    fderivWithin_subset hr₂B (hu₂ y hy) (hwB y (hr₂B hy))
  set Sem := holderSeminormOn (1 / 2) (fderivWithin ℝ w (halfBall ν x r₂))
    (halfBall ν x (r₂ / 2)) with hSem
  have hSem0 : 0 ≤ Sem := holderSeminormOn_nonneg _ _ _
  have hr₂32 : r₂ ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) = r₂ * √r₂ := by
    rw [show (1 + ((1 / 2 : ℝ≥0) : ℝ)) = 1 + 1 / 2 by norm_num, Real.rpow_add hr₂,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hr₂32, hD₂ x hxr₂B] at hT
  have hsq0 : 0 < √r₂ := Real.sqrt_pos.2 hr₂
  have hosc₂' := mul_le_mul_of_nonneg_left hosc₂ hCT0
  have hfirst : r₂ * ‖fderivWithin ℝ w B x‖ ≤ CT * regionOsc w B := by
    have h0 : 0 ≤ r₂ * √r₂ * Sem := by positivity
    linarith only [hT, hosc₂', h0]
  have hsemi : r₂ * √r₂ * Sem ≤ CT * regionOsc w B := by
    have h0 : 0 ≤ r₂ * ‖fderivWithin ℝ w B x‖ := by positivity
    linarith only [hT, hosc₂', h0]
  have hpart1 : r * ‖fderivWithin ℝ w B x‖ ≤ C * regionOsc w B := by
    have hr' : r = 2 / c * r₂ := by rw [hr₂def]; field_simp
    rw [hr']
    calc 2 / c * r₂ * ‖fderivWithin ℝ w B x‖ = 2 / c * (r₂ * ‖fderivWithin ℝ w B x‖) := by ring
      _ ≤ 2 / c * (CT * regionOsc w B) := by gcongr
      _ = 2 * CT / c * regionOsc w B := by ring
      _ ≤ C * regionOsc w B := by gcongr; exact le_max_left _ _
  refine ⟨hpart1, ?_⟩
  have hH2 := norm_hessianWithin_le_aux hCT0 hosc0 hν hr₂ (by linarith) hx0 hlam hU₀o hU₀c hΦ₀
    hell₀ hsym₀ hK₀c hK₀U hΛ hL0 hL h hgK hHg hHgC hCT hfirst hsemi
  have hr' : r = 2 / c * r₂ := by rw [hr₂def]; field_simp
  have hk : 0 ≤ 1 + (d : ℝ) * Λ / lam := by positivity
  calc r ^ 2 * ‖fderivWithin ℝ (fderivWithin ℝ w B) B x‖
      ≤ r ^ 2 * (2 * (32 * CT ^ 2 * regionOsc w B / r₂ ^ 2) * (1 + d * Λ / lam)) := by
        gcongr
    _ = 256 * CT ^ 2 * (1 + d * Λ / lam) / c ^ 2 * regionOsc w B := by
        rw [hr']; field_simp; ring
    _ ≤ C * regionOsc w B := by gcongr; exact le_max_right _ _

end BasicElliptic.Div
