/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Directional
public import BasicElliptic.Div.Quasilinear.GradientHolder
import Mathlib.Analysis.Calculus.ContDiff.Basic
import BasicElliptic.Holder.Algebra
import BasicElliptic.Holder.Closure
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# `C²` up to the flat part for quasilinear conormal solutions (`k = 1`)

`Div.contDiffOn_two_halfBall_of_quasilinear_conormal`: a `C¹` quasilinear conormal solution with
`Φ ∈ C²(U)`, `DΦ` symmetric and uniformly elliptic on the open convex `U ⊇ ∇w(B⁺)`, is `C²` on
`halfBall ν x (r/2)` (in fact near every point of `ball x r ∩ halfSpace ν`).

## Proof

Fix `y₀ ∈ ball x r ∩ halfSpace ν`, and an orthonormal basis `(b_i)`.

1. **Local data** (`exists_local_data`). By the local `C^{1,α}` lemma
   (`IsQuasilinearConormalSolOn.exists_holderOnWith_gradientWithin`) and the continuity of `∇w`,
   on a small `halfBall ν y₀ (4ρ)` the gradient is `α`-Hölder with values in a closed ball
   `K ⊆ U` on which `DΦ` is bounded and Lipschitz (`Φ ∈ C²`).
2. **Interior `C²`** (`contDiffOn_two_interior`). At points of `ball x r ∩ openHalfSpace ν`, small
   balls are half balls on which translations in every direction are admissible, so the
   directional lemma (`exists_hasFDerivWithinAt_fderivWithin_apply`) applies to every `b_i`.
3. **The equation in the interior** (`trace_hessian_eq_zero`). There `V = Φ ∘ ∇w` is `C¹`; by
   integration by parts and the fundamental lemma, `div V = Σ_i D²w(b_i, A b_i) = 0` with
   `A = DΦ(∇w)`.
4. **Up to the flat part.** On `S = halfBall ν y₀ (ρ/4)` the tangential derivatives
   `∂_{P b_i} w` (`P` the projection onto `ν^⊥`) have Hölder within-derivatives `g_i`
   (directional lemma with tangential directions). In the interior of `S`,
   `D²w(ξ, η) = Q(ξ, η) + ⟪ξ, ν⟫ ⟪η, ν⟫ ∂_νν w` with `Q` built from the `g_i`, and the equation
   gives `∂_νν w = -(Σ_i Q(b_i, A b_i)) / ⟪A ν, ν⟫`, continuous up to the flat part since
   `⟪A ν, ν⟫ ≥ lam`. Hence `D(∂_ν w)` extends continuously to `S`, and
   `hasFDerivWithinAt_closure_of_tendsto_fderiv` (on the interior of the convex `S`) gives the
   within-derivative of `∂_ν w` on `S`. Together, `Dw` has a continuous within-derivative on `S`,
  which is moreover `α`-Hölder (`exists_hessian_holder_halfBall`; used for `k ≥ 2`).
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology NNReal ContDiff

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A field of functionals whose values on an orthonormal basis have within-derivatives has a
within-derivative. -/
theorem hasFDerivWithinAt_of_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {D : E → E →L[ℝ] ℝ} {g : ι → E →L[ℝ] ℝ} {s : Set E} {y : E}
    (h : ∀ i, HasFDerivWithinAt (fun y ↦ D y (b i)) (g i) s y) :
    HasFDerivWithinAt D (∑ i, (g i).smulRight (innerSL ℝ (b i))) s y := by
  have hD : D = fun y ↦ ∑ i, D y (b i) • innerSL ℝ (b i) := by
    funext y
    ext ξ
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, innerSL_apply_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr' ξ]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  rw [hD]
  exact HasFDerivWithinAt.fun_sum fun i _ ↦ (h i).smul_const _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `C²` on a set with unique derivatives from a within-derivative with a continuous
within-derivative. -/
theorem contDiffOn_two_of_hasFDerivWithinAt {w : E → ℝ} {s : Set E} (hs : UniqueDiffOn ℝ s)
    {D : E → E →L[ℝ] ℝ} (hD : ∀ y ∈ s, HasFDerivWithinAt w (D y) s y)
    {Hs : E → E →L[ℝ] E →L[ℝ] ℝ} (hH : ∀ y ∈ s, HasFDerivWithinAt D (Hs y) s y)
    (hHc : ContinuousOn Hs s) : ContDiffOn ℝ 2 w s := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiffOn_succ_iff_fderivWithin hs]
  refine ⟨fun y hy ↦ (hD y hy).differentiableWithinAt, by simp, ?_⟩
  have heq : EqOn (fderivWithin ℝ w s) D s := fun y hy ↦ (hD y hy).fderivWithin (hs y hy)
  refine ContDiffOn.congr ?_ heq
  have h1 : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
  rw [h1, contDiffOn_succ_iff_fderivWithin hs]
  refine ⟨fun y hy ↦ (hH y hy).differentiableWithinAt, by simp, ?_⟩
  have heq' : EqOn (fderivWithin ℝ D s) Hs s := fun y hy ↦ (hH y hy).fderivWithin (hs y hy)
  exact (contDiffOn_zero.2 hHc).congr heq'

/-- **Local data** for the directional lemma at a point of `ball x r ∩ halfSpace ν`. -/
theorem exists_local_data {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ} {w : E → ℝ}
    (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U) (hUc : Convex ℝ U)
    (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {y₀ : E} (hy₀ : y₀ ∈ ball x r ∩ halfSpace ν)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ dist y₀ x + 4 * ρ ≤ r ∧
      ∃ K : Set E, Convex ℝ K ∧ K ⊆ U ∧ ∃ Λ L : ℝ, (∀ p ∈ K, ‖fderiv ℝ Φ p‖ ≤ Λ) ∧ 0 ≤ L ∧
        (∀ a ∈ K, ∀ b ∈ K, ‖fderiv ℝ Φ a - fderiv ℝ Φ b‖ ≤ L * ‖a - b‖) ∧
        (∀ y ∈ halfBall ν y₀ (4 * ρ), gradientWithin w (halfBall ν x r) y ∈ K) ∧
        ∃ Hw : ℝ≥0, HolderOnWith Hw α (gradientWithin w (halfBall ν x r))
            (halfBall ν y₀ (4 * ρ)) ∧
          ∃ M : ℝ, ∀ y ∈ halfBall ν y₀ (4 * ρ), ‖gradientWithin w (halfBall ν x r) y‖ ≤ M := by
  set B := halfBall ν x r with hB
  obtain ⟨α, hα, hα1, δ, hδ, H, hH⟩ := h.exists_holderOnWith_gradientWithin hν hr hx hU hUc
    hlam (hΦ.of_le (by norm_num)) hell hsym hrange hy₀
  have hy₀B : y₀ ∈ B := ⟨ball_subset_closedBall hy₀.1, hy₀.2⟩
  set p₀ := gradientWithin w B y₀ with hp₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p₀ (hrange y₀ hy₀B)
  set κ := ε / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  have hKU : closedBall p₀ κ ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨η, hη, hηc⟩ := Metric.continuousWithinAt_iff.1
    ((continuousOn_gradientWithin_halfBall hν hr hx h.1) y₀ hy₀B) κ hκ0
  have hdx : dist y₀ x < r := mem_ball.1 hy₀.1
  set ρ := min ρ₀ (min (δ / 4) (min (η / 8) ((r - dist y₀ x) / 4))) with hρ
  have hρ0 : 0 < ρ := by
    refine lt_min hρ₀ (lt_min (by positivity) (lt_min (by positivity) ?_))
    linarith
  have hρ1 : ρ ≤ ρ₀ := min_le_left _ _
  have hρ2 : ρ ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ η / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ4 : ρ ≤ (r - dist y₀ x) / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsub : halfBall ν y₀ (4 * ρ) ⊆ B :=
    inter_subset_inter_left _ (closedBall_subset_closedBall' (by linarith))
  -- `DΦ` is bounded and Lipschitz on `K`
  have hD1 : ContDiffOn ℝ 1 (fun p ↦ fderiv ℝ Φ p) U := hΦ.fderiv_of_isOpen hU (by norm_num)
  have hKc : IsCompact (closedBall p₀ κ) := isCompact_closedBall p₀ κ
  obtain ⟨Λ, hΛ⟩ := hKc.exists_bound_of_continuousOn
    ((hΦ.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU)
  obtain ⟨L₀, hL₀⟩ := hKc.exists_bound_of_continuousOn
    ((hD1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  set L := max L₀ 0 with hL
  have hlip : LipschitzOnWith (Real.toNNReal L) (fun p ↦ fderiv ℝ Φ p) (closedBall p₀ κ) := by
    refine (convex_closedBall p₀ κ).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun p ↦ fderiv ℝ (fun p ↦ fderiv ℝ Φ p) p) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · exact ((hD1.differentiableOn one_ne_zero p (hKU hp)).differentiableAt
        (hU.mem_nhds (hKU hp))).hasFDerivAt.hasFDerivWithinAt
    · rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
      exact (hL₀ p hp).trans (le_max_left _ _)
  refine ⟨α, hα, hα1, ρ, hρ0, hρ1, by linarith, closedBall p₀ κ, convex_closedBall p₀ κ, hKU,
    Λ, L, hΛ, le_max_right _ _, fun a ha b hb ↦ ?_, fun y hy ↦ ?_, H,
    hH.mono (halfBall_mono ν y₀ (by linarith)), ‖p₀‖ + κ, fun y hy ↦ ?_⟩
  · have := hlip.dist_le_mul a ha b hb
    rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)] at this
  · rw [mem_closedBall]
    exact (hηc (hsub hy) (by linarith [mem_closedBall.1 hy.1])).le
  · have : dist (gradientWithin w B y) p₀ < κ :=
      hηc (hsub hy) (by linarith [mem_closedBall.1 hy.1])
    rw [dist_eq_norm] at this
    linarith [norm_le_norm_add_norm_sub' (gradientWithin w B y) p₀]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A real Hölder bound with `α > 0` gives continuity. -/
theorem continuousOn_of_norm_sub_le {F : Type*} [NormedAddCommGroup F] {g : E → F} {S : Set E}
    {H α : ℝ} (hα : 0 < α) (hH0 : 0 ≤ H)
    (hH : ∀ y ∈ S, ∀ y' ∈ S, ‖g y - g y'‖ ≤ H * dist y y' ^ α) : ContinuousOn g S := by
  have : HolderOnWith (Real.toNNReal H) (Real.toNNReal α) g S :=
    holderOnWith_of_dist_le hH0 fun y hy y' hy' ↦ by
      rw [dist_eq_norm, Real.coe_toNNReal _ hα.le]; exact hH y hy y' hy'
  exact this.continuousOn (by simpa using hα)

/-- **Interior `C²`** (step 2 of the module docstring). -/
theorem contDiffOn_two_interior {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) :
    ContDiffOn ℝ 2 w (ball x r ∩ openHalfSpace ν) := by
  intro y₀ hy₀
  have hpos : 0 < ⟪y₀, ν⟫ := hy₀.2
  obtain ⟨α, hα, hα1, ρ, hρ, hρ₀, hdist, K, hK, hKU, Λ, L, hΛ, hL0, hL, hgK, Hw, hHw, M, hM⟩ :=
    exists_local_data hν hr hx hU hUc hlam hΦ hell hsym hrange h
      ⟨hy₀.1, mem_halfSpace.2 hpos.le⟩ (ρ₀ := ⟪y₀, ν⟫ / 8) (by positivity)
  have hinner : ∀ y ∈ closedBall y₀ (4 * ρ), 0 < ⟪y, ν⟫ := by
    intro y hy
    have h1 : |⟪y - y₀, ν⟫| ≤ dist y y₀ := by
      rw [dist_eq_norm]; exact (abs_real_inner_le_norm _ _).trans (by rw [hν, mul_one])
    have h2 : ⟪y - y₀, ν⟫ = ⟪y, ν⟫ - ⟪y₀, ν⟫ := inner_sub_left _ _ _
    linarith [(abs_le.1 h1).1, mem_closedBall.1 hy]
  set b := stdOrthonormalBasis ℝ E
  have hdir : ∀ i, ∃ g : E → E →L[ℝ] ℝ, (∀ y ∈ halfBall ν y₀ (ρ / 4),
      HasFDerivWithinAt (fun y ↦ fderivWithin ℝ w (halfBall ν x r) y (b i)) (g y)
        (halfBall ν y₀ (ρ / 4)) y) ∧
      ∃ H : ℝ, 0 ≤ H ∧ ∀ y ∈ halfBall ν y₀ (ρ / 4), ∀ y' ∈ halfBall ν y₀ (ρ / 4),
        ‖g y - g y'‖ ≤ H * dist y y' ^ (α : ℝ) := by
    intro i
    refine exists_hasFDerivWithinAt_fderivWithin_apply hα hα1 hν hU hUc
      (hΦ.of_le (by norm_num)) hlam hell hsym h hρ hpos.le hdist hK hKU hΛ hL0 hL hgK hHw hM
      (b.orthonormal.1 i).le fun t ht y hy ↦ ?_
    have hy4 : y ∈ closedBall y₀ (4 * ρ) := closedBall_subset_closedBall (by linarith) hy
    have hty : t • b i + y ∈ closedBall y₀ (4 * ρ) := by
      rw [mem_closedBall]
      have : dist (t • b i + y) y ≤ t := by
        rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht.1.le,
          b.orthonormal.1 i, mul_one]
      linarith [dist_triangle (t • b i + y) y y₀, mem_closedBall.1 hy, ht.2]
    exact ⟨fun _ ↦ (hinner y hy4).le, fun _ ↦ (hinner _ hty).le⟩
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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A function continuous on an open set times a continuous function supported in it is
continuous. -/
theorem continuous_mul_of_tsupport_subset {F φ : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hF : ContinuousOn F O) (hφ : Continuous φ) (hs : tsupport φ ⊆ O) :
    Continuous fun y ↦ F y * φ y := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  by_cases hy : y ∈ O
  · exact (hF.continuousAt (hO.mem_nhds hy)).mul hφ.continuousAt
  · have hy' : y ∉ tsupport φ := fun h ↦ hy (hs h)
    have h0 : (fun y ↦ F y * φ y) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy'] with z hz
      simp [hz]
    exact continuousAt_const.congr h0.symm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem integrable_mul_of_tsupport_subset {F φ : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hF : ContinuousOn F O) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ O) [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] : Integrable (fun y ↦ F y * φ y) μ :=
  (continuous_mul_of_tsupport_subset hO hF hφ hs).integrable_of_hasCompactSupport
    (hφc.mul_left (f := F))

/-- **The equation in nondivergence form in the interior** (step 3 of the module docstring):
`Σ_i D²w(b_i, A b_i) = 0` with `A = DΦ(∇w)`, i.e. `tr (DΦ(∇w) D²w) = 0`. -/
theorem trace_hessian_eq_zero {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {y : E} (hy : y ∈ ball x r ∩ openHalfSpace ν) :
    ∑ i, fderiv ℝ (fderiv ℝ w) y (b i) (fderiv ℝ Φ (∇ w y) (b i)) = 0 := by
  set Ω := ball x r ∩ openHalfSpace ν with hΩ
  have hΩo : IsOpen Ω := isOpen_ball.inter (isOpen_openHalfSpace ν)
  set B := halfBall ν x r with hB
  have hΩB : Ω ⊆ B := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, mem_halfSpace.2 (mem_openHalfSpace.1 hz.2).le⟩
  have hC2 := contDiffOn_two_interior hν hr hx hU hUc hlam hΦ hell hsym hrange h
  have hD1 : ContDiffOn ℝ 1 (fun z ↦ fderiv ℝ w z) Ω := hC2.fderiv_of_isOpen hΩo (by norm_num)
  have hD2c : ContinuousOn (fun z ↦ fderiv ℝ (fun z ↦ fderiv ℝ w z) z) Ω :=
    hD1.continuousOn_fderiv_of_isOpen hΩo le_rfl
  have hgr : ∀ z ∈ Ω, ∇ w z = gradientWithin w B z := fun z hz ↦
    (gradientWithin_halfBall_eq hz).symm
  have hgU : ∀ z ∈ Ω, ∇ w z ∈ U := fun z hz ↦ by rw [hgr z hz]; exact hrange z (hΩB hz)
  set T : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap with hT
  have hTa : ∀ ℓ, T ℓ = (InnerProductSpace.toDual ℝ E).symm ℓ := fun _ ↦ rfl
  have hgradD : ∀ z ∈ Ω, HasFDerivAt (fun z ↦ ∇ w z)
      (T ∘L fderiv ℝ (fun z ↦ fderiv ℝ w z) z) z := fun z hz ↦
    T.hasFDerivAt.comp z ((hD1.differentiableOn one_ne_zero z hz).differentiableAt
      (hΩo.mem_nhds hz)).hasFDerivAt
  set A : E → E →L[ℝ] E := fun z ↦ fderiv ℝ Φ (∇ w z) with hA
  have hVD : ∀ z ∈ Ω, HasFDerivAt (fun z ↦ Φ (∇ w z))
      (A z ∘L T ∘L fderiv ℝ (fun z ↦ fderiv ℝ w z) z) z := fun z hz ↦
    (((hΦ.differentiableOn (by norm_num)) _ (hgU z hz)).differentiableAt
      (hU.mem_nhds (hgU z hz))).hasFDerivAt.comp z (hgradD z hz)
  -- the components and their derivatives
  set term : ι → E → ℝ := fun j z ↦ ⟪b j, A z (T (fderiv ℝ (fun z ↦ fderiv ℝ w z) z (b j)))⟫
    with hterm
  have hVj : ∀ j, ∀ z ∈ Ω, HasFDerivAt (fun z ↦ ⟪b j, Φ (∇ w z)⟫)
      (innerSL ℝ (b j) ∘L (A z ∘L T ∘L fderiv ℝ (fun z ↦ fderiv ℝ w z) z)) z :=
    fun j z hz ↦ (innerSL ℝ (b j)).hasFDerivAt.comp z (hVD z hz)
  have hgc : ContinuousOn (fun z ↦ ∇ w z) Ω := fun z hz ↦
    (hgradD z hz).continuousAt.continuousWithinAt
  have hAc : ContinuousOn A Ω :=
    (hΦ.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp hgc hgU
  have hterm_c : ∀ j, ContinuousOn (term j) Ω := fun j ↦
    continuousOn_const.inner (hAc.clm_apply
      (T.continuous.comp_continuousOn (hD2c.clm_apply continuousOn_const)))
  have hVc : ∀ j, ContinuousOn (fun z ↦ ⟪b j, Φ (∇ w z)⟫) Ω := fun j ↦
    continuousOn_const.inner ((hΦ.continuousOn).comp hgc hgU)
  -- the weak identity against smooth tests supported in `Ω`
  have hzero : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ z, φ z • (∑ j, term j z) = 0 := by
    intro φ hφ hφc hφs
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
    have hw := h.2 φ ⟨hφ1, hφc, hφs.trans (fun z hz ↦ hz.1)⟩
    have hφ0 : ∀ z, z ∉ tsupport φ → φ z = 0 ∧ ∇ φ z = 0 := fun z hz ↦
      IsTestFn.eq_zero_and_gradient_eq_zero (U := tsupport φ) ⟨hφ1, hφc, subset_rfl⟩ hz
    have hpt : ∀ z, ⟪Φ (∇ w z), ∇ φ z⟫ = ∑ j, ⟪b j, Φ (∇ w z)⟫ * fderiv ℝ φ z (b j) := by
      intro z
      rw [← b.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [real_inner_comm (b j) (Φ (∇ w z))]
      congr 1
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have e1 : ∫ z in B, ⟪Φ (gradientWithin w B z), ∇ φ z⟫ =
        ∫ z, ∑ j, ⟪b j, Φ (∇ w z)⟫ * fderiv ℝ φ z (b j) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
        rw [(hφ0 z fun h' ↦ hz (hΩB (hφs h'))).2, inner_zero_right]]
      refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
      simp only
      rw [← hpt z]
      by_cases hz : z ∈ tsupport φ
      · rw [hgr z (hφs hz)]
      · rw [(hφ0 z hz).2, inner_zero_right, inner_zero_right]
    have hfd : ∀ j, Continuous fun z ↦ fderiv ℝ φ z (b j) := fun j ↦
      (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hint1 : ∀ j, Integrable fun z ↦ ⟪b j, Φ (∇ w z)⟫ * fderiv ℝ φ z (b j) := fun j ↦
      integrable_mul_of_tsupport_subset hΩo (hVc j) (hfd j) (hφc.fderiv_apply (𝕜 := ℝ) (b j))
        ((tsupport_fderiv_apply_subset ℝ (b j)).trans hφs)
    have hint2 : ∀ j, Integrable fun z ↦ term j z * φ z := fun j ↦
      integrable_mul_of_tsupport_subset hΩo (hterm_c j) hφd.continuous hφc hφs
    have hint3 : ∀ j, Integrable fun z ↦ ⟪b j, Φ (∇ w z)⟫ * φ z := fun j ↦
      integrable_mul_of_tsupport_subset hΩo (hVc j) hφd.continuous hφc hφs
    have hfdV : ∀ j z, fderiv ℝ (fun z ↦ ⟪b j, Φ (∇ w z)⟫) z (b j) * φ z = term j z * φ z := by
      intro j z
      by_cases hz : z ∈ tsupport φ
      · rw [(hVj j z (hφs hz)).fderiv]
        rfl
      · rw [(hφ0 z hz).1, mul_zero, mul_zero]
    have hibp : ∀ j, ∫ z, ⟪b j, Φ (∇ w z)⟫ * fderiv ℝ φ z (b j) = -∫ z, term j z * φ z := by
      intro j
      have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
        (f := fun z ↦ ⟪b j, Φ (∇ w z)⟫) (g := φ) (v := b j)
        ((hint2 j).congr (Eventually.of_forall fun z ↦ (hfdV j z).symm)) (hint1 j) (hint3 j)
        (fun z hz ↦ (hVj j z (hφs hz)).differentiableAt) (fun z _ ↦ hφd z)
      rw [this]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun z ↦ hfdV j z)
    rw [e1, integral_finsetSum _ fun j _ ↦ hint1 j] at hw
    simp only [hibp, Finset.sum_neg_distrib, neg_eq_zero] at hw
    rw [← integral_finsetSum _ fun j _ ↦ hint2 j] at hw
    rw [← hw]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    simp only [smul_eq_mul, Finset.mul_sum, mul_comm]
  have hsum_c : ContinuousOn (fun z ↦ ∑ j, term j z) Ω :=
    continuousOn_finsetSum _ fun j _ ↦ hterm_c j
  have hae := hΩo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hsum_c.locallyIntegrableOn hΩo.measurableSet) hzero
  have heq := Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hΩo.measurableSet).2 hae) hΩo
    hsum_c continuousOn_const
  have hy0 : ∑ j, term j y = 0 := heq hy
  rw [← hy0]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hs := hsym _ (hgU y hy) (b j) (T (fderiv ℝ (fun z ↦ fderiv ℝ w z) y (b j)))
  simp only [ContinuousLinearMap.coe_coe] at hs
  simp only [hterm, hA]
  rw [← hs, real_inner_comm, hTa, InnerProductSpace.toDual_symm_apply]

/-! ### The normal–normal derivative from the equation -/

section Algebra

variable {ι : Type*} [Fintype ι]

/-- The part of the Hessian determined by the tangential rows `g_i = D²w(·, b_i - ⟪b_i, ν⟫ ν)`:
`Q(ξ, η) = Σ_i ⟪b_i, η⟫ g_i ξ + ⟪η, ν⟫ Σ_i ⟪b_i, ξ⟫ g_i ν`. -/
@[expose] noncomputable def tangentialHessian (b : OrthonormalBasis ι ℝ E) (ν : E)
    (g : ι → E →L[ℝ] ℝ) (ξ η : E) : ℝ :=
  ∑ i, ⟪b i, η⟫ * g i ξ + ⟪η, ν⟫ * ∑ i, ⟪b i, ξ⟫ * g i ν

/-- The normal–normal second derivative solved from `Σ_j D²w(b_j, A b_j) = 0`:
`-(Σ_j Q(b_j, A b_j)) / ⟪A ν, ν⟫`. -/
@[expose] noncomputable def normalHessian (b : OrthonormalBasis ι ℝ E) (ν : E) (A : E →L[ℝ] E)
    (g : ι → E →L[ℝ] ℝ) : ℝ :=
  -(∑ j, tangentialHessian b ν g (b j) (A (b j))) / ⟪A ν, ν⟫

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The normal–normal derivative from the equation.** If `H` is symmetric, its tangential rows
are `g_i`, and `Σ_j H(b_j, A b_j) = 0` with `A` symmetric and `⟪A ν, ν⟫ ≠ 0`, then
`H(ξ, ν) = Σ_i ⟪b_i, ξ⟫ g_i ν + ⟪ν, ξ⟫ · normalHessian`. -/
theorem hessian_apply_normal (b : OrthonormalBasis ι ℝ E) {ν : E} (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : ∀ u v, H u v = H v u) {A : E →L[ℝ] E} (hA : (A : E →ₗ[ℝ] E).IsSymmetric)
    (hAν : ⟪A ν, ν⟫ ≠ 0) (heq : ∑ j, H (b j) (A (b j)) = 0) {g : ι → E →L[ℝ] ℝ}
    (hg : ∀ i ξ, g i ξ = H ξ (b i - ⟪b i, ν⟫ • ν)) (ξ : E) :
    H ξ ν = ∑ i, ⟪b i, ξ⟫ * g i ν + ⟪ν, ξ⟫ * normalHessian b ν A g := by
  -- `H(ξ, η) = Σ_i ⟪b_i, η⟫ g_i ξ + ⟪η, ν⟫ H(ξ, ν)`
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
  have L3 : ∀ ξ η, H ξ η = tangentialHessian b ν g ξ η + ⟪ξ, ν⟫ * ⟪η, ν⟫ * H ν ν := by
    intro ξ η
    rw [L1 ξ η, L2 ξ, tangentialHessian]; ring
  have hsumA : ∑ j, ⟪b j, ν⟫ * ⟪A (b j), ν⟫ = ⟪A ν, ν⟫ := by
    rw [real_inner_comm, ← b.sum_inner_mul_inner ν (A ν)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hs := hA (b j) ν
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [real_inner_comm (b j) ν, hs]
  have hnn : H ν ν = normalHessian b ν A g := by
    have heq' : ∑ j, (tangentialHessian b ν g (b j) (A (b j)) +
        ⟪b j, ν⟫ * ⟪A (b j), ν⟫ * H ν ν) = 0 := by
      rw [← heq]; exact Finset.sum_congr rfl fun j _ ↦ (L3 _ _).symm
    rw [Finset.sum_add_distrib] at heq'
    have : ∑ j, ⟪b j, ν⟫ * ⟪A (b j), ν⟫ * H ν ν = ⟪A ν, ν⟫ * H ν ν := by
      rw [← hsumA, Finset.sum_mul]
    rw [this] at heq'
    rw [normalHessian, eq_div_iff hAν]
    linarith
  rw [L2 ξ, hnn, real_inner_comm]

end Algebra

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An open subset of the closed half space lies in the open half space. -/
theorem subset_openHalfSpace_of_isOpen {ν : E} (hν : ‖ν‖ = 1) {O : Set E} (hO : IsOpen O)
    (hOH : O ⊆ halfSpace ν) : O ⊆ openHalfSpace ν := by
  intro z hz
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO z hz
  have hmem : z - (ε / 2) • ν ∈ ball z ε := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
      Real.norm_of_nonneg (by positivity)]
    linarith
  have h1 := mem_halfSpace.1 (hOH (hεO hmem))
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν] at h1
  exact mem_openHalfSpace.2 (by linarith)

/-- **Hölder second derivatives near every point of `ball x r ∩ halfSpace ν`** (step 4 of the
module docstring): on a small half ball `S` around `y₀`, `D_B w` has a within-derivative `Hs`
which is `α`-Hölder on `S`. -/
theorem exists_hessian_holder_halfBall {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {y₀ : E} (hy₀ : y₀ ∈ ball x r ∩ halfSpace ν) :
    ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧ ∃ ρ > 0, closedBall y₀ ρ ⊆ ball x r ∧
      ∃ Hs : E → E →L[ℝ] E →L[ℝ] ℝ,
        (∀ y ∈ halfBall ν y₀ ρ, HasFDerivWithinAt (fderivWithin ℝ w (halfBall ν x r)) (Hs y)
          (halfBall ν y₀ ρ) y) ∧
        ∃ C : ℝ≥0, HolderOnWith C α Hs (halfBall ν y₀ ρ) := by
  obtain ⟨α, hα, hα1, ρ, hρ, -, hdist, K, hK, hKU, Λ, L, hΛ, hL0, hL, hgK, Hw, hHw, M, hM⟩ :=
    exists_local_data hν hr hx hU hUc hlam hΦ hell hsym hrange h hy₀ one_pos
  set B := halfBall ν x r with hB
  set S := halfBall ν y₀ (ρ / 4) with hS
  have hy₀ν : 0 ≤ ⟪y₀, ν⟫ := hy₀.2
  have hSB : S ⊆ B := inter_subset_inter_left _ (closedBall_subset_closedBall' (by linarith))
  have huS : UniqueDiffOn ℝ S := uniqueDiffOn_halfBall hν (by positivity) (by linarith)
  have hBu : UniqueDiffOn ℝ B := uniqueDiffOn_halfBall hν hr hx
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
      ∃ H : ℝ, 0 ≤ H ∧ ∀ y ∈ S, ∀ y' ∈ S, ‖g y - g y'‖ ≤ H * dist y y' ^ (α : ℝ) := by
    intro i
    refine exists_hasFDerivWithinAt_fderivWithin_apply hα hα1 hν hU hUc
      (hΦ.of_le (by norm_num)) hlam hell hsym h hρ hy₀ν hdist hK hKU hΛ hL0 hL hgK hHw hM
      (he1 i) fun t _ y _ ↦ ?_
    rw [inner_add_left, real_inner_smul_left, hetan, mul_zero, zero_add]
  choose g hg H hH0 hH using hdir
  have hgc : ∀ i, ContinuousOn (g i) S := fun i ↦
    continuousOn_of_norm_sub_le (by exact_mod_cast hα) (hH0 i) (hH i)
  have hgH : ∀ i, ∃ C, HolderOnWith C α (g i) S := fun i ↦
    ⟨_, holderOnWith_of_dist_le (hH0 i) fun y hy y' hy' ↦ by
      rw [dist_eq_norm]; exact hH i y hy y' hy'⟩
  have hSc : IsCompact S := isCompact_halfBall ν y₀ (ρ / 4)
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
  have hC2 := contDiffOn_two_interior hν hr hx hU hUc hlam hΦ hell hsym hrange h
  have hΩo : IsOpen (ball x r ∩ openHalfSpace ν) := isOpen_ball.inter (isOpen_openHalfSpace ν)
  -- the coefficient `A = DΦ(∇w)` on `S`
  set A : E → E →L[ℝ] E := fun y ↦ fderiv ℝ Φ (gradientWithin w B y) with hA
  have hgwc : ContinuousOn (gradientWithin w B) S :=
    (continuousOn_gradientWithin_halfBall hν hr hx h.1).mono hSB
  have hAc : ContinuousOn A S :=
    (hΦ.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp hgwc fun y hy ↦ hrange y (hSB hy)
  have hApos : ∀ y ∈ S, 0 < ⟪A y ν, ν⟫ := fun y hy ↦ by
    have := hell _ (hrange y (hSB hy)) ν
    rw [hν] at this
    simp only [hA]
    linarith
  -- the candidate derivative of `∂_ν w`
  set gν : E → E →L[ℝ] ℝ := fun y ↦ ∑ i, (g i y ν) • innerSL ℝ (b i) +
    normalHessian b ν (A y) (fun i ↦ g i y) • innerSL ℝ ν with hgν
  have hnHc : ContinuousOn (fun y ↦ normalHessian b ν (A y) (fun i ↦ g i y)) S := by
    simp only [normalHessian, tangentialHessian]
    refine ContinuousOn.div (ContinuousOn.neg (continuousOn_finsetSum _ fun j _ ↦ ?_))
      ((hAc.clm_apply continuousOn_const).inner continuousOn_const)
      fun y hy ↦ (hApos y hy).ne'
    refine (continuousOn_finsetSum _ fun i _ ↦ ?_).add
      (((hAc.clm_apply continuousOn_const).inner continuousOn_const).mul
        (continuousOn_finsetSum _ fun i _ ↦ continuousOn_const.mul
          ((hgc i).clm_apply continuousOn_const)))
    exact (continuousOn_const.inner (hAc.clm_apply continuousOn_const)).mul
      ((hgc i).clm_apply continuousOn_const)
  have hgνc : ContinuousOn gν S := by
    refine (continuousOn_finsetSum _ fun i _ ↦ ?_).add (hnHc.smul continuousOn_const)
    exact ((hgc i).clm_apply continuousOn_const).smul continuousOn_const
  -- Hölder continuity of the pieces on `S`
  have hS4 : S ⊆ halfBall ν y₀ (4 * ρ) := halfBall_mono ν y₀ (by linarith)
  have hAH : ∃ C, HolderOnWith C α A S := by
    have hlip : LipschitzOnWith (Real.toNNReal L) (fun p ↦ fderiv ℝ Φ p) K :=
      LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ by
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]; exact hL a ha b hb
    exact ⟨_, holderOnWith_comp_lipschitzOnWith hlip (hHw.mono hS4) fun y hy ↦ hgK y (hS4 hy)⟩
  have hinner : ∀ (v : E) {V : E → E}, (∃ C, HolderOnWith C α V S) →
      ∃ C, HolderOnWith C α (fun y ↦ ⟪v, V y⟫) S := fun v V hV ↦ by
    simpa only [innerSL_apply_apply] using exists_holderOnWith_clm (innerSL ℝ v) hV
  have hinner' : ∀ (v : E) {V : E → E}, (∃ C, HolderOnWith C α V S) →
      ∃ C, HolderOnWith C α (fun y ↦ ⟪V y, v⟫) S := fun v V hV ↦ by
    simpa only [real_inner_comm v] using hinner v hV
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
  have hnHH : ∃ C, HolderOnWith C α
      (fun y ↦ normalHessian b ν (A y) (fun i ↦ g i y)) S := by
    have e : (fun y ↦ normalHessian b ν (A y) (fun i ↦ g i y)) = fun y ↦
        -(∑ j, (∑ i, ⟪b i, A y (b j)⟫ * g i y (b j) +
          ⟪A y (b j), ν⟫ * ∑ i, ⟪b i, b j⟫ * g i y ν)) * (⟪A y ν, ν⟫)⁻¹ := by
      funext y; simp only [normalHessian, tangentialHessian, div_eq_mul_inv]
    rw [e]
    refine hmul (exists_holderOnWith_neg (exists_holderOnWith_sum _ fun j _ ↦
      exists_holderOnWith_add (exists_holderOnWith_sum _ fun i _ ↦
        hmul (hinner (b i) (happ (b j) hAH)) (happR (b j) (hgH i)))
        (hmul (hinner' ν (happ (b j) hAH)) (exists_holderOnWith_sum _ fun i _ ↦
          hmul (exists_holderOnWith_const _) (happR ν (hgH i))))))
      (exists_holderOnWith_inv hlam (hinner' ν (happ ν hAH)) fun y hy ↦ ?_)
    have := hell _ (hrange y (hSB hy)) ν
    rw [hν] at this
    simp only [hA]
    linarith
  have hgνH : ∃ C, HolderOnWith C α gν S :=
    exists_holderOnWith_add (exists_holderOnWith_sum _ fun i _ ↦ hsmulc _ (happR ν (hgH i)))
      (hsmulc _ hnHH)
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
    have happ : ∀ v : E, HasFDerivAt (fun z ↦ fderivWithin ℝ w B z v)
        ((ContinuousLinearMap.apply ℝ ℝ v) ∘L H2) y := fun v ↦
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hD2).congr_of_eventuallyEq
        (hev.mono fun z hz ↦ by simp only [Function.comp_apply, hz,
          ContinuousLinearMap.apply_apply])
    have hSn : S ∈ 𝓝 y := mem_interior_iff_mem_nhds.1 hy
    have hgi : ∀ i ξ, g i y ξ = H2 ξ (b i - ⟪b i, ν⟫ • ν) := fun i ξ ↦ by
      have := ((hg i y (hΩ'S hy)).hasFDerivAt hSn).unique (happ (e i))
      rw [this]; rfl
    have hsymm : ∀ u v, H2 u v = H2 v u := fun u v ↦
      hcd.isSymmSndFDerivAt (by simp) u v
    have hgr : ∇ w y = gradientWithin w B y := (gradientWithin_halfBall_eq hyΩ).symm
    have heq := trace_hessian_eq_zero hν hr hx hU hUc hlam hΦ hell hsym hrange h b hyΩ
    rw [hgr] at heq
    have hAs : (A y : E →ₗ[ℝ] E).IsSymmetric := hsym _ (hrange y (hSB (hΩ'S hy)))
    convert happ ν using 1
    ext ξ
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.apply_apply]
    rw [hessian_apply_normal b H2 hsymm hAs (hApos y (hΩ'S hy)).ne' heq hgi ξ]
    simp only [hgν, add_apply, FunLike.coe_sum,
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
  refine ⟨α, hα, hα1, ρ / 4, by positivity, fun y hy ↦ ?_, Hs, hHd, hHsH⟩
  rw [mem_ball]
  linarith [mem_closedBall.1 hy, dist_triangle y y₀ x]

/-- **`C²` near every point of `ball x r ∩ halfSpace ν`** (step 4 of the module docstring). -/
theorem exists_contDiffOn_two_halfBall {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {y₀ : E} (hy₀ : y₀ ∈ ball x r ∩ halfSpace ν) :
    ∃ ρ > 0, ContDiffOn ℝ 2 w (halfBall ν y₀ ρ) := by
  obtain ⟨α, hα, -, ρ, hρ, hball, Hs, hHd, C, hC⟩ :=
    exists_hessian_holder_halfBall hν hr hx hU hUc hlam hΦ hell hsym hrange h hy₀
  have hy₀ν : 0 ≤ ⟪y₀, ν⟫ := hy₀.2
  have hSB : halfBall ν y₀ ρ ⊆ halfBall ν x r := fun y hy ↦
    ⟨ball_subset_closedBall (hball hy.1), hy.2⟩
  refine ⟨ρ, hρ, contDiffOn_two_of_hasFDerivWithinAt
    (uniqueDiffOn_halfBall hν hρ (by linarith)) (D := fderivWithin ℝ w (halfBall ν x r))
    (fun y hy ↦ ?_) hHd (hC.continuousOn hα)⟩
  exact ((h.1.differentiableOn one_ne_zero y (hSB hy)).hasFDerivWithinAt).mono hSB

/-- **`C²` up to the flat part for quasilinear conormal solutions** (`k = 1` of
`Div.QuasilinearConormalStatement`). -/
theorem contDiffOn_two_halfBall_of_quasilinear_conormal {ν x : E} {r : ℝ} {Φ : E → E}
    {U : Set E} {lam : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫)
    (hU : IsOpen U) (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) : ContDiffOn ℝ 2 w (halfBall ν x (r / 2)) := by
  intro y hy
  have hy' : y ∈ ball x r ∩ halfSpace ν :=
    ⟨mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (by linarith)), hy.2⟩
  obtain ⟨ρ, hρ, hc⟩ := exists_contDiffOn_two_halfBall hν hr hx hU hUc hlam hΦ hell hsym hrange
    h hy'
  refine (hc y ⟨mem_closedBall_self hρ.le, hy.2⟩).mono_of_mem_nhdsWithin ?_
  exact mem_of_superset (inter_mem_nhdsWithin _ (ball_mem_nhds y hρ))
    fun z hz ↦ ⟨ball_subset_closedBall hz.2, hz.1.2⟩

end BasicElliptic.Div
