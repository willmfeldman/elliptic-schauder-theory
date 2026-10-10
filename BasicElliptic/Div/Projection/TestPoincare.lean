/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Projection.GradientField
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Poincaré inequality for test functions on a ball

* `BasicElliptic.Div.integral_sq_le_of_isSmoothTestFn`: for `φ ∈ C_c^∞(B_R(x₀))` (and `E`
  nontrivial), `∫ φ² ≤ (2R)² ∫ ‖∇φ‖²`.
* `BasicElliptic.Div.abs_setIntegral_mul_le`: for `|f| ≤ M_f` on `B = B_R(x₀)`,
  `|∫_B f φ| ≤ 2R |B|^{1/2} M_f ‖∇φ‖_{L²(B)}`. This bounds the `f`-term of the weak identity by
  the `L²` norm of the test gradient, which is what the energy comparison needs.

## Proof

Fix a unit vector `ν` and put `g(y) = ⟪ν, y - x₀⟫`, so `∂_ν g = 1` and `|g| < R` on the ball.
Integration by parts (no boundary terms, `φ` has compact support) gives
`∫ φ² = ∫ φ² ∂_ν g = -∫ ∂_ν(φ²) g = -2 ∫ φ ∂_ν φ g ≤ 2R ∫ |φ| ‖∇φ‖`.
By `2R a b ≤ a²/2 + 2R² b²`, `∫ φ² ≤ ½ ∫ φ² + 2R² ∫ ‖∇φ‖²`, i.e. `∫ φ² ≤ 4R² ∫ ‖∇φ‖²`. (No Fubini
in an orthonormal frame is needed.) Then
`|∫_B f φ| ≤ M_f ∫_B |φ| ≤ M_f |B|^{1/2} ‖φ‖_{L²(B)}` by Cauchy–Schwarz in `L²(B)`.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace
open scoped Gradient ContDiff Topology

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem integrable_of_cont_cs {g : E → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable g :=
  hg.integrable_of_hasCompactSupport hgc

/-- **Poincaré inequality for test functions on a ball:** `∫ φ² ≤ (2R)² ∫ ‖∇φ‖²` for
`φ ∈ C_c^∞(B_R(x₀))`. -/
theorem integral_sq_le_of_isSmoothTestFn [Nontrivial E] {x₀ : E} {R : ℝ} {φ : E → ℝ}
    (hφ : IsSmoothTestFn (ball x₀ R) φ) :
    ∫ y, φ y ^ 2 ≤ (2 * R) ^ 2 * ∫ y, ‖∇ φ y‖ ^ 2 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set ν : E := ‖v‖⁻¹ • v
  have hν : ‖ν‖ = 1 := norm_smul_inv_norm hv
  set g : E → ℝ := fun y ↦ innerSL ℝ ν (y - x₀)
  have hg_deriv : ∀ y, HasFDerivAt g ((innerSL ℝ ν).comp (ContinuousLinearMap.id ℝ E)) y :=
    fun y ↦ (innerSL ℝ ν).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x₀)
  have hg_fd : ∀ y, fderiv ℝ g y ν = 1 := fun y ↦ by
    rw [(hg_deriv y).fderiv]
    simp [hν]
  have hg_cont : Continuous g := (innerSL ℝ ν).continuous.comp (continuous_id.sub continuous_const)
  set q : E → ℝ := fun y ↦ φ y * φ y
  have hq_diff : Differentiable ℝ q := hφ.differentiable.mul hφ.differentiable
  have hq_fd : ∀ y, fderiv ℝ q y ν = 2 * (φ y * fderiv ℝ φ y ν) := fun y ↦ by
    rw [fderiv_fun_mul (hφ.differentiable y) (hφ.differentiable y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hdφ := hφ.fderiv_apply ν
  have hqc : HasCompactSupport q := hφ.2.1.mul_left
  -- integration by parts
  have hibp : ∫ y, q y * fderiv ℝ g y ν = -∫ y, fderiv ℝ q y ν * g y := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
      (fun y _ ↦ hq_diff y) (fun y _ ↦ (hg_deriv y).differentiableAt)
    · simp_rw [hq_fd]
      exact integrable_of_cont_cs
        ((continuous_const.mul (hφ.1.continuous.mul hdφ.1.continuous)).mul hg_cont)
        (hdφ.2.1.mul_left.mul_left.mul_right)
    · simp_rw [hg_fd, mul_one]
      exact integrable_of_cont_cs (hφ.1.continuous.mul hφ.1.continuous) hqc
    · exact integrable_of_cont_cs ((hφ.1.continuous.mul hφ.1.continuous).mul hg_cont)
        hqc.mul_right
  simp_rw [hg_fd, mul_one, hq_fd] at hibp
  have hsq : ∀ y, φ y ^ 2 = q y := fun y ↦ sq (φ y)
  simp_rw [hsq]
  -- pointwise bound
  have hpt : ∀ y, -(2 * (φ y * fderiv ℝ φ y ν) * g y) ≤
      q y / 2 + 2 * R ^ 2 * ‖∇ φ y‖ ^ 2 := by
    intro y
    by_cases hy : y ∈ tsupport φ
    · have hyB : y ∈ ball x₀ R := hφ.2.2 hy
      have hgy : |g y| ≤ R := by
        have := abs_real_inner_le_norm ν (y - x₀)
        rw [hν, one_mul] at this
        exact this.trans (mem_ball_iff_norm.1 hyB).le
      have hdy : |fderiv ℝ φ y ν| ≤ ‖∇ φ y‖ := by
        rw [← inner_gradient_left]
        simpa [hν] using abs_real_inner_le_norm (∇ φ y) ν
      have h1 : -(2 * (φ y * fderiv ℝ φ y ν) * g y) ≤ 2 * R * (|φ y| * ‖∇ φ y‖) := by
        have : |2 * (φ y * fderiv ℝ φ y ν) * g y| ≤ 2 * R * (|φ y| * ‖∇ φ y‖) := by
          rw [abs_mul, abs_mul, abs_mul, abs_two]
          have := mul_le_mul (mul_le_mul_of_nonneg_left hdy (abs_nonneg (φ y))) hgy
            (abs_nonneg _) (by positivity)
          nlinarith
        exact (neg_le_abs _).trans this
      have h2 : 2 * R * (|φ y| * ‖∇ φ y‖) ≤ q y / 2 + 2 * R ^ 2 * ‖∇ φ y‖ ^ 2 := by
        have hq : q y = |φ y| ^ 2 := by simp [q, sq]
        rw [hq]
        nlinarith [sq_nonneg (|φ y| - 2 * R * ‖∇ φ y‖)]
      exact h1.trans h2
    · have : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp only [this, zero_mul, mul_zero, neg_zero, q]
      positivity
  have hgradc : Continuous fun y ↦ ‖∇ φ y‖ ^ 2 := (hφ.continuous_gradient.norm.pow 2)
  have hgradcs : HasCompactSupport fun y ↦ ‖∇ φ y‖ ^ 2 :=
    hφ.hasCompactSupport_gradient.comp_left (g := fun v : E ↦ ‖v‖ ^ 2) (by simp)
  have hint_q : Integrable q := integrable_of_cont_cs (hφ.1.continuous.mul hφ.1.continuous) hqc
  have hint_g : Integrable fun y ↦ ‖∇ φ y‖ ^ 2 := integrable_of_cont_cs hgradc hgradcs
  have hmono : ∫ y, q y ≤ ∫ y, (q y / 2 + 2 * R ^ 2 * ‖∇ φ y‖ ^ 2) := by
    rw [hibp, ← integral_neg]
    refine integral_mono ?_ ((hint_q.div_const 2).add (hint_g.const_mul _)) hpt
    exact (integrable_of_cont_cs
      ((continuous_const.mul (hφ.1.continuous.mul hdφ.1.continuous)).mul hg_cont)
      (hdφ.2.1.mul_left.mul_left.mul_right)).neg
  rw [integral_add (hint_q.div_const 2) (hint_g.const_mul _), integral_div,
    integral_const_mul] at hmono
  nlinarith

/-- The same inequality with integrals over the ball. -/
theorem setIntegral_sq_le_of_isSmoothTestFn [Nontrivial E] {x₀ : E} {R : ℝ} {φ : E → ℝ}
    (hφ : IsSmoothTestFn (ball x₀ R) φ) :
    ∫ y in ball x₀ R, φ y ^ 2 ≤ (2 * R) ^ 2 * ∫ y in ball x₀ R, ‖∇ φ y‖ ^ 2 := by
  have h1 : ∫ y in ball x₀ R, φ y ^ 2 = ∫ y, φ y ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hφ.2.2 h))]; simp
  have h2 : ∫ y in ball x₀ R, ‖∇ φ y‖ ^ 2 = ∫ y, ‖∇ φ y‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hφ.tsupport_gradient_subset h))]; simp
  rw [h1, h2]
  exact integral_sq_le_of_isSmoothTestFn hφ

/-- **The `f`-term of the weak identity.** For `|f| ≤ M_f` on `B = B_R(x₀)` and
`φ ∈ C_c^∞(B)`: `|∫_B f φ| ≤ 2R |B|^{1/2} M_f ‖∇φ‖_{L²(B)}`. -/
theorem abs_setIntegral_mul_le [Nontrivial E] {x₀ : E} {R : ℝ} {f : E → ℝ} {Mf : ℝ}
    (hf : ∀ y ∈ ball x₀ R, |f y| ≤ Mf) {φ : E → ℝ} (hφ : IsSmoothTestFn (ball x₀ R) φ) :
    |∫ y in ball x₀ R, f y * φ y| ≤
      2 * R * √(volume.real (ball x₀ R)) * Mf * √(∫ y in ball x₀ R, ‖∇ φ y‖ ^ 2) := by
  set μ := volume.restrict (ball x₀ R)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  rcases (Set.eq_empty_or_nonempty (ball x₀ R)) with hB | ⟨z, hz⟩
  · simp [μ, hB]
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hf z hz)
  have hR : 0 < R := pos_of_mem_ball hz
  have hfb : ∀ᵐ y ∂μ, ‖f y‖ ≤ Mf :=
    (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy ↦ hf y hy)
  have hφL : MemLp (fun y ↦ |φ y|) 2 μ :=
    memLp_two_of_continuous_of_hasCompactSupport hφ.1.continuous.abs hφ.2.1.abs
  have h1L : MemLp (fun _ : E ↦ Mf) 2 μ := memLp_const Mf
  -- `|∫ f φ| ≤ ∫ Mf |φ|`
  have hstep1 : |∫ y, f y * φ y ∂μ| ≤ ∫ y, Mf * |φ y| ∂μ := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ ↦ abs_nonneg _) ((hφL.integrable one_le_two).const_mul Mf) ?_)
    filter_upwards [hfb] with y hy
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).symm.le.trans hy) (abs_nonneg _)
  -- Cauchy–Schwarz in `L²(B)`
  have hstep2 : ∫ y, Mf * |φ y| ∂μ ≤ √(∫ y, ‖Mf‖ ^ 2 ∂μ) * √(∫ y, ‖|φ y|‖ ^ 2 ∂μ) := by
    have := real_inner_le_norm (h1L.toLp _) (hφL.toLp _)
    rw [inner_toLp_toLp, norm_toLp_eq_sqrt_integral, norm_toLp_eq_sqrt_integral] at this
    simpa [mul_comm] using this
  have hconst : ∫ y, ‖Mf‖ ^ 2 ∂μ = Mf ^ 2 * volume.real (ball x₀ R) := by
    simp [μ, integral_const, Measure.real, mul_comm]
  have hφsq : ∫ y, ‖|φ y|‖ ^ 2 ∂μ = ∫ y in ball x₀ R, φ y ^ 2 := by simp [μ]
  have hP := setIntegral_sq_le_of_isSmoothTestFn hφ
  have hsqrtP : √(∫ y in ball x₀ R, φ y ^ 2) ≤ 2 * R * √(∫ y in ball x₀ R, ‖∇ φ y‖ ^ 2) := by
    calc √(∫ y in ball x₀ R, φ y ^ 2)
        ≤ √((2 * R) ^ 2 * ∫ y in ball x₀ R, ‖∇ φ y‖ ^ 2) := Real.sqrt_le_sqrt hP
      _ = 2 * R * √(∫ y in ball x₀ R, ‖∇ φ y‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hconst, hφsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hMf] at hstep2
  calc |∫ y in ball x₀ R, f y * φ y| ≤ Mf * √(volume.real (ball x₀ R)) *
        √(∫ y in ball x₀ R, φ y ^ 2) := hstep1.trans hstep2
    _ ≤ Mf * √(volume.real (ball x₀ R)) * (2 * R * √(∫ y in ball x₀ R, ‖∇ φ y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsqrtP (by positivity)
    _ = _ := by ring

end BasicElliptic.Div
