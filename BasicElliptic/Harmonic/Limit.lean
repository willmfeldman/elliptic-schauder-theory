/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Harmonic.Estimates

/-!
# Locally uniform limits of harmonic functions

Let `E` be a finite-dimensional real inner product space.

* `BasicElliptic.weaklyHarmonicOn_of_tendstoLocallyUniformlyOn`: a locally uniform limit of
  continuous weakly harmonic functions is weakly harmonic.
* `BasicElliptic.harmonicOnNhd_of_tendstoLocallyUniformlyOn`: a locally uniform limit of harmonic
  functions is harmonic, and the derivatives converge locally uniformly.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001.

## Provenance

Ported from elliptic-bernoulli-foundations (W. M. Feldman), `EllipticBernoulli/Harmonic/Limit.lean`,
commit ea02c735ae1af1b0eab48928ff959c41ed49e9a8 (section `General`). Changes: namespace
`BasicElliptic`; `harmonicOnNhd_of_tendstoLocallyUniformlyOn'` renamed
`harmonicOnNhd_of_tendstoLocallyUniformlyOn`; the `E d` wrapper (`HarmonicLimitStatement`) is
not ported.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology ContinuousLinearMap
open scoped ContDiff Laplacian
open ViscositySolns.Analysis (WeaklyHarmonicOn tsupport_laplacian_subset)

public section

namespace BasicElliptic

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian of a smooth function is continuous. (Private helper; `continuous_laplacian`
in `Viscosity/Jet.lean` is the public, more general version.) -/
private theorem continuous_laplacian_of_contDiff {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (Δ χ) := by
  set b := stdOrthonormalBasis ℝ E
  have h : Δ χ = fun x ↦ ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) :=
    funext (ViscositySolns.Analysis.laplacian_eq_sum_fderiv_fderiv b (hχ.of_le (by norm_cast)))
  rw [h]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  have h1 : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ χ y (b i)) :=
    (hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  exact ((h1.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- A locally uniform limit of continuous weakly harmonic functions is weakly harmonic. -/
theorem weaklyHarmonicOn_of_tendstoLocallyUniformlyOn [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {ι : Type*} {p : Filter ι} [p.NeBot]
    {U : Set E} (hU : IsOpen U) {F : ι → E → ℝ} {f : E → ℝ}
    (hFc : ∀ k, ContinuousOn (F k) U) (hF : ∀ k, WeaklyHarmonicOn μ (F k) U)
    (hconv : TendstoLocallyUniformlyOn F f p U) : WeaklyHarmonicOn μ f U := by
  intro χ hχ hχc hχU
  have hfc : ContinuousOn f U := hconv.continuousOn (Frequently.of_forall hFc)
  have hΔc : Continuous (Δ χ) := continuous_laplacian_of_contDiff hχ
  have hΔs : tsupport (Δ χ) ⊆ tsupport χ := tsupport_laplacian_subset χ
  have hΔcs : HasCompactSupport (Δ χ) := hχc.mono' (subset_tsupport _ |>.trans hΔs)
  have hint : ∀ g : E → ℝ, ContinuousOn g U → Integrable (fun x ↦ Δ χ x • g x) μ :=
    fun g hg ↦ ((hΔc.continuousOn.smul hg).continuous_of_tsupport_subset hU
      ((tsupport_smul_subset_left _ _).trans (hΔs.trans hχU))).integrable_of_hasCompactSupport
      hΔcs.smul_right
  have hunif : TendstoUniformlyOn F f p (tsupport χ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hχU hχc
  set A := ∫ x, ‖Δ χ x‖ ∂μ
  have hAi : Integrable (fun x ↦ ‖Δ χ x‖) μ := (hΔc.integrable_of_hasCompactSupport hΔcs).norm
  -- `‖∫ Δχ f‖ ≤ ε A` for every `ε > 0`
  have hle : ∀ ε > 0, ‖∫ x, Δ χ x • f x ∂μ‖ ≤ ε * A := by
    intro ε hε
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.1 hunif ε hε).exists
    have hsub : ∫ x, Δ χ x • f x ∂μ = ∫ x, Δ χ x • (f x - F k x) ∂μ := by
      simp_rw [smul_sub]
      rw [integral_sub (hint f hfc) (hint _ (hFc k)), hF k χ hχ hχc hχU, sub_zero]
    rw [hsub, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hAi.const_mul ε) (Eventually.of_forall fun x ↦ ?_)
    rw [norm_smul]
    by_cases hx : x ∈ tsupport χ
    · rw [mul_comm ε]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← dist_eq_norm]
      exact (hk x hx).le
    · have : Δ χ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hΔs h)
      simp [this]
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  rw [zero_add]
  calc ‖∫ x, Δ χ x • f x ∂μ‖ ≤ (ε / (A + 1)) * A := hle _ (by positivity)
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-- **Limits of harmonic functions** (Gilbarg–Trudinger), general `E`. A locally
uniform limit of harmonic functions on an open set is harmonic, and the derivatives converge
locally uniformly. -/
theorem harmonicOnNhd_of_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι} [p.NeBot]
    {U : Set E} (hU : IsOpen U) {F : ι → E → ℝ} {f : E → ℝ} (hF : ∀ k, HarmonicOnNhd (F k) U)
    (hconv : TendstoLocallyUniformlyOn F f p U) :
    HarmonicOnNhd f U ∧ TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (F k)) (fderiv ℝ f) p U := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have hFc : ∀ k, ContinuousOn (F k) U := fun k ↦ (hF k).contDiffOn.continuousOn
  have hfc : ContinuousOn f U := hconv.continuousOn (Frequently.of_forall hFc)
  have hfw : WeaklyHarmonicOn μ f U := weaklyHarmonicOn_of_tendstoLocallyUniformlyOn hU hFc
    (fun k ↦ HarmonicOnNhd.weaklyHarmonicOn hU (hF k)) hconv
  have hf : HarmonicOnNhd f U := harmonicOnNhd_of_weaklyHarmonicOn hU hfc hfw
  refine ⟨hf, Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε x₀ hx₀ ↦ ?_⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- in dimension zero all derivatives vanish
    have h0 : ∀ L : E →L[ℝ] ℝ, L = 0 := fun L ↦ by
      ext v
      rw [Subsingleton.elim v 0, map_zero, zero_apply]
    exact ⟨univ, univ_mem, Eventually.of_forall fun k y _ ↦ by simp [h0 (fderiv ℝ f y),
      h0 (fderiv ℝ (F k) y), hε]⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set r := δ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hBU : closedBall x₀ (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hδU
  obtain ⟨C, hC, hest⟩ := exists_norm_fderiv_le_of_weaklyHarmonic μ hr
  have hunif : TendstoUniformlyOn F f p (closedBall x₀ (2 * r)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hBU (isCompact_closedBall _ _)
  set η := ε / (C + 1) with hη
  have hη0 : 0 < η := by positivity
  refine ⟨ball x₀ r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x₀ hr), ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif η hη0] with k hk y hy
  -- `F k - f` is harmonic, and small on the closed ball
  have hg : HarmonicOnNhd (F k - f) U := fun z hz ↦ (hF k z hz).sub (hf z hz)
  have hyU : y ∈ U := hBU (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith)) hy)
  have hsub : fderiv ℝ (F k - f) y = fderiv ℝ (F k) y - fderiv ℝ f y :=
    fderiv_sub ((hF k y hyU).1.differentiableAt (by norm_num))
      ((hf y hyU).1.differentiableAt (by norm_num))
  have hbound := hest U (F k - f) x₀ hU hg.contDiffOn.continuousOn
    (HarmonicOnNhd.weaklyHarmonicOn hU hg) hBU η
    (fun z hz ↦ by
      rw [Pi.sub_apply, abs_sub_comm, ← Real.dist_eq]
      exact (hk z hz).le) y hy
  rw [hsub] at hbound
  rw [dist_comm, dist_eq_norm]
  calc ‖fderiv ℝ (F k) y - fderiv ℝ f y‖ ≤ C * η := hbound
    _ < ε := by
        rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end General

end BasicElliptic
