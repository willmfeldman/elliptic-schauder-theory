/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Harmonic.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Interior estimates for harmonic functions

Let `E` be a finite-dimensional real inner product space. The constants below depend only on `E`
(in practice on `d = dim E`).

**Derivative bounds** ([GT]). For `u` harmonic on a neighbourhood of
`closedBall x₀ r` with `|u| ≤ M` there:
* `BasicElliptic.exists_norm_fderiv_le_div_of_harmonic`: `‖Du(x₀)‖ ≤ C M / r`;
* `BasicElliptic.exists_norm_hessian_le_of_harmonic`: `‖D²u(x₀)‖ ≤ C M / r²`;
* `BasicElliptic.exists_norm_fderiv_fderiv_fderiv_le_of_harmonic`: `‖D³u(x₀)‖ ≤ C M / r³`;
* `BasicElliptic.norm_iteratedFDeriv_le_of_harmonic`: the three combined, for
  `iteratedFDeriv ℝ k u x₀` and `k ≤ 3`, with one constant.
* `BasicElliptic.HarmonicOnNhd.fderiv_apply`: directional derivatives of harmonic functions are
  harmonic.

**`L²` to sup** (for a Haar measure `μ`). For `W : E → F` harmonic on a neighbourhood of
`closedBall y s`:
* `BasicElliptic.norm_sq_le_setIntegral_div_of_harmonic`:
  `‖W y‖² ≤ (∫_{B_s(y)} ‖W‖²) / |B_s|`;
* `BasicElliptic.setIntegral_norm_sub_sq_eq`: the expansion
  `∫_s ‖V - c‖² = ∫_s ‖V‖² - 2 ⟪∫_s V, c⟫ + |s| ‖c‖²`.

## Proof of the derivative bounds

The fixed-scale gradient bound comes from reproducing `u` by a radial kernel (mean value
property) and differentiating the kernel (`exists_norm_fderiv_le_of_weaklyHarmonic`); rescaling
`v(y) = u(x₀ + r y)` gives the scale-invariant form. Since `D_v u` is harmonic, the Hessian bound
is the gradient bound applied twice (on `B_{r/2}`), and the third-derivative bound is the Hessian
bound applied to `D_v u` on `B_{r/2}`. The constants are not sharp.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001.

## Provenance

Ported from elliptic-bernoulli-foundations (W. M. Feldman),
`EllipticBernoulli/Harmonic/GradientEstimate.lean`, commit
32fb58231146c940715b274d781ff92d865eb108: `eqOn_indicator_convolution_of_weaklyHarmonic`,
`exists_norm_fderiv_le_of_weaklyHarmonic`, `HarmonicOnNhd.fderiv_apply`,
`exists_norm_fderiv_le_div_of_harmonic` and `norm_hessian_le_of_harmonic` (renamed
`exists_norm_hessian_le_of_harmonic`). Changes: namespace `BasicElliptic`; `E d` generalized to a
finite-dimensional inner product space `E` (the Haar measure is chosen by `borelize`); the
`1 ≤ d` hypothesis is replaced by a case split on `Nontrivial E`. The third-derivative bound,
the `iteratedFDeriv` packaging and the `L²` bounds are new.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology ContinuousLinearMap
open scoped ContDiff Laplacian Convolution RealInnerProductSpace
open ViscositySolns.Analysis (WeaklyHarmonicOn exists_radial_kernel fderiv_convolution_apply
  integral_radial_smul_eq_of_weaklyHarmonic)

public section

namespace BasicElliptic

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Reproduction by a radial kernel.** If `u` is continuous and weakly
harmonic on `U ⊇ closedBall x₀ (2 r)` and `g (‖·‖²)` is a smooth radial kernel of integral one
vanishing outside `closedBall 0 r`, then `u = (1_B u) ⋆ g (‖·‖²)` on `ball x₀ r`, where
`B = closedBall x₀ (2 r)`. -/
theorem eqOn_indicator_convolution_of_weaklyHarmonic [Nontrivial E] {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hcont : ContinuousOn u U) (hu : WeaklyHarmonicOn μ u U) {x₀ : E} {r : ℝ}
    (hr : 0 < r) (hBU : closedBall x₀ (2 * r) ⊆ U) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg0 : ∀ t, r ^ 2 ≤ t → g t = 0) (hg1 : ∫ y, g (‖y‖ ^ 2) ∂μ = 1) :
    EqOn u ((closedBall x₀ (2 * r)).indicator u ⋆[lsmul ℝ ℝ, μ] fun y ↦ g (‖y‖ ^ 2))
      (ball x₀ r) := by
  set B := closedBall x₀ (2 * r)
  set ρ : E → ℝ := fun y ↦ g (‖y‖ ^ 2) with hρ_def
  set f := B.indicator u with hf_def
  intro x hx
  have hxB : closedBall x r ⊆ B := closedBall_subset_closedBall' (by
    rw [mem_ball] at hx
    linarith)
  have hk : Continuous fun s : ℝ ↦ g (s ^ 2) := hg.continuous.comp (continuous_pow 2)
  have hmvp := integral_radial_smul_eq_of_weaklyHarmonic hU hcont hu (hxB.trans hBU) hk
    (fun s hs ↦ hg0 _ (pow_le_pow_left₀ hr.le hs.le 2))
  rw [hg1, one_smul] at hmvp
  rw [← hmvp, convolution_def]
  conv_rhs => rw [← integral_add_left_eq_self _ x]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [lsmul_apply, smul_eq_mul, sub_add_cancel_left, norm_neg, hρ_def]
  by_cases hy : ‖y‖ ≤ r
  · rw [hf_def, indicator_of_mem (hxB (by simpa [mem_closedBall, dist_eq_norm] using hy)),
      mul_comm]
  · have := hg0 (‖y‖ ^ 2) (pow_le_pow_left₀ hr.le (not_le.mp hy).le 2)
    simp [this]

variable (μ) in
/-- **Interior gradient estimate at a fixed scale.** For `r > 0` there is `C` such that every
continuous weakly harmonic `u` on an open `U ⊇ closedBall x₀ (2 r)` with `|u| ≤ M` on
`closedBall x₀ (2 r)` satisfies `‖Du(x)‖ ≤ C M` for `x ∈ ball x₀ r`. -/
theorem exists_norm_fderiv_le_of_weaklyHarmonic [Nontrivial E] {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set E) (u : E → ℝ) (x₀ : E), IsOpen U → ContinuousOn u U →
      WeaklyHarmonicOn μ u U → closedBall x₀ (2 * r) ⊆ U → ∀ M : ℝ,
      (∀ y ∈ closedBall x₀ (2 * r), |u y| ≤ M) → ∀ x ∈ ball x₀ r, ‖fderiv ℝ u x‖ ≤ C * M := by
  obtain ⟨g, hg, hg0, hg1⟩ := exists_radial_kernel μ hr
  set ρ : E → ℝ := fun y ↦ g (‖y‖ ^ 2) with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := hg.comp (contDiff_norm_sq ℝ)
  have hρ0 : ∀ y, r < ‖y‖ → ρ y = 0 := fun y hy ↦
    hg0 _ (pow_le_pow_left₀ hr.le hy.le 2)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) r) fun y hy ↦
      hρ0 y (by rwa [mem_closedBall_zero_iff, not_le] at hy)
  have hDρ : Continuous fun y ↦ ‖fderiv ℝ ρ y‖ := (hρ.continuous_fderiv (by simp)).norm
  have hDρi : Integrable (fun y ↦ ‖fderiv ℝ ρ y‖) μ :=
    hDρ.integrable_of_hasCompactSupport (hρc.fderiv (𝕜 := ℝ)).norm
  refine ⟨∫ y, ‖fderiv ℝ ρ y‖ ∂μ, integral_nonneg fun _ ↦ norm_nonneg _,
    fun U u x₀ hU hcont hu hBU M hM x hx ↦ ?_⟩
  set B := closedBall x₀ (2 * r)
  set f := B.indicator u with hf_def
  have hf : LocallyIntegrable f μ :=
    (((hcont.mono hBU).integrableOn_compact (isCompact_closedBall _ _)).integrable_indicator
      measurableSet_closedBall).locallyIntegrable
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_closedBall_self (by positivity)))
  have hfM : ∀ t, |f t| ≤ M := fun t ↦ by
    by_cases ht : t ∈ B
    · rw [hf_def, indicator_of_mem ht]
      exact hM t ht
    · rw [hf_def, indicator_of_notMem ht, abs_zero]
      exact hM0
  have heq : u =ᶠ[𝓝 x] f ⋆[lsmul ℝ ℝ, μ] ρ :=
    (eqOn_indicator_convolution_of_weaklyHarmonic hU hcont hu hr hBU hg hg0 hg1).eventuallyEq_of_mem
      (isOpen_ball.mem_nhds hx)
  rw [heq.fderiv_eq]
  refine opNorm_le_bound _ (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) hM0) fun v ↦ ?_
  rw [fderiv_convolution_apply hf (hρ.of_le (by exact_mod_cast le_top)) hρc x v,
    convolution_def]
  have hbound : Integrable (fun t ↦ M * (‖fderiv ℝ ρ (x - t)‖ * ‖v‖)) μ :=
    ((hDρi.comp_sub_left x).mul_const _).const_mul _
  calc ‖∫ t, (lsmul ℝ ℝ) (f t) (fderiv ℝ ρ (x - t) v) ∂μ‖
      ≤ ∫ t, M * (‖fderiv ℝ ρ (x - t)‖ * ‖v‖) ∂μ := by
        refine norm_integral_le_of_norm_le hbound (Eventually.of_forall fun t ↦ ?_)
        rw [lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hfM t) (le_opNorm _ _) (norm_nonneg _) hM0
    _ = (∫ y, ‖fderiv ℝ ρ y‖ ∂μ) * M * ‖v‖ := by
        rw [integral_const_mul, integral_mul_const,
          integral_sub_left_eq_self (fun y ↦ ‖fderiv ℝ ρ y‖) μ x]
        ring

end General

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `Δ f x = ∑ᵢ D_{eᵢ} D_{eᵢ} f (x)` for `f` which is `C²` at `x`. -/
private theorem laplacian_eq_sum_fderiv_fderiv_of_contDiffAt {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y (stdOrthonormalBasis ℝ E i)) x
      (stdOrthonormalBasis ℝ E i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

omit [FiniteDimensional ℝ E] in
/-- Symmetry of second directional derivatives. -/
private theorem fderiv_fderiv_apply_comm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (a b : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y b) x a = fderiv ℝ (fun y ↦ fderiv ℝ f y a) x b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hf.isSymmSndFDerivAt (by simp) a b

omit [FiniteDimensional ℝ E] in
/-- Differentiating `y ↦ c y v` for a family of continuous linear maps `c`. -/
theorem fderiv_apply_const_apply {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {c : E → G →L[ℝ] H} {x : E}
    (hc : DifferentiableAt ℝ c x) (v : G) (h : E) :
    fderiv ℝ (fun y ↦ c y v) x h = fderiv ℝ c x h v := by
  rw [fderiv_clm_apply hc (differentiableAt_const _)]
  simp

/-- **Derivatives of harmonic functions are harmonic.** If `u` is harmonic on the
open set `U`, so is its directional derivative `D_v u = fun x ↦ fderiv ℝ u x v`. The proof
commutes `Δ` with `D_v` using the symmetry of second derivatives of the `C^∞` function `u`. -/
theorem HarmonicOnNhd.fderiv_apply {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : HarmonicOnNhd u U) (v : E) : HarmonicOnNhd (fun x ↦ fderiv ℝ u x v) U := by
  have hs : ContDiffOn ℝ ∞ u U := HarmonicOnNhd.contDiffOn_top hU hu
  have hD : ∀ w : E, ContDiffOn ℝ ∞ (fun x ↦ fderiv ℝ u x w) U := fun w ↦
    (hs.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hDD : ∀ w w' : E, ContDiffOn ℝ ∞ (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ u y w) x w') U :=
    fun w w' ↦ ((hD w).fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have h2 : ∀ {g : E → ℝ}, ContDiffOn ℝ ∞ g U → ∀ y ∈ U, ContDiffAt ℝ 2 g y := fun hg y hy ↦
    (hg.contDiffAt (hU.mem_nhds hy)).of_le (by norm_cast)
  set b := stdOrthonormalBasis ℝ E
  intro x hx
  refine ⟨h2 (hD v) x hx, ?_⟩
  filter_upwards [hU.mem_nhds hx] with y hy
  rw [laplacian_eq_sum_fderiv_fderiv_of_contDiffAt (h2 (hD v) y hy), Pi.zero_apply]
  -- `D_e D_e D_v u = D_v D_e D_e u`
  have hstep : ∀ e : E, fderiv ℝ (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ u y v) z e) y e =
      fderiv ℝ (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ u y e) z e) y v := by
    intro e
    have hev : (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ u y v) z e) =ᶠ[𝓝 y]
        fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ u y e) z v := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact fderiv_fderiv_apply_comm (h2 hs z hz) e v
    rw [hev.fderiv_eq]
    exact fderiv_fderiv_apply_comm (h2 (hD e) y hy) e v
  simp_rw [hstep]
  -- the sum of the `D_v D_e D_e u` is `D_v Δu = 0`
  have hdiff : ∀ i ∈ (Finset.univ : Finset _), DifferentiableAt ℝ
      (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) z (b i)) y := fun i _ ↦
    ((hDD (b i) (b i)).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hsum := fderiv_fun_sum (u := Finset.univ) hdiff
  rw [← sum_apply, ← hsum]
  have hΔ : (fun z ↦ ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) z (b i)) =ᶠ[𝓝 y]
      fun _ ↦ (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [← laplacian_eq_sum_fderiv_fderiv_of_contDiffAt (h2 hs z hz)]
    exact (hu z hz).2.eq_of_nhds
  rw [hΔ.fderiv_eq]
  simp

variable (E) in
/-- **Scale-invariant interior gradient estimate.** There is `C = C(E) ≥ 0` such that a harmonic
`u` on a neighbourhood of `closedBall x₀ r` with `|u| ≤ M` there satisfies
`‖Du(x₀)‖ ≤ C M / r`. -/
theorem exists_norm_fderiv_le_div_of_harmonic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E → ℝ) (x₀ : E) (r M : ℝ), 0 < r →
      HarmonicOnNhd u (closedBall x₀ r) → (∀ y ∈ closedBall x₀ r, |u y| ≤ M) →
      ‖fderiv ℝ u x₀‖ ≤ C * M / r := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨0, le_rfl, fun u x₀ r M _ _ _ ↦ ?_⟩
    have : fderiv ℝ u x₀ = 0 := ContinuousLinearMap.ext fun v ↦ by
      rw [Subsingleton.elim v 0, map_zero, zero_apply]
    simp [this]
  borelize E
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_fderiv_le_of_weaklyHarmonic (Measure.addHaar : Measure E) (r := 1 / 2)
      (by norm_num)
  refine ⟨C, hC, fun u x₀ r M hr hu hM ↦ ?_⟩
  -- the rescaled function `v y = u (x₀ + r y)`
  set v : E → ℝ := fun y ↦ u (x₀ + r • y) with hv
  set U := {y : E | HarmonicAt v y}
  have hU : IsOpen U := isOpen_setOfPred_harmonicAt v
  have hvU : HarmonicOnNhd v U := fun y hy ↦ hy
  have hmaps : ∀ y ∈ closedBall (0 : E) 1, x₀ + r • y ∈ closedBall x₀ r := fun y hy ↦ by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    rw [mem_closedBall_zero_iff] at hy
    nlinarith
  have hB : closedBall (0 : E) (2 * (1 / 2)) ⊆ U := fun y hy ↦
    HarmonicAt.comp_add_smul (hu _ (hmaps y (by simpa using hy)))
  have hvM : ∀ y ∈ closedBall (0 : E) (2 * (1 / 2)), |v y| ≤ M := fun y hy ↦
    hM _ (hmaps y (by simpa using hy))
  have h0 := hest U v 0 hU hvU.contDiffOn.continuousOn (HarmonicOnNhd.weaklyHarmonicOn hU hvU)
    hB M hvM 0 (mem_ball_self (by norm_num))
  -- the chain rule: `Dv(0) w = r Du(x₀) w`
  have hux : DifferentiableAt ℝ u x₀ :=
    (hu x₀ (mem_closedBall_self hr.le)).1.differentiableAt (by norm_num)
  have hchain : ∀ w, fderiv ℝ v 0 w = r * fderiv ℝ u x₀ w := by
    intro w
    have hlin : HasFDerivAt (fun y : E ↦ x₀ + r • y) (r • ContinuousLinearMap.id ℝ E) 0 :=
      ((hasFDerivAt_id (0 : E)).const_smul r).const_add x₀
    have hx : x₀ + r • (0 : E) = x₀ := by simp
    have hu' : HasFDerivAt u (fderiv ℝ u x₀) (x₀ + r • (0 : E)) := by
      rw [hx]; exact hux.hasFDerivAt
    have := (hu'.comp (0 : E) hlin).fderiv
    rw [hv, show (fun y ↦ u (x₀ + r • y)) = u ∘ fun y ↦ x₀ + r • y from rfl, this]
    simp
  refine opNorm_le_bound _ (by
    have := (abs_nonneg _).trans (hM x₀ (mem_closedBall_self hr.le))
    positivity) fun w ↦ ?_
  have hw := le_opNorm (fderiv ℝ v 0) w
  rw [hchain, norm_mul, Real.norm_of_nonneg hr.le] at hw
  have : r * ‖fderiv ℝ u x₀ w‖ ≤ C * M * ‖w‖ :=
    hw.trans (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  linarith

variable (E) in
/-- **Scale-invariant second-derivative estimate.** There is `C = C(E) ≥ 0` such that a harmonic
`u` on a neighbourhood of `closedBall x₀ r` with `|u| ≤ M` there satisfies
`‖D²u(x₀)‖ ≤ C M / r²`. One may take `C = 4 C₁²` with `C₁` the constant of
`exists_norm_fderiv_le_div_of_harmonic`. -/
theorem exists_norm_hessian_le_of_harmonic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E → ℝ) (x₀ : E) (r M : ℝ), 0 < r →
      HarmonicOnNhd u (closedBall x₀ r) → (∀ y ∈ closedBall x₀ r, |u y| ≤ M) →
      ‖fderiv ℝ (fderiv ℝ u) x₀‖ ≤ C * M / r ^ 2 := by
  obtain ⟨C, hC, hest⟩ := exists_norm_fderiv_le_div_of_harmonic E
  refine ⟨4 * C ^ 2, by positivity, fun u x₀ r M hr hu hM ↦ ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_closedBall_self hr.le))
  set V := {y | HarmonicAt u y}
  have hV : IsOpen V := isOpen_setOfPred_harmonicAt u
  have huV : HarmonicOnNhd u V := fun y hy ↦ hy
  have hBV : closedBall x₀ r ⊆ V := fun y hy ↦ hu y hy
  have hr2 : 0 < r / 2 := by positivity
  -- the gradient bound on the half ball
  have hgrad : ∀ y ∈ closedBall x₀ (r / 2), ‖fderiv ℝ u y‖ ≤ C * M / (r / 2) := by
    intro y hy
    have hsub : closedBall y (r / 2) ⊆ closedBall x₀ r :=
      closedBall_subset_closedBall' (by rw [mem_closedBall] at hy; linarith)
    exact hest u y (r / 2) M hr2 (hu.mono hsub) (fun z hz ↦ hM z (hsub hz))
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) x₀ :=
    ((hu x₀ (mem_closedBall_self hr.le)).1.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  -- `w = D_v u` is harmonic near `closedBall x₀ (r / 2)`
  have hw : HarmonicOnNhd (fun y ↦ fderiv ℝ u y v) (closedBall x₀ (r / 2)) :=
    (HarmonicOnNhd.fderiv_apply hV huV v).mono
      ((closedBall_subset_closedBall (by linarith)).trans hBV)
  have hwM : ∀ y ∈ closedBall x₀ (r / 2), |fderiv ℝ u y v| ≤ C * M / (r / 2) * ‖v‖ :=
    fun y hy ↦ by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hgrad y hy) (norm_nonneg _))
  have hwest := hest _ x₀ (r / 2) _ hr2 hw hwM
  have hfd : fderiv ℝ (fun y ↦ fderiv ℝ u y v) x₀ h = fderiv ℝ (fderiv ℝ u) x₀ h v :=
    fderiv_apply_const_apply hd2 v h
  calc ‖fderiv ℝ (fderiv ℝ u) x₀ h v‖ = ‖fderiv ℝ (fun y ↦ fderiv ℝ u y v) x₀ h‖ := by rw [hfd]
    _ ≤ ‖fderiv ℝ (fun y ↦ fderiv ℝ u y v) x₀‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * (C * M / (r / 2) * ‖v‖) / (r / 2) * ‖h‖ := by gcongr
    _ = 4 * C ^ 2 * M / r ^ 2 * ‖h‖ * ‖v‖ := by field_simp; ring

variable (E) in
/-- **Scale-invariant third-derivative estimate.** There is `C = C(E) ≥ 0` such that a harmonic
`u` on a neighbourhood of `closedBall x₀ r` with `|u| ≤ M` there satisfies
`‖D³u(x₀)‖ ≤ C M / r³`. Proof: the Hessian bound for the harmonic `D_v u` on `B_{r/2}(x₀)`, where
`|D_v u| ≤ 2 C₁ M ‖v‖ / r` by the gradient bound. -/
theorem exists_norm_fderiv_fderiv_fderiv_le_of_harmonic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E → ℝ) (x₀ : E) (r M : ℝ), 0 < r →
      HarmonicOnNhd u (closedBall x₀ r) → (∀ y ∈ closedBall x₀ r, |u y| ≤ M) →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x₀‖ ≤ C * M / r ^ 3 := by
  obtain ⟨C₁, hC₁, hest₁⟩ := exists_norm_fderiv_le_div_of_harmonic E
  obtain ⟨C₂, hC₂, hest₂⟩ := exists_norm_hessian_le_of_harmonic E
  refine ⟨8 * C₁ * C₂, by positivity, fun u x₀ r M hr hu hM ↦ ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_closedBall_self hr.le))
  set V := {y | HarmonicAt u y}
  have hV : IsOpen V := isOpen_setOfPred_harmonicAt u
  have huV : HarmonicOnNhd u V := fun y hy ↦ hy
  have hBV : closedBall x₀ r ⊆ V := fun y hy ↦ hu y hy
  have hx₀V : V ∈ 𝓝 x₀ := hV.mem_nhds (hBV (mem_closedBall_self hr.le))
  have hr2 : 0 < r / 2 := by positivity
  -- smoothness of `u` near `x₀`
  have hs : ContDiffOn ℝ ∞ u V := HarmonicOnNhd.contDiffOn_top hV huV
  have hD1 : ContDiffOn ℝ ∞ (fderiv ℝ u) V := hs.fderiv_of_isOpen hV (m := ∞) (by simp)
  have hD2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ u)) V :=
    hD1.fderiv_of_isOpen hV (m := ∞) (by simp)
  have hdiff1 : ∀ y ∈ V, DifferentiableAt ℝ (fderiv ℝ u) y := fun y hy ↦
    (hD1.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
  have hdiff2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x₀ :=
    (hD2.contDiffAt hx₀V).differentiableAt (by simp)
  -- the gradient bound on the half ball
  have hgrad : ∀ y ∈ closedBall x₀ (r / 2), ‖fderiv ℝ u y‖ ≤ C₁ * M / (r / 2) := by
    intro y hy
    have hsub : closedBall y (r / 2) ⊆ closedBall x₀ r :=
      closedBall_subset_closedBall' (by rw [mem_closedBall] at hy; linarith)
    exact hest₁ u y (r / 2) M hr2 (hu.mono hsub) (fun z hz ↦ hM z (hsub hz))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun k ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  -- `w = D_v u` is harmonic near `closedBall x₀ (r / 2)` and bounded there
  set w : E → ℝ := fun y ↦ fderiv ℝ u y v with hw_def
  have hwV : HarmonicOnNhd w V := HarmonicOnNhd.fderiv_apply hV huV v
  have hw : HarmonicOnNhd w (closedBall x₀ (r / 2)) :=
    hwV.mono ((closedBall_subset_closedBall (by linarith)).trans hBV)
  have hwM : ∀ y ∈ closedBall x₀ (r / 2), |w y| ≤ C₁ * M / (r / 2) * ‖v‖ :=
    fun y hy ↦ by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hgrad y hy) (norm_nonneg _))
  have hwest := hest₂ w x₀ (r / 2) _ hr2 hw hwM
  -- `D³u(x₀) h k v = D²w(x₀) h k`
  have hws : ContDiffOn ℝ ∞ w V := HarmonicOnNhd.contDiffOn_top hV hwV
  have hDw : ContDiffOn ℝ ∞ (fderiv ℝ w) V := hws.fderiv_of_isOpen hV (m := ∞) (by simp)
  have hdiffw : DifferentiableAt ℝ (fderiv ℝ w) x₀ :=
    (hDw.contDiffAt hx₀V).differentiableAt (by simp)
  have hev : (fun y ↦ fderiv ℝ w y k) =ᶠ[𝓝 x₀] fun y ↦ fderiv ℝ (fderiv ℝ u) y k v := by
    filter_upwards [hx₀V] with y hy
    exact fderiv_apply_const_apply (hdiff1 y hy) v k
  have hdiffk : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fderiv ℝ u) y k) x₀ :=
    hdiff2.clm_apply (differentiableAt_const _)
  have hfd : fderiv ℝ (fderiv ℝ w) x₀ h k = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x₀ h k v := by
    rw [← fderiv_apply_const_apply hdiffw k h, hev.fderiv_eq,
      fderiv_apply_const_apply hdiffk v h, fderiv_apply_const_apply hdiff2 k h]
  calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x₀ h k v‖ = ‖fderiv ℝ (fderiv ℝ w) x₀ h k‖ := by
        rw [hfd]
    _ ≤ ‖fderiv ℝ (fderiv ℝ w) x₀‖ * ‖h‖ * ‖k‖ := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ C₂ * (C₁ * M / (r / 2) * ‖v‖) / (r / 2) ^ 2 * ‖h‖ * ‖k‖ := by gcongr
    _ = 8 * C₁ * C₂ * M / r ^ 3 * ‖h‖ * ‖k‖ * ‖v‖ := by field_simp; ring

variable (E) in
/-- **Derivative bounds for harmonic functions, `k ≤ 3`** ([GT]). There is
`C = C(E) ≥ 0` such that for `k ≤ 3`, a harmonic `u` on a neighbourhood of `closedBall x₀ r`
with `|u| ≤ M` there satisfies `‖D^k u(x₀)‖ ≤ C M / r^k`. -/
theorem norm_iteratedFDeriv_le_of_harmonic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ 3, ∀ (u : E → ℝ) (x₀ : E) (r M : ℝ), 0 < r →
      HarmonicOnNhd u (closedBall x₀ r) → (∀ y ∈ closedBall x₀ r, |u y| ≤ M) →
      ‖iteratedFDeriv ℝ k u x₀‖ ≤ C * M / r ^ k := by
  obtain ⟨C₁, hC₁, hest₁⟩ := exists_norm_fderiv_le_div_of_harmonic E
  obtain ⟨C₂, hC₂, hest₂⟩ := exists_norm_hessian_le_of_harmonic E
  obtain ⟨C₃, hC₃, hest₃⟩ := exists_norm_fderiv_fderiv_fderiv_le_of_harmonic E
  refine ⟨1 + C₁ + C₂ + C₃, by positivity, fun k hk u x₀ r M hr hu hM ↦ ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_closedBall_self hr.le))
  have hmono : ∀ {c : ℝ} (n : ℕ), c ≤ 1 + C₁ + C₂ + C₃ → c * M / r ^ n ≤
      (1 + C₁ + C₂ + C₃) * M / r ^ n := fun n hc ↦ by gcongr
  interval_cases k
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    refine (hM x₀ (mem_closedBall_self hr.le)).trans ?_
    rw [pow_zero, div_one]
    nlinarith
  · rw [norm_iteratedFDeriv_one]
    exact (hest₁ u x₀ r M hr hu hM).trans (by simpa using hmono 1 (by linarith))
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    exact (hest₂ u x₀ r M hr hu hM).trans (hmono 2 (by linarith))
  · rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    exact (hest₃ u x₀ r M hr hu hM).trans (hmono 3 (by linarith))

end Derivatives

section L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- **Expansion of the square.** `∫_s ‖V - c‖² = ∫_s ‖V‖² - 2 ⟪∫_s V, c⟫ + |s| ‖c‖²` for
`V ∈ L²(s)` with `|s| < ∞`. -/
theorem setIntegral_norm_sub_sq_eq {V : E → F} {s : Set E} (hs : μ s ≠ ⊤)
    (hV : IntegrableOn V s μ) (hV2 : IntegrableOn (fun y ↦ ‖V y‖ ^ 2) s μ) (c : F) :
    ∫ y in s, ‖V y - c‖ ^ 2 ∂μ =
      ∫ y in s, ‖V y‖ ^ 2 ∂μ - 2 * ⟪∫ y in s, V y ∂μ, c⟫ + μ.real s * ‖c‖ ^ 2 := by
  have hc : IntegrableOn (fun _ ↦ ‖c‖ ^ 2) s μ := integrableOn_const hs
  have hin : IntegrableOn (fun y ↦ 2 * ⟪V y, c⟫) s μ := (hV.inner_const c).const_mul 2
  have hsub : IntegrableOn (fun y ↦ ‖V y‖ ^ 2 - 2 * ⟪V y, c⟫) s μ := hV2.sub hin
  simp_rw [norm_sub_sq_real]
  rw [integral_add hsub hc, integral_sub hV2 hin, integral_const_mul, setIntegral_const,
    smul_eq_mul, real_inner_comm, ← integral_inner hV]
  simp_rw [real_inner_comm c]

omit [BorelSpace E] in
private theorem measureReal_ball_pos {x : E} {s : ℝ} (hs : 0 < s) : 0 < μ.real (ball x s) :=
  ENNReal.toReal_pos (measure_ball_pos μ x hs).ne' measure_ball_lt_top.ne

/-- **`L²` to sup.** For `W` harmonic on a neighbourhood of `closedBall y s`,
`‖W y‖² ≤ (∫_{B_s(y)} ‖W‖²) / |B_s(y)|`. -/
theorem norm_sq_le_setIntegral_div_of_harmonic {W : E → F} {y : E} {s : ℝ} (hs : 0 < s)
    (hW : HarmonicOnNhd W (closedBall y s)) :
    ‖W y‖ ^ 2 ≤ (∫ z in ball y s, ‖W z‖ ^ 2 ∂μ) / μ.real (ball y s) := by
  have hpos := measureReal_ball_pos (μ := μ) (x := y) hs
  have hcont : ContinuousOn W (closedBall y s) := hW.contDiffOn.continuousOn
  have hV : IntegrableOn W (ball y s) μ :=
    (hcont.integrableOn_compact (isCompact_closedBall y s)).mono_set ball_subset_closedBall
  have hV2 : IntegrableOn (fun z ↦ ‖W z‖ ^ 2) (ball y s) μ :=
    ((hcont.norm.pow 2).integrableOn_compact (isCompact_closedBall y s)).mono_set
      ball_subset_closedBall
  have hexp := setIntegral_norm_sub_sq_eq measure_ball_lt_top.ne hV hV2 (W y)
  rw [HarmonicOnNhd.setIntegral_ball_eq_smul hW, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hexp
  have hnn : 0 ≤ ∫ z in ball y s, ‖W z - W y‖ ^ 2 ∂μ := setIntegral_nonneg measurableSet_ball
    fun _ _ ↦ sq_nonneg _
  rw [le_div_iff₀ hpos]
  nlinarith

end L2

end BasicElliptic
