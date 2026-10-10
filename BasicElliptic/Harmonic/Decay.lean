/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Harmonic.Estimates
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Campanato and Morrey decay for harmonic fields

Let `E` be a finite-dimensional real inner product space of dimension `d` with an additive Haar
measure `μ` (`volume` in applications), and `F` a finite-dimensional real inner product space.
For a field `V : E → F` whose components `⟪V, e⟫` are harmonic on `ball x r`, with
`‖V‖² ∈ L¹(B_r(x))`, and `0 < ρ ≤ r` ([GM]):

* `BasicElliptic.harmonic_campanato_decay`:
  `∫_{B_ρ} ‖V − V_ρ‖² ≤ C (ρ/r)^{d+2} ∫_{B_r} ‖V − V_r‖²`, where `V_s = ⨍_{B_s(x)} V`.

In the statement `C` is chosen after `μ`, but the constant of the proof,
`4^{d+2} + 64 · 2^d · C₁²`, depends only on `E` (`C₁` is the constant of
`exists_norm_fderiv_le_div_of_harmonic`; only ratios of ball volumes enter).

Auxiliary: `BasicElliptic.setIntegral_norm_sub_setAverage_sq_le` (the mean minimizes
`c ↦ ∫_s ‖V − c‖²`).

## Proof

For `ρ > r/4` both bounds are trivial (monotonicity in the domain, and the mean minimizes). For
`ρ ≤ r/4`, put `W = V − V_r`, harmonic on `B_r`. The `L²`-to-sup bound on balls `B_{r/2}(y)`,
`y ∈ B̄_{3r/8}(x)`, gives `sup_{B̄_{3r/8}} ‖W‖² ≤ A / |B_{r/2}|` with `A = ∫_{B_r} ‖W‖²`. The
gradient bound on `B̄_{r/8}(z)`, `z ∈ B_{r/4}`, applied to the scalar harmonic `⟪W, e⟫`, and the
mean value inequality give `‖V y − V x‖ ≤ 8 C₁ (ρ/r) (A / |B_{r/2}|)^{1/2}` on `B_ρ`. Then
`∫_{B_ρ} ‖V − V_ρ‖² ≤ ∫_{B_ρ} ‖V − V x‖² ≤ 64 C₁² 2^d (ρ/r)^{d+2} A`. The Morrey bound is the
`L²`-to-sup bound directly.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, 2012, Proposition 5.8.

## Provenance

New (W. M. Feldman).
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology
open scoped RealInnerProductSpace

public section

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] [FiniteDimensional ℝ F] in
/-- **The mean minimizes the quadratic deviation.** For `V ∈ L²(s)`, `|s| < ∞` and any `c`,
`∫_s ‖V − ⨍_s V‖² ≤ ∫_s ‖V − c‖²`. -/
theorem setIntegral_norm_sub_setAverage_sq_le [CompleteSpace F] {V : E → F} {s : Set E}
    (hs : μ s ≠ ⊤) (hV : IntegrableOn V s μ) (hV2 : IntegrableOn (fun y ↦ ‖V y‖ ^ 2) s μ)
    (c : F) :
    ∫ y in s, ‖V y - ⨍ z in s, V z ∂μ‖ ^ 2 ∂μ ≤ ∫ y in s, ‖V y - c‖ ^ 2 ∂μ := by
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · rw [setIntegral_measure_zero _ h0, setIntegral_measure_zero _ h0]
  set m := ⨍ z in s, V z ∂μ with hm
  have hpos : 0 < μ.real s := ENNReal.toReal_pos h0 hs
  have hint : ∫ y in s, V y ∂μ = μ.real s • m := by
    rw [hm, setAverage_eq, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [setIntegral_norm_sub_sq_eq hs hV hV2, setIntegral_norm_sub_sq_eq hs hV hV2, hint,
    real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have key : 0 ≤ μ.real s * ‖m - c‖ ^ 2 := by positivity
  rw [norm_sub_sq_real] at key
  nlinarith [key]

/-- `|B_ρ(x)| = (ρ/s)^d |B_s(y)|` (also in dimension zero). -/
private theorem measureReal_ball_eq_div_pow_mul (x y : E) {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) :
    μ.real (ball x ρ) = (ρ / s) ^ finrank ℝ E * μ.real (ball y s) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h1 : ball x ρ = univ := eq_univ_of_forall fun z ↦ by
      rw [Subsingleton.elim z x]; exact mem_ball_self hρ
    have h2 : ball y s = univ := eq_univ_of_forall fun z ↦ by
      rw [Subsingleton.elim z y]; exact mem_ball_self hs
    simp [h1, h2, finrank_zero_of_subsingleton]
  have h : ∀ (z : E) {t : ℝ}, 0 < t → μ.real (ball z t) = t ^ finrank ℝ E * μ.real (ball 0 1) :=
    fun z t ht ↦ by
      rw [measureReal_def, Measure.addHaar_ball_of_pos μ z ht, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), measureReal_def]
  rw [h x hρ, h y hs, div_pow]
  field_simp

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A continuous field on a ball with square-integrable norm is integrable there. -/
private theorem integrableOn_ball_of_sq {V : E → F} {x : E} {r : ℝ}
    (hc : ContinuousOn V (ball x r)) (h2 : IntegrableOn (fun y ↦ ‖V y‖ ^ 2) (ball x r) μ) :
    IntegrableOn V (ball x r) μ := by
  refine Integrable.mono' ((integrableOn_const (C := (1 : ℝ)) measure_ball_lt_top.ne).add h2)
    (hc.aestronglyMeasurable measurableSet_ball) (Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖V y‖ - 1), norm_nonneg (V y)]

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- `‖V − c‖²` is integrable on a ball if `‖V‖²` is (and `V` is continuous there). -/
private theorem integrableOn_ball_sub_sq {V : E → F} {x : E} {r : ℝ}
    (hc : ContinuousOn V (ball x r)) (h2 : IntegrableOn (fun y ↦ ‖V y‖ ^ 2) (ball x r) μ)
    (c : F) : IntegrableOn (fun y ↦ ‖V y - c‖ ^ 2) (ball x r) μ := by
  refine Integrable.mono' ((h2.const_mul 2).add
    (integrableOn_const (C := 2 * ‖c‖ ^ 2) measure_ball_lt_top.ne))
    ((hc.sub continuousOn_const).norm.pow 2 |>.aestronglyMeasurable
    measurableSet_ball) (Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have := norm_sub_le (V y) c
  nlinarith [norm_nonneg (V y - c), norm_nonneg (V y), norm_nonneg c, sq_nonneg (‖V y‖ - ‖c‖)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] [FiniteDimensional ℝ F] in
/-- Bounding a set integral by the measure times a pointwise bound. -/
private theorem setIntegral_le_measureReal_mul {f : E → ℝ} {s : Set E} (hs : MeasurableSet s)
    (hμ : μ s ≠ ⊤) (hf : IntegrableOn f s μ) {K : ℝ} (hK : ∀ y ∈ s, f y ≤ K) :
    ∫ y in s, f y ∂μ ≤ μ.real s * K := by
  have := setIntegral_mono_on hf (integrableOn_const hμ) hs hK
  rwa [setIntegral_const, smul_eq_mul] at this

variable (E μ F) in
/-- **Campanato decay for harmonic fields** ([GM]). There is
`C = C(E) ≥ 0` such that, for `V : E → F` with harmonic components on `ball x r`, `‖V‖² ∈ L¹`
there, and `0 < ρ ≤ r`,
`∫_{B_ρ} ‖V − V_ρ‖² ≤ C (ρ/r)^{d+2} ∫_{B_r} ‖V − V_r‖²`. -/
theorem harmonic_campanato_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : E → F) (x : E) (r ρ : ℝ), 0 < ρ → ρ ≤ r →
      (∀ e : F, HarmonicOnNhd (fun y ↦ ⟪V y, e⟫) (ball x r)) →
      IntegrableOn (fun y ↦ ‖V y‖ ^ 2) (ball x r) μ →
      ∫ y in ball x ρ, ‖V y - ⨍ z in ball x ρ, V z ∂μ‖ ^ 2 ∂μ ≤
        C * (ρ / r) ^ (finrank ℝ E + 2) *
          ∫ y in ball x r, ‖V y - ⨍ z in ball x r, V z ∂μ‖ ^ 2 ∂μ := by
  obtain ⟨C₁, hC₁, hest⟩ := exists_norm_fderiv_le_div_of_harmonic E
  set d := finrank ℝ E
  refine ⟨4 ^ (d + 2) + 64 * 2 ^ d * C₁ ^ 2, by positivity,
    fun V x r ρ hρ hρr hVe hint ↦ ?_⟩
  have hr : 0 < r := hρ.trans_le hρr
  have hV : HarmonicOnNhd V (ball x r) := harmonicOnNhd_of_forall_inner hVe
  have hVc : ContinuousOn V (ball x r) := hV.contDiffOn.continuousOn
  have hVi : IntegrableOn V (ball x r) μ := integrableOn_ball_of_sq hVc hint
  set a := ⨍ z in ball x r, V z ∂μ with ha
  set A := ∫ y in ball x r, ‖V y - a‖ ^ 2 ∂μ with hA
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hsubρ : ball x ρ ⊆ ball x r := ball_subset_ball hρr
  -- the mean over `B_ρ` beats any constant
  have hmin : ∀ c : F, ∫ y in ball x ρ, ‖V y - ⨍ z in ball x ρ, V z ∂μ‖ ^ 2 ∂μ ≤
      ∫ y in ball x ρ, ‖V y - c‖ ^ 2 ∂μ := fun c ↦
    setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne (hVi.mono_set hsubρ)
      (hint.mono_set hsubρ) c
  rcases lt_or_ge (r / 4) ρ with hbig | hsmall
  · -- trivial range `ρ > r/4`
    have h1 : ∫ y in ball x ρ, ‖V y - a‖ ^ 2 ∂μ ≤ A :=
      setIntegral_mono_set (integrableOn_ball_sub_sq hVc hint a)
        (Eventually.of_forall fun _ ↦ sq_nonneg _) hsubρ.eventuallyLE
    have h2 : (1 : ℝ) ≤ 4 ^ (d + 2) * (ρ / r) ^ (d + 2) := by
      rw [← mul_pow]
      refine one_le_pow₀ ?_
      rw [mul_div_assoc', le_div_iff₀ hr]
      linarith
    calc _ ≤ ∫ y in ball x ρ, ‖V y - a‖ ^ 2 ∂μ := hmin a
      _ ≤ A := h1
      _ ≤ 4 ^ (d + 2) * (ρ / r) ^ (d + 2) * A := le_mul_of_one_le_left hA0 h2
      _ ≤ (4 ^ (d + 2) + 64 * 2 ^ d * C₁ ^ 2) * (ρ / r) ^ (d + 2) * A := by
        gcongr
        nlinarith [sq_nonneg C₁, pow_pos (two_pos : (0 : ℝ) < 2) d]
  -- main range `ρ ≤ r/4`
  set W : E → F := fun y ↦ V y - a with hW_def
  have hW : HarmonicOnNhd W (ball x r) := hV.sub (harmonicOnNhd_const a)
  have hr2 : 0 < r / 2 := by positivity
  have hpos2 : 0 < μ.real (ball x (r / 2)) :=
    ENNReal.toReal_pos (measure_ball_pos μ x hr2).ne' measure_ball_lt_top.ne
  set M2 := A / μ.real (ball x (r / 2)) with hM2
  have hM20 : 0 ≤ M2 := div_nonneg hA0 hpos2.le
  set M := Real.sqrt M2 with hM
  -- `L²` to sup on `B̄_{3r/8}`
  have hsup : ∀ y ∈ closedBall x (3 * r / 8), ‖W y‖ ≤ M := by
    intro y hy
    rw [mem_closedBall] at hy
    have hsub : closedBall y (r / 2) ⊆ ball x r := fun z hz ↦ by
      rw [mem_closedBall] at hz
      rw [mem_ball]
      linarith [dist_triangle z y x]
    have h1 := norm_sq_le_setIntegral_div_of_harmonic (μ := μ) hr2 (hW.mono hsub)
    have hmono : ∫ z in ball y (r / 2), ‖W z‖ ^ 2 ∂μ ≤ A :=
      setIntegral_mono_set (integrableOn_ball_sub_sq hVc hint a)
        (Eventually.of_forall fun _ ↦ sq_nonneg _)
        (ball_subset_closedBall.trans hsub).eventuallyLE
    have hμeq : μ.real (ball y (r / 2)) = μ.real (ball x (r / 2)) := by
      rw [Measure.addHaar_real_ball_center, Measure.addHaar_real_ball_center μ x]
    rw [hμeq] at h1
    have : ‖W y‖ ^ 2 ≤ M2 := h1.trans (div_le_div_of_nonneg_right hmono hpos2.le)
    rw [hM]
    exact Real.le_sqrt_of_sq_le this
  -- Lipschitz bound on `B_{r/4}` via the scalar gradient bound
  have hlip : ∀ y ∈ ball x ρ, ‖V y - V x‖ ≤ 8 * C₁ * M / r * ρ := by
    intro y hy
    have hyx : V y - V x = W y - W x := by simp [hW_def]
    rw [hyx]
    rcases eq_or_ne (W y - W x) 0 with h0 | h0
    · rw [h0, norm_zero]; positivity
    set e : F := ‖W y - W x‖⁻¹ • (W y - W x) with he
    have hnorm : ‖e‖ = 1 := by rw [he, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
    have hinner : ⟪W y - W x, e⟫ = ‖W y - W x‖ := by
      rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [norm_ne_zero_iff.2 h0]
    set g : E → ℝ := fun z ↦ ⟪W z, e⟫ with hg
    have hgh : HarmonicOnNhd g (ball x r) := harmonicOnNhd_inner_left hW e
    have hgb : ∀ z ∈ closedBall x (3 * r / 8), |g z| ≤ M := fun z hz ↦ by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hnorm, mul_one]
      exact hsup z hz
    have hgrad : ∀ z ∈ ball x (r / 4), ‖fderiv ℝ g z‖ ≤ 8 * C₁ * M / r := by
      intro z hz
      rw [mem_ball] at hz
      have hsub : closedBall z (r / 8) ⊆ closedBall x (3 * r / 8) := fun w hw ↦ by
        rw [mem_closedBall] at hw ⊢
        linarith [dist_triangle w z x]
      have hsub' : closedBall x (3 * r / 8) ⊆ ball x r := closedBall_subset_ball (by linarith)
      have := hest g z (r / 8) M (by positivity) (hgh.mono (hsub.trans hsub'))
        (fun w hw ↦ hgb w (hsub hw))
      calc ‖fderiv ℝ g z‖ ≤ C₁ * M / (r / 8) := this
        _ = 8 * C₁ * M / r := by field_simp
    have hdiff : ∀ z ∈ ball x (r / 4), DifferentiableAt ℝ g z := fun z hz ↦
      (hgh z (ball_subset_ball (by linarith) hz)).1.differentiableAt (by norm_num)
    have hxb : x ∈ ball x (r / 4) := mem_ball_self (by positivity)
    have hyb : y ∈ ball x (r / 4) := ball_subset_ball hsmall hy
    have hmv := (convex_ball x (r / 4)).norm_image_sub_le_of_norm_fderiv_le hdiff hgrad hxb hyb
    have hgyx : g y - g x = ‖W y - W x‖ := by
      rw [hg]; simp only; rw [← inner_sub_left, hinner]
    rw [hgyx, Real.norm_of_nonneg (norm_nonneg _)] at hmv
    refine hmv.trans ?_
    have : ‖y - x‖ ≤ ρ := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
    have hK : 0 ≤ 8 * C₁ * M / r := by positivity
    exact mul_le_mul_of_nonneg_left this hK
  -- integrate
  have hKsq : ∀ y ∈ ball x ρ, ‖V y - V x‖ ^ 2 ≤ (8 * C₁ * M / r * ρ) ^ 2 := fun y hy ↦
    pow_le_pow_left₀ (norm_nonneg _) (hlip y hy) 2
  have hint2 : IntegrableOn (fun y ↦ ‖V y - V x‖ ^ 2) (ball x ρ) μ :=
    (integrableOn_ball_sub_sq hVc hint (V x)).mono_set hsubρ
  have hstep := setIntegral_le_measureReal_mul measurableSet_ball measure_ball_lt_top.ne hint2
    hKsq
  have hmeas : μ.real (ball x ρ) = (ρ / (r / 2)) ^ d * μ.real (ball x (r / 2)) :=
    measureReal_ball_eq_div_pow_mul x x hρ hr2
  have hMsq : M ^ 2 = M2 := Real.sq_sqrt hM20
  have hfinal : μ.real (ball x ρ) * (8 * C₁ * M / r * ρ) ^ 2 =
      64 * 2 ^ d * C₁ ^ 2 * (ρ / r) ^ (d + 2) * A := by
    have h2 : ρ / (r / 2) = 2 * (ρ / r) := by field_simp
    have h3 : (8 * C₁ * M / r * ρ) ^ 2 = 64 * C₁ ^ 2 * M ^ 2 * (ρ / r) ^ 2 := by
      field_simp; ring
    rw [hmeas, h2, h3, hMsq, hM2, mul_pow, pow_add]
    field_simp
  calc _ ≤ ∫ y in ball x ρ, ‖V y - V x‖ ^ 2 ∂μ := hmin (V x)
    _ ≤ μ.real (ball x ρ) * (8 * C₁ * M / r * ρ) ^ 2 := hstep
    _ = 64 * 2 ^ d * C₁ ^ 2 * (ρ / r) ^ (d + 2) * A := hfinal
    _ ≤ (4 ^ (d + 2) + 64 * 2 ^ d * C₁ ^ 2) * (ρ / r) ^ (d + 2) * A := by
      gcongr
      exact le_add_of_nonneg_left (by positivity)

end BasicElliptic
