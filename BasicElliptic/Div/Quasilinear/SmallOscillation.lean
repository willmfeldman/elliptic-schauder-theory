/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Projection.HarmonicReplacement
public import BasicElliptic.Harmonic.Decay
public import BasicElliptic.Campanato.Density
import BasicElliptic.Div.Projection.TestPoincare

/-!
# One comparison step for coefficients close to the identity

`BasicElliptic.Div.campanato_step_small_osc`: there is `C = C(E)` such that, if a bounded,
measurable, weakly curl-free field `F` on `B_r = B_r(z)` satisfies the weak identity
`∫_{B_r} ⟪ã F, ∇φ⟫ = ∫_{B_r} ⟪G, ∇φ⟫` (`Div.IsWeakEqOn ã G 0 F B_r B_r`) with only
`‖ã(y) - 1‖ ≤ ε` and `‖G(y) - c‖ ≤ ε_G` on `B_r` (no continuity of `ã`, `G`), then for
`0 < ρ ≤ r`

`∫_{B_ρ} ‖F - F_ρ‖² ≤ C (((ρ/r)^{d+2} + ε²) ∫_{B_r} ‖F‖² + ε_G² r^d)`.

This is the comparison step of the small-oscillation Campanato argument for `C¹` quasilinear
solutions (Giaquinta–Martinazzi): unlike `campanato_decay_at_point`
(`Div/Interior/PointDecay.lean`), no Hölder continuity of the coefficients is assumed, only their
closeness to the identity.

## Proof

The harmonic replacement (`Div.exists_harmonic_replacement` with `f = 0`, which also exports
`V ∈ L²(B_r)`) gives a harmonic `V` with
`‖F - V‖ ≤ ‖F - ãF‖ + ‖G - c‖ ≤ ε ‖F‖ + ε_G |B_r|^{1/2}` (norms in `L²(B_r)`). The mean minimizes
`c ↦ ∫ ‖F - c‖²`, so with the harmonic decay `C_h` (`Harmonic/Decay.lean`),
`ψ(ρ) ≤ 4 C_h (ρ/r)^{d+2} ψ(r) + (4 C_h + 2) ‖F - V‖²` (`comparison`), and `ψ(r) ≤ ∫_{B_r} ‖F‖²`.

## Provenance

`comparison'` is a copy (with `f = 0`) of the private lemma `comparison` of
`Div/Interior/PointDecay.lean`. The harmonic replacement `Div.exists_harmonic_replacement` exports
`V ∈ L²`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient ContDiff Topology

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private instance isFiniteMeasure_restrict_ball' (x : E) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (ball x r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem integrable_norm_sq' {μ : Measure E} {g : E → E} (hg : MemLp g 2 μ) :
    Integrable (fun y ↦ ‖g y‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_sub_sq_le' (u v w : E) :
    ‖u - w‖ ^ 2 ≤ 2 * ‖v - w‖ ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub u v w
  have h0 := norm_nonneg (u - w)
  nlinarith [sq_nonneg (‖v - w‖ - ‖u - v‖), norm_nonneg (v - w), norm_nonneg (u - v)]

/-- The comparison chain (copy of the private `comparison` of `Div/Interior/PointDecay.lean`): for
`F, V ∈ L²(B_r)` with `V` harmonic, `ψ(ρ) ≤ 4 C_h (ρ/r)^{d+2} ψ(r) + (4 C_h + 2) ∫_{B_r} ‖F - V‖²`.
-/
private theorem comparison' {Ch : ℝ} (hCh : 0 ≤ Ch)
    (hdecay : ∀ (V : E → E) (x : E) (r ρ : ℝ), 0 < ρ → ρ ≤ r →
      (∀ e : E, HarmonicOnNhd (fun y ↦ ⟪V y, e⟫) (ball x r)) →
      IntegrableOn (fun y ↦ ‖V y‖ ^ 2) (ball x r) →
      ∫ y in ball x ρ, ‖V y - ⨍ z in ball x ρ, V z‖ ^ 2 ≤
        Ch * (ρ / r) ^ (finrank ℝ E + 2) * ∫ y in ball x r, ‖V y - ⨍ z in ball x r, V z‖ ^ 2)
    {x₀ : E} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) {F V : E → E}
    (hFL : MemLp F 2 (volume.restrict (ball x₀ r))) (hVL : MemLp V 2 (volume.restrict (ball x₀ r)))
    (hVh : ∀ e : E, HarmonicOnNhd (fun y ↦ ⟪V y, e⟫) (ball x₀ r)) :
    ∫ y in ball x₀ ρ, ‖F y - ⨍ z in ball x₀ ρ, F z‖ ^ 2 ≤
      4 * Ch * (ρ / r) ^ (finrank ℝ E + 2) * (∫ y in ball x₀ r, ‖F y - ⨍ z in ball x₀ r, F z‖ ^ 2)
        + (4 * Ch + 2) * ∫ y in ball x₀ r, ‖F y - V y‖ ^ 2 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hρsub : ball x₀ ρ ⊆ ball x₀ r := ball_subset_ball hρr
  have hFLρ : MemLp F 2 (volume.restrict (ball x₀ ρ)) :=
    hFL.mono_measure (Measure.restrict_mono hρsub le_rfl)
  have hVLρ : MemLp V 2 (volume.restrict (ball x₀ ρ)) :=
    hVL.mono_measure (Measure.restrict_mono hρsub le_rfl)
  have hFVL : MemLp (fun y ↦ F y - V y) 2 (volume.restrict (ball x₀ r)) := hFL.sub hVL
  set mV := ⨍ z in ball x₀ ρ, V z
  set mF := ⨍ z in ball x₀ r, F z
  set D := ∫ y in ball x₀ r, ‖F y - V y‖ ^ 2 with hDdef
  set ψr := ∫ y in ball x₀ r, ‖F y - mF‖ ^ 2 with hψr
  have hψr0 : 0 ≤ ψr := setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hD0 : 0 ≤ D := setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have sa : ∫ y in ball x₀ ρ, ‖F y - ⨍ z in ball x₀ ρ, F z‖ ^ 2 ≤
      2 * (∫ y in ball x₀ ρ, ‖V y - mV‖ ^ 2) + 2 * ∫ y in ball x₀ ρ, ‖F y - V y‖ ^ 2 := by
    have hi1 : IntegrableOn (fun y ↦ ‖V y - mV‖ ^ 2) (ball x₀ ρ) :=
      integrable_norm_sq' (hVLρ.sub (memLp_const mV))
    have hi2 : IntegrableOn (fun y ↦ ‖F y - V y‖ ^ 2) (ball x₀ ρ) :=
      integrable_norm_sq' (hFLρ.sub hVLρ)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi1.const_mul 2)
      (hi2.const_mul 2)]
    exact (setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hFLρ.integrable one_le_two) (integrable_norm_sq' hFLρ) mV).trans
      (integral_mono (integrable_norm_sq' (hFLρ.sub (memLp_const mV)))
        ((hi1.const_mul 2).add (hi2.const_mul 2)) fun y ↦ norm_sub_sq_le' (F y) (V y) mV)
  have sc : ∫ y in ball x₀ ρ, ‖V y - mV‖ ^ 2 ≤
      Ch * (ρ / r) ^ (finrank ℝ E + 2) * ∫ y in ball x₀ r, ‖V y - ⨍ z in ball x₀ r, V z‖ ^ 2 :=
    hdecay V x₀ r ρ hρ hρr hVh (integrable_norm_sq' hVL)
  have sd : ∫ y in ball x₀ r, ‖V y - ⨍ z in ball x₀ r, V z‖ ^ 2 ≤ 2 * D + 2 * ψr := by
    have hi1 : IntegrableOn (fun y ↦ ‖F y - V y‖ ^ 2) (ball x₀ r) := integrable_norm_sq' hFVL
    have hi2 : IntegrableOn (fun y ↦ ‖F y - mF‖ ^ 2) (ball x₀ r) :=
      integrable_norm_sq' (hFL.sub (memLp_const mF))
    refine (setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hVL.integrable one_le_two) (integrable_norm_sq' hVL) mF).trans ?_
    rw [hDdef, hψr, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi1.const_mul 2) (hi2.const_mul 2)]
    refine integral_mono (integrable_norm_sq' (hVL.sub (memLp_const mF)))
      ((hi1.const_mul 2).add (hi2.const_mul 2)) fun y ↦ ?_
    have := norm_sub_sq_le' (V y) (F y) mF
    rw [norm_sub_rev (V y) (F y)] at this
    simpa only [add_comm] using this
  have sf : ∫ y in ball x₀ ρ, ‖F y - V y‖ ^ 2 ≤ D :=
    setIntegral_mono_set (integrable_norm_sq' hFVL) (Eventually.of_forall fun _ ↦ sq_nonneg _)
      hρsub.eventuallyLE
  set q := (ρ / r) ^ (finrank ℝ E + 2)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr)
  have hsd := mul_le_mul_of_nonneg_left sd (mul_nonneg hCh hq0)
  have hqD : Ch * q * D ≤ Ch * 1 * D :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq1 hCh) hD0
  linarith

/-- `√(∫_s g) ≤ c √|s|` for `|g| ≤ c²` on a ball. -/
private theorem sqrt_setIntegral_le {x₀ : E} {r : ℝ} {g : E → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y ∈ ball x₀ r, |g y| ≤ c ^ 2) :
    √(∫ y in ball x₀ r, g y) ≤ c * √(volume.real (ball x₀ r)) := by
  have h1 : ∫ y in ball x₀ r, g y ≤ c ^ 2 * volume.real (ball x₀ r) :=
    (Real.le_norm_self _).trans ((norm_setIntegral_le_of_norm_le_const measure_ball_lt_top
      fun y hy ↦ by rw [Real.norm_eq_abs]; exact h y hy))
  calc √(∫ y in ball x₀ r, g y) ≤ √(c ^ 2 * volume.real (ball x₀ r)) := Real.sqrt_le_sqrt h1
    _ = c * √(volume.real (ball x₀ r)) := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

variable (E) in
/-- **One comparison step for coefficients close to the identity** (see the module docstring).
There is `C = C(E) ≥ 0` such that, if `F` is measurable, bounded and weakly curl-free on
`B_r(z)` and `∫_{B_r} ⟪ã F, ∇φ⟫ = ∫_{B_r} ⟪G, ∇φ⟫` for `φ ∈ C¹_c(B_r)`, with `ã`, `G`
measurable, `‖ã - 1‖ ≤ ε` and `‖G - c‖ ≤ ε_G` on `B_r`, then for `0 < ρ ≤ r`
`∫_{B_ρ} ‖F - F_ρ‖² ≤ C (((ρ/r)^{d+2} + ε²) ∫_{B_r} ‖F‖² + ε_G² r^d)`. -/
theorem campanato_step_small_osc :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : E) (r ρ M ε εG : ℝ) (F G : E → E) (c : E)
      (ã : E → E →L[ℝ] E), 0 < ρ → ρ ≤ r →
      AEStronglyMeasurable F (volume.restrict (ball z r)) → (∀ y ∈ ball z r, ‖F y‖ ≤ M) →
      IsWeakCurlFree F (ball z r) →
      AEStronglyMeasurable ã (volume.restrict (ball z r)) → (∀ y ∈ ball z r, ‖ã y - 1‖ ≤ ε) →
      AEStronglyMeasurable G (volume.restrict (ball z r)) → (∀ y ∈ ball z r, ‖G y - c‖ ≤ εG) →
      IsWeakEqOn ã G 0 F (ball z r) (ball z r) →
      ∫ y in ball z ρ, ‖F y - ⨍ y' in ball z ρ, F y'‖ ^ 2 ≤
        C * (((ρ / r) ^ (finrank ℝ E + 2) + ε ^ 2) * (∫ y in ball z r, ‖F y‖ ^ 2) +
          εG ^ 2 * r ^ finrank ℝ E) := by
  obtain ⟨Ch, hCh, hdecay⟩ := harmonic_campanato_decay E (volume : Measure E) E
  set vB := unitBallVolume E
  have hvB : 0 < vB := unitBallVolume_pos
  refine ⟨(4 * Ch + 2) * 2 * (1 + vB), by positivity, ?_⟩
  intro z r ρ M ε εG F G c ã hρ hρr hFm hFM hcurl hãm hã hGm hG hweak
  have hr : 0 < r := hρ.trans_le hρr
  set B := ball z r with hBdef
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hã z (mem_ball_self hr))
  have hεG : 0 ≤ εG := (norm_nonneg _).trans (hG z (mem_ball_self hr))
  have hFL : MemLp F 2 (volume.restrict B) :=
    MemLp.of_bound hFm M ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall hFM))
  have hGL : MemLp G 2 (volume.restrict B) :=
    MemLp.of_bound hGm (‖c‖ + εG) ((ae_restrict_iff' measurableSet_ball).2
      (Eventually.of_forall fun y hy ↦ (norm_le_norm_add_norm_sub' (G y) c).trans
        (add_le_add le_rfl (hG y hy))))
  have hãb : ∀ y ∈ B, ‖ã y‖ ≤ 1 + ε := fun y hy ↦
    (norm_le_norm_add_norm_sub' (ã y) 1).trans (add_le_add ContinuousLinearMap.norm_id_le
      (hã y hy))
  obtain ⟨V, hVh, hVL, hFV, -⟩ := exists_harmonic_replacement hr c hFL hcurl hãm hãb hGL
    (f := 0) (Mf := 0) (fun _ _ ↦ by simp)
    fun φ h1 h2 h3 ↦ by simpa using hweak φ (IsSmoothTestFn.isTestFn (U := B) ⟨h1, h2, h3⟩)
  simp only [mul_zero, add_zero] at hFV
  set I := ∫ y in B, ‖F y‖ ^ 2 with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hFi : Integrable (fun y ↦ ‖F y‖ ^ 2) (volume.restrict B) := integrable_norm_sq' hFL
  -- the energy of `F - V`
  have h1 : √(∫ y in B, ‖F y - ã y (F y)‖ ^ 2) ≤ ε * √I := by
    have hle : ∫ y in B, ‖F y - ã y (F y)‖ ^ 2 ≤ ∫ y in B, ε ^ 2 * ‖F y‖ ^ 2 := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _)
        (hFi.const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have he : F y - ã y (F y) = -((ã y - 1) (F y)) := by simp
      rw [he, norm_neg, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (((ã y - 1).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hã y hy) (norm_nonneg _))) 2
    rw [integral_const_mul] at hle
    calc √(∫ y in B, ‖F y - ã y (F y)‖ ^ 2) ≤ √(ε ^ 2 * I) := Real.sqrt_le_sqrt hle
      _ = ε * √I := by rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]
  have h2 : √(∫ y in B, ‖G y - c‖ ^ 2) ≤ εG * √(volume.real B) :=
    sqrt_setIntegral_le hεG fun y hy ↦ by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hG y hy) 2
  set D := ∫ y in B, ‖F y - V y‖ ^ 2 with hDdef
  have hD0 : 0 ≤ D := setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hvol : volume.real B = r ^ finrank ℝ E * vB := measureReal_ball_eq hr
  have hD : D ≤ 2 * ε ^ 2 * I + 2 * εG ^ 2 * (r ^ finrank ℝ E * vB) := by
    have hs : √D ≤ ε * √I + εG * √(volume.real B) := hFV.trans (add_le_add h1 h2)
    have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    rw [Real.sq_sqrt hD0] at h3
    have e1 : (ε * √I) ^ 2 = ε ^ 2 * I := by rw [mul_pow, Real.sq_sqrt hI0]
    have e2 : (εG * √(volume.real B)) ^ 2 = εG ^ 2 * (r ^ finrank ℝ E * vB) := by
      rw [mul_pow, Real.sq_sqrt measureReal_nonneg, hvol]
    nlinarith [sq_nonneg (ε * √I - εG * √(volume.real B))]
  -- the mean minimizes
  have hψr : ∫ y in B, ‖F y - ⨍ z in B, F z‖ ^ 2 ≤ I := by
    simpa using setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hFL.integrable one_le_two) hFi (0 : E)
  have hcomp := comparison' hCh hdecay hρ hρr hFL hVL hVh
  set q := (ρ / r) ^ (finrank ℝ E + 2)
  have hq0 : 0 ≤ q := by positivity
  set rd := r ^ finrank ℝ E
  have hrd : 0 ≤ rd := by positivity
  have k1 : 4 * Ch * q * (∫ y in B, ‖F y - ⨍ z in B, F z‖ ^ 2) ≤ 4 * Ch * q * I :=
    mul_le_mul_of_nonneg_left hψr (by positivity)
  have k2 : (4 * Ch + 2) * D ≤
      (4 * Ch + 2) * (2 * ε ^ 2 * I + 2 * εG ^ 2 * (rd * vB)) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have k3 : 4 * Ch * q * I ≤ (4 * Ch + 2) * 2 * (1 + vB) * (q * I) := by
    have : 4 * Ch ≤ (4 * Ch + 2) * 2 * (1 + vB) := by nlinarith
    nlinarith [mul_nonneg hq0 hI0]
  have k4 : (4 * Ch + 2) * (2 * ε ^ 2 * I) ≤ (4 * Ch + 2) * 2 * (1 + vB) * (ε ^ 2 * I) := by
    have : 0 ≤ (4 * Ch + 2) * 2 * (ε ^ 2 * I) := by positivity
    nlinarith
  have k5 : (4 * Ch + 2) * (2 * εG ^ 2 * (rd * vB)) ≤
      (4 * Ch + 2) * 2 * (1 + vB) * (εG ^ 2 * rd) := by
    have : 0 ≤ (4 * Ch + 2) * 2 * (εG ^ 2 * rd) := by positivity
    nlinarith
  calc _ ≤ _ := hcomp
    _ ≤ (4 * Ch + 2) * 2 * (1 + vB) * ((q + ε ^ 2) * I + εG ^ 2 * rd) := by
        nlinarith

end BasicElliptic.Div
