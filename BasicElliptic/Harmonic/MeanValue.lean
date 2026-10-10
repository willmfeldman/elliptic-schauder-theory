/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import BasicElliptic.Harmonic.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Mean-value property of harmonic functions

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`.

* `HarmonicOnNhd.setIntegral_ball_eq`: the mean-value property on balls,
  `∫_{B_R(x₀)} u = |B_R| u(x₀)` for `u` harmonic on a neighbourhood of `closedBall x₀ R`.
* `HarmonicOnNhd.setIntegral_ball_eq_smul`: the same for a harmonic field `V : E → F` (with `F`
  a complete real inner product space), `∫_{B_R(x₀)} V = |B_R| • V(x₀)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, Berlin, 2001 (reprint of the 1998 edition).

## Provenance

* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti, path
  `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean`,
  commit 90cca67c0c8e91cd30b0d46cb58101f8c5c59236. License: Apache-2.0. Upstream notice:
  `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`
* Extent: `HarmonicOnNhd.setIntegral_ball_eq` (adapted from
  `setIntegral_ball_eq_of_harmonicOnNhd_zero` and `HarmonicOnNhd.setIntegral_ball_eq`).
* Via: elliptic-bernoulli-foundations (W. M. Feldman), `EllipticBernoulli/Harmonic/MeanValue.lean`,
  commit 32fb58231146c940715b274d781ff92d865eb108.
* Changes: namespace changed to `BasicElliptic` (EB: `EllipticBernoulli`); the weak-harmonicity
  API replaced by `ViscositySolns.Analysis.` names; module form.
  `HarmonicOnNhd.setIntegral_ball_eq_smul` is new.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology
open scoped ContDiff Laplacian RealInnerProductSpace
open ViscositySolns.Analysis (WeaklyHarmonicOn integral_toSphere_eq_of_weaklyHarmonic
  integral_eq_integral_Ioi_integral_toSphere)

public section

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Measure

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The mean-value property on balls, for a weakly harmonic function, centred form. -/
private lemma setIntegral_ball_zero_add_eq [Nontrivial E] {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hcont : ContinuousOn u U) (hu : WeaklyHarmonicOn μ u U) {x₀ : E} {R : ℝ}
    (hΩ : closedBall x₀ R ⊆ U) (hR : 0 < R) :
    ∫ y in ball (0 : E) R, u (x₀ + y) ∂μ = μ.real (ball (0 : E) R) * u x₀ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  set v : E → ℝ := fun y ↦ u (x₀ + y) with hv
  have hvcont : ContinuousOn v (closedBall (0 : E) R) :=
    (hcont.mono hΩ).comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ by
      rw [mem_closedBall, dist_eq_norm] at hy ⊢
      simpa using hy
  have hint : Integrable ((ball (0 : E) R).indicator v) μ :=
    ((hvcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall).integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball, integral_eq_integral_Ioi_integral_toSphere _ hint]
  have hinner : ∀ s ∈ Ioi (0 : ℝ), s ^ (Module.finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, (ball (0 : E) R).indicator v (s • (θ : E)) ∂μ.toSphere =
        (Iio R).indicator (fun s ↦ s ^ (Module.finrank ℝ E - 1) • (μ.toSphere.real univ • u x₀))
          s := by
    intro s hs
    have hs : 0 < s := hs
    have hmem : ∀ θ : sphere (0 : E) 1, s • (θ : E) ∈ ball (0 : E) R ↔ s < R := fun θ ↦ by
      rw [mem_ball_zero_iff, norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
    by_cases hsR : s < R
    · rw [indicator_of_mem (mem_Iio.mpr hsR)]
      simp_rw [indicator_of_mem ((hmem _).mpr hsR)]
      rw [hv, integral_toSphere_eq_of_weaklyHarmonic hU hcont hu
        ((closedBall_subset_closedBall hsR.le).trans hΩ) hs.le]
    · rw [indicator_of_notMem (by simpa using hsR)]
      simp_rw [indicator_of_notMem ((not_congr (hmem _)).mpr hsR)]
      simp
  have hball : μ.real (ball (0 : E) R) = R ^ (m + 1) * μ.real (ball (0 : E) 1) := by
    rw [measureReal_def, Measure.addHaar_ball μ _ hR.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hm, measureReal_def]
  have hsph : μ.toSphere.real univ = ((m : ℝ) + 1) * μ.real (ball (0 : E) 1) := by
    rw [Measure.toSphere_real_apply_univ, hm]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio, integral_smul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le, integral_pow, hball, hsph, smul_smul, hm,
    Nat.add_sub_cancel, zero_pow (Nat.succ_ne_zero m), sub_zero, smul_eq_mul]
  field_simp

/-- **The mean-value property on balls.** If `u` is harmonic on a neighbourhood of the closed
ball `closedBall x₀ R`, then `∫_{B_R(x₀)} u = |B_R| u(x₀)`. (For `R ≤ 0` both sides vanish.) -/
theorem HarmonicOnNhd.setIntegral_ball_eq {u : E → ℝ} {x₀ : E} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) :
    ∫ x in ball x₀ R, u x ∂μ = μ.real (ball x₀ R) * u x₀ := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.mpr hR]
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [setIntegral_congr_fun measurableSet_ball (g := fun _ ↦ u x₀)
      fun x _ ↦ congrArg u (Subsingleton.elim x x₀), setIntegral_const, smul_eq_mul]
  -- the harmonic points form an open set containing the closed ball
  set U := {x : E | HarmonicAt u x}
  have hU : IsOpen U := isOpen_setOfPred_harmonicAt u
  have hΩ : closedBall x₀ R ⊆ U := fun x hx ↦ hu x hx
  have huU : HarmonicOnNhd u U := fun x hx ↦ hx
  have h := setIntegral_ball_zero_add_eq hU huU.contDiffOn.continuousOn
    (HarmonicOnNhd.weaklyHarmonicOn (μ := μ) hU huU) hΩ hR
  rw [Measure.addHaar_real_ball_center, ← h, ← integral_indicator measurableSet_ball,
    ← integral_indicator measurableSet_ball, ← integral_add_left_eq_self _ x₀]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  classical
  simp only [indicator_apply, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]

/-- **The mean-value property on balls, vector form.** If `V : E → F` is harmonic on a
neighbourhood of `closedBall x₀ R`, then `∫_{B_R(x₀)} V = |B_R| • V(x₀)`. -/
theorem HarmonicOnNhd.setIntegral_ball_eq_smul {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {V : E → F} {x₀ : E} {R : ℝ}
    (hV : HarmonicOnNhd V (closedBall x₀ R)) :
    ∫ x in ball x₀ R, V x ∂μ = μ.real (ball x₀ R) • V x₀ := by
  have hint : IntegrableOn V (ball x₀ R) μ :=
    (hV.contDiffOn.continuousOn.integrableOn_compact (isCompact_closedBall x₀ R)).mono_set
      ball_subset_closedBall
  refine ext_inner_right ℝ fun e ↦ ?_
  have h := HarmonicOnNhd.setIntegral_ball_eq (μ := μ) (harmonicOnNhd_inner_left hV e)
  calc ⟪∫ x in ball x₀ R, V x ∂μ, e⟫ = ⟪e, ∫ x in ball x₀ R, V x ∂μ⟫ := real_inner_comm _ _
    _ = ∫ x in ball x₀ R, ⟪e, V x⟫ ∂μ := (integral_inner hint e).symm
    _ = ∫ x in ball x₀ R, ⟪V x, e⟫ ∂μ := by congr 1; ext x; exact real_inner_comm _ _
    _ = μ.real (ball x₀ R) * ⟪V x₀, e⟫ := h
    _ = ⟪μ.real (ball x₀ R) • V x₀, e⟫ := (real_inner_smul_left _ _ _).symm

end Measure

variable {u : E → ℝ} {x y : E} {r s : ℝ}

end BasicElliptic
