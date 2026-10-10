/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import BasicElliptic.Campanato.Density

/-!
# Ball-measure helpers shared by the divergence-form files

Moved here from private copies in `Div/Interior/GradientCampanato.lean`,
`Div/Boundary/Decay.lean` and `Div/Boundary/InteriorDecay.lean`.

* `BasicElliptic.abs_det_le_pow_of_norm_le`: `|det M| ≤ K^d` when `‖M‖ ≤ K` (compare `|M(B_1)|`
  with `|B_K|`).
* `BasicElliptic.memLp_restrict_ball_of_bound`: a measurable field bounded on a ball is in
  `L²` of the ball.
-/

open MeasureTheory Metric Set Filter Module

public section

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `|det M| ≤ K^d` when `‖M‖ ≤ K`: compare `|M(B_1)| = |det M| |B_1|` with `|B_K|`. -/
theorem abs_det_le_pow_of_norm_le {M : E ≃L[ℝ] E} {K : ℝ} (hK : 0 < K)
    (hM : ‖(M : E →L[ℝ] E)‖ ≤ K) :
    |LinearMap.det (M : E →ₗ[ℝ] E)| ≤ K ^ finrank ℝ E := by
  have h1 : volume ((M : E → E) '' ball 0 1) =
      ENNReal.ofReal |LinearMap.det (M : E →ₗ[ℝ] E)| * volume (ball (0 : E) 1) :=
    Measure.addHaar_image_continuousLinearEquiv volume M _
  have h2 : (M : E → E) '' ball 0 1 ⊆ ball 0 K := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖M z‖ = ‖(M : E →L[ℝ] E) z‖ := rfl
      _ ≤ ‖(M : E →L[ℝ] E)‖ * ‖z‖ := (M : E →L[ℝ] E).le_opNorm z
      _ ≤ K * ‖z‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
      _ < K := by nlinarith [norm_nonneg z]
  have h3 := ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono h2 (μ := volume))
  rw [h1, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at h3
  have h4 : (volume (ball (0 : E) K)).toReal = K ^ finrank ℝ E * unitBallVolume E :=
    measureReal_ball_eq hK
  have h5 : (volume (ball (0 : E) 1)).toReal = unitBallVolume E := by
    have := measureReal_ball_eq (E := E) (x := 0) one_pos
    rw [one_pow, one_mul] at this
    exact this
  rw [h4, h5] at h3
  exact le_of_mul_le_mul_right h3 unitBallVolume_pos

/-- A measurable field bounded on a ball is in `L²` of the ball. -/
theorem memLp_restrict_ball_of_bound {F : E → E} {x₀ : E} {r M : ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict (ball x₀ r)))
    (hFM : ∀ y ∈ ball x₀ r, ‖F y‖ ≤ M) : MemLp F 2 (volume.restrict (ball x₀ r)) :=
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  MemLp.of_bound hFm M ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall hFM))

end BasicElliptic
