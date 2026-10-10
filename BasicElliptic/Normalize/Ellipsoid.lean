/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Basic.HalfSpace
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import BasicElliptic.Harmonic.Decay
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Ellipsoids versus balls, and the transfer of Campanato bounds

Let `T z = x₀ + M z` with `‖M z‖ ≤ K ‖z‖` and `‖M⁻¹ y‖ ≤ K' ‖y‖`.

* `BasicElliptic.ball_subset_image_affine_ball`: `ball (T z) ρ ⊆ T (ball z (K' ρ))`.
* The average minimizes `c ↦ ∫_U ‖F - c‖²`: reused from `BasicElliptic.Harmonic.Decay`
  (`setIntegral_norm_sub_setAverage_sq_le`).
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The sandwich -/

theorem ball_subset_image_affine_ball (M : E ≃L[ℝ] E) (x₀ : E) {K' : ℝ} (hK' : 0 < K')
    (hMK' : ∀ y, ‖M.symm y‖ ≤ K' * ‖y‖) (z : E) (ρ : ℝ) :
    ball (x₀ + M z) ρ ⊆ (fun z ↦ x₀ + M z) '' ball z (K' * ρ) := by
  intro y hy
  refine ⟨M.symm (y - x₀), ?_, by simp⟩
  rw [mem_ball, dist_eq_norm] at hy ⊢
  have : M.symm (y - x₀) - z = M.symm (y - (x₀ + M z)) := by
    rw [map_sub, map_sub, map_add, ContinuousLinearEquiv.symm_apply_apply]; abel
  rw [this]
  exact (hMK' _).trans_lt (mul_lt_mul_of_pos_left hy hK')

/-! ### Campanato transfer -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

end BasicElliptic
