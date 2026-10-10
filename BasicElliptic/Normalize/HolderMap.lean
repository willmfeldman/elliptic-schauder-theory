/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Holder
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import BasicElliptic.Holder.Algebra

/-!
# Conjugated coefficient fields

* `BasicElliptic.norm_comp_comp_sub_le`: `‖A ∘ X ∘ B - A ∘ Z ∘ B‖ ≤ ‖A‖ ‖B‖ ‖X - Z‖`, which
  controls the oscillation of a conjugated coefficient field `ã = M⁻¹ (a ∘ T) M⁻†` by that of `a`.
-/

public section

open Set
open scoped NNReal ENNReal

namespace BasicElliptic

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]

/-- `‖A ∘ X ∘ B - A ∘ Y ∘ B‖ ≤ ‖A‖ ‖B‖ ‖X - Y‖`: the oscillation of a conjugated coefficient
`M⁻¹ a M⁻†` is controlled by `‖M⁻¹‖² ‖a - a'‖`. -/
theorem norm_comp_comp_sub_le (A B X Z : E →L[ℝ] E) :
    ‖A ∘L X ∘L B - A ∘L Z ∘L B‖ ≤ ‖A‖ * ‖B‖ * ‖X - Z‖ := by
  have : A ∘L X ∘L B - A ∘L Z ∘L B = A ∘L (X - Z) ∘L B := by
    ext v; simp
  rw [this]
  calc ‖A ∘L (X - Z) ∘L B‖ ≤ ‖A‖ * (‖X - Z‖ * ‖B‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖A‖ * ‖B‖ * ‖X - Z‖ := by ring

end BasicElliptic
