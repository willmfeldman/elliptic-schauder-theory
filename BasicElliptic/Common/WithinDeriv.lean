/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Holder
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import BasicElliptic.Common.UniformLimit
import BasicElliptic.Holder.Algebra
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Within-derivatives versus within-gradients

Shared helpers, used in `Div/Boundary/{Estimate,Main}.lean`, `Div/Quasilinear/Directional.lean`
and `Div/Higher/Directional.lean`. The names live in the namespace `BasicElliptic.Div`.

* `Div.norm_fderivWithin_eq_norm_gradientWithin`, `Div.dist_fderivWithin_eq_dist_gradientWithin`:
  the Riesz map `fderivWithin ↦ gradientWithin` is an isometry;
* `Div.eHolderSeminormOn_fderivWithin_eq`, `Div.holderSeminormOn_fderivWithin_eq`: hence the Hölder
  seminorms agree;
* `Div.abs_translate_sub_le`: mean value bound for a translate;
* `Div.abs_diffQuot_sub_le`: convergence rate of difference quotients for a function with Hölder
  within-gradient.
-/

public section

open Set
open scoped Gradient NNReal

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The norm of the within-gradient is the norm of the within-derivative. -/
theorem norm_fderivWithin_eq_norm_gradientWithin (w : E → ℝ) (s : Set E) (y : E) :
    ‖fderivWithin ℝ w s y‖ = ‖gradientWithin w s y‖ := by
  rw [gradientWithin, LinearIsometryEquiv.norm_map]

/-- Distances of within-derivatives are distances of within-gradients. -/
theorem dist_fderivWithin_eq_dist_gradientWithin (w : E → ℝ) (s : Set E) (y y' : E) :
    dist (fderivWithin ℝ w s y) (fderivWithin ℝ w s y') =
      dist (gradientWithin w s y) (gradientWithin w s y') := by
  simp only [gradientWithin, LinearIsometryEquiv.dist_map]

/-- The extended Hölder seminorms of `D_s w` and `∇_s w` agree (the Riesz map is an
isometry). -/
theorem eHolderSeminormOn_fderivWithin_eq (α : ℝ≥0) (w : E → ℝ) (s t : Set E) :
    eHolderSeminormOn α (fderivWithin ℝ w s) t = eHolderSeminormOn α (gradientWithin w s) t := by
  have hiff : ∀ C : ℝ≥0, HolderOnWith C α (fderivWithin ℝ w s) t ↔
      HolderOnWith C α (gradientWithin w s) t :=
    fun C ↦ by simp only [holderOnWith_iff_dist_le, dist_fderivWithin_eq_dist_gradientWithin]
  simp only [eHolderSeminormOn, hiff]

/-- The Hölder seminorms of `D_s w` and `∇_s w` agree (the Riesz map is an isometry). -/
theorem holderSeminormOn_fderivWithin_eq (α : ℝ≥0) (w : E → ℝ) (s t : Set E) :
    holderSeminormOn α (fderivWithin ℝ w s) t = holderSeminormOn α (gradientWithin w s) t := by
  rw [holderSeminormOn, holderSeminormOn, eHolderSeminormOn_fderivWithin_eq]

/-- Mean value bound for a translate: `|w (h e + y) - w y| ≤ M h`. -/
theorem abs_translate_sub_le {w : E → ℝ} {B S : Set E} (hS : Convex ℝ S) (hSB : S ⊆ B)
    (hw : DifferentiableOn ℝ w B) {M : ℝ} (hM : ∀ y ∈ S, ‖gradientWithin w B y‖ ≤ M) {e y : E}
    {t : ℝ} (ht : 0 ≤ t) (he : ‖e‖ ≤ 1) (hy : y ∈ S) (hy' : t • e + y ∈ S) :
    |w (t • e + y) - w y| ≤ M * t := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y hy)
  have h := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le (f' := fderivWithin ℝ w B)
    (fun z hz ↦ ((hw z (hSB hz)).hasFDerivWithinAt).mono hSB)
    (fun z hz ↦ (norm_fderivWithin_eq_norm_gradientWithin w B z).le.trans (hM z hz)) hy hy'
  rw [add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht] at h
  rw [← Real.norm_eq_abs]
  calc ‖w (t • e + y) - w y‖ ≤ M * (t * ‖e‖) := h
    _ ≤ M * (t * 1) := by gcongr
    _ = M * t := by ring

/-- Convergence of difference quotients: `|t⁻¹ (w (t e + y) - w y) - ∂_e w (y)| ≤ H_w t^α`. -/
theorem abs_diffQuot_sub_le {w : E → ℝ} {B S : Set E} (hS : Convex ℝ S) (hSB : S ⊆ B)
    (hw : DifferentiableOn ℝ w B) {Hw α : ℝ≥0}
    (hHw : HolderOnWith Hw α (gradientWithin w B) S) {e y : E} {t : ℝ} (ht : 0 < t)
    (he : ‖e‖ ≤ 1) (hy : y ∈ S) (hy' : t • e + y ∈ S) :
    |t⁻¹ * (w (t • e + y) - w y) - fderivWithin ℝ w B y e| ≤ Hw * t ^ (α : ℝ) := by
  have h := norm_sub_sub_fderiv_le_of_holder hS (u := w) (u' := fderivWithin ℝ w B)
    (fun z hz ↦ ((hw z (hSB hz)).hasFDerivWithinAt).mono hSB) (H := Hw) (α := α)
    α.2 Hw.2 (fun a ha b hb ↦ by
      rw [← dist_eq_norm, dist_fderivWithin_eq_dist_gradientWithin]
      exact hHw.dist_le ha hb) hy hy'
  rw [add_sub_cancel_right, map_smul, smul_eq_mul, Real.norm_eq_abs] at h
  have hte : ‖t • e‖ ≤ t := by
    rw [norm_smul, Real.norm_of_nonneg ht.le]; nlinarith [norm_nonneg e]
  have h2 : ‖t • e‖ ^ (1 + (α : ℝ)) ≤ t ^ (1 + (α : ℝ)) :=
    Real.rpow_le_rpow (norm_nonneg _) hte (by positivity)
  have e1 : t⁻¹ * (w (t • e + y) - w y) - fderivWithin ℝ w B y e =
      t⁻¹ * (w (t • e + y) - w y - t * fderivWithin ℝ w B y e) := by
    field_simp
  rw [e1, abs_mul, abs_of_pos (inv_pos.2 ht)]
  calc t⁻¹ * |w (t • e + y) - w y - t * fderivWithin ℝ w B y e|
      ≤ t⁻¹ * (Hw * t ^ (1 + (α : ℝ))) := by
        gcongr
        exact h.trans (mul_le_mul_of_nonneg_left h2 Hw.2)
    _ = Hw * t ^ (α : ℝ) := by
        rw [Real.rpow_add ht, Real.rpow_one]; field_simp


end BasicElliptic.Div
