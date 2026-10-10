/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Div
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Half balls: null sets, reflection calculus and gradients within

Elementary facts shared by the conormal boundary theory:

* `volume_flatPart`: the flat part `{⟪·, ν⟫ = 0}` is a null set (`ν ≠ 0`);
* `halfBall_ae_eq`, `ball_inter_halfSpace_ae_eq`: the closed half ball `halfBall ν x r` agrees a.e.
  with `ball x r ∩ openHalfSpace ν` and with `ball x r ∩ halfSpace ν`;
* `inner_reflect_left`, `reflect_mem_ball`, `hasGradientAt_comp_reflect`, `IsTestFn.comp_reflect`:
  calculus of the reflection `reflect ν` (self-adjoint; preserves balls centred on the flat part);
* `gradientWithin_halfBall_eq`, `hasGradientAt_of_mem_ball_inter`,
  `continuousOn_gradientWithin_halfBall`: the within-gradient on the closed half ball.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The reflection -/

/-- The reflection across the flat part is self-adjoint. -/
theorem inner_reflect_left (ν u v : E) : ⟪reflect ν u, v⟫ = ⟪u, reflect ν v⟫ := by
  calc ⟪reflect ν u, v⟫ = ⟪reflect ν u, reflect ν (reflect ν v)⟫ := by rw [reflect_reflect]
    _ = ⟪u, reflect ν v⟫ := (reflect ν).inner_map_map u (reflect ν v)

/-- The reflection preserves distances to points of the flat part. -/
theorem dist_reflect_eq {ν x : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) (y : E) :
    dist (reflect ν y) x = dist y x := by
  have hRx : reflect ν x = x := reflect_eq_self_of_mem_flatPart hν hx
  calc dist (reflect ν y) x = dist (reflect ν y) (reflect ν x) := by rw [hRx]
    _ = dist y x := (reflect ν).dist_map y x

/-- The reflection preserves balls centred on the flat part. -/
theorem reflect_mem_ball {ν x y : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) {r : ℝ} :
    reflect ν y ∈ ball x r ↔ y ∈ ball x r := by
  rw [mem_ball, mem_ball, dist_reflect_eq hν hx]

/-- Chain rule for the gradient of `φ ∘ reflect ν`. -/
theorem hasGradientAt_comp_reflect [CompleteSpace E] (ν : E) {φ : E → ℝ} {g y : E}
    (h : HasGradientAt φ g (reflect ν y)) :
    HasGradientAt (fun z ↦ φ (reflect ν z)) (reflect ν g) y := by
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  have h' := h.comp y ((reflect ν).toLinearIsometry.toContinuousLinearMap).hasFDerivAt
  refine h'.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply]
  exact (inner_reflect_left ν g v).symm

/-- Test functions on a ball centred on the flat part are stable under the reflection. -/
theorem IsTestFn.comp_reflect {ν x : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) {r : ℝ}
    {φ : E → ℝ} (h : IsTestFn (ball x r) φ) : IsTestFn (ball x r) (fun z ↦ φ (reflect ν z)) := by
  refine ⟨h.1.comp (reflect ν).contDiff, h.2.1.comp_homeomorph (reflect ν).toHomeomorph, ?_⟩
  refine (tsupport_comp_subset_preimage φ (reflect ν).continuous).trans fun y hy ↦ ?_
  exact (reflect_mem_ball hν hx).1 (h.2.2 hy)


private theorem norm_sub_reflect_le {ν y z : E} (hν : ‖ν‖ = 1) (hy : 0 ≤ ⟪y, ν⟫)
    (hz : ⟪z, ν⟫ ≤ 0) : ‖y - reflect ν z‖ ≤ ‖y - z‖ := by
  have h : y - reflect ν z = (y - z) + (2 * ⟪z, ν⟫) • ν := by
    rw [reflect_apply hν]; abel
  have h2 : ‖y - reflect ν z‖ ^ 2 = ‖y - z‖ ^ 2 + 4 * ⟪z, ν⟫ * ⟪y, ν⟫ := by
    rw [h, norm_add_sq_real, real_inner_smul_right, norm_smul, hν, inner_sub_left,
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have h3 : 4 * ⟪z, ν⟫ * ⟪y, ν⟫ ≤ 0 := by nlinarith
  nlinarith [norm_nonneg (y - reflect ν z), norm_nonneg (y - z)]

/-- The fold onto the half space is `1`-Lipschitz. -/
theorem dist_fold_le {ν : E} (hν : ‖ν‖ = 1) (y z : E) : dist (fold ν y) (fold ν z) ≤ dist y z := by
  unfold fold
  split_ifs with hy hz hz
  · exact le_rfl
  · rw [dist_eq_norm, dist_eq_norm]; exact norm_sub_reflect_le hν hy (not_le.1 hz).le
  · rw [dist_comm, dist_eq_norm, dist_comm, dist_eq_norm]
    exact norm_sub_reflect_le hν hz (not_le.1 hy).le
  · exact ((reflect ν).dist_map y z).le

/-- The fold maps a closed ball centred on the flat part onto the closed half ball. -/
theorem fold_mem_halfBall {ν x y : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) {r : ℝ}
    (hy : y ∈ closedBall x r) : fold ν y ∈ halfBall ν x r := by
  refine ⟨?_, fold_mem_halfSpace hν y⟩
  have hRx : fold ν x = x := fold_of_mem (mem_halfSpace.2 hx.ge)
  rw [mem_closedBall, ← hRx]
  exact (dist_fold_le hν y x).trans (mem_closedBall.1 hy)

/-! ### Gradients within the closed half ball -/

theorem isCompact_halfBall [ProperSpace E] (ν x : E) (r : ℝ) : IsCompact (halfBall ν x r) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_halfBall ν x r) (isBounded_halfBall ν x r)

/-- At points of `ball x r ∩ openHalfSpace ν` the within-gradient on the half ball is the
gradient. -/
theorem gradientWithin_halfBall_eq [CompleteSpace E] {ν x y : E} {r : ℝ} {w : E → ℝ}
    (hy : y ∈ ball x r ∩ openHalfSpace ν) : gradientWithin w (halfBall ν x r) y = ∇ w y := by
  rw [gradientWithin, gradient, fderivWithin_of_mem_nhds]
  exact mem_interior_iff_mem_nhds.1 (ball_inter_openHalfSpace_subset_interior_halfBall ν x r hy)

theorem hasGradientAt_of_mem_ball_inter [CompleteSpace E] {ν x y : E} {r : ℝ} {w : E → ℝ}
    (hw : ContDiffOn ℝ 1 w (halfBall ν x r)) (hy : y ∈ ball x r ∩ openHalfSpace ν) :
    HasGradientAt w (gradientWithin w (halfBall ν x r) y) y := by
  have hn : halfBall ν x r ∈ 𝓝 y :=
    mem_interior_iff_mem_nhds.1 (ball_inter_openHalfSpace_subset_interior_halfBall ν x r hy)
  rw [gradientWithin_halfBall_eq hy]
  exact ((hw.contDiffAt hn).differentiableAt one_ne_zero).hasGradientAt

theorem continuousOn_gradientWithin_halfBall [CompleteSpace E] {ν x : E} {r : ℝ} {w : E → ℝ}
    (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hw : ContDiffOn ℝ 1 w (halfBall ν x r)) :
    ContinuousOn (gradientWithin w (halfBall ν x r)) (halfBall ν x r) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    (hw.continuousOn_fderivWithin (uniqueDiffOn_halfBall hν hr hx) le_rfl)

/-! ### Null sets -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The flat part is a null set. -/
theorem volume_flatPart {ν : E} (hν : ν ≠ 0) : volume (flatPart ν) = 0 := by
  have h : flatPart ν = ((ℝ ∙ ν)ᗮ : Submodule ℝ E) := by
    ext y
    simp [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
  rw [h]
  refine Measure.addHaar_submodule _ _ fun htop ↦ hν ?_
  have : ν ∈ (ℝ ∙ ν)ᗮ := htop ▸ Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
  exact inner_self_eq_zero.1 this

/-- The closed half ball agrees a.e. with `ball x r ∩ openHalfSpace ν`. -/
theorem halfBall_ae_eq {ν : E} (hν : ν ≠ 0) (x : E) (r : ℝ) :
    halfBall ν x r =ᵐ[volume] (ball x r ∩ openHalfSpace ν : Set E) := by
  have : Nontrivial E := ⟨⟨ν, 0, hν⟩⟩
  refine ae_eq_set.2 ⟨measure_mono_null ?_ (measure_union_null
    (Measure.addHaar_sphere volume x r) (volume_flatPart hν)), ?_⟩
  · rintro y ⟨⟨hyc, hyH⟩, hyn⟩
    by_cases hb : y ∈ ball x r
    · exact Or.inr (le_antisymm (not_lt.1 fun h ↦ hyn ⟨hb, h⟩) hyH)
    · exact Or.inl (mem_sphere.2 (le_antisymm (mem_closedBall.1 hyc) (not_lt.1 hb)))
  · have hsub : ball x r ∩ openHalfSpace ν ⊆ halfBall ν x r := fun y hy ↦
      ⟨ball_subset_closedBall hy.1, mem_halfSpace.2 (mem_openHalfSpace.1 hy.2).le⟩
    rw [sdiff_eq_empty.2 hsub, measure_empty]

/-- The closed half ball agrees a.e. with `ball x r ∩ halfSpace ν`. -/
theorem ball_inter_halfSpace_ae_eq {ν : E} (hν : ν ≠ 0) (x : E) (r : ℝ) :
    (ball x r ∩ halfSpace ν : Set E) =ᵐ[volume] halfBall ν x r := by
  refine ae_eq_set.2 ⟨?_, measure_mono_null ?_ (ae_eq_set.1 (halfBall_ae_eq hν x r)).1⟩
  · have hsub : ball x r ∩ halfSpace ν ⊆ halfBall ν x r := fun y hy ↦
      ⟨ball_subset_closedBall hy.1, hy.2⟩
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  · exact sdiff_subset_sdiff_right fun y hy ↦
      (⟨hy.1, mem_halfSpace.2 (mem_openHalfSpace.1 hy.2).le⟩ : y ∈ ball x r ∩ halfSpace ν)

/-- A bounded a.e.-strongly measurable function is integrable on a half ball. -/
theorem integrableOn_halfBall_of_bound {F : Type*} [NormedAddCommGroup F] {ν x : E} {r : ℝ}
    {g : E → F} (hg : AEStronglyMeasurable g (volume.restrict (halfBall ν x r))) {M : ℝ}
    (hM : ∀ y ∈ halfBall ν x r, ‖g y‖ ≤ M) : IntegrableOn g (halfBall ν x r) := by
  have : IsFiniteMeasure (volume.restrict (halfBall ν x r)) :=
    isFiniteMeasure_restrict.2 (isBounded_halfBall ν x r).measure_lt_top.ne
  exact Integrable.of_bound hg M
    ((ae_restrict_iff' (measurableSet_halfBall ν x r)).2 (Eventually.of_forall hM))

end BasicElliptic
