/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Half spaces, half balls and the reflection across the flat part

Let `E` be a real inner product space and `ν : E` (a unit vector in all applications).

* `BasicElliptic.halfSpace ν = {x | 0 ≤ ⟪x, ν⟫}`: the closed half space.
* `BasicElliptic.openHalfSpace ν = {x | 0 < ⟪x, ν⟫}`: its interior.
* `BasicElliptic.flatPart ν = {x | ⟪x, ν⟫ = 0}`: the hyperplane bounding it.
* `BasicElliptic.halfBall ν x r = closedBall x r ∩ halfSpace ν`: the closed half ball. The centre
  `x` is arbitrary; the flat-boundary statements assume `-r < ⟪x, ν⟫` so that the half ball has
  nonempty interior (`interior_halfBall_nonempty`).
* `BasicElliptic.reflect ν`: the reflection `y ↦ y - 2 ⟪y, ν⟫ ν` across `flatPart ν` (for
  `‖ν‖ = 1`; `reflect_apply`), as a `LinearIsometryEquiv` (Mathlib's `Submodule.reflection` in
  `(ℝ ∙ ν)ᗮ`).
* `BasicElliptic.fold ν`: the identity on `halfSpace ν` and `reflect ν` off it.
* `BasicElliptic.evenExt`, `BasicElliptic.oddExt`: even and odd extensions of a function across
  `flatPart ν`; `BasicElliptic.reflectField`, `BasicElliptic.reflectCoeff`: the even reflections of
  a vector field and of a coefficient field.

Derivatives on half balls are taken with `fderivWithin` on the closed set; the needed
uniqueness is `uniqueDiffOn_halfBall`.
-/

@[expose] public noncomputable section

open Metric Set RealInnerProductSpace

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Definitions -/

/-- The closed half space `{x | 0 ≤ ⟪x, ν⟫}`. -/
def halfSpace (ν : E) : Set E := {x | 0 ≤ ⟪x, ν⟫}

/-- The open half space `{x | 0 < ⟪x, ν⟫}`. -/
def openHalfSpace (ν : E) : Set E := {x | 0 < ⟪x, ν⟫}

/-- The flat part `{x | ⟪x, ν⟫ = 0}`, the boundary hyperplane of `halfSpace ν`. -/
def flatPart (ν : E) : Set E := {x | ⟪x, ν⟫ = 0}

/-- The closed half ball `closedBall x r ∩ halfSpace ν`. -/
def halfBall (ν x : E) (r : ℝ) : Set E := closedBall x r ∩ halfSpace ν

@[simp] theorem mem_halfSpace {ν x : E} : x ∈ halfSpace ν ↔ 0 ≤ ⟪x, ν⟫ := Iff.rfl

@[simp] theorem mem_openHalfSpace {ν x : E} : x ∈ openHalfSpace ν ↔ 0 < ⟪x, ν⟫ := Iff.rfl

@[simp] theorem mem_flatPart {ν x : E} : x ∈ flatPart ν ↔ ⟪x, ν⟫ = 0 := Iff.rfl

theorem mem_halfBall {ν x y : E} {r : ℝ} :
    y ∈ halfBall ν x r ↔ dist y x ≤ r ∧ 0 ≤ ⟪y, ν⟫ := Iff.rfl

theorem halfBall_subset_closedBall (ν x : E) (r : ℝ) : halfBall ν x r ⊆ closedBall x r :=
  inter_subset_left

theorem halfBall_subset_halfSpace (ν x : E) (r : ℝ) : halfBall ν x r ⊆ halfSpace ν :=
  inter_subset_right

theorem halfBall_mono (ν x : E) {r s : ℝ} (h : r ≤ s) : halfBall ν x r ⊆ halfBall ν x s :=
  inter_subset_inter_left _ (closedBall_subset_closedBall h)

theorem flatPart_subset_halfSpace (ν : E) : flatPart ν ⊆ halfSpace ν :=
  fun _ hx ↦ (mem_flatPart.1 hx).ge

theorem openHalfSpace_subset_halfSpace (ν : E) : openHalfSpace ν ⊆ halfSpace ν :=
  fun _ hx ↦ (mem_openHalfSpace.1 hx).le

/-! ### Topology, convexity, measurability -/

theorem isClosed_halfSpace (ν : E) : IsClosed (halfSpace ν) :=
  isClosed_le continuous_const (continuous_id.inner continuous_const)

theorem isOpen_openHalfSpace (ν : E) : IsOpen (openHalfSpace ν) :=
  isOpen_lt continuous_const (continuous_id.inner continuous_const)

theorem isClosed_halfBall (ν x : E) (r : ℝ) : IsClosed (halfBall ν x r) :=
  isClosed_closedBall.inter (isClosed_halfSpace ν)

theorem isBounded_halfBall (ν x : E) (r : ℝ) : Bornology.IsBounded (halfBall ν x r) :=
  isBounded_closedBall.subset (halfBall_subset_closedBall ν x r)

theorem convex_halfSpace (ν : E) : Convex ℝ (halfSpace ν) :=
  convex_halfSpace_ge ((innerₛₗ ℝ).flip ν).isLinear 0

theorem convex_halfBall (ν x : E) (r : ℝ) : Convex ℝ (halfBall ν x r) :=
  (convex_closedBall x r).inter (convex_halfSpace ν)

theorem measurableSet_halfSpace [MeasurableSpace E] [OpensMeasurableSpace E] (ν : E) :
    MeasurableSet (halfSpace ν) :=
  (isClosed_halfSpace ν).measurableSet

theorem measurableSet_openHalfSpace [MeasurableSpace E] [OpensMeasurableSpace E] (ν : E) :
    MeasurableSet (openHalfSpace ν) :=
  (isOpen_openHalfSpace ν).measurableSet

theorem measurableSet_halfBall [MeasurableSpace E] [OpensMeasurableSpace E] (ν x : E) (r : ℝ) :
    MeasurableSet (halfBall ν x r) :=
  (isClosed_halfBall ν x r).measurableSet

theorem ball_inter_openHalfSpace_subset_interior_halfBall (ν x : E) (r : ℝ) :
    ball x r ∩ openHalfSpace ν ⊆ interior (halfBall ν x r) :=
  interior_maximal
    (inter_subset_inter ball_subset_closedBall (openHalfSpace_subset_halfSpace ν))
    (isOpen_ball.inter (isOpen_openHalfSpace ν))

theorem real_inner_self_of_norm_eq_one {ν : E} (hν : ‖ν‖ = 1) : ⟪ν, ν⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hν, one_pow]

/-- A half ball with `-r < ⟪x, ν⟫` (centre anywhere, ball meeting the open half space) has nonempty
interior. -/
theorem interior_halfBall_nonempty {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r)
    (hx : -r < ⟪x, ν⟫) : (interior (halfBall ν x r)).Nonempty := by
  refine Set.Nonempty.mono (ball_inter_openHalfSpace_subset_interior_halfBall ν x r) ?_
  rcases lt_or_ge 0 ⟪x, ν⟫ with h | h
  · exact ⟨x, mem_ball_self hr, h⟩
  · refine ⟨x + ((r - ⟪x, ν⟫) / 2) • ν, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [mem_openHalfSpace, inner_add_left, real_inner_smul_left,
        real_inner_self_of_norm_eq_one hν]
      linarith

/-- Uniqueness of within-derivatives on half balls. -/
theorem uniqueDiffOn_halfBall {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r)
    (hx : -r < ⟪x, ν⟫) : UniqueDiffOn ℝ (halfBall ν x r) :=
  uniqueDiffOn_convex (convex_halfBall ν x r) (interior_halfBall_nonempty hν hr hx)

/-! ### Reflection across the flat part -/

/-- The reflection across `flatPart ν`: Mathlib's reflection in the hyperplane `(ℝ ∙ ν)ᗮ`. For
`‖ν‖ = 1` it is `y ↦ y - 2 ⟪y, ν⟫ ν` (`reflect_apply`). -/
def reflect (ν : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ν)ᗮ.reflection

theorem reflect_apply {ν : E} (hν : ‖ν‖ = 1) (y : E) :
    reflect ν y = y - (2 * ⟪y, ν⟫) • ν := by
  rw [reflect, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, hν,
    real_inner_comm]
  simp only [RCLike.ofReal_real_eq_id, id, one_pow, div_one]
  module

@[simp] theorem reflect_reflect (ν y : E) : reflect ν (reflect ν y) = y :=
  Submodule.reflection_reflection _ y

theorem inner_reflect {ν : E} (hν : ‖ν‖ = 1) (y : E) : ⟪reflect ν y, ν⟫ = -⟪y, ν⟫ := by
  rw [reflect_apply hν, inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν]
  ring

theorem reflect_eq_self_of_mem_flatPart {ν y : E} (hν : ‖ν‖ = 1) (hy : y ∈ flatPart ν) :
    reflect ν y = y := by
  rw [reflect_apply hν, mem_flatPart.1 hy]
  simp

/-- The fold onto the half space: the identity on `halfSpace ν`, `reflect ν` off it. -/
def fold (ν : E) (y : E) : E := if 0 ≤ ⟪y, ν⟫ then y else reflect ν y

theorem fold_of_mem {ν y : E} (hy : y ∈ halfSpace ν) : fold ν y = y :=
  ite_eq_left_iff.2 fun h ↦ (h hy).elim

theorem fold_mem_halfSpace {ν : E} (hν : ‖ν‖ = 1) (y : E) : fold ν y ∈ halfSpace ν := by
  unfold fold
  split_ifs with h
  · exact h
  · rw [mem_halfSpace, inner_reflect hν]; linarith [not_le.1 h]

/-- The even extension `h ∘ fold ν` of a function given on `halfSpace ν`. -/
def evenExt {β : Type*} (ν : E) (h : E → β) (y : E) : β := h (fold ν y)

/-- The odd extension of a real function given on `halfSpace ν`: `h` on the half space and
`-h ∘ reflect ν` off it. -/
def oddExt (ν : E) (h : E → ℝ) (y : E) : ℝ :=
  if 0 ≤ ⟪y, ν⟫ then h y else -h (reflect ν y)

/-- Even reflection of a vector field: `G` on the half space, `R (G (R y))` off it
(`R = reflect ν`). Off the flat part, `∇(w ∘ fold ν) = reflectField ν (∇w)`. -/
def reflectField (ν : E) (G : E → E) (y : E) : E :=
  if 0 ≤ ⟪y, ν⟫ then G y else reflect ν (G (reflect ν y))

/-- Even reflection of a coefficient field: `a` on the half space, `R ∘ a (R y) ∘ R` off it
(`R = reflect ν`). -/
def reflectCoeff (ν : E) (a : E → E →L[ℝ] E) (y : E) : E →L[ℝ] E :=
  if 0 ≤ ⟪y, ν⟫ then a y
  else (reflect ν : E →L[ℝ] E) ∘L a (reflect ν y) ∘L (reflect ν : E →L[ℝ] E)

end BasicElliptic
