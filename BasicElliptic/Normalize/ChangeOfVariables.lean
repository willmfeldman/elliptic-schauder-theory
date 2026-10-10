/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Div
public import BasicElliptic.Defs.Nondiv
public import BasicElliptic.Normalize.Cholesky
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Transport of weak identities and of the nondivergence operator under affine maps

For `M : E ≃L[ℝ] E` and `x₀ : E` put `T z = x₀ + M z` and
`w̃ = w ∘ T`, so that `∇w̃(z) = M† ∇w(T z)`. The weak identity of `Div.IsWeakEqOn` on `s` (tests in
`C¹_c(U)`) becomes the same identity on `T⁻¹ s` (tests in `C¹_c(T⁻¹ U)`) with

* `ã(z) = M⁻¹ a(T z) M⁻†`, `G̃(z) = M⁻¹ G(T z)`, `F̃(z) = M† F(T z)`, `f̃(z) = f(T z)`.

Every integral over `T⁻¹ s` is `|det M|⁻¹` times the integral over `s` (`setIntegral_comp_affine`);
the Jacobian factor is common to all three terms and cancels. (This uses the corrected
parenthesization `(∫_s ⟪G, ∇φ⟫) + ∫_s f φ` of `Div.IsWeakEqOn`.)

Main declarations:

* `BasicElliptic.Div.IsWeakEqOn.comp_affine`, `BasicElliptic.Div.IsWeakSolWithin.comp_affine`: the
  transport on a general region.
* `BasicElliptic.Div.IsWeakSolWithin.restrict`: restriction to `s' ⊆ s`, `U' ⊆ U` with
  `s ∩ U' ⊆ s'`.
* `BasicElliptic.Div.IsConormalSolOn.comp_affine`: for half-space-preserving `M`
  (`⟪M z, ν⟫ = m ⟪z, ν⟫`, `m > 0`) and `x₀ ∈ flatPart ν`, a conormal solution on
  `halfBall ν x₀ r` becomes a conormal solution on the inscribed half ball `halfBall ν 0 ρ`,
  `‖M‖ ρ ≤ r`; tests need not vanish on the flat part.
  `Div.IsConormalSolOn.comp_affine_preimage` is the version on the full transported region.
* Restriction helpers: `setIntegral_eq_of_inter_subset`,
  `IsTestFn.eq_zero_and_gradient_eq_zero`, `gradientWithin_eq_of_subset`.
* `BasicElliptic.Nondiv.op_comp_affine`: `op ã b̃ (T⁻¹ s) w̃ = (op a b s w) ∘ T` with
  `b̃ = M⁻¹ (b ∘ T)`.
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace ContinuousLinearMap
open scoped Gradient Pointwise

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Affine maps -/

/-- The affine homeomorphism `z ↦ x₀ + M z`. -/
private def affineHomeomorph (M : E ≃L[ℝ] E) (x₀ : E) : E ≃ₜ E :=
  M.toHomeomorph.trans (Homeomorph.addLeft x₀)

private theorem continuous_affine (M : E ≃L[ℝ] E) (x₀ : E) : Continuous fun z ↦ x₀ + M z :=
  continuous_const.add M.continuous

private theorem hasFDerivAt_affine (M : E ≃L[ℝ] E) (x₀ z : E) :
    HasFDerivAt (fun z ↦ x₀ + M z) (M : E →L[ℝ] E) z :=
  (M : E →L[ℝ] E).hasFDerivAt.const_add x₀

/-- The inverse affine map, written in the same form. -/
private theorem preimage_affine_symm (M : E ≃L[ℝ] E) (x₀ : E) (U : Set E) :
    (fun x ↦ -M.symm x₀ + M.symm x) ⁻¹' ((fun z ↦ x₀ + M z) ⁻¹' U) = U := by
  ext x; simp

private theorem affine_symm_comp (M : E ≃L[ℝ] E) (x₀ z : E) :
    -M.symm x₀ + M.symm (x₀ + M z) = z := by
  simp

theorem uniqueDiffOn_preimage_affine {s : Set E} (hs : UniqueDiffOn ℝ s) (M : E ≃L[ℝ] E)
    (x₀ : E) : UniqueDiffOn ℝ ((fun z ↦ x₀ + M z) ⁻¹' s) := by
  have : (fun z ↦ x₀ + M z) ⁻¹' s = (fun x ↦ -M.symm x₀ + M.symm x) '' s := by
    ext z
    refine ⟨fun hz ↦ ⟨_, hz, affine_symm_comp M x₀ z⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    simpa using hx
  rw [this]
  exact hs.image (fun x _ ↦ ((M.symm : E →L[ℝ] E).hasFDerivAt.const_add _).hasFDerivWithinAt)
    fun _ _ ↦ M.symm.surjective.denseRange

theorem measurableSet_preimage_affine [MeasurableSpace E] [BorelSpace E] {s : Set E}
    (hs : MeasurableSet s) (M : E ≃L[ℝ] E) (x₀ : E) :
    MeasurableSet ((fun z ↦ x₀ + M z) ⁻¹' s) :=
  hs.preimage (continuous_affine M x₀).measurable

variable [FiniteDimensional ℝ E]

/-! ### Change of variables in integrals -/

/-- Change of variables under `z ↦ x₀ + M z`:
`∫_{T⁻¹ s} g(x₀ + M z) dz = |det M|⁻¹ ∫_s g`. -/
theorem setIntegral_comp_affine [MeasurableSpace E] [BorelSpace E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (M : E ≃L[ℝ] E) (x₀ : E) (g : E → F) (s : Set E) :
    ∫ z in (fun z ↦ x₀ + M z) ⁻¹' s, g (x₀ + M z) =
      |LinearMap.det (M : E →ₗ[ℝ] E)|⁻¹ • ∫ x in s, g x := by
  let T : E ≃ᵐ E := (affineHomeomorph M x₀).toMeasurableEquiv
  have hdet : LinearMap.det (M : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  have hmap : Measure.map T volume =
      ENNReal.ofReal |(LinearMap.det (M : E →ₗ[ℝ] E))⁻¹| • (volume : Measure E) := by
    have hT : (T : E → E) = (fun x ↦ x₀ + x) ∘ (M : E →ₗ[ℝ] E) := rfl
    rw [hT, ← Measure.map_map (measurable_const_add x₀)
        (M : E →ₗ[ℝ] E).continuous_of_finiteDimensional.measurable,
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet,
      Measure.map_smul _ (measurable_const_add x₀).aemeasurable,
      map_add_left_eq_self]
  have := setIntegral_map_equiv T g s (μ := volume)
  rw [hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_inv] at this
  exact this.symm

/-! ### Test functions and gradients -/

omit [FiniteDimensional ℝ E] in
/-- Test functions pull back to test functions. -/
theorem IsTestFn.comp_affine {U : Set E} {φ : E → ℝ} (h : IsTestFn U φ) (M : E ≃L[ℝ] E)
    (x₀ : E) : IsTestFn ((fun z ↦ x₀ + M z) ⁻¹' U) (fun z ↦ φ (x₀ + M z)) := by
  refine ⟨h.1.comp (contDiff_const.add M.contDiff), ?_, ?_⟩
  · exact h.2.1.comp_homeomorph (affineHomeomorph M x₀)
  · exact (tsupport_comp_subset_preimage φ (continuous_affine M x₀)).trans
      (preimage_mono h.2.2)

private theorem toDual_adjoint (M : E ≃L[ℝ] E) (g : E) :
    InnerProductSpace.toDual ℝ E (adjoint (M : E →L[ℝ] E) g) =
      (InnerProductSpace.toDual ℝ E g).comp (M : E →L[ℝ] E) := by
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, coe_comp, Function.comp_apply]
  exact adjoint_inner_left _ _ _

/-- Chain rule for the gradient: `∇(φ ∘ T)(z) = M† ∇φ(T z)`. -/
theorem gradient_comp_affine {φ : E → ℝ} (M : E ≃L[ℝ] E) (x₀ : E) {z : E}
    (hφ : DifferentiableAt ℝ φ (x₀ + M z)) :
    ∇ (fun z ↦ φ (x₀ + M z)) z = adjoint (M : E →L[ℝ] E) (∇ φ (x₀ + M z)) := by
  have h : HasFDerivAt (fun z ↦ φ (x₀ + M z))
      (InnerProductSpace.toDual ℝ E (adjoint (M : E →L[ℝ] E) (∇ φ (x₀ + M z)))) z := by
    rw [toDual_adjoint]
    exact hφ.hasGradientAt.hasFDerivAt.comp z (hasFDerivAt_affine M x₀ z)
  rw [gradient, h.fderiv, LinearIsometryEquiv.symm_apply_apply]

/-- Chain rule for the gradient within a set. -/
theorem gradientWithin_comp_affine {w : E → ℝ} {s : Set E} (M : E ≃L[ℝ] E) (x₀ : E) {z : E}
    (hw : DifferentiableWithinAt ℝ w s (x₀ + M z))
    (hs : UniqueDiffWithinAt ℝ ((fun z ↦ x₀ + M z) ⁻¹' s) z) :
    gradientWithin (fun z ↦ w (x₀ + M z)) ((fun z ↦ x₀ + M z) ⁻¹' s) z =
      adjoint (M : E →L[ℝ] E) (gradientWithin w s (x₀ + M z)) := by
  have h : HasFDerivWithinAt (fun z ↦ w (x₀ + M z))
      (InnerProductSpace.toDual ℝ E (adjoint (M : E →L[ℝ] E) (gradientWithin w s (x₀ + M z))))
      ((fun z ↦ x₀ + M z) ⁻¹' s) z := by
    rw [toDual_adjoint]
    exact hw.hasGradientWithinAt.hasFDerivWithinAt.comp z
      (hasFDerivAt_affine M x₀ z).hasFDerivWithinAt (mapsTo_preimage _ _)
  rw [gradientWithin, h.fderivWithin hs, LinearIsometryEquiv.symm_apply_apply]

/-! ### Half-space-preserving affine maps: sets -/

section HalfSpace

variable {ν x₀ : E} {M : E ≃L[ℝ] E} {m : ℝ}

omit [FiniteDimensional ℝ E] in
theorem inner_affine_eq (hx₀ : ⟪x₀, ν⟫ = 0) (hMν : ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫) (z : E) :
    ⟪x₀ + M z, ν⟫ = m * ⟪z, ν⟫ := by
  rw [inner_add_left, hx₀, hMν, zero_add]

omit [FiniteDimensional ℝ E] in
/-- A half-space-preserving affine map pulls `halfSpace ν` back to itself. -/
theorem preimage_affine_halfSpace (hm : 0 < m) (hx₀ : ⟪x₀, ν⟫ = 0)
    (hMν : ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫) :
    (fun z ↦ x₀ + M z) ⁻¹' halfSpace ν = halfSpace ν := by
  ext z
  simp only [mem_preimage, mem_halfSpace, inner_affine_eq hx₀ hMν]
  exact mul_nonneg_iff_of_pos_left hm

omit [FiniteDimensional ℝ E] in
theorem preimage_affine_halfBall (hm : 0 < m) (hx₀ : ⟪x₀, ν⟫ = 0)
    (hMν : ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫) (r : ℝ) :
    (fun z ↦ x₀ + M z) ⁻¹' halfBall ν x₀ r =
      (fun z ↦ x₀ + M z) ⁻¹' closedBall x₀ r ∩ halfSpace ν := by
  rw [halfBall, preimage_inter, preimage_affine_halfSpace hm hx₀ hMν]

omit [FiniteDimensional ℝ E] in
/-- The ellipsoid `T⁻¹ (ball x₀ r)` contains the ball `ball 0 ρ` when `‖M‖ ρ ≤ r`. -/
theorem ball_subset_preimage_affine_ball {r ρ : ℝ} (hr : 0 < r)
    (hρr : ‖(M : E →L[ℝ] E)‖ * ρ ≤ r) :
    ball 0 ρ ⊆ (fun z ↦ x₀ + M z) ⁻¹' ball x₀ r := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz
  rw [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left]
  have hnorm : ‖M z‖ ≤ ‖(M : E →L[ℝ] E)‖ * ‖z‖ := (M : E →L[ℝ] E).le_opNorm z
  rcases (norm_nonneg (M : E →L[ℝ] E)).eq_or_lt with h0 | h0
  · calc ‖M z‖ ≤ ‖(M : E →L[ℝ] E)‖ * ‖z‖ := hnorm
      _ = 0 := by rw [← h0, zero_mul]
      _ < r := hr
  · calc ‖M z‖ ≤ ‖(M : E →L[ℝ] E)‖ * ‖z‖ := hnorm
      _ < ‖(M : E →L[ℝ] E)‖ * ρ := mul_lt_mul_of_pos_left hz h0
      _ ≤ r := hρr

omit [FiniteDimensional ℝ E] in
theorem closedBall_subset_preimage_affine_closedBall {r ρ : ℝ}
    (hρr : ‖(M : E →L[ℝ] E)‖ * ρ ≤ r) :
    closedBall 0 ρ ⊆ (fun z ↦ x₀ + M z) ⁻¹' closedBall x₀ r := by
  intro z hz
  rw [mem_closedBall, dist_zero_right] at hz
  rw [mem_preimage, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  exact ((M : E →L[ℝ] E).le_opNorm z).trans
    ((mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans hρr)

omit [FiniteDimensional ℝ E] in
/-- The transported half ball `T⁻¹ (halfBall ν x₀ r)` contains the half ball `halfBall ν 0 ρ` when
`‖M‖ ρ ≤ r`. -/
theorem halfBall_subset_preimage_affine_halfBall (hm : 0 < m) (hx₀ : ⟪x₀, ν⟫ = 0)
    (hMν : ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫) {r ρ : ℝ} (hρr : ‖(M : E →L[ℝ] E)‖ * ρ ≤ r) :
    halfBall ν 0 ρ ⊆ (fun z ↦ x₀ + M z) ⁻¹' halfBall ν x₀ r := by
  rw [preimage_affine_halfBall hm hx₀ hMν]
  exact inter_subset_inter (closedBall_subset_preimage_affine_closedBall hρr) subset_rfl

omit [FiniteDimensional ℝ E] in
/-- Inside `ball 0 ρ` the transported half ball is contained in `halfBall ν 0 ρ`. -/
theorem preimage_affine_halfBall_inter_ball_subset (hm : 0 < m) (hx₀ : ⟪x₀, ν⟫ = 0)
    (hMν : ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫) (r ρ : ℝ) :
    (fun z ↦ x₀ + M z) ⁻¹' halfBall ν x₀ r ∩ ball 0 ρ ⊆ halfBall ν 0 ρ := by
  rw [preimage_affine_halfBall hm hx₀ hMν]
  rintro z ⟨⟨-, hz⟩, hz'⟩
  exact ⟨ball_subset_closedBall hz', hz⟩

end HalfSpace

/-! ### Restriction of integrals to a smaller region -/

/-- If `g` vanishes outside `U'` and `s ∩ U' ⊆ s' ⊆ s`, then `∫_s g = ∫_{s'} g`. Used to pass
from the transported region to an inscribed (half) ball; tests supported in `U'` and their
gradients vanish outside `U'`. -/
theorem setIntegral_eq_of_inter_subset {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {s s' U' : Set X} {g : X → ℝ} (hsm : MeasurableSet s) (hs' : s' ⊆ s) (hss' : s ∩ U' ⊆ s')
    (hg : ∀ y ∉ U', g y = 0) : ∫ y in s, g y ∂μ = ∫ y in s', g y ∂μ :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hsm hs' fun y hy ↦
    hg y fun hyU ↦ hy.2 (hss' ⟨hy.1, hyU⟩)

/-- A test function and its gradient vanish outside its support set `U`. -/
theorem IsTestFn.eq_zero_and_gradient_eq_zero {U : Set E} {φ : E → ℝ} (hφ : IsTestFn U φ)
    {y : E} (hy : y ∉ U) : φ y = 0 ∧ ∇ φ y = 0 := by
  have hout : y ∉ tsupport φ := fun h ↦ hy (hφ.2.2 h)
  refine ⟨image_eq_zero_of_notMem_tsupport hout, ?_⟩
  have : fderiv ℝ φ y = 0 := by
    by_contra hne
    exact hout (support_fderiv_subset ℝ hne)
  rw [gradient, this, map_zero]

/-- Gradients within nested sets agree where the smaller set has unique derivatives. -/
theorem gradientWithin_eq_of_subset {w : E → ℝ} {s s' : Set E} (hs' : s' ⊆ s) {y : E}
    (hu : UniqueDiffWithinAt ℝ s' y) (hw : DifferentiableWithinAt ℝ w s y) :
    gradientWithin w s' y = gradientWithin w s y := by
  rw [gradientWithin, gradientWithin, fderivWithin_subset hs' hu hw]

/-! ### Transport of the weak identity -/

private theorem inner_transport (M : E ≃L[ℝ] E) (A : E →L[ℝ] E) (F g : E) :
    ⟪((M.symm : E →L[ℝ] E) ∘L A ∘L adjoint (M.symm : E →L[ℝ] E))
        (adjoint (M : E →L[ℝ] E) F), adjoint (M : E →L[ℝ] E) g⟫ = ⟪A F, g⟫ := by
  have h1 : adjoint (M.symm : E →L[ℝ] E) (adjoint (M : E →L[ℝ] E) F) = F := by
    rw [← comp_apply, adjoint_symm_comp_adjoint, one_apply_eq_self]
  simp only [coe_comp, Function.comp_apply, h1]
  rw [adjoint_inner_right]
  simp

private theorem inner_transport' (M : E ≃L[ℝ] E) (G g : E) :
    ⟪M.symm G, adjoint (M : E →L[ℝ] E) g⟫ = ⟪G, g⟫ := by
  rw [adjoint_inner_right]
  simp

namespace Div

variable [MeasurableSpace E] [BorelSpace E]

/-- **Transport of the weak identity** under `T z = x₀ + M z`:
`ã = M⁻¹ (a ∘ T) M⁻†`, `G̃ = M⁻¹ (G ∘ T)`, `F̃ = M† (F ∘ T)`, `f̃ = f ∘ T`, region `T⁻¹ s`, tests in
`C¹_c(T⁻¹ U)`. -/
theorem IsWeakEqOn.comp_affine {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {F : E → E}
    {s U : Set E} (h : IsWeakEqOn a G f F s U) (M : E ≃L[ℝ] E) (x₀ : E) :
    IsWeakEqOn (fun z ↦ (M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjoint (M.symm : E →L[ℝ] E))
      (fun z ↦ M.symm (G (x₀ + M z))) (fun z ↦ f (x₀ + M z))
      (fun z ↦ adjoint (M : E →L[ℝ] E) (F (x₀ + M z)))
      ((fun z ↦ x₀ + M z) ⁻¹' s) ((fun z ↦ x₀ + M z) ⁻¹' U) := by
  intro ψ hψ
  set φ : E → ℝ := fun x ↦ ψ (-M.symm x₀ + M.symm x) with hφdef
  have hφ : IsTestFn U φ := by
    have := hψ.comp_affine M.symm (-M.symm x₀)
    rwa [preimage_affine_symm] at this
  have hψφ : ψ = fun z ↦ φ (x₀ + M z) := by
    funext z; simp only [hφdef, affine_symm_comp]
  have hgrad : ∀ z, ∇ ψ z = adjoint (M : E →L[ℝ] E) (∇ φ (x₀ + M z)) := fun z ↦ by
    rw [hψφ]
    exact gradient_comp_affine M x₀ (hφ.1.differentiable one_ne_zero _)
  have key := h φ hφ
  simp only [hgrad, inner_transport, inner_transport']
  have h1 : ∫ z in (fun z ↦ x₀ + M z) ⁻¹' s, ⟪a (x₀ + M z) (F (x₀ + M z)), ∇ φ (x₀ + M z)⟫ =
      |LinearMap.det (M : E →ₗ[ℝ] E)|⁻¹ • ∫ x in s, ⟪a x (F x), ∇ φ x⟫ :=
    setIntegral_comp_affine M x₀ (fun x ↦ ⟪a x (F x), ∇ φ x⟫) s
  have h2 : ∫ z in (fun z ↦ x₀ + M z) ⁻¹' s, ⟪G (x₀ + M z), ∇ φ (x₀ + M z)⟫ =
      |LinearMap.det (M : E →ₗ[ℝ] E)|⁻¹ • ∫ x in s, ⟪G x, ∇ φ x⟫ :=
    setIntegral_comp_affine M x₀ (fun x ↦ ⟪G x, ∇ φ x⟫) s
  have h3 : ∫ z in (fun z ↦ x₀ + M z) ⁻¹' s, f (x₀ + M z) * ψ z =
      |LinearMap.det (M : E →ₗ[ℝ] E)|⁻¹ • ∫ x in s, f x * φ x := by
    rw [hψφ]
    exact setIntegral_comp_affine M x₀ (fun x ↦ f x * φ x) s
  rw [h1, h2, h3, key, smul_add]

/-- **Transport of a region-general weak solution** under `T z = x₀ + M z`:
`w̃ = w ∘ T` solves the identity on `T⁻¹ s` against `C¹_c(T⁻¹ U)` with
`ã = M⁻¹ (a ∘ T) M⁻†`, `G̃ = M⁻¹ (G ∘ T)`, `f̃ = f ∘ T` (see `IsWeakEqOn.comp_affine`). -/
theorem IsWeakSolWithin.comp_affine {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ}
    {s U : Set E} {w : E → ℝ} (h : IsWeakSolWithin a G f s U w) (hs : UniqueDiffOn ℝ s)
    (hsm : MeasurableSet s) (M : E ≃L[ℝ] E) (x₀ : E) :
    IsWeakSolWithin
      (fun z ↦ (M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjoint (M.symm : E →L[ℝ] E))
      (fun z ↦ M.symm (G (x₀ + M z))) (fun z ↦ f (x₀ + M z))
      ((fun z ↦ x₀ + M z) ⁻¹' s) ((fun z ↦ x₀ + M z) ⁻¹' U) (fun z ↦ w (x₀ + M z)) := by
  refine ⟨h.1.comp (contDiff_const.add M.contDiff).contDiffOn (mapsTo_preimage _ _), ?_⟩
  intro ψ hψ
  have key := h.2.comp_affine M x₀ ψ hψ
  have hmeas := measurableSet_preimage_affine hsm M x₀
  have hT := uniqueDiffOn_preimage_affine hs M x₀
  have heq : EqOn (gradientWithin (fun z ↦ w (x₀ + M z)) ((fun z ↦ x₀ + M z) ⁻¹' s))
      (fun z ↦ adjoint (M : E →L[ℝ] E) (gradientWithin w s (x₀ + M z)))
      ((fun z ↦ x₀ + M z) ⁻¹' s) := fun z hz ↦
    gradientWithin_comp_affine M x₀ ((h.1.differentiableOn one_ne_zero) _ hz) (hT z hz)
  refine Eq.trans (setIntegral_congr_fun hmeas fun z hz ↦ ?_) key
  simp only [heq hz]

/-- Restriction of a weak solution to a smaller region `s' ⊆ s` and smaller test domain
`U' ⊆ U`, provided `s ∩ U' ⊆ s'` (tests supported in `U'` do not see `s \ s'`). -/
theorem IsWeakSolWithin.restrict {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ}
    {s U s' U' : Set E} {w : E → ℝ} (h : IsWeakSolWithin a G f s U w) (hU : U' ⊆ U)
    (hs' : s' ⊆ s) (hss' : s ∩ U' ⊆ s') (hsm : MeasurableSet s) (hs'm : MeasurableSet s')
    (hu : UniqueDiffOn ℝ s') : IsWeakSolWithin a G f s' U' w := by
  refine ⟨h.1.mono hs', fun φ hφ ↦ ?_⟩
  have key := h.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hU⟩
  have h0 := fun y hy ↦ hφ.eq_zero_and_gradient_eq_zero (y := y) hy
  rw [setIntegral_eq_of_inter_subset hsm hs' hss' fun y hy ↦ by simp [(h0 y hy).2],
    setIntegral_eq_of_inter_subset hsm hs' hss' fun y hy ↦ by simp [(h0 y hy).2],
    setIntegral_eq_of_inter_subset hsm hs' hss' fun y hy ↦ by simp [(h0 y hy).1]] at key
  refine Eq.trans (setIntegral_congr_fun hs'm fun y hy ↦ ?_) key
  simp only [gradientWithin_eq_of_subset hs' (hu y hy) ((h.1.differentiableOn one_ne_zero) y
    (hs' hy))]

/-- Transport of a conormal solution to the full transported region: if `x₀ ∈ flatPart ν` and `w`
is a conormal solution on `halfBall ν x₀ r`, then `w̃ = w ∘ T` satisfies the weak identity on
`T⁻¹ (halfBall ν x₀ r)` against `C¹_c(T⁻¹ (ball x₀ r))`, with `ã = M⁻¹ (a ∘ T) M⁻†`,
`G̃ = M⁻¹ (G ∘ T)`, `f̃ = f ∘ T`. -/
theorem IsConormalSolOn.comp_affine_preimage {ν : E} (hν : ‖ν‖ = 1) {a : E → E →L[ℝ] E}
    {G : E → E} {f : E → ℝ} {x₀ : E} {r : ℝ} {w : E → ℝ} (h : IsConormalSolOn ν a G f x₀ r w)
    (hx₀ : ⟪x₀, ν⟫ = 0) (hr : 0 < r) (M : E ≃L[ℝ] E) :
    IsWeakSolWithin
      (fun z ↦ (M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjoint (M.symm : E →L[ℝ] E))
      (fun z ↦ M.symm (G (x₀ + M z))) (fun z ↦ f (x₀ + M z))
      ((fun z ↦ x₀ + M z) ⁻¹' halfBall ν x₀ r) ((fun z ↦ x₀ + M z) ⁻¹' ball x₀ r)
      (fun z ↦ w (x₀ + M z)) :=
  IsWeakSolWithin.comp_affine h (uniqueDiffOn_halfBall hν hr (by rw [hx₀]; linarith))
    (measurableSet_halfBall ν x₀ r) M x₀

/-- **Transport of a conormal solution**. Let `M` preserve the half
space, `⟪M z, ν⟫ = m ⟪z, ν⟫` with `m > 0`, and let `x₀ ∈ flatPart ν`. If `w` is a conormal solution
on `halfBall ν x₀ r`, then `w̃ = w(x₀ + M ·)` is a conormal solution on the inscribed half ball
`halfBall ν 0 ρ` whenever `‖M‖ ρ ≤ r`, with `ã = M⁻¹ (a ∘ T) M⁻†`, `G̃ = M⁻¹ (G ∘ T)`,
`f̃ = f ∘ T`. The tests on the new half ball need not vanish on the flat part. -/
theorem IsConormalSolOn.comp_affine {ν : E} (hν : ‖ν‖ = 1) {a : E → E →L[ℝ] E} {G : E → E}
    {f : E → ℝ} {x₀ : E} {r : ℝ} {w : E → ℝ} (h : IsConormalSolOn ν a G f x₀ r w)
    (hx₀ : ⟪x₀, ν⟫ = 0) (hr : 0 < r) {M : E ≃L[ℝ] E} {m : ℝ} (hm : 0 < m)
    (hMν : ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ‖(M : E →L[ℝ] E)‖ * ρ ≤ r) :
    IsConormalSolOn ν
      (fun z ↦ (M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjoint (M.symm : E →L[ℝ] E))
      (fun z ↦ M.symm (G (x₀ + M z))) (fun z ↦ f (x₀ + M z)) 0 ρ (fun z ↦ w (x₀ + M z)) :=
  (h.comp_affine_preimage hν hx₀ hr M).restrict (ball_subset_preimage_affine_ball hr hρr)
    (halfBall_subset_preimage_affine_halfBall hm hx₀ hMν hρr)
    (preimage_affine_halfBall_inter_ball_subset hm hx₀ hMν r ρ)
    (measurableSet_preimage_affine (measurableSet_halfBall ν x₀ r) M x₀)
    (measurableSet_halfBall ν 0 ρ) (uniqueDiffOn_halfBall hν hρ (by simp; linarith))

end Div

/-! ### The nondivergence operator -/

private theorem update_vec_zero {X : Type*} (x y z : X) :
    Function.update ![x, y] 0 z = ![z, y] := by
  ext i; fin_cases i <;> rfl

private theorem update_vec_one {X : Type*} (x y z : X) :
    Function.update ![x, y] 1 z = ![x, z] := by
  ext i; fin_cases i <;> rfl

/-- A continuous bilinear-in-`Fin 2` map as a bilinear map. -/
private noncomputable def bilinOfFinTwo (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y ↦ H ![x, y])
    (fun x x' y ↦ by
      have := H.map_update_add ![x, y] 0 x x'
      rwa [update_vec_zero, update_vec_zero, update_vec_zero] at this)
    (fun c x y ↦ by
      have := H.map_update_smul ![x, y] 0 c x; rwa [update_vec_zero, update_vec_zero] at this)
    (fun x y y' ↦ by
      have := H.map_update_add ![x, y] 1 y y'
      rwa [update_vec_one, update_vec_one, update_vec_one] at this)
    (fun c x y ↦ by
      have := H.map_update_smul ![x, y] 1 c y; rwa [update_vec_one, update_vec_one] at this)

omit [FiniteDimensional ℝ E] in
private theorem bilinOfFinTwo_apply (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ)
    (x y : E) : bilinOfFinTwo H x y = H ![x, y] := rfl

/-- Trace manipulation: `∑ᵢ β(X eᵢ, Y eᵢ) = ∑ᵢ β(X Y† eᵢ, eᵢ)` for an orthonormal basis `e`. -/
private theorem sum_bilin_eq {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    (β : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X Y : E →L[ℝ] E) :
    ∑ i, β (X (e i)) (Y (e i)) = ∑ i, β (X (adjoint Y (e i))) (e i) := by
  calc ∑ i, β (X (e i)) (Y (e i)) = ∑ i, ∑ j, ⟪e j, Y (e i)⟫ * β (X (e i)) (e j) :=
        Finset.sum_congr rfl fun i _ ↦ by
          conv_lhs => rw [← e.sum_repr' (Y (e i))]
          simp [map_sum, map_smul]
    _ = ∑ j, ∑ i, ⟪e j, Y (e i)⟫ * β (X (e i)) (e j) := Finset.sum_comm
    _ = ∑ j, β (X (adjoint Y (e j))) (e j) :=
        Finset.sum_congr rfl fun j _ ↦ by
          conv_rhs => rw [← e.sum_repr' (adjoint Y (e j))]
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [adjoint_inner_right, real_inner_comm]

/-- **Transport of the nondivergence operator** under `T z = x₀ + M z`: with
`ã = M⁻¹ (a ∘ T) M⁻†` and `b̃ = M⁻¹ (b ∘ T)`,
`tr (ã D²w̃) + ⟪b̃, ∇w̃⟫ = (tr (a D²w) + ⟪b, ∇w⟫) ∘ T` on `T⁻¹ s`. -/
theorem Nondiv.op_comp_affine {a : E → E →L[ℝ] E} {b : E → E} {s : Set E} {w : E → ℝ}
    (hw : DifferentiableOn ℝ w s) (hs : UniqueDiffOn ℝ s) (M : E ≃L[ℝ] E) (x₀ : E) {z : E}
    (hz : x₀ + M z ∈ s) :
    Nondiv.op (fun z ↦ (M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjoint (M.symm : E →L[ℝ] E))
        (fun z ↦ M.symm (b (x₀ + M z))) ((fun z ↦ x₀ + M z) ⁻¹' s) (fun z ↦ w (x₀ + M z)) z =
      Nondiv.op a b s w (x₀ + M z) := by
  -- the Hessian
  set s₁ : Set E := (fun y ↦ x₀ + y) ⁻¹' s with hs₁
  have hs₁u : UniqueDiffOn ℝ s₁ := by
    have := uniqueDiffOn_preimage_affine hs (ContinuousLinearEquiv.refl ℝ E) x₀
    simpa using this
  have hvadd : x₀ +ᵥ s₁ = s := by
    ext y; constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hy; exact ⟨y - x₀, by simpa [hs₁] using hy, by simp [vadd_eq_add]⟩
  have hpre : (fun z ↦ x₀ + M z) ⁻¹' s = M ⁻¹' s₁ := rfl
  have hD2 : iteratedFDerivWithin ℝ 2 (fun z ↦ w (x₀ + M z)) ((fun z ↦ x₀ + M z) ⁻¹' s) z =
      (iteratedFDerivWithin ℝ 2 w s (x₀ + M z)).compContinuousLinearMap
        fun _ ↦ (M : E →L[ℝ] E) := by
    rw [hpre]
    have := M.iteratedFDerivWithin_comp_right (fun y ↦ w (x₀ + y)) hs₁u (x := z) hz 2
    rw [show ((fun y ↦ w (x₀ + y)) ∘ M) = fun z ↦ w (x₀ + M z) from rfl] at this
    rw [this, iteratedFDerivWithin_comp_add_left, hvadd]
  -- the gradient
  have hgrad := gradientWithin_comp_affine (s := s) M x₀ (hw _ hz)
    (uniqueDiffOn_preimage_affine hs M x₀ z hz)
  simp only [Nondiv.op]
  rw [hD2, hgrad, inner_transport']
  congr 1
  set H := iteratedFDerivWithin ℝ 2 w s (x₀ + M z)
  have hl : ∀ i, (H.compContinuousLinearMap fun _ ↦ (M : E →L[ℝ] E))
      ![((M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjoint (M.symm : E →L[ℝ] E))
        (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i] =
      bilinOfFinTwo H ((a (x₀ + M z) ∘L adjoint (M.symm : E →L[ℝ] E))
        (stdOrthonormalBasis ℝ E i)) ((M : E →L[ℝ] E) (stdOrthonormalBasis ℝ E i)) := by
    intro i
    rw [bilinOfFinTwo_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    ext j; fin_cases j <;> simp
  simp_rw [hl]
  rw [sum_bilin_eq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [bilinOfFinTwo_apply, coe_comp, Function.comp_apply, ← comp_apply (adjoint _),
    adjoint_symm_comp_adjoint, one_apply_eq_self]

end BasicElliptic
