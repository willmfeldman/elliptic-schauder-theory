/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Div
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Gradient fields of test functions in `L²`

Let `E` be a finite-dimensional real inner product space with its volume measure and `U ⊆ E`.
We work in the real Hilbert space `L2Field U = L²(U; E)` of square-integrable vector fields on
`U` (the measure is `volume.restrict U`).

* `BasicElliptic.Div.IsSmoothTestFn U φ`: `φ ∈ C_c^∞(U)`.
* `BasicElliptic.Div.testGradients U`: the subspace `{∇φ : φ ∈ C_c^∞(U)}` of `L2Field U`.
* `BasicElliptic.Div.gradClosure U`: its closure `X`, a complete subspace; its orthogonal
  projection is Mathlib's `Submodule.starProjection` (the name at this Mathlib pin; the old
  `orthogonalProjection` is now `orthogonalProjectionOnto`, with values in the subspace).
* `BasicElliptic.Div.curlTests U`: the fields `(∂_w ψ) u - (∂_u ψ) w`, `ψ ∈ C_c^∞(U)`.
* `BasicElliptic.Div.curlFree U`: the orthogonal complement of the curl tests, i.e. the weakly
  curl-free fields: `∫_U ⟪F, u⟫ ∂_w ψ = ∫_U ⟪F, w⟫ ∂_u ψ` for all `ψ ∈ C_c^∞(U)`, `u, w ∈ E`
  (`mem_curlFree_iff`). It is closed, being an orthogonal complement.
* `BasicElliptic.Div.IsWeakCurlFree F U`, `BasicElliptic.Div.IsWeakDivFree F U`: the
  function-level conditions.

## Main results

* `BasicElliptic.Div.gradClosure_le_curlFree`: every element of `X` is weakly curl-free.
  For `∇φ` this is `∫ ∂_u φ ∂_w ψ = -∫ φ ∂_u ∂_w ψ = -∫ φ ∂_w ∂_u ψ = ∫ ∂_w φ ∂_u ψ` (integration
  by parts twice and symmetry of second derivatives of `ψ`). Weak curl-freeness passes to
  `L²`-limits because it says `F ⊥ t` for each fixed curl test `t ∈ L²`, a closed condition; hence
  it holds on the closure `X`.
* `BasicElliptic.Div.isWeakCurlFree_gradient_of_contDiffOn`: `∇w` is weakly curl-free on an open
  `U` for `w ∈ C¹(U)` (integration by parts against `∂_v ψ`, `∂_u ψ`).
* `BasicElliptic.Div.isWeakCurlFree_of_mem_curlFree`, `isWeakDivFree_of_mem_orthogonal`,
  `IsWeakCurlFree.toLp_mem`: translations between `L²` membership and function-level conditions.
* `BasicElliptic.Div.norm_starProjection_le_of_forall_inner_le`: if `|⟪F, t⟫| ≤ C ‖t‖` on a
  subspace `T`, then `‖P F‖ ≤ C` for the projection `P` onto the closure of `T` (the energy
  comparison: `‖P F‖² = ⟪F, P F⟫` since `F - P F ⊥ P F`).
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace
open scoped Gradient ContDiff Topology

@[expose] public noncomputable section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `φ ∈ C_c^∞(U)`: `φ` is smooth, compactly supported, with `tsupport φ ⊆ U`. -/
def IsSmoothTestFn (U : Set E) (φ : E → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-! ### Test functions -/

namespace IsSmoothTestFn

variable {U : Set E} {φ ψ : E → ℝ}

theorem zero : IsSmoothTestFn U (0 : E → ℝ) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

theorem add (hφ : IsSmoothTestFn U φ) (hψ : IsSmoothTestFn U ψ) : IsSmoothTestFn U (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
    (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩

theorem const_smul (hφ : IsSmoothTestFn U φ) (c : ℝ) : IsSmoothTestFn U (c • φ) :=
  ⟨hφ.1.const_smul c, hφ.2.1.smul_left, (tsupport_smul_subset_right (fun _ : E ↦ c) φ).trans hφ.2.2⟩

theorem differentiable (h : IsSmoothTestFn U φ) : Differentiable ℝ φ :=
  h.1.differentiable (by simp)

theorem contDiff_fderiv (h : IsSmoothTestFn U φ) : ContDiff ℝ ∞ (fderiv ℝ φ) :=
  h.1.fderiv_right (m := ∞) le_rfl

theorem continuous_fderiv (h : IsSmoothTestFn U φ) : Continuous (fderiv ℝ φ) :=
  h.contDiff_fderiv.continuous

/-- A directional derivative `∂_v φ` of a test function is a test function. -/
theorem fderiv_apply (h : IsSmoothTestFn U φ) (v : E) :
    IsSmoothTestFn U (fun y ↦ fderiv ℝ φ y v) := by
  refine ⟨h.contDiff_fderiv.clm_apply contDiff_const, ?_, ?_⟩
  · exact h.2.1.fderiv_apply ℝ v
  · exact (tsupport_fderiv_apply_subset ℝ v).trans h.2.2

variable [CompleteSpace E]

theorem continuous_gradient (h : IsSmoothTestFn U φ) : Continuous (∇ φ) :=
  (toDual ℝ E).symm.continuous.comp h.continuous_fderiv

theorem hasCompactSupport_gradient (h : IsSmoothTestFn U φ) : HasCompactSupport (∇ φ) := by
  change HasCompactSupport ((fun L ↦ (toDual ℝ E).symm L) ∘ fderiv ℝ φ)
  exact (h.2.1.fderiv ℝ).comp_left (map_zero _)

theorem tsupport_gradient_subset (h : IsSmoothTestFn U φ) : tsupport (∇ φ) ⊆ U := by
  change tsupport ((fun L ↦ (toDual ℝ E).symm L) ∘ fderiv ℝ φ) ⊆ U
  exact (tsupport_comp_subset (map_zero _) _).trans ((tsupport_fderiv_subset ℝ).trans h.2.2)

end IsSmoothTestFn

section Gradient

variable [CompleteSpace E]

theorem inner_gradient_left (φ : E → ℝ) (y v : E) : ⟪∇ φ y, v⟫ = fderiv ℝ φ y v := by
  simp [gradient, toDual_symm_apply]

theorem inner_gradient_right (φ : E → ℝ) (y v : E) : ⟪v, ∇ φ y⟫ = fderiv ℝ φ y v := by
  rw [real_inner_comm, inner_gradient_left]

theorem gradient_add_of_differentiable {φ ψ : E → ℝ} (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ) : ∇ (φ + ψ) = ∇ φ + ∇ ψ := by
  ext y
  simp only [gradient, Pi.add_apply]
  rw [fderiv_add (hφ y) (hψ y), map_add]

theorem gradient_const_smul_of_differentiable {φ : E → ℝ} (hφ : Differentiable ℝ φ) (c : ℝ) :
    ∇ (c • φ) = c • ∇ φ := by
  ext y
  simp only [gradient, Pi.smul_apply]
  rw [fderiv_const_smul (hφ y), map_smul]

end Gradient

/-- Symmetry of second directional derivatives of a smooth function:
`∂_u (∂_w ψ) = ∂_w (∂_u ψ)`. -/
theorem fderiv_fderiv_apply_comm {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (y u w : E) :
    fderiv ℝ (fun z ↦ fderiv ℝ ψ z w) y u = fderiv ℝ (fun z ↦ fderiv ℝ ψ z u) y w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hψ.fderiv_right (m := 1) (by simp)).differentiable (by simp) y
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using (hψ.contDiffAt (x := y)).isSymmSndFDerivAt (by simp) u w

/-! ### `L²` coercions -/

section L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A continuous compactly supported field is in `L²(μ)` for a locally finite `μ`. -/
theorem memLp_two_of_continuous_of_hasCompactSupport {F' : Type*} [NormedAddCommGroup F']
    [TopologicalSpace α] [OpensMeasurableSpace α] [IsFiniteMeasureOnCompacts μ] {g : α → F'}
    (hg : Continuous g)
    (hgc : HasCompactSupport g) : MemLp g 2 μ :=
  hg.memLp_of_hasCompactSupport hgc

/-- `⟪toLp f, toLp g⟫ = ∫ ⟪f, g⟫`. -/
theorem inner_toLp_toLp {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    {f g : α → F'} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ y, ⟪f y, g y⟫ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

/-- `⟪v, toLp g⟫ = ∫ ⟪v, g⟫`. -/
theorem inner_toLp_right {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    (v : Lp F' 2 μ) {g : α → F'} (hg : MemLp g 2 μ) :
    ⟪v, hg.toLp g⟫ = ∫ y, ⟪v y, g y⟫ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with y h2
  rw [h2]

/-- `‖v‖² = ∫ ‖v‖²` in `L²`. -/
theorem norm_sq_eq_integral {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    (v : Lp F' 2 μ) : ‖v‖ ^ 2 = ∫ y, ‖v y‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- `‖v‖ = √(∫ ‖v‖²)` in `L²`. -/
theorem norm_eq_sqrt_integral {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    (v : Lp F' 2 μ) : ‖v‖ = √(∫ y, ‖v y‖ ^ 2 ∂μ) := by
  rw [← norm_sq_eq_integral, Real.sqrt_sq (norm_nonneg _)]

/-- `‖toLp f‖ = √(∫ ‖f‖²)`. -/
theorem norm_toLp_eq_sqrt_integral {F' : Type*} [NormedAddCommGroup F']
    [InnerProductSpace ℝ F'] {f : α → F'} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = √(∫ y, ‖f y‖ ^ 2 ∂μ) := by
  rw [norm_eq_sqrt_integral]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with y h
  rw [h]

end L2

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Hilbert space `L²(U; E)` of square-integrable vector fields on `U`. -/
abbrev L2Field (U : Set E) := Lp E 2 (volume.restrict U)

/-- `F` is weakly curl-free on `U`: `∫_U ⟪F, u⟫ ∂_w ψ = ∫_U ⟪F, w⟫ ∂_u ψ` for all
`ψ ∈ C_c^∞(U)` and `u, w ∈ E` (for smooth `F` this is `∂_w F_u = ∂_u F_w`). -/
def IsWeakCurlFree (F : E → E) (U : Set E) : Prop :=
  ∀ ψ : E → ℝ, IsSmoothTestFn U ψ → ∀ u w : E,
    ∫ y in U, ⟪F y, u⟫ * fderiv ℝ ψ y w = ∫ y in U, ⟪F y, w⟫ * fderiv ℝ ψ y u

/-- `F` is weakly divergence-free on `U`: `∫_U ⟪F, ∇φ⟫ = 0` for all `φ ∈ C_c^∞(U)`. -/
def IsWeakDivFree (F : E → E) (U : Set E) : Prop :=
  ∀ φ : E → ℝ, IsSmoothTestFn U φ → ∫ y in U, ⟪F y, ∇ φ y⟫ = 0

/-! ### The subspaces -/

section Subspaces

variable (U : Set E)

/-- The gradients of test functions, `{∇φ : φ ∈ C_c^∞(U)}`, as a subspace of `L²(U; E)`. An
element is an `L²` class that agrees a.e. on `U` with some `∇φ`. -/
def testGradients : Submodule ℝ (L2Field U) where
  carrier := {v | ∃ φ, IsSmoothTestFn U φ ∧ (v : E → E) =ᵐ[volume.restrict U] ∇ φ}
  zero_mem' := ⟨0, IsSmoothTestFn.zero, by
    filter_upwards [Lp.coeFn_zero E 2 (volume.restrict U)] with y hy
    rw [hy]
    simp [gradient]⟩
  add_mem' := by
    rintro v w ⟨φ, hφ, hv⟩ ⟨ψ, hψ, hw⟩
    refine ⟨φ + ψ, hφ.add hψ, ?_⟩
    filter_upwards [Lp.coeFn_add v w, hv, hw] with y h1 h2 h3
    rw [h1, gradient_add_of_differentiable hφ.differentiable hψ.differentiable]
    simp [h2, h3]
  smul_mem' := by
    rintro c v ⟨φ, hφ, hv⟩
    refine ⟨c • φ, hφ.const_smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c v, hv] with y h1 h2
    rw [h1, gradient_const_smul_of_differentiable hφ.differentiable]
    simp [h2]

/-- The closure `X` of the test gradients in `L²(U; E)`. -/
def gradClosure : Submodule ℝ (L2Field U) := (testGradients U).topologicalClosure

/-- The curl test fields `(∂_w ψ) u - (∂_u ψ) w` with `ψ ∈ C_c^∞(U)` and `u, w ∈ E`. -/
def curlTests : Set (L2Field U) :=
  {t | ∃ ψ, IsSmoothTestFn U ψ ∧ ∃ u w : E,
    (t : E → E) =ᵐ[volume.restrict U] fun y ↦ fderiv ℝ ψ y w • u - fderiv ℝ ψ y u • w}

/-- The weakly curl-free fields: the orthogonal complement of the curl tests. -/
def curlFree : Submodule ℝ (L2Field U) := (Submodule.span ℝ (curlTests U))ᗮ

instance : (gradClosure U).HasOrthogonalProjection := by
  unfold gradClosure; infer_instance

theorem isClosed_curlFree : IsClosed (curlFree U : Set (L2Field U)) :=
  Submodule.isClosed_orthogonal _

theorem testGradients_le_gradClosure : testGradients U ≤ gradClosure U :=
  Submodule.le_topologicalClosure _

end Subspaces

variable {U : Set E}

theorem mem_curlFree_iff_inner (v : L2Field U) :
    v ∈ curlFree U ↔ ∀ t ∈ curlTests U, ⟪t, v⟫ = 0 := by
  refine ⟨fun h t ht ↦ Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span ht) h,
    fun h ↦ (Submodule.mem_orthogonal _ _).2 fun t ht ↦ ?_⟩
  induction ht using Submodule.span_induction with
  | mem t ht => exact h t ht
  | zero => simp
  | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [real_inner_smul_left, ha, mul_zero]

/-- The curl test field of `ψ, u, w` is in `L²`. -/
theorem IsSmoothTestFn.memLp_curl {ψ : E → ℝ} (hψ : IsSmoothTestFn U ψ) (u w : E) :
    MemLp (fun y ↦ fderiv ℝ ψ y w • u - fderiv ℝ ψ y u • w) 2 (volume.restrict U) := by
  refine memLp_two_of_continuous_of_hasCompactSupport ?_ ?_
  · exact ((hψ.fderiv_apply w).1.continuous.smul continuous_const).sub
      ((hψ.fderiv_apply u).1.continuous.smul continuous_const)
  · exact ((hψ.fderiv_apply w).2.1.smul_right).sub (hψ.fderiv_apply u).2.1.smul_right

/-- The gradient of a test function is in `L²`. -/
theorem IsSmoothTestFn.memLp_gradient {φ : E → ℝ} (hφ : IsSmoothTestFn U φ) :
    MemLp (∇ φ) 2 (volume.restrict U) :=
  memLp_two_of_continuous_of_hasCompactSupport hφ.continuous_gradient
    hφ.hasCompactSupport_gradient

theorem IsSmoothTestFn.toLp_gradient_mem {φ : E → ℝ} (hφ : IsSmoothTestFn U φ) :
    hφ.memLp_gradient.toLp (∇ φ) ∈ testGradients U :=
  ⟨φ, hφ, hφ.memLp_gradient.coeFn_toLp⟩

/-- An integral over `U` of a function vanishing off `U` is the integral over `E`. -/
private theorem setIntegral_eq_integral_of_tsupport {g : E → ℝ} {s : Set E} (hs : s ⊆ U)
    (hg : ∀ y ∉ s, g y = 0) : ∫ y in U, g y = ∫ y, g y :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ hg y fun h ↦ hy (hs h)

private theorem integrable_of_continuous_of_hasCompactSupport {g : E → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable g :=
  hg.integrable_of_hasCompactSupport hgc

/-- `∫ (∂_v φ) g = -∫ φ ∂_v g` for test functions `φ, g` (both smooth with compact support). -/
private theorem integral_fderiv_mul_eq_neg {φ g : E → ℝ} (hφ : IsSmoothTestFn U φ)
    (hg : IsSmoothTestFn U g) (v : E) :
    ∫ y, g y * fderiv ℝ φ y v = -∫ y, fderiv ℝ g y v * φ y := by
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun y _ ↦ hg.differentiable y) (fun y _ ↦ hφ.differentiable y)
  · exact integrable_of_continuous_of_hasCompactSupport
      ((hg.fderiv_apply v).1.continuous.mul hφ.1.continuous) (hφ.2.1.mul_left)
  · exact integrable_of_continuous_of_hasCompactSupport
      (hg.1.continuous.mul (hφ.fderiv_apply v).1.continuous) ((hφ.fderiv_apply v).2.1.mul_left)
  · exact integrable_of_continuous_of_hasCompactSupport
      (hg.1.continuous.mul hφ.1.continuous) hφ.2.1.mul_left

/-- For test functions `φ, ψ`: `∫ ∂_u φ ∂_w ψ = ∫ ∂_w φ ∂_u ψ`. -/
theorem integral_fderiv_mul_fderiv_comm {φ ψ : E → ℝ} (hφ : IsSmoothTestFn U φ)
    (hψ : IsSmoothTestFn U ψ) (u w : E) :
    ∫ y, fderiv ℝ ψ y w * fderiv ℝ φ y u = ∫ y, fderiv ℝ ψ y u * fderiv ℝ φ y w := by
  rw [integral_fderiv_mul_eq_neg hφ (hψ.fderiv_apply w) u,
    integral_fderiv_mul_eq_neg hφ (hψ.fderiv_apply u) w]
  simp_rw [fderiv_fderiv_apply_comm hψ.1 _ u w]

/-- **Test gradients are weakly curl-free.** -/
theorem testGradients_le_curlFree : testGradients U ≤ curlFree U := by
  rintro v ⟨φ, hφ, hv⟩
  rw [mem_curlFree_iff_inner]
  rintro t ⟨ψ, hψ, u, w, ht⟩
  rw [L2.inner_def]
  have hae : ∀ᵐ y ∂(volume.restrict U), ⟪(t : E → E) y, (v : E → E) y⟫ =
      fderiv ℝ ψ y w * fderiv ℝ φ y u - fderiv ℝ ψ y u * fderiv ℝ φ y w := by
    filter_upwards [ht, hv] with y h1 h2
    rw [h1, h2, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      inner_gradient_right, inner_gradient_right]
  rw [integral_congr_ae hae]
  have hsupp : ∀ y ∉ tsupport φ,
      fderiv ℝ ψ y w * fderiv ℝ φ y u - fderiv ℝ ψ y u * fderiv ℝ φ y w = 0 := by
    intro y hy
    have : fderiv ℝ φ y = 0 := by
      by_contra h
      exact hy (tsupport_fderiv_subset ℝ (subset_tsupport _ h))
    simp [this]
  rw [setIntegral_eq_integral_of_tsupport hφ.2.2 hsupp, integral_sub, sub_eq_zero]
  · exact integral_fderiv_mul_fderiv_comm hφ hψ u w
  · exact integrable_of_continuous_of_hasCompactSupport
      ((hψ.fderiv_apply w).1.continuous.mul (hφ.fderiv_apply u).1.continuous)
      (hφ.fderiv_apply u).2.1.mul_left
  · exact integrable_of_continuous_of_hasCompactSupport
      ((hψ.fderiv_apply u).1.continuous.mul (hφ.fderiv_apply w).1.continuous)
      (hφ.fderiv_apply w).2.1.mul_left

/-- **Weak curl-freeness passes to `L²` limits:** every element of `X` is weakly curl-free.
(Curl-freeness of `v` says `⟪t, v⟫ = 0` for each fixed curl test `t ∈ L²`, a closed condition in
`v`; it holds on `{∇φ}` by `testGradients_le_curlFree`, hence on the closure.) -/
theorem gradClosure_le_curlFree : gradClosure U ≤ curlFree U :=
  Submodule.topologicalClosure_minimal _ testGradients_le_curlFree (isClosed_curlFree U)

/-- `ψ • u ∈ L²` for a test function `ψ` and a constant vector `u`. -/
theorem IsSmoothTestFn.memLp_smul_const {ψ : E → ℝ} (hψ : IsSmoothTestFn U ψ) (u : E) :
    MemLp (fun y ↦ ψ y • u) 2 (volume.restrict U) :=
  memLp_two_of_continuous_of_hasCompactSupport (hψ.1.continuous.smul continuous_const)
    hψ.2.1.smul_right

/-- Function-level weak curl-freeness of an `L²` field gives membership in `curlFree`. -/
theorem IsWeakCurlFree.toLp_mem {F : E → E} (hF : MemLp F 2 (volume.restrict U))
    (hcurl : IsWeakCurlFree F U) : hF.toLp F ∈ curlFree U := by
  rw [mem_curlFree_iff_inner]
  rintro t ⟨ψ, hψ, u, w, ht⟩
  rw [real_inner_comm, L2.inner_def]
  have hae : ∀ᵐ y ∂(volume.restrict U), ⟪(hF.toLp F : E → E) y, (t : E → E) y⟫ =
      ⟪F y, u⟫ * fderiv ℝ ψ y w - ⟪F y, w⟫ * fderiv ℝ ψ y u := by
    filter_upwards [ht, hF.coeFn_toLp] with y h1 h2
    rw [h1, h2, inner_sub_right, real_inner_smul_right, real_inner_smul_right, mul_comm,
      mul_comm (fderiv ℝ ψ y u)]
  rw [integral_congr_ae hae, integral_sub, hcurl ψ hψ u w, sub_self]
  · exact (L2.integrable_inner (hF.toLp F) (((hψ.fderiv_apply w).memLp_smul_const u).toLp _)).congr
      (by filter_upwards [hF.coeFn_toLp, ((hψ.fderiv_apply w).memLp_smul_const u).coeFn_toLp]
            with y h1 h2
          rw [h1, h2, real_inner_smul_right, mul_comm])
  · exact (L2.integrable_inner (hF.toLp F) (((hψ.fderiv_apply u).memLp_smul_const w).toLp _)).congr
      (by filter_upwards [hF.coeFn_toLp, ((hψ.fderiv_apply u).memLp_smul_const w).coeFn_toLp]
            with y h1 h2
          rw [h1, h2, real_inner_smul_right, mul_comm])

/-! ### Constants annihilate `X` -/

/-- `∫ ∂_c φ = 0` for a test function `φ` (integration by parts against the constant `1`). -/
theorem integral_fderiv_apply_eq_zero {φ : E → ℝ} (hφ : IsSmoothTestFn U φ) (c : E) :
    ∫ y, fderiv ℝ φ y c = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : E ↦ (1 : ℝ)) (g := φ) (v := c) (by simp) ?_ ?_
    (fun y _ ↦ differentiableAt_const _) (fun y _ ↦ hφ.differentiable y)
  · simpa using h
  · simpa using integrable_of_continuous_of_hasCompactSupport (hφ.fderiv_apply c).1.continuous
      (hφ.fderiv_apply c).2.1
  · simpa using integrable_of_continuous_of_hasCompactSupport hφ.1.continuous hφ.2.1

/-! ### Function-level consequences of membership -/

/-- `⟪v, u⟫ g ∈ L¹(U)` for `v ∈ L²(U; E)`, `u ∈ E` and a test function `g`. -/
theorem integrable_inner_mul (v : L2Field U) (u : E) {g : E → ℝ} (hg : IsSmoothTestFn U g) :
    Integrable (fun y ↦ ⟪(v : E → E) y, u⟫ * g y) (volume.restrict U) :=
  (L2.integrable_inner v ((hg.memLp_smul_const u).toLp _)).congr
    (by filter_upwards [(hg.memLp_smul_const u).coeFn_toLp] with y h
        rw [h, real_inner_smul_right, mul_comm])

/-- Elements of `curlFree U` are weakly curl-free (function-level form). -/
theorem isWeakCurlFree_of_mem_curlFree {v : L2Field U} (hv : v ∈ curlFree U) :
    IsWeakCurlFree (v : E → E) U := by
  intro ψ hψ u w
  have h := (mem_curlFree_iff_inner v).1 hv _ ⟨ψ, hψ, u, w, (hψ.memLp_curl u w).coeFn_toLp⟩
  rw [real_inner_comm, inner_toLp_right] at h
  have hae : ∀ᵐ y ∂(volume.restrict U),
      ⟪(v : E → E) y, fderiv ℝ ψ y w • u - fderiv ℝ ψ y u • w⟫ =
        ⟪(v : E → E) y, u⟫ * fderiv ℝ ψ y w - ⟪(v : E → E) y, w⟫ * fderiv ℝ ψ y u :=
    Eventually.of_forall fun y ↦ by
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, mul_comm,
        mul_comm (fderiv ℝ ψ y u)]
  rw [integral_congr_ae hae, integral_sub (integrable_inner_mul v u (hψ.fderiv_apply w))
    (integrable_inner_mul v w (hψ.fderiv_apply u)), sub_eq_zero] at h
  exact h

/-- Elements of `Xᗮ` are weakly divergence-free (function-level form). -/
theorem isWeakDivFree_of_mem_orthogonal {v : L2Field U} (hv : v ∈ (gradClosure U)ᗮ) :
    IsWeakDivFree (v : E → E) U := by
  intro φ hφ
  have h := Submodule.inner_right_of_mem_orthogonal
    (testGradients_le_gradClosure U hφ.toLp_gradient_mem) hv
  rwa [real_inner_comm, inner_toLp_right] at h

/-- `∫_U ⟪c, ∇φ⟫ = 0` for a constant `c` and a test function `φ`. -/
theorem setIntegral_inner_gradient_eq_zero {φ : E → ℝ} (hφ : IsSmoothTestFn U φ) (c : E) :
    ∫ y in U, ⟪c, ∇ φ y⟫ = 0 := by
  simp_rw [inner_gradient_right]
  rw [setIntegral_eq_integral_of_tsupport hφ.2.2
    (fun y hy ↦ by rw [fderiv_of_notMem_tsupport ℝ hy, zero_apply]),
    integral_fderiv_apply_eq_zero hφ c]

/-! ### Gradients of `C¹` functions are weakly curl-free -/

private theorem integrable_of_continuousOn_of_support_subset {g : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hg : ContinuousOn g K) (hsupp : Function.support g ⊆ K) : Integrable g :=
  (integrableOn_iff_integrable_of_support_subset hsupp).1 (hg.integrableOn_compact hK)

/-- `∫ ∂_u w · χ = -∫ w ∂_u χ` for `w ∈ C¹(U)` and a test function `χ` supported in `tsupport ψ`,
`ψ ∈ C_c^∞(U)`. -/
private theorem integral_mul_fderiv_eq_neg_of_contDiffOn (hU : IsOpen U) {w : E → ℝ}
    (hw : ContDiffOn ℝ 1 w U) {ψ χ : E → ℝ} (hψ : IsSmoothTestFn U ψ) (hχ : IsSmoothTestFn U χ)
    (hχψ : tsupport χ ⊆ tsupport ψ) (u : E) :
    ∫ y, χ y * fderiv ℝ w y u = -∫ y, fderiv ℝ χ y u * w y := by
  set K := tsupport ψ
  have hK : IsCompact K := hψ.2.1
  have hKU : K ⊆ U := hψ.2.2
  have hwc : ContinuousOn w K := hw.continuousOn.mono hKU
  have hdwc : ContinuousOn (fun y ↦ fderiv ℝ w y u) K :=
    ((hw.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono hKU
  have hχK : ∀ y, y ∉ K → χ y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hy (hχψ h)
  have hdχK : ∀ y, y ∉ K → fderiv ℝ χ y = 0 := fun y hy ↦
    fderiv_of_notMem_tsupport ℝ fun h ↦ hy (hχψ h)
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun y _ ↦ hχ.differentiable y) (fun y hy ↦ ?_)
  · refine integrable_of_continuousOn_of_support_subset hK
      (((hχ.fderiv_apply u).1.continuous.continuousOn).mul hwc) fun y hy ↦ ?_
    by_contra h
    exact hy (by simp [hdχK y h])
  · refine integrable_of_continuousOn_of_support_subset hK
      (hχ.1.continuous.continuousOn.mul hdwc) fun y hy ↦ ?_
    by_contra h
    exact hy (by simp [hχK y h])
  · refine integrable_of_continuousOn_of_support_subset hK
      (hχ.1.continuous.continuousOn.mul hwc) fun y hy ↦ ?_
    by_contra h
    exact hy (by simp [hχK y h])
  · have hyU : y ∈ U := hKU (hχψ hy)
    exact (hw.differentiableOn one_ne_zero y hyU).differentiableAt (hU.mem_nhds hyU)

/-- **Gradients of `C¹` functions are weakly curl-free:** for `U` open and `w ∈ C¹(U)`,
`∫_U ∂_u w ∂_v ψ = -∫ w ∂_u ∂_v ψ = -∫ w ∂_v ∂_u ψ = ∫_U ∂_v w ∂_u ψ` (integration by parts
against the test functions `∂_v ψ`, `∂_u ψ`, and symmetry of `D²ψ`). -/
theorem isWeakCurlFree_gradient_of_contDiffOn (hU : IsOpen U) {w : E → ℝ}
    (hw : ContDiffOn ℝ 1 w U) : IsWeakCurlFree (∇ w) U := by
  intro ψ hψ u v
  simp_rw [inner_gradient_left]
  have hoff : ∀ a b : E, ∀ y ∉ U, fderiv ℝ w y a * fderiv ℝ ψ y b = 0 := fun a b y hy ↦ by
    rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψ.2.2 h)), zero_apply, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hoff u v),
    setIntegral_eq_integral_of_forall_compl_eq_zero (hoff v u)]
  simp_rw [mul_comm (fderiv ℝ w _ _)]
  rw [integral_mul_fderiv_eq_neg_of_contDiffOn hU hw hψ (hψ.fderiv_apply v)
      (tsupport_fderiv_apply_subset ℝ v) u,
    integral_mul_fderiv_eq_neg_of_contDiffOn hU hw hψ (hψ.fderiv_apply u)
      (tsupport_fderiv_apply_subset ℝ u) v]
  simp_rw [fderiv_fderiv_apply_comm hψ.1 _ u v]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A smooth test function is a `C¹_c` test function in the sense of the frozen
`BasicElliptic.IsTestFn`. -/
theorem IsSmoothTestFn.isTestFn {φ : E → ℝ} (hφ : IsSmoothTestFn U φ) :
    BasicElliptic.IsTestFn U φ :=
  ⟨hφ.1.of_le (by simp), hφ.2.1, hφ.2.2⟩

/-! ### Abstract projection bounds -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Energy comparison, abstract form.** If `|⟪F, t⟫| ≤ C ‖t‖` for all `t` in a subspace `T`,
then the orthogonal projection `P` onto the closure of `T` satisfies `‖P F‖ ≤ C`. Indeed the
bound passes to the closure by continuity, and `‖P F‖² = ⟪F, P F⟫` because `F - P F ⊥ P F`. -/
theorem norm_starProjection_le_of_forall_inner_le (T : Submodule ℝ H) (F : H) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ t ∈ T, |⟪F, t⟫| ≤ C * ‖t‖) :
    ‖T.topologicalClosure.starProjection F‖ ≤ C := by
  have hcl : ∀ t ∈ T.topologicalClosure, |⟪F, t⟫| ≤ C * ‖t‖ := by
    intro t ht
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at ht
    exact closure_minimal (s := (T : Set H)) (t := {t | |⟪F, t⟫| ≤ C * ‖t‖}) h
      (isClosed_le (continuous_const.inner continuous_id).abs
        (continuous_const.mul continuous_norm)) ht
  set p := T.topologicalClosure.starProjection F
  have hp : p ∈ T.topologicalClosure := Submodule.starProjection_apply_mem _ F
  have hFp : ⟪F, p⟫ = ‖p‖ ^ 2 := by
    have := Submodule.starProjection_inner_eq_zero F p hp
    rw [inner_sub_left, sub_eq_zero] at this
    rw [this, real_inner_self_eq_norm_sq]
  have h1 : ‖p‖ ^ 2 ≤ C * ‖p‖ := by
    have := hcl p hp
    rw [hFp, abs_of_nonneg (sq_nonneg _)] at this
    exact this
  nlinarith [norm_nonneg p]

omit [CompleteSpace H] in
/-- The orthogonal part `F - P F` has norm at most `‖F‖` (Pythagoras). -/
theorem norm_sub_starProjection_le (K : Submodule ℝ H) [K.HasOrthogonalProjection] (F : H) :
    ‖F - K.starProjection F‖ ≤ ‖F‖ := by
  have h0 : ⟪K.starProjection F, F - K.starProjection F⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero F _ (Submodule.starProjection_apply_mem _ F)
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [add_sub_cancel] at this
  nlinarith [norm_nonneg F, norm_nonneg (F - K.starProjection F),
    sq_nonneg ‖K.starProjection F‖]

end Abstract

end BasicElliptic.Div
