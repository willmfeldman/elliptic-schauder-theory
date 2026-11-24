/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Three.ThirdOrder
public import BasicElliptic.Statements.Div

/-!
# The uniform third-order estimate

* `Div.estimate_three_fixed`: the estimate for one fixed unit normal `ν`, with constants
  depending on `E`, `ν`, `lam`, `M`, `δ` (the first-, second- and third-order estimates at the
  centre; at centres outside the closed half space all within-derivatives vanish).
* `Div.quasilinear_conormal_estimate_three_aux`: `Div.QuasilinearConormalEstimateThreeStatement`.
  All hypotheses and conclusions are invariant under a linear isometry `R`
  (`w ↦ w ∘ R`, `Φ ↦ R⁻¹ ∘ Φ ∘ R`, `ν ↦ R⁻¹ ν`), so the constants for a fixed `ν₀` serve every
  unit `ν` (`R` the reflection taking `ν₀` to `ν`).
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace Module
open scoped NNReal Gradient ContDiff Topology

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem iteratedFDerivWithin_eq_zero_of_notMem_closure {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {s : Set E} {x : E} (hx : x ∉ closure s) (n : ℕ) :
    iteratedFDerivWithin ℝ (n + 1) f s x = 0 := by
  rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
    fderivWithin_zero_of_notMem_closure hx, LinearIsometryEquiv.map_zero]

set_option maxSynthPendingDepth 6 in
variable (E) in
/-- **The uniform third-order estimate for a fixed unit normal.** -/
theorem estimate_three_fixed {ν : E} (hν : ‖ν‖ = 1) (lam M δ : ℝ) (hlam : 0 < lam)
    (hδ : 0 < δ) :
    ∃ η > 0, ∃ C : ℝ, ∀ (Φ : E → E), ContDiffOn ℝ 3 Φ (ball 0 δ) →
      (∀ p ∈ ball (0 : E) δ, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫) →
      (∀ p ∈ ball (0 : E) δ, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric) →
      (∀ p ∈ ball (0 : E) δ, ‖fderiv ℝ Φ p‖ ≤ M ∧ ‖iteratedFDeriv ℝ 2 Φ p‖ ≤ M ∧
        ‖iteratedFDeriv ℝ 3 Φ p‖ ≤ M) →
      ∀ (x : E) (r : ℝ) (w : E → ℝ), 0 < r → -r < ⟪x, ν⟫ →
        IsQuasilinearConormalSolOn ν Φ x r w →
        (∀ y ∈ halfBall ν x r, ‖gradientWithin w (halfBall ν x r) y‖ ≤ η) →
        r * ‖fderivWithin ℝ w (halfBall ν x r) x‖ ≤ C * regionOsc w (halfBall ν x r) ∧
        r ^ 2 * ‖fderivWithin ℝ (fderivWithin ℝ w (halfBall ν x r)) (halfBall ν x r) x‖ ≤
          C * regionOsc w (halfBall ν x r) ∧
        r ^ 3 * ‖iteratedFDerivWithin ℝ 3 w (halfBall ν x r) x‖ ≤
          C * regionOsc w (halfBall ν x r) := by
  by_cases hM : 0 ≤ M
  swap
  · refine ⟨1, one_pos, 0, fun Φ _ _ _ hb ↦ ?_⟩
    exfalso
    have := (hb 0 (mem_ball_self hδ)).1
    linarith [norm_nonneg (fderiv ℝ Φ 0)]
  obtain ⟨η₁, hη₁, κ₁, hκ₁, hκ₁2, C₁, hC₁, hP1⟩ := first_order_estimate E hν hlam hM hδ
  obtain ⟨η₂, hη₂, κ₂, hκ₂, hκ₂8, C₂, hC₂, hP2⟩ := second_order_estimate E hν hlam hM hδ
  obtain ⟨η₃, hη₃, C₃, hC₃, hP3⟩ := third_order_estimate E hν hlam hM hδ
  refine ⟨min η₁ (min η₂ η₃), lt_min hη₁ (lt_min hη₂ hη₃), C₁ + C₂ + C₃, ?_⟩
  intro Φ hΦ hell hsym hbd x r w hr hx h hgrad
  have hS : StructureBounds Φ lam M δ := ⟨hlam, hδ, hΦ, hell, hsym, hbd⟩
  set B := halfBall ν x r with hB
  have hBne : B.Nonempty := (interior_halfBall_nonempty hν hr hx).mono interior_subset
  have hosc0 : 0 ≤ regionOsc w B :=
    regionOsc_nonneg_of_compact (isCompact_halfBall ν x r) h.1.continuousOn hBne
  have hC0 : 0 ≤ C₁ + C₂ + C₃ := by positivity
  rcases lt_or_ge ⟪x, ν⟫ 0 with hxneg | hx0
  · have hxB : x ∉ closure B := by
      rw [(isClosed_halfBall ν x r).closure_eq]
      exact fun hxB ↦ (not_le.2 hxneg) hxB.2
    rw [fderivWithin_zero_of_notMem_closure hxB, fderivWithin_zero_of_notMem_closure hxB,
      iteratedFDerivWithin_eq_zero_of_notMem_closure hxB 2]
    have h0 := mul_nonneg hC0 hosc0
    exact ⟨by simpa using h0, by simpa using h0, by simpa using h0⟩
  have hg₁ : ∀ y ∈ B, ‖gradientWithin w B y‖ ≤ η₁ := fun y hy ↦
    (hgrad y hy).trans (min_le_left _ _)
  have hg₂ : ∀ y ∈ B, ‖gradientWithin w B y‖ ≤ η₂ := fun y hy ↦
    (hgrad y hy).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hg₃ : ∀ y ∈ B, ‖gradientWithin w B y‖ ≤ η₃ := fun y hy ↦
    (hgrad y hy).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨-, h1, -⟩ := hP1 Φ hS x r w hr hx0 h hg₁
  obtain ⟨h2, -⟩ := hP2 Φ hS x r w hr hx0 h hg₂
  have h3 := hP3 Φ hS x r w hr hx0 h hg₃
  have hxκ : x ∈ halfBall ν x (κ₂ * r) := ⟨mem_closedBall_self (by positivity), hx0⟩
  have h2' := h2 x hxκ
  rw [← fderivWithin_fderivWithin_halfBall_eq w (mem_ball_self hr) (mem_ball_self hr)] at h2'
  refine ⟨h1.trans ?_, h2'.trans ?_, h3.trans ?_⟩ <;>
  · gcongr
    linarith

/-! ### Rotation -/

section Rotation

variable (R : E ≃ₗᵢ[ℝ] E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem preimage_halfBall_linearIsometryEquiv {ν₀ x : E} {r : ℝ} :
    R ⁻¹' halfBall (R ν₀) x r = halfBall ν₀ (R.symm x) r := by
  ext z
  simp only [mem_preimage, mem_halfBall, LinearIsometryEquiv.inner_map_map]
  rw [show dist (R z) x = dist z (R.symm x) by
    rw [← R.dist_map z (R.symm x), LinearIsometryEquiv.apply_symm_apply]]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem preimage_ball_linearIsometryEquiv {x : E} {r : ℝ} :
    R ⁻¹' ball x r = ball (R.symm x) r := by
  ext z
  simp only [mem_preimage, mem_ball]
  rw [← R.dist_map z (R.symm x), LinearIsometryEquiv.apply_symm_apply]

omit [MeasurableSpace E] [BorelSpace E] in
theorem toDual_symm_comp_linearIsometryEquiv (ℓ : StrongDual ℝ E) :
    (InnerProductSpace.toDual ℝ E).symm (ℓ.comp (R : E →L[ℝ] E)) =
      R.symm ((InnerProductSpace.toDual ℝ E).symm ℓ) := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext v
  rw [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
    ← R.inner_map_map, LinearIsometryEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- The within-gradient of `w ∘ R`. -/
theorem gradientWithin_comp_linearIsometryEquiv {w : E → ℝ} {s : Set E} {z : E}
    (hw : DifferentiableWithinAt ℝ w s (R z)) (hs : UniqueDiffWithinAt ℝ (R ⁻¹' s) z) :
    gradientWithin (fun z ↦ w (R z)) (R ⁻¹' s) z = R.symm (gradientWithin w s (R z)) := by
  have hd : HasFDerivWithinAt (fun z ↦ w (R z))
      ((fderivWithin ℝ w s (R z)).comp (R : E →L[ℝ] E)) (R ⁻¹' s) z :=
    hw.hasFDerivWithinAt.comp z (R : E →L[ℝ] E).hasFDerivWithinAt (mapsTo_preimage _ _)
  rw [gradientWithin, hd.fderivWithin hs, toDual_symm_comp_linearIsometryEquiv]
  rfl

end Rotation

set_option maxSynthPendingDepth 6 in
variable (E) in
/-- **The uniform third-order quasilinear conormal estimate.** -/
theorem quasilinear_conormal_estimate_three_aux : QuasilinearConormalEstimateThreeStatement E := by
  intro lam M δ hlam hδ
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, 0, fun ν Φ hν ↦ ?_⟩
    exfalso
    rw [Subsingleton.elim ν 0, norm_zero] at hν
    exact zero_ne_one hν
  obtain ⟨ν₀, hν₀⟩ := exists_norm_eq E zero_le_one
  obtain ⟨η, hη, C, hC⟩ := estimate_three_fixed E hν₀ lam M δ hlam hδ
  refine ⟨η, hη, max C 0, ?_⟩
  intro ν Φ hν hΦ hell hsym hbd x r w hr hx h hgrad
  set B := halfBall ν x r with hB
  have hBne : B.Nonempty := (interior_halfBall_nonempty hν hr hx).mono interior_subset
  have hosc0 : 0 ≤ regionOsc w B :=
    regionOsc_nonneg_of_compact (isCompact_halfBall ν x r) h.1.continuousOn hBne
  have hCC : C * regionOsc w B ≤ max C 0 * regionOsc w B := by gcongr; exact le_max_left _ _
  have hC0 : 0 ≤ max C 0 * regionOsc w B := mul_nonneg (le_max_right _ _) hosc0
  rcases lt_or_ge ⟪x, ν⟫ 0 with hxneg | hx0
  · have hxB : x ∉ closure B := by
      rw [(isClosed_halfBall ν x r).closure_eq]
      exact fun hxB ↦ (not_le.2 hxneg) hxB.2
    rw [fderivWithin_zero_of_notMem_closure hxB, fderivWithin_zero_of_notMem_closure hxB,
      iteratedFDerivWithin_eq_zero_of_notMem_closure hxB 2]
    exact ⟨by simpa using hC0, by simpa using hC0, by simpa using hC0⟩
  have hxB : x ∈ B := ⟨mem_closedBall_self hr.le, hx0⟩
  -- the rotation
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (ν₀ - ν))ᗮ.reflection with hR
  have hRν : R ν₀ = ν := Submodule.reflection_sub (by rw [hν₀, hν])
  set x' := R.symm x with hx'
  set B' := halfBall ν₀ x' r with hB'
  have hBB' : R ⁻¹' B = B' := by
    have := preimage_halfBall_linearIsometryEquiv R (ν₀ := ν₀) (x := x) (r := r)
    rw [hRν] at this
    exact this
  have hballB' : R ⁻¹' ball x r = ball x' r := preimage_ball_linearIsometryEquiv R
  have hRx' : R x' = x := LinearIsometryEquiv.apply_symm_apply R x
  have hx'ν : ⟪x', ν₀⟫ = ⟪x, ν⟫ := by
    rw [← R.inner_map_map, hRx', hRν]
  set w' : E → ℝ := fun z ↦ w (R z) with hw'
  set Φ' : E → E := fun p ↦ R.symm (Φ (R p)) with hΦ'
  have huB := uniqueDiffOn_halfBall hν hr hx
  have huB' := uniqueDiffOn_halfBall hν₀ hr (by rw [hx'ν]; exact hx)
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hgrad' : ∀ z ∈ B', gradientWithin w' B' z = R.symm (gradientWithin w B (R z)) :=
    fun z hz ↦ by
      have hzB : R z ∈ B := by rw [← hBB'] at hz; exact hz
      rw [← hBB']
      exact gradientWithin_comp_linearIsometryEquiv R (hwB _ hzB) (hBB' ▸ huB' z hz)
  -- the rotated solution
  have hsol' : IsQuasilinearConormalSolOn ν₀ Φ' x' r w' := by
    have hlin := isQuasilinearConormalSolOn_iff.1 h
    have ht := IsWeakSolWithin.comp_affine hlin huB (measurableSet_halfBall ν x r)
      R.toContinuousLinearEquiv 0
    simp only [zero_add] at ht
    have e1 : (fun z ↦ (0 : E) + R.toContinuousLinearEquiv z) = (R : E → E) := by
      funext z; simp
    refine ⟨?_, fun φ hφ ↦ ?_⟩
    · have := ht.1
      rwa [show (fun z ↦ w (R.toContinuousLinearEquiv z)) = w' from rfl,
        show (fun z ↦ R.toContinuousLinearEquiv z) ⁻¹' B = R ⁻¹' B from rfl, hBB'] at this
    · have hφ' : IsTestFn ((fun z ↦ R.toContinuousLinearEquiv z) ⁻¹' ball x r) φ := by
        rwa [show (fun z ↦ R.toContinuousLinearEquiv z) ⁻¹' ball x r = R ⁻¹' ball x r from rfl,
          hballB']
      have key := ht.2 φ hφ'
      simp only [Pi.zero_apply, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
        zero_apply, inner_zero_left, integral_zero, zero_mul, add_zero] at key
      rw [show (fun z ↦ R.toContinuousLinearEquiv z) ⁻¹' B = B' from hBB'] at key
      refine Eq.trans (setIntegral_congr_fun (measurableSet_halfBall ν₀ x' r) fun z hz ↦ ?_)
        key.symm
      rw [hgrad' z hz]
      simp only [hΦ', LinearIsometryEquiv.apply_symm_apply]
      rfl
  -- the rotated structure
  have hRb : ∀ p ∈ ball (0 : E) δ, R p ∈ ball (0 : E) δ := fun p hp ↦ by
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hp
  have hfd : ∀ p ∈ ball (0 : E) δ, fderiv ℝ Φ' p =
      (R.symm : E →L[ℝ] E) ∘L fderiv ℝ Φ (R p) ∘L (R : E →L[ℝ] E) := fun p hp ↦ by
    have hd : HasFDerivAt Φ (fderiv ℝ Φ (R p)) (R p) :=
      (((hΦ.differentiableOn (by norm_num)) _ (hRb p hp)).differentiableAt
        (isOpen_ball.mem_nhds (hRb p hp))).hasFDerivAt
    exact ((R.symm : E →L[ℝ] E).hasFDerivAt.comp p
      (hd.comp p (R : E →L[ℝ] E).hasFDerivAt)).fderiv
  have hΦ'3 : ContDiffOn ℝ 3 Φ' (ball 0 δ) :=
    (R.symm : E →L[ℝ] E).contDiff.comp_contDiffOn
      (hΦ.comp (R : E →L[ℝ] E).contDiff.contDiffOn hRb)
  have hell' : ∀ p ∈ ball (0 : E) δ, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ' p ξ, ξ⟫ :=
    fun p hp ξ ↦ by
      rw [hfd p hp]
      have := hell (R p) (hRb p hp) (R ξ)
      rw [LinearIsometryEquiv.norm_map] at this
      calc lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ (R p) (R ξ), R ξ⟫ := this
        _ = ⟪R (R.symm (fderiv ℝ Φ (R p) (R ξ))), R ξ⟫ := by
            rw [LinearIsometryEquiv.apply_symm_apply]
        _ = _ := by rw [R.inner_map_map]; rfl
  have hsym' : ∀ p ∈ ball (0 : E) δ, (fderiv ℝ Φ' p : E →ₗ[ℝ] E).IsSymmetric :=
    fun p hp a c ↦ by
      have hs := hsym (R p) (hRb p hp) (R a) (R c)
      simp only [ContinuousLinearMap.coe_coe] at hs ⊢
      rw [hfd p hp]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        LinearIsometryEquiv.coe_coe'']
      rw [← R.inner_map_map, LinearIsometryEquiv.apply_symm_apply, hs, ← R.symm.inner_map_map,
        LinearIsometryEquiv.symm_apply_apply]
  have hnorm' : ∀ p (i : ℕ), ‖iteratedFDeriv ℝ i Φ' p‖ = ‖iteratedFDeriv ℝ i Φ (R p)‖ :=
    fun p i ↦ by
      rw [show Φ' = R.symm ∘ (Φ ∘ R) from rfl, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
        LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
  have hbd' : ∀ p ∈ ball (0 : E) δ, ‖fderiv ℝ Φ' p‖ ≤ M ∧ ‖iteratedFDeriv ℝ 2 Φ' p‖ ≤ M ∧
      ‖iteratedFDeriv ℝ 3 Φ' p‖ ≤ M := fun p hp ↦ by
    obtain ⟨h1, h2, h3⟩ := hbd (R p) (hRb p hp)
    refine ⟨?_, by rw [hnorm']; exact h2, by rw [hnorm']; exact h3⟩
    rw [← norm_iteratedFDeriv_one, hnorm', norm_iteratedFDeriv_one]; exact h1
  have hgrad'' : ∀ z ∈ B', ‖gradientWithin w' B' z‖ ≤ η := fun z hz ↦ by
    rw [hgrad' z hz, LinearIsometryEquiv.norm_map]
    exact hgrad _ (by rw [← hBB'] at hz; exact hz)
  obtain ⟨c1, c2, c3⟩ := hC Φ' hΦ'3 hell' hsym' hbd' x' r w' hr (by rw [hx'ν]; exact hx) hsol'
    hgrad''
  -- back to the original variables
  have hosc : regionOsc w' B' = regionOsc w B := by
    have : w' '' B' = w '' B := by
      rw [← hBB', show w' = w ∘ R from rfl, image_comp, image_preimage_eq B R.surjective]
    rw [regionOsc_def, regionOsc_def, this]
  have hx'B' : x' ∈ B' := by rw [← hBB']; change R x' ∈ B; rw [hRx']; exact hxB
  have hiter : ∀ i : ℕ, ‖iteratedFDerivWithin ℝ i w' B' x'‖ =
      ‖iteratedFDerivWithin ℝ i w B x‖ := fun i ↦ by
    rw [← hBB', show w' = w ∘ R from rfl,
      LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right R w huB (by rw [hRx']; exact hxB),
      hRx']
  have hn1 : ∀ {f : E → ℝ} {s : Set E} {z : E}, UniqueDiffOn ℝ s → z ∈ s →
      ‖fderivWithin ℝ f s z‖ = ‖iteratedFDerivWithin ℝ 1 f s z‖ := fun hs hz ↦
    (norm_iteratedFDerivWithin_one _ (hs _ hz)).symm
  have hn2 : ∀ {f : E → ℝ} {s : Set E} {z : E}, UniqueDiffOn ℝ s → z ∈ s →
      ‖fderivWithin ℝ (fderivWithin ℝ f s) s z‖ = ‖iteratedFDerivWithin ℝ 2 f s z‖ :=
    fun hs hz ↦ by
      rw [← norm_iteratedFDerivWithin_fderivWithin hs hz, norm_iteratedFDerivWithin_one _ (hs _ hz)]
  rw [hosc, hn1 huB' hx'B', hiter, ← hn1 huB hxB] at c1
  rw [hosc, hn2 huB' hx'B', hiter, ← hn2 huB hxB] at c2
  rw [hosc, hiter] at c3
  exact ⟨c1.trans hCC, c2.trans hCC, c3.trans hCC⟩

end BasicElliptic.Div
