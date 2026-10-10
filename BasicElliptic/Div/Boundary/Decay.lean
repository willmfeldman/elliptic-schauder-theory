/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Reflection
public import BasicElliptic.Div.Interior.PointDecay
public import BasicElliptic.Defs.Elliptic
import BasicElliptic.Normalize.Cholesky
import BasicElliptic.Normalize.ChangeOfVariables
import BasicElliptic.Normalize.Ellipsoid
import BasicElliptic.Normalize.HolderMap
import BasicElliptic.Campanato.Density
import BasicElliptic.Harmonic.Decay
import BasicElliptic.Common.BallMeasure
import BasicElliptic.Common.RealArith

/-!
# Campanato decay of `∇w` at a flat boundary point

`BasicElliptic.Div.campanato_decay_at_flat_point`: let `w` be a conormal weak solution on
`halfBall ν x₀ δ` (`Div.IsConormalSolOn`) with `x₀` on the flat part, `a` symmetric,
uniformly elliptic (`lam`, `Λ`) and `K_a`-Hölder, `G` `K_G`-Hölder with `‖G x₀‖ ≤ M_G`, `f`
measurable with `|f| ≤ M_f`, and `‖∇w‖ ≤ M₀` (`∇w` the within-gradient). Then for every
`S ⊆ halfSpace ν` and `0 < ρ ≤ √(lam/Λ) δ`

`∫_{B_ρ(x₀) ∩ S} ‖∇w - (∇w)_{B_ρ(x₀) ∩ S}‖²`
  `≤ C ρ^{d+2α} ((M₀ + M_G)² δ^{-2α} + K_a² (M₀ + M_G)² + K_G² + M_f² δ^{2-2α})`

with `C = C(E, α, lam, Λ)`.

## Proof

1. **Normalize**: `M` with `M M† = a(x₀)` and `⟪M z, ν⟫ = m ⟪z, ν⟫`
   (`exists_halfSpace_sqrt`); `w̃ = w(x₀ + M ·)` is a conormal solution on `halfBall ν 0 R̃`,
   `R̃ = δ/√Λ` (`IsConormalSolOn.comp_affine`), with `ã(0) = 1` and Hölder bounds at `0`.
2. **Shift** (`IsConormalSolOn.sub_inner`): with `t = ⟪G̃(0), ν⟫`, `w̃ - t ⟪ν, ·⟫` solves the
   problem with flux `G̃ - t ã ν`, which is tangential at `0`, so `R` fixes it.
3. **Reflect** (`Div/Reflection.lean`): the even reflection is a weak solution on the full ball
   with weakly curl-free gradient field `F̌` and data Hölder **at `0`** only.
4. **Decay**: the interior `campanato_decay_at_point` for `F̌`, with `ψ(R̃) ≤ ‖F̌‖_∞² |B_R̃|`
   (`reflected_decay`); then the algebra of `Div/Interior/GradientCampanato.lean`
   (`gradCampanato_raw_bound_le`, `bracket_le`).
5. **Transfer back**: `B_ρ(x₀) ∩ S ⊆ T(B_{ρ/√lam}(0)) ∩ halfSpace ν`, the mean minimizes, change
   variables (`T⁻¹ (halfSpace ν) = halfSpace ν`), and on the upper half
   `∇w ∘ T - c = M^{-†} (F̌ - F̌_ρ̃)`; finally enlarge `B_ρ̃ ∩ halfSpace ν` to `B_ρ̃`.

The helpers `abs_det_le_pow_of_norm_le`, `gradCampanatoCoeff` and `gradCampanato_raw_bound_le`
are shared with `Div/Interior/GradientCampanato.lean` (`Common/BallMeasure.lean`,
`Common/RealArith.lean`).

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012. (GM)
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient ContDiff Topology NNReal

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Subtracting a linear function -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The within-gradient of `w - ⟪q, ·⟫` is `∇w - q`. -/
theorem gradientWithin_sub_inner {s : Set E} {w : E → ℝ} {y : E} (q : E)
    (hs : UniqueDiffWithinAt ℝ s y) (hw : DifferentiableWithinAt ℝ w s y) :
    gradientWithin (fun z ↦ w z - ⟪q, z⟫) s y = gradientWithin w s y - q := by
  have hl : HasFDerivWithinAt (fun z : E ↦ ⟪q, z⟫) (toDual ℝ E q) s y := by
    have : (fun z : E ↦ ⟪q, z⟫) = ⇑(toDual ℝ E q) := funext fun z ↦ by
      rw [toDual_apply_apply]
    rw [this]; exact (toDual ℝ E q).hasFDerivWithinAt
  have h := hw.hasFDerivWithinAt.fun_sub hl
  rw [gradientWithin, h.fderivWithin hs, map_sub, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- **Subtracting a linear function** from a conormal solution: `w - ⟪q, ·⟫` solves the conormal
problem with `G` replaced by `G - a q` (continuous data). -/
theorem IsConormalSolOn.sub_inner {ν x : E} {r : ℝ} {a : E → E →L[ℝ] E} {G : E → E}
    {f : E → ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫)
    (ha : ContinuousOn a (halfBall ν x r)) (hG : ContinuousOn G (halfBall ν x r))
    (h : IsConormalSolOn ν a G f x r w) (q : E) :
    IsConormalSolOn ν a (fun y ↦ G y - a y q) f x r (fun y ↦ w y - ⟪q, y⟫) := by
  set B := halfBall ν x r with hB
  have hu := uniqueDiffOn_halfBall hν hr hx
  have hgr : ∀ y ∈ B, gradientWithin (fun z ↦ w z - ⟪q, z⟫) B y = gradientWithin w B y - q :=
    fun y hy ↦ gradientWithin_sub_inner q (hu y hy) (h.1.differentiableOn one_ne_zero y hy)
  refine ⟨h.1.sub (contDiff_const.inner ℝ contDiff_id).contDiffOn, fun φ hφ ↦ ?_⟩
  have key := h.2 φ hφ
  have hBc : IsCompact B := isCompact_halfBall ν x r
  have hφc : Continuous (∇ φ) :=
    (toDual ℝ E).symm.continuous.comp (hφ.1.continuous_fderiv one_ne_zero)
  have hgc := continuousOn_gradientWithin_halfBall hν hr hx h.1
  have i1 : IntegrableOn (fun y ↦ ⟪a y (gradientWithin w B y), ∇ φ y⟫) B :=
    ContinuousOn.integrableOn_compact hBc ((ha.clm_apply hgc).inner hφc.continuousOn)
  have i2 : IntegrableOn (fun y ↦ ⟪a y q, ∇ φ y⟫) B :=
    ContinuousOn.integrableOn_compact hBc
      ((ha.clm_apply continuousOn_const).inner hφc.continuousOn)
  have i3 : IntegrableOn (fun y ↦ ⟪G y, ∇ φ y⟫) B :=
    ContinuousOn.integrableOn_compact hBc (hG.inner hφc.continuousOn)
  have e1 : ∫ y in B, ⟪a y (gradientWithin (fun z ↦ w z - ⟪q, z⟫) B y), ∇ φ y⟫ =
      (∫ y in B, ⟪a y (gradientWithin w B y), ∇ φ y⟫) - ∫ y in B, ⟪a y q, ∇ φ y⟫ := by
    rw [← integral_sub i1 i2]
    refine setIntegral_congr_fun (measurableSet_halfBall ν x r) fun y hy ↦ ?_
    simp only [hgr y hy, map_sub, inner_sub_left]
  have e2 : ∫ y in B, ⟪G y - a y q, ∇ φ y⟫ =
      (∫ y in B, ⟪G y, ∇ φ y⟫) - ∫ y in B, ⟪a y q, ∇ φ y⟫ := by
    rw [← integral_sub i3 i2]
    simp only [inner_sub_left]
  change ∫ y in B, ⟪a y (gradientWithin (fun z ↦ w z - ⟪q, z⟫) B y), ∇ φ y⟫ =
    (∫ y in B, ⟪G y - a y q, ∇ φ y⟫) + ∫ y in B, f y * φ y
  rw [e1, e2]
  linarith [key]

/-! ### Decay in normalized coordinates -/

/-- The conclusion of `campanato_decay_at_point` with constant `Cd`, as a predicate. -/
private def DecayProp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α Cd : ℝ) : Prop :=
  ∀ (x₀ : E) (R M K KG Kf : ℝ) (F G : E → E) (f : E → ℝ)
      (ã : E → E →L[ℝ] E), 0 < R →
      AEStronglyMeasurable F (volume.restrict (ball x₀ R)) → (∀ y ∈ ball x₀ R, ‖F y‖ ≤ M) →
      IsWeakCurlFree F (ball x₀ R) →
      AEStronglyMeasurable ã (volume.restrict (ball x₀ R)) →
      (∀ y ∈ ball x₀ R, ‖ã y - 1‖ ≤ K * dist y x₀ ^ α) →
      AEStronglyMeasurable G (volume.restrict (ball x₀ R)) →
      (∀ y ∈ ball x₀ R, ‖G y - G x₀‖ ≤ KG * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R, |f y| ≤ Kf) →
      IsWeakEqOn ã G f F (ball x₀ R) (ball x₀ R) →
      ∀ ρ ∈ Ioc 0 R, ∫ y in ball x₀ ρ, ‖F y - ⨍ z in ball x₀ ρ, F z‖ ^ 2 ≤
        Cd * ((ρ / R) ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (∫ y in ball x₀ R, ‖F y - ⨍ z in ball x₀ R, F z‖ ^ 2) +
          ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (K ^ 2 * M ^ 2 + KG ^ 2 + Kf ^ 2 * R ^ (2 - 2 * α)))

private instance isFiniteMeasure_restrict_ball'' (x : E) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (ball x r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem integrable_norm_sq {μ : Measure E} {g : E → E} (hg : MemLp g 2 μ) :
    Integrable (fun y ↦ ‖g y‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg

/-- `∫_s g ≤ C |s|` for `|g| ≤ C` on a ball. -/
private theorem setIntegral_le_of_abs_le {g : E → ℝ} {x₀ : E} {r C : ℝ}
    (h : ∀ y ∈ ball x₀ r, |g y| ≤ C) : ∫ y in ball x₀ r, g y ≤ C * volume.real (ball x₀ r) :=
  (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const measure_ball_lt_top
    fun y hy ↦ by rw [Real.norm_eq_abs]; exact h y hy)

/-- **Decay in normalized coordinates**. Let `w` be a conormal solution on
`halfBall ν 0 R` with continuous `a`, `G`, `a 0 = 1`, Hölder bounds at `0`, `f` measurable with
`|f| ≤ Mf`, and `‖∇w‖ ≤ N`. Put `t = ⟪G 0, ν⟫`. The even reflection `F̌` of the gradient of
`w - t ⟪ν, ·⟫` (which has tangential flux `G - t a ν` at `0`) satisfies the one-point decay on
`ball 0 R`. -/
private theorem reflected_decay {α Cd : ℝ} (hCd : 0 ≤ Cd) (hdec : DecayProp E α Cd) {ν : E}
    {R K KG Mf N : ℝ}
    {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ}
    (hν : ‖ν‖ = 1) (hR : 0 < R) (haC : ContinuousOn a (halfBall ν 0 R))
    (hGC : ContinuousOn G (halfBall ν 0 R)) (ha0 : a 0 = 1)
    (ha : ∀ z ∈ halfBall ν 0 R, ‖a z - 1‖ ≤ K * dist z 0 ^ α)
    (hG : ∀ z ∈ halfBall ν 0 R, ‖G z - G 0‖ ≤ KG * dist z 0 ^ α)
    (hfm : AEStronglyMeasurable f (volume.restrict (halfBall ν 0 R)))
    (hf : ∀ z ∈ halfBall ν 0 R, |f z| ≤ Mf)
    (hw : IsConormalSolOn ν a G f 0 R w)
    (hN : ∀ z ∈ halfBall ν 0 R, ‖gradientWithin w (halfBall ν 0 R) z‖ ≤ N) :
    MemLp (reflectField ν (gradientWithin (fun y ↦ w y - ⟪⟪G 0, ν⟫ • ν, y⟫)
      (halfBall ν 0 R))) 2 (volume.restrict (ball 0 R)) ∧ ∀ ρ ∈ Ioc 0 R,
      ∫ z in ball 0 ρ, ‖reflectField ν (gradientWithin (fun y ↦ w y - ⟪⟪G 0, ν⟫ • ν, y⟫)
          (halfBall ν 0 R)) z - ⨍ z' in ball 0 ρ, reflectField ν
          (gradientWithin (fun y ↦ w y - ⟪⟪G 0, ν⟫ • ν, y⟫) (halfBall ν 0 R)) z'‖ ^ 2 ≤
        Cd * ((ρ / R) ^ ((finrank ℝ E : ℝ) + 2 * α) *
            ((N + |⟪G 0, ν⟫|) ^ 2 * volume.real (ball (0 : E) R)) +
          ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (K ^ 2 * (N + |⟪G 0, ν⟫|) ^ 2 + (KG + K * |⟪G 0, ν⟫|) ^ 2 +
              Mf ^ 2 * R ^ (2 - 2 * α))) := by
  set B := halfBall ν (0 : E) R with hB
  set t := ⟪G 0, ν⟫ with ht
  set q : E := t • ν with hq
  have hx0 : ⟪(0 : E), ν⟫ = 0 := inner_zero_left _
  have hxR : -R < ⟪(0 : E), ν⟫ := by rw [hx0]; linarith
  have hBm : MeasurableSet B := measurableSet_halfBall ν 0 R
  have hBc : IsCompact B := isCompact_halfBall ν 0 R
  have hqn : ‖q‖ = |t| := by rw [hq, norm_smul, hν, mul_one, Real.norm_eq_abs]
  set w' : E → ℝ := fun y ↦ w y - ⟪q, y⟫ with hw'def
  set G' : E → E := fun y ↦ G y - a y q with hG'def
  have hw' : IsConormalSolOn ν a G' f 0 R w' := hw.sub_inner hν hR hxR haC hGC q
  have hG'C : ContinuousOn G' B := hGC.sub (haC.clm_apply continuousOn_const)
  have hu := uniqueDiffOn_halfBall hν hR hxR
  have hgr : ∀ z ∈ B, gradientWithin w' B z = gradientWithin w B z - q := fun z hz ↦
    gradientWithin_sub_inner q (hu z hz) (hw.1.differentiableOn one_ne_zero z hz)
  set F := reflectField ν (gradientWithin w' B) with hF
  -- the reflected problem
  obtain ⟨Λ', hΛ'⟩ := hBc.exists_bound_of_continuousOn haC
  obtain ⟨MG', hMG'⟩ := hBc.exists_bound_of_continuousOn hG'C
  have hrefl := IsConormalSolOn.evenReflect E ν 0 R Λ' MG' Mf a G' f w' hν hR hx0
    (haC.aestronglyMeasurable hBm) hΛ' (hG'C.aestronglyMeasurable hBm) hMG' hfm hf hw'
  have hcurl : IsWeakCurlFree F (ball 0 R) := isWeakCurlFree_reflectField hν hx0 hw'.1
  have hgc' : ContinuousOn (gradientWithin w' B) B :=
    continuousOn_gradientWithin_halfBall hν hR hxR hw'.1
  have hFm : AEStronglyMeasurable F (volume.restrict (ball 0 R)) :=
    aestronglyMeasurable_reflectField hν hx0 (hgc'.aestronglyMeasurable hBm)
  have hFb : ∀ y ∈ ball (0 : E) R, ‖F y‖ ≤ N + |t| := norm_reflectField_le hν hx0 fun z hz ↦ by
    rw [hgr z hz, ← hqn]; exact (norm_sub_le _ _).trans (by linarith [hN z hz])
  have ham : AEStronglyMeasurable (reflectCoeff ν a) (volume.restrict (ball 0 R)) :=
    aestronglyMeasurable_reflectCoeff hν hx0 (haC.aestronglyMeasurable hBm)
  have hab : ∀ y ∈ ball (0 : E) R, ‖reflectCoeff ν a y - 1‖ ≤ K * dist y 0 ^ α :=
    norm_reflectCoeff_sub_one_le hν hx0 ha
  have hGm : AEStronglyMeasurable (reflectField ν G') (volume.restrict (ball 0 R)) :=
    aestronglyMeasurable_reflectField hν hx0 (hG'C.aestronglyMeasurable hBm)
  have hG'0 : G' 0 = G 0 - q := by rw [hG'def]; simp only [ha0, one_apply_eq_self]
  have hG'ν : ⟪G' 0, ν⟫ = 0 := by
    rw [hG'0, inner_sub_left, hq, real_inner_smul_left, real_inner_self_of_norm_eq_one hν,
      mul_one, ht, sub_self]
  have hGb : ∀ y ∈ ball (0 : E) R,
      ‖reflectField ν G' y - reflectField ν G' 0‖ ≤ (KG + K * |t|) * dist y 0 ^ α := by
    have h0 : reflectField ν G' 0 = G' 0 := by simp [reflectField]
    rw [h0]
    refine norm_reflectField_sub_le hν hx0 hG'ν fun z hz ↦ ?_
    have : G' z - G' 0 = (G z - G 0) - (a z - 1) q := by
      rw [hG'0, hG'def]; simp only [sub_apply, one_apply_eq_self]
      abel
    rw [this]
    have hdz : 0 ≤ dist z 0 ^ α := Real.rpow_nonneg dist_nonneg _
    calc ‖(G z - G 0) - (a z - 1) q‖ ≤ ‖G z - G 0‖ + ‖a z - 1‖ * ‖q‖ :=
          (norm_sub_le _ _).trans (add_le_add le_rfl ((a z - 1).le_opNorm q))
      _ ≤ KG * dist z 0 ^ α + K * dist z 0 ^ α * |t| := by
          rw [hqn]; gcongr
          · exact hG z hz
          · exact ha z hz
      _ = (KG + K * |t|) * dist z 0 ^ α := by ring
  have hfb : ∀ y ∈ ball (0 : E) R, |evenExt ν f y| ≤ Mf := fun y hy ↦
    hf _ (fold_mem_halfBall hν hx0 (ball_subset_closedBall hy))
  have hL := memLp_restrict_ball_of_bound hFm hFb
  refine ⟨hL, fun ρ hρ ↦ ?_⟩
  have h := hdec 0 R (N + |t|) K (KG + K * |t|) Mf F (reflectField ν G') (evenExt ν f)
    (reflectCoeff ν a) hR hFm hFb hcurl ham hab hGm hGb hfb hrefl.2 ρ hρ
  refine h.trans ?_
  have hψR : ∫ y in ball (0 : E) R, ‖F y - ⨍ z in ball (0 : E) R, F z‖ ^ 2 ≤
      (N + |t|) ^ 2 * volume.real (ball (0 : E) R) := by
    refine (setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hL.integrable one_le_two) (integrable_norm_sq hL) 0).trans ?_
    refine setIntegral_le_of_abs_le fun z hz ↦ ?_
    rw [sub_zero, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hFb z hz) 2
  have hρR : 0 ≤ ρ / R := div_nonneg hρ.1.le hR.le
  gcongr

/-! ### Algebra and volume (as in `Div/Interior/GradientCampanato.lean`) -/


/-! ### Transport -/

/-- Measurability transports along `z ↦ x₀ + M z`. -/
private theorem aestronglyMeasurable_comp_affine {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] {g : E → X} {s : Set E} (M : E ≃L[ℝ] E) (x₀ : E)
    (hg : AEStronglyMeasurable g (volume.restrict s)) :
    AEStronglyMeasurable (fun z ↦ g (x₀ + M z))
      (volume.restrict ((fun z ↦ x₀ + M z) ⁻¹' s)) := by
  let T : E ≃ₜ E := M.toHomeomorph.trans (Homeomorph.addLeft x₀)
  have hT : MeasurableEmbedding T := T.measurableEmbedding
  have hdet : LinearMap.det (M : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  have hmap : Measure.map T volume =
      ENNReal.ofReal |(LinearMap.det (M : E →ₗ[ℝ] E))⁻¹| • (volume : Measure E) := by
    have hT' : (T : E → E) = (fun x ↦ x₀ + x) ∘ (M : E →ₗ[ℝ] E) := rfl
    rw [hT', ← Measure.map_map (measurable_const_add x₀)
        (M : E →ₗ[ℝ] E).continuous_of_finiteDimensional.measurable,
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet,
      Measure.map_smul _ (measurable_const_add x₀).aemeasurable, map_add_left_eq_self]
  change AEStronglyMeasurable (g ∘ T) (volume.restrict (T ⁻¹' s))
  rw [← hT.aestronglyMeasurable_map_iff, ← hT.restrict_map, hmap, Measure.restrict_smul]
  exact hg.smul_measure _

/-- The bracket of `gradCampanato_raw_bound_le` with the shifted constants is controlled by
`3 P² ((M₀ + M_G)² δ^{-2α} + K_a² (M₀ + M_G)² + K_G² + M_f² δ^{2-2α})`, `P = 1 + 1/l²`. -/
private theorem bracket_le {M₀ MG t s l Ka KG Mf δ α P : ℝ} (hM₀0 : 0 ≤ M₀) (hMG0 : 0 ≤ MG)
    (hl : 0 < l) (hls : l ≤ s) (htb : |t| ≤ MG / l) (hKa : 0 ≤ Ka) (hKG : 0 ≤ KG)
    (hP1 : 1 ≤ P) (hP : P = 1 + 1 / l ^ 2) (hδ : 0 < δ) :
    (M₀ + |t| / s) ^ 2 * δ ^ (-(2 * α)) + Ka ^ 2 * (M₀ + |t| / s) ^ 2 +
      (KG + Ka * |t| / l) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * α) ≤
    3 * P ^ 2 * ((M₀ + MG) ^ 2 * δ ^ (-(2 * α)) + Ka ^ 2 * (M₀ + MG) ^ 2 + KG ^ 2 +
      Mf ^ 2 * δ ^ (2 - 2 * α)) := by
  have hs : 0 < s := hl.trans_le hls
  have hts : |t| / s ≤ MG / l ^ 2 := by
    calc |t| / s ≤ |t| / l := div_le_div_of_nonneg_left (abs_nonneg _) hl hls
      _ ≤ MG / l / l := by gcongr
      _ = MG / l ^ 2 := by ring
  have htl : |t| / l ≤ MG / l ^ 2 := by
    calc |t| / l ≤ MG / l / l := by gcongr
      _ = MG / l ^ 2 := by ring
  have hMGl : MG / l ^ 2 ≤ (M₀ + MG) / l ^ 2 := by gcongr; linarith
  have hP' : P = 1 + 1 / l ^ 2 := hP
  have hA : 0 ≤ M₀ + |t| / s := by positivity
  have hA' : M₀ + |t| / s ≤ P * (M₀ + MG) := by
    rw [hP', add_mul, one_mul, one_div_mul_eq_div]
    have : 0 ≤ M₀ / l ^ 2 := by positivity
    have : (M₀ + MG) / l ^ 2 = M₀ / l ^ 2 + MG / l ^ 2 := by ring
    linarith
  have hB : 0 ≤ KG + Ka * |t| / l := by positivity
  have hB' : KG + Ka * |t| / l ≤ P * (KG + Ka * (M₀ + MG)) := by
    rw [hP', add_mul, one_mul, one_div_mul_eq_div]
    have h1 : Ka * |t| / l ≤ Ka * ((M₀ + MG) / l ^ 2) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (htl.trans hMGl) hKa
    have h2 : 0 ≤ KG / l ^ 2 := by positivity
    have h3 : (KG + Ka * (M₀ + MG)) / l ^ 2 = KG / l ^ 2 + Ka * ((M₀ + MG) / l ^ 2) := by ring
    have h4 : 0 ≤ Ka * (M₀ + MG) := by positivity
    linarith
  have hA2 : (M₀ + |t| / s) ^ 2 ≤ P ^ 2 * (M₀ + MG) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hA hA' 2
  have hB2 : (KG + Ka * |t| / l) ^ 2 ≤ 2 * P ^ 2 * (KG ^ 2 + Ka ^ 2 * (M₀ + MG) ^ 2) := by
    calc (KG + Ka * |t| / l) ^ 2 ≤ (P * (KG + Ka * (M₀ + MG))) ^ 2 :=
          pow_le_pow_left₀ hB hB' 2
      _ ≤ 2 * P ^ 2 * (KG ^ 2 + Ka ^ 2 * (M₀ + MG) ^ 2) := by
          nlinarith [sq_nonneg (KG - Ka * (M₀ + MG)), sq_nonneg P]
  have hd1 : 0 ≤ δ ^ (-(2 * α)) := Real.rpow_nonneg hδ.le _
  have hd2 : 0 ≤ δ ^ (2 - 2 * α) := Real.rpow_nonneg hδ.le _
  have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP1
  have i1 : (M₀ + |t| / s) ^ 2 * δ ^ (-(2 * α)) ≤
      P ^ 2 * ((M₀ + MG) ^ 2 * δ ^ (-(2 * α))) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hA2 hd1
  have i2 : Ka ^ 2 * (M₀ + |t| / s) ^ 2 ≤ P ^ 2 * (Ka ^ 2 * (M₀ + MG) ^ 2) := by
    nlinarith [sq_nonneg Ka]
  have i4 : Mf ^ 2 * δ ^ (2 - 2 * α) ≤ P ^ 2 * (Mf ^ 2 * δ ^ (2 - 2 * α)) :=
    le_mul_of_one_le_left (by positivity) hP2
  have hX0a : 0 ≤ (M₀ + MG) ^ 2 * δ ^ (-(2 * α)) := by positivity
  have hX0b : 0 ≤ Ka ^ 2 * (M₀ + MG) ^ 2 := by positivity
  have hX0c : 0 ≤ Mf ^ 2 * δ ^ (2 - 2 * α) := by positivity
  have hX0d : 0 ≤ P ^ 2 := by positivity
  nlinarith [mul_nonneg hX0d hX0a, mul_nonneg hX0d hX0b, mul_nonneg hX0d hX0c,
    mul_nonneg hX0d (sq_nonneg KG)]

variable (E) in
/-- **Campanato decay of `∇w` at a flat boundary point** (GM).
There is `C = C(E, α, lam, Λ) ≥ 0` such that, for a conormal solution `w` on
`halfBall ν x₀ δ` with `x₀` on the flat part, `a` symmetric, uniformly elliptic (`lam`, `Λ`) and
`K_a`-Hölder, `G` `K_G`-Hölder with `‖G x₀‖ ≤ M_G`, `f` measurable with `|f| ≤ M_f`, and
`‖∇w‖ ≤ M₀` on the half ball: for every `S ⊆ halfSpace ν` and `0 < ρ ≤ √(lam/Λ) δ`,

`∫_{B_ρ(x₀) ∩ S} ‖∇w - (∇w)_{B_ρ(x₀) ∩ S}‖²`
  `≤ C ρ^{d+2α} ((M₀ + M_G)² δ^{-2α} + K_a² (M₀ + M_G)² + K_G² + M_f² δ^{2-2α})`.

See the module docstring for the proof. -/
theorem campanato_decay_at_flat_point {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν x₀ : E) (Ka KG : ℝ≥0) (Mf M₀ MG δ : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → ⟪x₀, ν⟫ = 0 → 0 < δ →
      IsUniformlyElliptic lam Λ a (halfBall ν x₀ δ) → IsSymmetricOn a (halfBall ν x₀ δ) →
      HolderOnWith Ka α a (halfBall ν x₀ δ) → HolderOnWith KG α G (halfBall ν x₀ δ) →
      ‖G x₀‖ ≤ MG →
      AEStronglyMeasurable f (volume.restrict (halfBall ν x₀ δ)) →
      (∀ y ∈ halfBall ν x₀ δ, |f y| ≤ Mf) → IsConormalSolOn ν a G f x₀ δ w →
      (∀ y ∈ halfBall ν x₀ δ, ‖gradientWithin w (halfBall ν x₀ δ) y‖ ≤ M₀) →
      ∀ (S : Set E), S ⊆ halfSpace ν → ∀ ρ : ℝ, 0 < ρ → ρ ≤ √(lam / Λ) * δ →
        ∫ y in ball x₀ ρ ∩ S, ‖gradientWithin w (halfBall ν x₀ δ) y -
            ⨍ z in ball x₀ ρ ∩ S, gradientWithin w (halfBall ν x₀ δ) z‖ ^ 2 ≤
          C * ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            ((M₀ + MG) ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 +
              (KG : ℝ) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ))) := by
  obtain ⟨Cd, hCd, hdec⟩ := campanato_decay_at_point E (α := (α : ℝ))
    (by exact_mod_cast hα) (by exact_mod_cast hα1)
  set s := √Λ with hsdef
  set l := √lam with hldef
  set d := finrank ℝ E
  set b : ℝ := (d : ℝ) + 2 * α with hb
  have hl : 0 < l := Real.sqrt_pos.2 hlam
  set Q := gradCampanatoCoeff (unitBallVolume E) s l α
  have hQ : 0 ≤ Q := gradCampanatoCoeff_nonneg unitBallVolume_pos.le (Real.sqrt_nonneg _)
  set P : ℝ := 1 + 1 / l ^ 2 with hP
  have hP1 : 1 ≤ P := by rw [hP]; have : 0 ≤ 1 / l ^ 2 := by positivity
                         linarith
  refine ⟨s ^ d / lam * Cd * l ^ (-b) * Q * (3 * P ^ 2), by
    have := Real.rpow_nonneg hl.le (-b); have := Real.sqrt_nonneg Λ; positivity, ?_⟩
  intro ν x₀ Ka KG Mf M₀ MG δ a G f w hν hx₀ hδ hell hsym ha hG hMG hfm hfb hw hM₀ S hS ρ hρ hρδ
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have : Nontrivial E := ⟨⟨ν, 0, hν0⟩⟩
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hx₀B : x₀ ∈ halfBall ν x₀ δ := ⟨mem_closedBall_self hδ.le, mem_halfSpace.2 hx₀.ge⟩
  -- `lam ≤ Λ`
  have hlamΛ : lam ≤ Λ := by
    obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
    have hξ0 : 0 < ‖ξ‖ ^ 2 := by positivity
    have h1 := (hell x₀ hx₀B).1 ξ
    have h2 : ⟪a x₀ ξ, ξ⟫ ≤ Λ * ‖ξ‖ ^ 2 :=
      (real_inner_le_norm _ _).trans (by
        calc ‖a x₀ ξ‖ * ‖ξ‖ ≤ ‖a x₀‖ * ‖ξ‖ * ‖ξ‖ :=
              mul_le_mul_of_nonneg_right ((a x₀).le_opNorm ξ) (norm_nonneg _)
          _ ≤ Λ * ‖ξ‖ * ‖ξ‖ := by
              gcongr; exact (hell x₀ hx₀B).2
          _ = Λ * ‖ξ‖ ^ 2 := by ring)
    nlinarith
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  have hs : 0 < s := Real.sqrt_pos.2 hΛ
  have hls : l ≤ s := Real.sqrt_le_sqrt hlamΛ
  obtain ⟨M, hMM, ⟨m, hm1, -, hMν⟩, hMn, hMn'⟩ := exists_halfSpace_sqrt hν hlam
    (hsym x₀ hx₀B) (hell x₀ hx₀B).1 (hell x₀ hx₀B).2
  have hm : 0 < m := hl.trans_le hm1
  set R := δ / s with hR
  have hR0 : 0 < R := div_pos hδ hs
  have hMR : ‖(M : E →L[ℝ] E)‖ * R ≤ δ := by
    calc ‖(M : E →L[ℝ] E)‖ * R ≤ s * R := mul_le_mul_of_nonneg_right hMn hR0.le
      _ = δ := by rw [hR]; field_simp
  set T : E → E := fun z ↦ x₀ + M z with hT
  set adjM := ContinuousLinearMap.adjoint (M : E →L[ℝ] E) with hadjMdef
  set adjMi := ContinuousLinearMap.adjoint (M.symm : E →L[ℝ] E) with hadjMidef
  have hadjM : ‖adjM‖ ≤ s := by
    rw [show ‖adjM‖ = ‖(M : E →L[ℝ] E)‖ from LinearIsometryEquiv.norm_map _ _]; exact hMn
  have hadjMi : ‖adjMi‖ ≤ 1 / l := by
    rw [show ‖adjMi‖ = ‖(M.symm : E →L[ℝ] E)‖ from LinearIsometryEquiv.norm_map _ _]
    exact hMn'
  have hinv : ∀ v, adjMi (adjM v) = v := fun v ↦ by
    rw [← ContinuousLinearMap.comp_apply, adjoint_symm_comp_adjoint, one_apply_eq_self]
  have hMz : ∀ z, ‖M z‖ ≤ s * ‖z‖ := fun z ↦
    ((M : E →L[ℝ] E).le_opNorm z).trans (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))
  have hdistT : ∀ z, dist (T z) x₀ ≤ s * dist z 0 := fun z ↦ by
    rw [dist_eq_norm, dist_zero_right, hT]
    simp only [add_sub_cancel_left]
    exact hMz z
  set Bt := halfBall ν (0 : E) R with hBt
  have hTB : ∀ z ∈ Bt, T z ∈ halfBall ν x₀ δ := fun z hz ↦ by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall]
      calc dist (T z) x₀ ≤ s * dist z 0 := hdistT z
        _ ≤ s * R := mul_le_mul_of_nonneg_left (mem_closedBall.1 hz.1) hs.le
        _ = δ := by rw [hR]; field_simp
    · rw [mem_halfSpace, hT, inner_affine_eq hx₀ hMν]
      exact mul_nonneg hm.le hz.2
  have hmapsT : MapsTo T Bt (halfBall ν x₀ δ) := hTB
  have hcontT : Continuous T := continuous_const.add M.continuous
  have haC : ContinuousOn a (halfBall ν x₀ δ) := ha.continuousOn hα
  have hGC : ContinuousOn G (halfBall ν x₀ δ) := hG.continuousOn hα
  -- the transported problem
  have hwT := hw.comp_affine hν hx₀ hδ hm hMν hR0 hMR
  set at' : E → E →L[ℝ] E :=
    fun z ↦ (M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjMi with hat'
  set Gt : E → E := fun z ↦ M.symm (G (x₀ + M z)) with hGt
  set ft : E → ℝ := fun z ↦ f (x₀ + M z) with hft
  set wt : E → ℝ := fun z ↦ w (x₀ + M z) with hwt
  have hatC : ContinuousOn at' Bt :=
    continuousOn_const.clm_comp ((haC.comp hcontT.continuousOn hmapsT).clm_comp
      continuousOn_const)
  have hGtC : ContinuousOn Gt Bt :=
    (M.symm : E →L[ℝ] E).continuous.comp_continuousOn (hGC.comp hcontT.continuousOn hmapsT)
  have hat0 : at' 0 = 1 := by
    rw [hat']
    simp only [map_zero, add_zero]
    exact symm_comp_comp_adjoint_symm_eq_one hMM
  have hatH : ∀ z ∈ Bt, ‖at' z - 1‖ ≤ Ka * s ^ (α : ℝ) / l ^ 2 * dist z 0 ^ (α : ℝ) :=
    fun z hz ↦ by
    rw [← hat0, hat']
    simp only [map_zero, add_zero]
    refine (norm_comp_comp_sub_le _ _ _ _).trans ?_
    have h1 : ‖a (x₀ + M z) - a x₀‖ ≤ Ka * (s ^ (α : ℝ) * dist z 0 ^ (α : ℝ)) := by
      rw [← dist_eq_norm]
      refine (ha.dist_le (hTB z hz) hx₀B).trans (mul_le_mul_of_nonneg_left ?_ Ka.2)
      rw [← Real.mul_rpow hs.le dist_nonneg]
      exact Real.rpow_le_rpow dist_nonneg (hdistT z) α.2
    calc ‖(M.symm : E →L[ℝ] E)‖ * ‖adjMi‖ * ‖a (x₀ + M z) - a x₀‖
        ≤ 1 / l * (1 / l) * (Ka * (s ^ (α : ℝ) * dist z 0 ^ (α : ℝ))) := by
          gcongr
      _ = _ := by field_simp
  have hGtH : ∀ z ∈ Bt, ‖Gt z - Gt 0‖ ≤ KG * s ^ (α : ℝ) / l * dist z 0 ^ (α : ℝ) :=
    fun z hz ↦ by
    rw [hGt]
    simp only [map_zero, add_zero]
    rw [← map_sub]
    have h1 : ‖G (x₀ + M z) - G x₀‖ ≤ KG * (s ^ (α : ℝ) * dist z 0 ^ (α : ℝ)) := by
      rw [← dist_eq_norm]
      refine (hG.dist_le (hTB z hz) hx₀B).trans (mul_le_mul_of_nonneg_left ?_ KG.2)
      rw [← Real.mul_rpow hs.le dist_nonneg]
      exact Real.rpow_le_rpow dist_nonneg (hdistT z) α.2
    calc ‖M.symm (G (x₀ + M z) - G x₀)‖
        ≤ ‖(M.symm : E →L[ℝ] E)‖ * ‖G (x₀ + M z) - G x₀‖ :=
          (M.symm : E →L[ℝ] E).le_opNorm _
      _ ≤ 1 / l * (KG * (s ^ (α : ℝ) * dist z 0 ^ (α : ℝ))) := by gcongr
      _ = _ := by field_simp
  have hftm : AEStronglyMeasurable ft (volume.restrict Bt) :=
    (aestronglyMeasurable_comp_affine M x₀ hfm).mono_measure
      (Measure.restrict_mono hTB le_rfl)
  have hftb : ∀ z ∈ Bt, |ft z| ≤ Mf := fun z hz ↦ hfb _ (hTB z hz)
  -- the transported gradient
  have hxR : -R < ⟪(0 : E), ν⟫ := by rw [inner_zero_left]; linarith
  have huBt := uniqueDiffOn_halfBall hν hR0 hxR
  have hgT : ∀ z ∈ Bt, gradientWithin wt Bt z =
      adjM (gradientWithin w (halfBall ν x₀ δ) (T z)) := fun z hz ↦ by
    have hsub : Bt ⊆ T ⁻¹' halfBall ν x₀ δ := hTB
    have hdw : DifferentiableWithinAt ℝ w (halfBall ν x₀ δ) (T z) :=
      hw.1.differentiableOn one_ne_zero _ (hTB z hz)
    have hdT : DifferentiableWithinAt ℝ T (T ⁻¹' halfBall ν x₀ δ) z :=
      ((contDiff_const.add M.contDiff).differentiable one_ne_zero z).differentiableWithinAt
    have hdwt : DifferentiableWithinAt ℝ wt (T ⁻¹' halfBall ν x₀ δ) z :=
      hdw.comp z hdT (fun _ h ↦ h)
    rw [gradientWithin_eq_of_subset hsub (huBt z hz) hdwt]
    exact gradientWithin_comp_affine M x₀ hdw ((huBt z hz).mono hsub)
  have hN : ∀ z ∈ Bt, ‖gradientWithin wt Bt z‖ ≤ s * M₀ := fun z hz ↦ by
    rw [hgT z hz]
    exact (adjM.le_opNorm _).trans (mul_le_mul hadjM (hM₀ _ (hTB z hz)) (norm_nonneg _) hs.le)
  -- the reflected decay in normalized coordinates
  set t := ⟪Gt 0, ν⟫ with ht
  set q : E := t • ν with hq
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans hMG
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ x₀ hx₀B)
  have htb : |t| ≤ MG / l := by
    have h1 : |t| ≤ ‖Gt 0‖ := by
      rw [ht]; refine (abs_real_inner_le_norm _ _).trans ?_; rw [hν, mul_one]
    have h2 : ‖Gt 0‖ ≤ 1 / l * MG := by
      rw [hGt]; simp only [map_zero, add_zero]
      exact ((M.symm : E →L[ℝ] E).le_opNorm _).trans
        (mul_le_mul hMn' hMG (norm_nonneg _) (by positivity))
    calc |t| ≤ 1 / l * MG := h1.trans h2
      _ = MG / l := by ring
  obtain ⟨hFL, hdecay⟩ := reflected_decay hCd hdec hν hR0 hatC hGtC hat0 hatH hGtH hftm hftb
    hwT hN
  set F := reflectField ν (gradientWithin (fun y ↦ wt y - ⟪q, y⟫) Bt) with hF
  set ρt := ρ / l with hρt
  have hρt0 : 0 < ρt := div_pos hρ hl
  have hρδ' : ρ ≤ l / s * δ := by
    rwa [hsdef, hldef, ← Real.sqrt_div' lam hΛ.le]
  have hρtR : ρt ≤ R := by
    rw [hρt, hR, div_le_div_iff₀ hl hs]
    calc ρ * s ≤ l / s * δ * s := mul_le_mul_of_nonneg_right hρδ' hs.le
      _ = δ * l := by field_simp
  have hψt := hdecay ρt ⟨hρt0, hρtR⟩
  rw [measureReal_ball_eq hR0] at hψt
  have raw := gradCampanato_raw_bound_le (d := d) (α := (α : ℝ)) (Ka := (Ka : ℝ))
    (KG := (KG : ℝ) + Ka * |t| / l) (Mf := Mf) (M₀ := M₀ + |t| / s) hs hl hδ hρt0 hCd
    (unitBallVolume_pos (E := E)).le
  have e1 : s * (M₀ + |t| / s) = s * M₀ + |t| := by field_simp
  have e2 : ((KG : ℝ) + Ka * |t| / l) * s ^ (α : ℝ) / l =
      KG * s ^ (α : ℝ) / l + Ka * s ^ (α : ℝ) / l ^ 2 * |t| := by field_simp
  rw [e1, e2] at raw
  set X := (M₀ + MG) ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 +
    (KG : ℝ) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) with hX
  have hY := bracket_le (α := (α : ℝ)) hM₀0 hMG0 hl hls htb Ka.2 KG.2 hP1 hP hδ (Mf := Mf)
  have hψt2 : ∫ z in ball 0 ρt, ‖F z - ⨍ z' in ball 0 ρt, F z'‖ ^ 2 ≤
      Cd * ρt ^ b * Q * (3 * P ^ 2 * X) := by
    refine hψt.trans (le_trans (le_of_eq ?_) (raw.trans ?_))
    · rfl
    · exact mul_le_mul_of_nonneg_left hY (by
        have := Real.rpow_nonneg hρt0.le b; positivity)
  -- back to the original coordinates
  set gW := gradientWithin w (halfBall ν x₀ δ) with hgW
  set ct := ⨍ z in ball 0 ρt, F z with hct
  set c := adjMi (ct + q) with hc
  have hxδ : -δ < ⟪x₀, ν⟫ := by rw [hx₀]; linarith
  have hgWc : ContinuousOn gW (halfBall ν x₀ δ) :=
    continuousOn_gradientWithin_halfBall hν hδ hxδ hw.1
  have hBδc : IsCompact (halfBall ν x₀ δ) := isCompact_halfBall ν x₀ δ
  have hgi : IntegrableOn gW (halfBall ν x₀ δ) := ContinuousOn.integrableOn_compact hBδc hgWc
  have hgi2 : IntegrableOn (fun y ↦ ‖gW y‖ ^ 2) (halfBall ν x₀ δ) :=
    ContinuousOn.integrableOn_compact hBδc (hgWc.norm.pow 2)
  have hgc : IntegrableOn (fun y ↦ ‖gW y - c‖ ^ 2) (halfBall ν x₀ δ) :=
    ContinuousOn.integrableOn_compact hBδc ((hgWc.sub continuousOn_const).norm.pow 2)
  have hTBρ : T '' ball 0 ρt ∩ halfSpace ν ⊆ halfBall ν x₀ δ := by
    rintro _ ⟨⟨z, hz, rfl⟩, hzH⟩
    refine ⟨?_, hzH⟩
    rw [mem_closedBall]
    rw [mem_ball] at hz
    calc dist (T z) x₀ ≤ s * dist z 0 := hdistT z
      _ ≤ s * R := mul_le_mul_of_nonneg_left (hz.le.trans hρtR) hs.le
      _ = δ := by rw [hR]; field_simp
  have hBT : ball x₀ ρ ⊆ T '' ball 0 ρt := by
    have := ball_subset_image_affine_ball M x₀ (K' := 1 / l) (by positivity)
      (fun y ↦ ((M.symm : E →L[ℝ] E).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right hMn' (norm_nonneg _))) 0 ρ
    rwa [map_zero, add_zero, one_div_mul_eq_div] at this
  have hsubS : ball x₀ ρ ∩ S ⊆ T '' ball 0 ρt ∩ halfSpace ν := fun y hy ↦ ⟨hBT hy.1, hS hy.2⟩
  have hsubB : ball x₀ ρ ∩ S ⊆ halfBall ν x₀ δ := hsubS.trans hTBρ
  -- step 1: the mean minimizes, and monotonicity in the domain
  have hs1 : ∫ y in ball x₀ ρ ∩ S, ‖gW y - ⨍ z in ball x₀ ρ ∩ S, gW z‖ ^ 2 ≤
      ∫ y in T '' ball 0 ρt ∩ halfSpace ν, ‖gW y - c‖ ^ 2 := by
    have hfin : volume (ball x₀ ρ ∩ S) ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
    refine (setIntegral_norm_sub_setAverage_sq_le hfin (hgi.mono_set hsubB)
      (hgi2.mono_set hsubB) c).trans ?_
    exact setIntegral_mono_set (hgc.mono_set hTBρ) (Eventually.of_forall fun _ ↦ sq_nonneg _)
      hsubS.eventuallyLE
  -- step 2: change of variables
  have hTinj : Function.Injective T := fun z z' h ↦ M.injective (add_left_cancel h)
  have hdet0 : LinearMap.det (M : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  have hcov := setIntegral_comp_affine M x₀ (fun y ↦ ‖gW y - c‖ ^ 2)
    (T '' ball 0 ρt ∩ halfSpace ν)
  rw [preimage_inter, Set.preimage_image_eq _ hTinj, preimage_affine_halfSpace hm hx₀ hMν]
    at hcov
  have hs2 : ∫ y in T '' ball 0 ρt ∩ halfSpace ν, ‖gW y - c‖ ^ 2 =
      |LinearMap.det (M : E →ₗ[ℝ] E)| *
        ∫ z in ball 0 ρt ∩ halfSpace ν, ‖gW (x₀ + M z) - c‖ ^ 2 := by
    rw [hcov, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hdet0), one_mul]
  -- step 3: compare with the reflected field
  have hpt : ∀ z ∈ ball (0 : E) ρt ∩ halfSpace ν, gW (x₀ + M z) - c = adjMi (F z - ct) := by
    intro z hz
    have hzB : z ∈ Bt := ⟨ball_subset_closedBall (ball_subset_ball hρtR hz.1), hz.2⟩
    have hFz : F z = adjM (gW (x₀ + M z)) - q := by
      have h0 : 0 ≤ ⟪z, ν⟫ := hz.2
      rw [hF]
      simp only [reflectField, h0, ite_true]
      rw [gradientWithin_sub_inner q (huBt z hzB) (hwT.1.differentiableOn one_ne_zero z hzB),
        hgT z hzB]
    rw [hFz, hc, map_sub, map_sub, map_add, hinv]
    abel
  have hFLρ : MemLp F 2 (volume.restrict (ball 0 ρt)) :=
    hFL.mono_measure (Measure.restrict_mono (ball_subset_ball hρtR) le_rfl)
  have hFi : Integrable (fun z ↦ ‖F z - ct‖ ^ 2) (volume.restrict (ball 0 ρt)) :=
    integrable_norm_sq (hFLρ.sub (memLp_const ct))
  have hmBH : MeasurableSet (ball (0 : E) ρt ∩ halfSpace ν) :=
    measurableSet_ball.inter (measurableSet_halfSpace ν)
  have hs3 : ∫ z in ball 0 ρt ∩ halfSpace ν, ‖gW (x₀ + M z) - c‖ ^ 2 ≤
      (1 / l) ^ 2 * ∫ z in ball 0 ρt, ‖F z - ct‖ ^ 2 := by
    rw [setIntegral_congr_fun hmBH (g := fun z ↦ ‖adjMi (F z - ct)‖ ^ 2)
      fun z hz ↦ by simp only [hpt z hz]]
    calc ∫ z in ball 0 ρt ∩ halfSpace ν, ‖adjMi (F z - ct)‖ ^ 2
        ≤ ∫ z in ball 0 ρt ∩ halfSpace ν, (1 / l) ^ 2 * ‖F z - ct‖ ^ 2 := by
          refine integral_mono ?_ ((hFi.const_mul _).mono_measure
            (Measure.restrict_mono inter_subset_left le_rfl)) fun z ↦ ?_
          · exact (integrable_norm_sq (adjMi.lipschitzWith.comp_memLp (by simp)
              (hFLρ.sub (memLp_const ct)))).mono_measure
              (Measure.restrict_mono inter_subset_left le_rfl)
          · calc ‖adjMi (F z - ct)‖ ^ 2 ≤ (‖adjMi‖ * ‖F z - ct‖) ^ 2 :=
                  pow_le_pow_left₀ (norm_nonneg _) (adjMi.le_opNorm _) 2
              _ ≤ (1 / l * ‖F z - ct‖) ^ 2 := by gcongr
              _ = (1 / l) ^ 2 * ‖F z - ct‖ ^ 2 := by ring
      _ = (1 / l) ^ 2 * ∫ z in ball 0 ρt ∩ halfSpace ν, ‖F z - ct‖ ^ 2 := integral_const_mul _ _
      _ ≤ (1 / l) ^ 2 * ∫ z in ball 0 ρt, ‖F z - ct‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (setIntegral_mono_set hFi
            (Eventually.of_forall fun _ ↦ sq_nonneg _) inter_subset_left.eventuallyLE)
            (by positivity)
  have hdet := abs_det_le_pow_of_norm_le hs hMn
  have hψt0 : 0 ≤ ∫ z in ball 0 ρt, ‖F z - ct‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hl2 : l ^ 2 = lam := Real.sq_sqrt hlam.le
  have hρtb : ρt ^ b = ρ ^ b * l ^ (-b) := by
    rw [hρt, Real.div_rpow hρ.le hl.le, Real.rpow_neg hl.le, div_eq_mul_inv]
  calc _ ≤ ∫ y in T '' ball 0 ρt ∩ halfSpace ν, ‖gW y - c‖ ^ 2 := hs1
    _ = |LinearMap.det (M : E →ₗ[ℝ] E)| *
          ∫ z in ball 0 ρt ∩ halfSpace ν, ‖gW (x₀ + M z) - c‖ ^ 2 := hs2
    _ ≤ s ^ d * ((1 / l) ^ 2 * ∫ z in ball 0 ρt, ‖F z - ct‖ ^ 2) := by
        gcongr
    _ ≤ s ^ d * ((1 / l) ^ 2 * (Cd * ρt ^ b * Q * (3 * P ^ 2 * X))) := by
        gcongr
    _ = _ := by
        rw [hρtb, div_pow, one_pow, hl2, hX]
        ring

end BasicElliptic.Div
