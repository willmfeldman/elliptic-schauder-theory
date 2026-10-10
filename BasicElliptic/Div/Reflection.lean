/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Div
public import BasicElliptic.Div.Boundary.HalfBall
public import BasicElliptic.Div.Projection.GradientField
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Even reflection of conormal weak solutions

`Div.IsConormalSolOn.evenReflect` proves `Div.EvenReflectStatement`:
if the centre `x` lies on the flat part and `w` is a conormal weak solution on `halfBall ν x r`
with bounded measurable `a`, `G`, `f` (no continuity, no symmetry), then `evenExt ν w` is a weak
solution on `ball x r` with explicit gradient field `reflectField ν (gradientWithin w _)` for the
reflected data `reflectCoeff ν a`, `reflectField ν G`, `evenExt ν f`.

## Proof

Write `R = reflect ν` and `B⁺ = halfBall ν x r`.

* **Gradient.** Off the flat part (a null set, `volume_flatPart`) `evenExt ν w` is `w` or `w ∘ R`
  near the point, and `∇(w ∘ R)(y) = R ∇w(R y)` (`hasGradientAt_comp_reflect`).
* **Weak identity.** For an integrand `g`, split `ball x r` into `ball ∩ {⟪·, ν⟫ ≥ 0}` and its
  complement and change variables by the measure-preserving involution `R` on the latter:
  `∫_{B_r} g = ∫_{B⁺} g + ∫_{B⁺} g ∘ R` (up to null sets). On the upper half the reflected data
  are the original data; on the lower half `R a(z) R (R ∇w(z)) = R a(z) ∇w(z)`, and
  `⟪R u, ∇φ(R z)⟫ = ⟪u, ∇(φ ∘ R)(z)⟫`. Hence the left side for `φ` equals the conormal left side
  for the test `φ + φ ∘ R ∈ C¹_c(B_r)`, which need **not** vanish on the flat part; the right
  sides match in the same way.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Splitting a ball centred on the flat part into the upper half and the reflected lower half. -/
theorem setIntegral_ball_eq_halfBall_add_reflect {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    {g : E → ℝ} (h1 : IntegrableOn g (ball x r ∩ halfSpace ν))
    (h2 : IntegrableOn (fun z ↦ g (reflect ν z)) (ball x r ∩ openHalfSpace ν)) :
    IntegrableOn g (ball x r) ∧
      ∫ y in ball x r, g y =
        (∫ y in halfBall ν x r, g y) + ∫ y in ball x r ∩ openHalfSpace ν, g (reflect ν y) := by
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have hpre : reflect ν ⁻¹' (ball x r \ halfSpace ν) = ball x r ∩ openHalfSpace ν := by
    ext z
    simp only [mem_preimage, Set.mem_sdiff, mem_inter_iff, mem_halfSpace, mem_openHalfSpace,
      reflect_mem_ball hν hx, inner_reflect hν, not_le, neg_neg_iff_pos]
  have hmp : MeasurePreserving (reflect ν) volume volume := (reflect ν).measurePreserving
  have hme : MeasurableEmbedding (reflect ν) := (reflect ν).toHomeomorph.measurableEmbedding
  have h2' : IntegrableOn g (ball x r \ halfSpace ν) := by
    rw [← hmp.integrableOn_comp_preimage hme, hpre]
    exact h2
  have hint : IntegrableOn g (ball x r) := by
    rw [← inter_union_sdiff (ball x r) (halfSpace ν)]
    exact h1.union h2'
  refine ⟨hint, ?_⟩
  rw [← integral_inter_add_sdiff (measurableSet_halfSpace ν) hint,
    setIntegral_congr_set (ball_inter_halfSpace_ae_eq hν0 x r),
    ← hmp.setIntegral_preimage_emb hme g (ball x r \ halfSpace ν), hpre]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Off the flat part, the reflected within-gradient is the gradient of the even extension. -/
theorem hasGradientAt_evenExt {ν x y : E} {r : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    (hw : ContDiffOn ℝ 1 w (halfBall ν x r)) (hyB : y ∈ ball x r) (hyF : y ∉ flatPart ν) :
    HasGradientAt (evenExt ν w) (reflectField ν (gradientWithin w (halfBall ν x r)) y) y := by
  set R := reflect ν with hR
  set gW := gradientWithin w (halfBall ν x r)
  rcases lt_or_gt_of_ne (show ⟪y, ν⟫ ≠ 0 from hyF) with hneg | hpos
  · have hRy : R y ∈ ball x r ∩ openHalfSpace ν :=
      ⟨(reflect_mem_ball hν hx).2 hyB, by
        rw [mem_openHalfSpace, hR, inner_reflect hν]; linarith⟩
    have h1 := hasGradientAt_comp_reflect ν (hasGradientAt_of_mem_ball_inter hw hRy)
    have hev : evenExt ν w =ᶠ[𝓝 y] fun z ↦ w (R z) := by
      filter_upwards [(isOpen_lt (continuous_id.inner continuous_const)
        continuous_const).mem_nhds hneg] with z hz
      have hz' : ¬ 0 ≤ ⟪z, ν⟫ := not_le.2 hz
      simp [evenExt, fold, hz', hR]
    have hF : reflectField ν gW y = R (gW (R y)) := by
      simp [reflectField, not_le.2 hneg, hR]
    rw [hF]
    exact HasFDerivAt.congr_of_eventuallyEq h1 hev
  · have h1 := hasGradientAt_of_mem_ball_inter hw ⟨hyB, hpos⟩
    have hev : evenExt ν w =ᶠ[𝓝 y] w := by
      filter_upwards [(isOpen_lt continuous_const
        (continuous_id.inner continuous_const)).mem_nhds hpos] with z hz
      have hz' : 0 ≤ ⟪z, ν⟫ := le_of_lt hz
      simp [evenExt, fold, hz']
    have hF : reflectField ν gW y = gW y := by simp [reflectField, hpos.le]
    rw [hF]
    exact HasFDerivAt.congr_of_eventuallyEq h1 hev

variable (E) in
/-- **Even reflection with measurable coefficients** (`Div.EvenReflectStatement`). -/
theorem Div.IsConormalSolOn.evenReflect : Div.EvenReflectStatement E := by
  intro ν x r Λ MG Mf a G f w hν hr hx ha haΛ hG hGM hf hfM hsol
  set R := reflect ν with hR
  set B := halfBall ν x r with hB
  set gW := gradientWithin w B with hgW
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have hxr : -r < ⟪x, ν⟫ := by rw [hx]; linarith
  have hBm : MeasurableSet B := measurableSet_halfBall ν x r
  have hgc : ContinuousOn gW B := continuousOn_gradientWithin_halfBall hν hr hxr hsol.1
  obtain ⟨Mw, hMw⟩ := (isCompact_halfBall ν x r).exists_bound_of_continuousOn hgc
  -- lower half: `R y` lies in the open upper half
  have hlow : ∀ z ∈ ball x r ∩ openHalfSpace ν, ¬ 0 ≤ ⟪R z, ν⟫ := fun z hz ↦ by
    rw [hR, inner_reflect hν, not_le, neg_neg_iff_pos]; exact hz.2
  have hupB : ball x r ∩ openHalfSpace ν ⊆ B := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, mem_halfSpace.2 (mem_openHalfSpace.1 hz.2).le⟩
  have hupB' : ball x r ∩ halfSpace ν ⊆ B := fun z hz ↦ ⟨ball_subset_closedBall hz.1, hz.2⟩
  refine ⟨?_, ?_⟩
  · -- the reflected field is the gradient of the even extension off the flat part
    have hnull : ∀ᵐ y ∂(volume : Measure E), y ∉ flatPart ν :=
      measure_eq_zero_iff_ae_notMem.1 (volume_flatPart hν0)
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hnull] with y hyB hyF
    exact hasGradientAt_evenExt hν hx hsol.1 hyB hyF
  · intro φ hφ
    -- integrability of the three integrands against a test function on the half ball
    have hint : ∀ χ : E → ℝ, IsTestFn (ball x r) χ →
        IntegrableOn (fun y ↦ ⟪a y (gW y), ∇ χ y⟫) B ∧
        IntegrableOn (fun y ↦ ⟪G y, ∇ χ y⟫) B ∧ IntegrableOn (fun y ↦ f y * χ y) B := by
      intro χ hχ
      have hχc : Continuous (∇ χ) :=
        (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hχ.1.continuous_fderiv one_ne_zero)
      obtain ⟨Mχ, hMχ⟩ := (isCompact_halfBall ν x r).exists_bound_of_continuousOn
        hχc.continuousOn
      obtain ⟨Mχ', hMχ'⟩ := (isCompact_halfBall ν x r).exists_bound_of_continuousOn
        hχ.1.continuous.continuousOn
      have hgm : AEStronglyMeasurable gW (volume.restrict B) := hgc.aestronglyMeasurable hBm
      have hχm : AEStronglyMeasurable (∇ χ) (volume.restrict B) := hχc.aestronglyMeasurable
      refine ⟨?_, ?_, ?_⟩
      · refine integrableOn_halfBall_of_bound (M := Λ * Mw * Mχ) ?_ fun y hy ↦ ?_
        · have h : AEStronglyMeasurable (fun y ↦ a y (gW y)) (volume.restrict B) :=
            (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ ha hgm
          exact h.inner hχm
        · calc ‖⟪a y (gW y), ∇ χ y⟫‖ ≤ ‖a y (gW y)‖ * ‖∇ χ y‖ := by
                rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _
            _ ≤ (‖a y‖ * ‖gW y‖) * ‖∇ χ y‖ :=
                mul_le_mul_of_nonneg_right ((a y).le_opNorm _) (norm_nonneg _)
            _ ≤ (Λ * Mw) * Mχ := by
                have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (haΛ y hy)
                have hMw0 : 0 ≤ Mw := (norm_nonneg _).trans (hMw y hy)
                exact mul_le_mul (mul_le_mul (haΛ y hy) (hMw y hy) (norm_nonneg _) hΛ)
                  (hMχ y hy) (norm_nonneg _) (mul_nonneg hΛ hMw0)
      · refine integrableOn_halfBall_of_bound (M := MG * Mχ) (hG.inner hχm) fun y hy ↦ ?_
        calc ‖⟪G y, ∇ χ y⟫‖ ≤ ‖G y‖ * ‖∇ χ y‖ := by
              rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _
          _ ≤ MG * Mχ := mul_le_mul (hGM y hy) (hMχ y hy) (norm_nonneg _)
              ((norm_nonneg _).trans (hGM y hy))
      · refine integrableOn_halfBall_of_bound (M := Mf * Mχ')
          (hf.mul hχ.1.continuous.aestronglyMeasurable) fun y hy ↦ ?_
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hfM y hy) (hMχ' y hy) (norm_nonneg _) ((abs_nonneg _).trans (hfM y hy))
    -- the reflected test function
    set φR : E → ℝ := fun z ↦ φ (R z) with hφRdef
    have hφR : IsTestFn (ball x r) φR := IsTestFn.comp_reflect hν hx hφ
    have hgradR : ∀ z, ∇ φR z = R (∇ φ (R z)) := fun z ↦
      (hasGradientAt_comp_reflect ν
        ((hφ.1.differentiable one_ne_zero (R z)).hasGradientAt)).gradient
    set ψ : E → ℝ := fun z ↦ φ z + φR z with hψdef
    have hψ : IsTestFn (ball x r) ψ := by
      refine ⟨hφ.1.add hφR.1, hφ.2.1.add hφR.2.1, ?_⟩
      exact (tsupport_add φ φR).trans (union_subset hφ.2.2 hφR.2.2)
    have hgradψ : ∀ z, ∇ ψ z = ∇ φ z + ∇ φR z := fun z ↦ by
      simp only [gradient, hψdef]
      rw [fderiv_fun_add (hφ.1.differentiable one_ne_zero z) (hφR.1.differentiable one_ne_zero z),
        map_add]
    obtain ⟨hA1, hG1, hF1⟩ := hint φ hφ
    obtain ⟨hA2, hG2, hF2⟩ := hint φR hφR
    have hconormal := hsol.2 ψ hψ
    -- pointwise identities on the two halves
    have hup : ∀ y ∈ ball x r ∩ halfSpace ν, reflectCoeff ν a y = a y ∧
        reflectField ν gW y = gW y ∧ reflectField ν G y = G y ∧ evenExt ν f y = f y :=
      fun y hy ↦ by
        have h0 : 0 ≤ ⟪y, ν⟫ := hy.2
        simp [reflectCoeff, reflectField, evenExt, fold, h0]
    have hdown : ∀ z ∈ ball x r ∩ openHalfSpace ν,
        ⟪reflectCoeff ν a (R z) (reflectField ν gW (R z)), ∇ φ (R z)⟫ =
          ⟪a z (gW z), ∇ φR z⟫ ∧
        ⟪reflectField ν G (R z), ∇ φ (R z)⟫ = ⟪G z, ∇ φR z⟫ ∧
        evenExt ν f (R z) * φ (R z) = f z * φR z := fun z hz ↦ by
      have h0 : ¬ 0 ≤ ⟪reflect ν z, ν⟫ := hlow z hz
      simp only [reflectCoeff, reflectField, evenExt, fold, h0, ite_false, hR,
        reflect_reflect, ContinuousLinearMap.comp_apply, hgradR, ContinuousLinearEquiv.coe_coe]
      refine ⟨?_, inner_reflect_left _ _ _, rfl⟩
      change ⟪reflect ν (a z (reflect ν (reflect ν (gW z)))), ∇ φ (reflect ν z)⟫ = _
      rw [reflect_reflect, inner_reflect_left]
    -- split each integral over the ball
    have hsplitA := setIntegral_ball_eq_halfBall_add_reflect hν hx
      (g := fun y ↦ ⟪reflectCoeff ν a y (reflectField ν gW y), ∇ φ y⟫)
      ((hA1.mono_set hupB').congr_fun (fun y hy ↦ by
        simp only [(hup y hy).1, (hup y hy).2.1]) (measurableSet_ball.inter
          (measurableSet_halfSpace ν)))
      ((hA2.mono_set hupB).congr_fun (fun z hz ↦ (hdown z hz).1.symm)
        (measurableSet_ball.inter (measurableSet_openHalfSpace ν)))
    have hsplitG := setIntegral_ball_eq_halfBall_add_reflect hν hx
      (g := fun y ↦ ⟪reflectField ν G y, ∇ φ y⟫)
      ((hG1.mono_set hupB').congr_fun (fun y hy ↦ by
        simp only [(hup y hy).2.2.1]) (measurableSet_ball.inter
          (measurableSet_halfSpace ν)))
      ((hG2.mono_set hupB).congr_fun (fun z hz ↦ (hdown z hz).2.1.symm)
        (measurableSet_ball.inter (measurableSet_openHalfSpace ν)))
    have hsplitF := setIntegral_ball_eq_halfBall_add_reflect hν hx
      (g := fun y ↦ evenExt ν f y * φ y)
      ((hF1.mono_set hupB').congr_fun (fun y hy ↦ by
        simp only [(hup y hy).2.2.2]) (measurableSet_ball.inter
          (measurableSet_halfSpace ν)))
      ((hF2.mono_set hupB).congr_fun (fun z hz ↦ (hdown z hz).2.2.symm)
        (measurableSet_ball.inter (measurableSet_openHalfSpace ν)))
    -- reassemble
    have hset := (halfBall_ae_eq hν0 x r).symm
    have hmo : MeasurableSet (ball x r ∩ openHalfSpace ν) :=
      measurableSet_ball.inter (measurableSet_openHalfSpace ν)
    have hB0 : ∀ y ∈ B, 0 ≤ ⟪y, ν⟫ := fun y hy ↦ hy.2
    have eA : ∫ y in ball x r, ⟪reflectCoeff ν a y (reflectField ν gW y), ∇ φ y⟫ =
        (∫ y in B, ⟪a y (gW y), ∇ φ y⟫) + ∫ y in B, ⟪a y (gW y), ∇ φR y⟫ := by
      rw [hsplitA.2, setIntegral_congr_fun hmo (fun z hz ↦ (hdown z hz).1),
        setIntegral_congr_set hset]
      congr 1
      refine setIntegral_congr_fun hBm fun y hy ↦ ?_
      simp [reflectCoeff, reflectField, hB0 y hy]
    have eG : ∫ y in ball x r, ⟪reflectField ν G y, ∇ φ y⟫ =
        (∫ y in B, ⟪G y, ∇ φ y⟫) + ∫ y in B, ⟪G y, ∇ φR y⟫ := by
      rw [hsplitG.2, setIntegral_congr_fun hmo (fun z hz ↦ (hdown z hz).2.1),
        setIntegral_congr_set hset]
      congr 1
      refine setIntegral_congr_fun hBm fun y hy ↦ ?_
      simp [reflectField, hB0 y hy]
    have eF : ∫ y in ball x r, evenExt ν f y * φ y =
        (∫ y in B, f y * φ y) + ∫ y in B, f y * φR y := by
      rw [hsplitF.2, setIntegral_congr_fun hmo (fun z hz ↦ (hdown z hz).2.2),
        setIntegral_congr_set hset]
      congr 1
      refine setIntegral_congr_fun hBm fun y hy ↦ ?_
      simp [evenExt, fold, hB0 y hy]
    have eA2 : ∫ y in B, ⟪a y (gW y), ∇ ψ y⟫ =
        (∫ y in B, ⟪a y (gW y), ∇ φ y⟫) + ∫ y in B, ⟪a y (gW y), ∇ φR y⟫ := by
      rw [← integral_add hA1 hA2]
      congr 1; ext y; rw [hgradψ, inner_add_right]
    have eG2 : ∫ y in B, ⟪G y, ∇ ψ y⟫ =
        (∫ y in B, ⟪G y, ∇ φ y⟫) + ∫ y in B, ⟪G y, ∇ φR y⟫ := by
      rw [← integral_add hG1 hG2]
      congr 1; ext y; rw [hgradψ, inner_add_right]
    have eF2 : ∫ y in B, f y * ψ y = (∫ y in B, f y * φ y) + ∫ y in B, f y * φR y := by
      rw [← integral_add hF1 hF2]
      congr 1; ext y; rw [hψdef, mul_add]
    rw [eA, eG, eF]
    linarith [hconormal, eA2, eG2, eF2]

/-! ### The reflected gradient is weakly curl-free -/

/-- **Curl-freeness of the reflected gradient**. If `w ∈ C¹(halfBall ν x r)` with
`x` on the flat part, then `reflectField ν (gradientWithin w _)` is weakly curl-free on
`ball x r`.

Proof: `evenExt ν w` is Lipschitz on `closedBall x r` (`w` is Lipschitz on the convex compact half
ball and `fold ν` is `1`-Lipschitz); a McShane extension `g` is globally Lipschitz and its line
derivative is `⟪F, u⟫` a.e. on the ball (`hasGradientAt_evenExt`). Rademacher's integration by
parts `integral_lineDeriv_mul_eq` moves the derivative onto the test function, and the symmetry of
second derivatives finishes. No integration by parts on the half space is needed. -/
theorem isWeakCurlFree_reflectField {ν x : E} {r : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1)
    (hx : ⟪x, ν⟫ = 0) (hw : ContDiffOn ℝ 1 w (halfBall ν x r)) :
    Div.IsWeakCurlFree (reflectField ν (gradientWithin w (halfBall ν x r))) (ball x r) := by
  set F := reflectField ν (gradientWithin w (halfBall ν x r)) with hF
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  obtain ⟨K, hK⟩ := hw.exists_lipschitzOnWith one_ne_zero (convex_halfBall ν x r)
    (isCompact_halfBall ν x r)
  have hW : LipschitzOnWith K (evenExt ν w) (closedBall x r) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
    exact (hK.dist_le_mul _ (fold_mem_halfBall hν hx hy) _ (fold_mem_halfBall hν hx hz)).trans
      (mul_le_mul_of_nonneg_left (dist_fold_le hν y z) K.coe_nonneg)
  obtain ⟨g, hg, hgW⟩ := hW.extend_real
  have hline : ∀ᵐ y ∂(volume.restrict (ball x r)), ∀ u, lineDeriv ℝ g y u = ⟪F y, u⟫ := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (volume_flatPart hν0))] with y hyB hyF u
    have h1 := hasGradientAt_evenExt hν hx hw hyB hyF
    have hev : g =ᶠ[𝓝 y] evenExt ν w := Filter.eventually_of_mem (isOpen_ball.mem_nhds hyB)
      fun z hz ↦ (hgW (ball_subset_closedBall hz)).symm
    have h2 : HasFDerivAt g (InnerProductSpace.toDual ℝ E (F y)) y :=
      (hasGradientAt_iff_hasFDerivAt.1 h1).congr_of_eventuallyEq hev
    rw [(h2.hasLineDerivAt u).lineDeriv, InnerProductSpace.toDual_apply_apply]
  have key : ∀ ψ, Div.IsSmoothTestFn (ball x r) ψ → ∀ u v : E,
      ∫ y in ball x r, ⟪F y, u⟫ * fderiv ℝ ψ y v =
        -∫ y, fderiv ℝ (fun z ↦ fderiv ℝ ψ z v) y u * g y := by
    intro ψ hψ u v
    set h : E → ℝ := fun z ↦ fderiv ℝ ψ z v with hh
    have hhc : ContDiff ℝ 1 h := (hψ.1.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const
    have hhs : HasCompactSupport h := hψ.2.1.fderiv_apply (𝕜 := ℝ) v
    obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hhs hhc one_ne_zero
    have h0 : ∀ y ∉ ball x r, h y = 0 := fun y hy ↦ by
      by_contra hne
      have : fderiv ℝ ψ y ≠ 0 := fun h0 ↦ hne (by rw [hh]; simp [h0])
      exact hy (hψ.2.2 (support_fderiv_subset ℝ this))
    calc ∫ y in ball x r, ⟪F y, u⟫ * h y = ∫ y in ball x r, lineDeriv ℝ g y u * h y :=
          integral_congr_ae (hline.mono fun y hy ↦ by simp only [hy u])
      _ = ∫ y, lineDeriv ℝ g y u * h y :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [h0 y hy, mul_zero]
      _ = ∫ y, lineDeriv ℝ h y (-u) * g y := hg.integral_lineDeriv_mul_eq hD hhs u
      _ = -∫ y, fderiv ℝ h y u * g y := by
          rw [← integral_neg]
          congr 1
          ext y
          rw [(hhc.differentiable one_ne_zero y).lineDeriv_eq_fderiv, map_neg, neg_mul]
  intro ψ hψ u v
  rw [key ψ hψ u v, key ψ hψ v u]
  congr 2
  ext y
  rw [Div.fderiv_fderiv_apply_comm hψ.1]

/-! ### Pointwise Hölder bounds and measurability of the reflected data -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The reflected coefficients keep a pointwise Hölder bound at a centre on the flat part, relative
to the identity (`R 1 R = 1`). -/
theorem norm_reflectCoeff_sub_one_le {ν x : E} {r K α : ℝ} {a : E → E →L[ℝ] E}
    (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    (ha : ∀ y ∈ halfBall ν x r, ‖a y - 1‖ ≤ K * dist y x ^ α) :
    ∀ y ∈ ball x r, ‖reflectCoeff ν a y - 1‖ ≤ K * dist y x ^ α := by
  intro y hy
  by_cases h : 0 ≤ ⟪y, ν⟫
  · simp only [reflectCoeff, h, ite_true]
    exact ha y ⟨ball_subset_closedBall hy, h⟩
  · simp only [reflectCoeff, h, ite_false]
    have hRy : reflect ν y ∈ halfBall ν x r :=
      ⟨ball_subset_closedBall ((reflect_mem_ball hν hx).2 hy), by
        rw [mem_halfSpace, inner_reflect hν]; linarith [not_le.1 h]⟩
    set Rc : E →L[ℝ] E := (reflect ν : E →L[ℝ] E) with hRc
    have hRn : ‖Rc‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
      rw [one_mul]; exact (LinearIsometryEquiv.norm_map _ v).le
    have heq : Rc ∘L a (reflect ν y) ∘L Rc - 1 = Rc ∘L (a (reflect ν y) - 1) ∘L Rc := by
      ext v
      simp [hRc]
    rw [heq]
    calc ‖Rc ∘L (a (reflect ν y) - 1) ∘L Rc‖ ≤ ‖Rc‖ * (‖a (reflect ν y) - 1‖ * ‖Rc‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖a (reflect ν y) - 1‖ * 1) := by gcongr
      _ ≤ K * dist y x ^ α := by
          rw [one_mul, mul_one, ← dist_reflect_eq hν hx y]; exact ha _ hRy

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The reflected field keeps a pointwise Hölder bound at a centre on the flat part, relative to a
tangential value `g₀` (`R g₀ = g₀`). -/
theorem norm_reflectField_sub_le {ν x g₀ : E} {r K α : ℝ} {G : E → E}
    (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) (hg₀ : ⟪g₀, ν⟫ = 0)
    (hG : ∀ y ∈ halfBall ν x r, ‖G y - g₀‖ ≤ K * dist y x ^ α) :
    ∀ y ∈ ball x r, ‖reflectField ν G y - g₀‖ ≤ K * dist y x ^ α := by
  intro y hy
  by_cases h : 0 ≤ ⟪y, ν⟫
  · simp only [reflectField, h, ite_true]
    exact hG y ⟨ball_subset_closedBall hy, h⟩
  · simp only [reflectField, h, ite_false]
    have hRy : reflect ν y ∈ halfBall ν x r :=
      ⟨ball_subset_closedBall ((reflect_mem_ball hν hx).2 hy), by
        rw [mem_halfSpace, inner_reflect hν]; linarith [not_le.1 h]⟩
    have hRg : reflect ν g₀ = g₀ := reflect_eq_self_of_mem_flatPart hν hg₀
    calc ‖reflect ν (G (reflect ν y)) - g₀‖ = ‖reflect ν (G (reflect ν y) - g₀)‖ := by
          rw [map_sub, hRg]
      _ = ‖G (reflect ν y) - g₀‖ := LinearIsometryEquiv.norm_map _ _
      _ ≤ K * dist y x ^ α := by rw [← dist_reflect_eq hν hx y]; exact hG _ hRy

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Sup bounds pass to the reflected field. -/
theorem norm_reflectField_le {ν x : E} {r M : ℝ} {G : E → E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    (hG : ∀ y ∈ halfBall ν x r, ‖G y‖ ≤ M) : ∀ y ∈ ball x r, ‖reflectField ν G y‖ ≤ M := by
  intro y hy
  by_cases h : 0 ≤ ⟪y, ν⟫
  · simp only [reflectField, h, ite_true]
    exact hG y ⟨ball_subset_closedBall hy, h⟩
  · simp only [reflectField, h, ite_false]
    rw [LinearIsometryEquiv.norm_map]
    exact hG _ ⟨ball_subset_closedBall ((reflect_mem_ball hν hx).2 hy), by
      rw [mem_halfSpace, inner_reflect hν]; linarith [not_le.1 h]⟩

/-- Measurability of a reflected quantity: `p` on the upper half, `T ∘ p ∘ R` below. -/
private theorem aestronglyMeasurable_reflect {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    {p : E → X} {T : X → X} (hT : Continuous T)
    (hp : AEStronglyMeasurable p (volume.restrict (halfBall ν x r))) :
    AEStronglyMeasurable (fun y ↦ if 0 ≤ ⟪y, ν⟫ then p y else T (p (reflect ν y)))
      (volume.restrict (ball x r)) := by
  classical
  have hfun : (fun y ↦ if 0 ≤ ⟪y, ν⟫ then p y else T (p (reflect ν y))) =
      (halfSpace ν).piecewise p (fun y ↦ T (p (reflect ν y))) := by
    funext y
    by_cases h : 0 ≤ ⟪y, ν⟫ <;> simp [Set.piecewise, h]
  rw [hfun]
  refine AEStronglyMeasurable.piecewise (measurableSet_halfSpace ν) ?_ ?_
  · rw [Measure.restrict_restrict (measurableSet_halfSpace ν)]
    have hsub : halfSpace ν ∩ ball x r ⊆ halfBall ν x r := fun y hy ↦
      ⟨ball_subset_closedBall hy.2, hy.1⟩
    exact hp.mono_measure (Measure.restrict_mono hsub le_rfl)
  · rw [Measure.restrict_restrict (measurableSet_halfSpace ν).compl]
    have hpre : (halfSpace ν)ᶜ ∩ ball x r = reflect ν ⁻¹' (ball x r ∩ openHalfSpace ν) := by
      ext z
      simp only [mem_inter_iff, mem_compl_iff, mem_halfSpace, mem_preimage, mem_openHalfSpace,
        reflect_mem_ball hν hx, inner_reflect hν, not_le, neg_pos]
      tauto
    rw [hpre]
    have hmp : MeasurePreserving (reflect ν) volume volume := (reflect ν).measurePreserving
    have hme : MeasurableEmbedding (reflect ν) := (reflect ν).toHomeomorph.measurableEmbedding
    have hsub : ball x r ∩ openHalfSpace ν ⊆ halfBall ν x r := fun z hz ↦
      ⟨ball_subset_closedBall hz.1, mem_halfSpace.2 (mem_openHalfSpace.1 hz.2).le⟩
    have hp' : AEStronglyMeasurable p (volume.restrict (ball x r ∩ openHalfSpace ν)) :=
      hp.mono_measure (Measure.restrict_mono hsub le_rfl)
    exact hT.comp_aestronglyMeasurable
      (hp'.comp_measurePreserving (hmp.restrict_preimage_emb hme _))

theorem aestronglyMeasurable_reflectField {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    {G : E → E} (hG : AEStronglyMeasurable G (volume.restrict (halfBall ν x r))) :
    AEStronglyMeasurable (reflectField ν G) (volume.restrict (ball x r)) :=
  aestronglyMeasurable_reflect hν hx (reflect ν).continuous hG

theorem aestronglyMeasurable_reflectCoeff {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    {a : E → E →L[ℝ] E} (ha : AEStronglyMeasurable a (volume.restrict (halfBall ν x r))) :
    AEStronglyMeasurable (reflectCoeff ν a) (volume.restrict (ball x r)) :=
  aestronglyMeasurable_reflect hν hx (T := fun A ↦ (reflect ν : E →L[ℝ] E) ∘L A ∘L
    (reflect ν : E →L[ℝ] E)) (by fun_prop) ha

end BasicElliptic
