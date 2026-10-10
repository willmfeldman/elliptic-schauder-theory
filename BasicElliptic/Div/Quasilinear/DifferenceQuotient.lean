/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Boundary.Patch
public import BasicElliptic.Normalize.ChangeOfVariables
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Difference quotients for the quasilinear conormal problem

Let `w` be a quasilinear conormal weak solution on `halfBall ν x r`
(`Div.IsQuasilinearConormalSolOn ν Φ x r w`: `∫_{B⁺} ⟪Φ(∇w), ∇φ⟫ = 0` for `φ ∈ C¹_c(B)`).

* `Div.isQuasilinearConormalSolOn_iff`: this is the linear conormal problem
  `Div.IsConormalSolOn ν 0 (Φ ∘ ∇w) 0 x r w` (zero coefficient, flux `G = Φ(∇w)`); this lets the
  linear transport and restriction lemmas act on quasilinear solutions.
* `Div.IsQuasilinearConormalSolOn.restrict`: restriction to a smaller half ball.
* `Div.IsQuasilinearConormalSolOn.translate`: translation `w(v + ·)` by a vector `v` that preserves
  the half space on the ball in question (`⟪v, ν⟫ = 0`, or the ball lies in the open half space).
* `Div.chordCoeff Φ p q = ∫₀¹ DΦ(q + t (p - q)) dt`: then `Φ p - Φ q = chordCoeff Φ p q (p - q)`
  (`Div.sub_eq_chordCoeff_apply`), and the chord coefficient inherits symmetry, ellipticity, the
  norm bound and a Lipschitz bound from `DΦ`.
* `Div.IsQuasilinearConormalSolOn.sub`: **the difference-quotient weak identity**. If `w₁` and
  `w₂` are quasilinear conormal solutions on the same half ball, `w₁ - w₂` is a **linear**
  conormal solution with coefficient `a(y) = chordCoeff Φ (∇w₁ y) (∇w₂ y)`. With
  `w₁ = w(· + h e)`, `w₂ = w` this is the identity
  `∫_{B⁺} ⟪a_h ∇(D_h w), ∇φ⟫ = 0` for the difference quotient (up to the factor `h`).
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology Interval

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Quasilinear solutions as linear solutions -/

/-- A quasilinear conormal solution is a linear conormal solution with zero coefficient and flux
`G = Φ ∘ ∇w`. -/
theorem isQuasilinearConormalSolOn_iff {ν : E} {Φ : E → E} {x : E} {r : ℝ} {w : E → ℝ} :
    IsQuasilinearConormalSolOn ν Φ x r w ↔
      IsConormalSolOn ν 0 (fun y ↦ Φ (gradientWithin w (halfBall ν x r) y)) 0 x r w := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun φ hφ ↦ ?_⟩
    simp only [Pi.zero_apply, zero_apply, inner_zero_left, integral_zero, zero_mul, add_zero]
    exact (h2 φ hφ).symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun φ hφ ↦ ?_⟩
    have := h2 φ hφ
    simp only [Pi.zero_apply, zero_apply, inner_zero_left, integral_zero, zero_mul,
      add_zero] at this
    exact this.symm

/-- Restriction of a quasilinear conormal solution to a smaller half ball. -/
theorem IsQuasilinearConormalSolOn.restrict {ν : E} {Φ : E → E} {x : E} {r : ℝ} {w : E → ℝ}
    (hν : ‖ν‖ = 1) (h : IsQuasilinearConormalSolOn ν Φ x r w) {y : E} {s : ℝ} (hs : 0 < s)
    (hy : -s < ⟪y, ν⟫) (hsub : closedBall y s ⊆ closedBall x r) (hsub' : ball y s ⊆ ball x r) :
    IsQuasilinearConormalSolOn ν Φ y s w := by
  have h1 := (isQuasilinearConormalSolOn_iff.1 h).restrict_halfBall hν hs hy hsub hsub'
  refine isQuasilinearConormalSolOn_iff.2 ⟨h1.1, fun φ hφ ↦ ?_⟩
  have key := h1.2 φ hφ
  have hsub'' : halfBall ν y s ⊆ halfBall ν x r := inter_subset_inter_left _ hsub
  have hu := uniqueDiffOn_halfBall hν hs hy
  have hc : ∫ z in halfBall ν y s, ⟪Φ (gradientWithin w (halfBall ν y s) z), ∇ φ z⟫ =
      ∫ z in halfBall ν y s, ⟪Φ (gradientWithin w (halfBall ν x r) z), ∇ φ z⟫ := by
    refine setIntegral_congr_fun (measurableSet_halfBall ν y s) fun z hz ↦ ?_
    rw [gradientWithin_eq_of_subset hsub'' (hu z hz)
      ((h.1.differentiableOn one_ne_zero) z (hsub'' hz))]
  rw [hc]
  exact key

omit [MeasurableSpace E] [BorelSpace E] in
/-- The within-gradient of a translate. -/
theorem gradientWithin_translate {ν z v : E} {s : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (hs : 0 < s)
    (hz : -s < ⟪z, ν⟫) {S : Set E} (hS : ∀ y ∈ halfBall ν z s, v + y ∈ S)
    (hw : DifferentiableOn ℝ w S)
    (hsub : (fun y ↦ v + y) '' halfBall ν z s ⊆ S) {y : E} (hy : y ∈ halfBall ν z s) :
    gradientWithin (fun y ↦ w (v + y)) (halfBall ν z s) y = gradientWithin w S (v + y) := by
  have hT : HasFDerivWithinAt (fun y ↦ w (v + y)) (fderivWithin ℝ w S (v + y))
      (halfBall ν z s) y := by
    have h1 := (hw (v + y) (hS y hy)).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt (fun y : E ↦ v + y) (ContinuousLinearMap.id ℝ E)
        (halfBall ν z s) y := ((hasFDerivAt_id y).const_add v).hasFDerivWithinAt
    have := h1.comp y h2 (fun u hu ↦ hsub ⟨u, hu, rfl⟩)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  rw [gradientWithin, gradientWithin, hT.fderivWithin (uniqueDiffOn_halfBall hν hs hz y hy)]

/-- Translation invariance of set integrals. -/
theorem setIntegral_comp_add_left {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E) (g : E → F) (S : Set E) :
    ∫ y in (fun y ↦ v + y) ⁻¹' S, g (v + y) = ∫ u in S, g u := by
  exact (measurePreserving_add_left volume v).setIntegral_preimage_emb
    (measurableEmbedding_addLeft v) g S

/-- **Translation of a quasilinear conormal solution** by a vector `v` that preserves the half
space on `closedBall z s` (`hcompat`; e.g. `⟪v, ν⟫ = 0`): `w(v + ·)` is a solution on
`halfBall ν z s` when `w` is one on `halfBall ν x r ⊇ halfBall ν (v + z) s`. -/
theorem IsQuasilinearConormalSolOn.translate {ν : E} {Φ : E → E} {x : E} {r : ℝ} {w : E → ℝ}
    (hν : ‖ν‖ = 1) (h : IsQuasilinearConormalSolOn ν Φ x r w) {z v : E} {s : ℝ} (hs : 0 < s)
    (hz : -s < ⟪z, ν⟫) (hzv : -s < ⟪v + z, ν⟫) (hsub : closedBall (v + z) s ⊆ closedBall x r)
    (hsub' : ball (v + z) s ⊆ ball x r)
    (hcompat : ∀ y ∈ closedBall z s, (0 ≤ ⟪v + y, ν⟫ ↔ 0 ≤ ⟪y, ν⟫)) :
    IsQuasilinearConormalSolOn ν Φ z s (fun y ↦ w (v + y)) := by
  have h1 := h.restrict hν hs hzv hsub hsub'
  set B := halfBall ν z s with hB
  set B' := halfBall ν (v + z) s with hB'
  have hdist : ∀ y, dist (v + y) (v + z) = dist y z := fun y ↦ by
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub]
  have hpre : (fun y ↦ v + y) ⁻¹' B' = B := by
    ext y
    simp only [hB', hB, mem_preimage, mem_halfBall, hdist]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hcompat y (mem_closedBall.2 h1)).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hcompat y (mem_closedBall.2 h1)).2 h2⟩
  have hmaps : ∀ y ∈ B, v + y ∈ B' := fun y hy ↦ by
    rw [← hpre] at hy; exact hy
  have hBu := uniqueDiffOn_halfBall hν hs hz
  refine ⟨h1.1.comp (contDiff_const.add contDiff_id).contDiffOn hmaps, fun φ hφ ↦ ?_⟩
  -- the translated test function
  set ψ : E → ℝ := fun u ↦ φ (-v + u) with hψ
  have hψt : IsTestFn (ball (v + z) s) ψ := by
    have := hφ.comp_affine (ContinuousLinearEquiv.refl ℝ E) (-v)
    have e : (fun u ↦ -v + (ContinuousLinearEquiv.refl ℝ E) u) ⁻¹' ball z s = ball (v + z) s := by
      ext u
      simp only [ContinuousLinearEquiv.coe_refl', id, mem_preimage, mem_ball, dist_eq_norm]
      rw [show -v + u - z = u - (v + z) by abel]
    rw [e] at this
    simpa using this
  have hgψ : ∀ y, ∇ ψ (v + y) = ∇ φ y := fun y ↦ by
    have := gradient_comp_affine (ContinuousLinearEquiv.refl ℝ E) (-v) (z := v + y)
      (φ := φ) (hφ.1.differentiable one_ne_zero _)
    simp only [ContinuousLinearEquiv.coe_refl', id, neg_add_cancel_left] at this
    simpa [hψ, ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.adjoint_id] using this
  have key := h1.2 ψ hψt
  have hgw : ∀ y ∈ B, gradientWithin (fun y ↦ w (v + y)) B y = gradientWithin w B' (v + y) :=
    fun y hy ↦ gradientWithin_translate hν hs hz hmaps (h1.1.differentiableOn one_ne_zero)
      (by rintro _ ⟨u, hu, rfl⟩; exact hmaps u hu) hy
  have hint := setIntegral_comp_add_left v
    (fun u ↦ ⟪Φ (gradientWithin w B' u), ∇ ψ u⟫) B'
  rw [hpre] at hint
  rw [← key, ← hint]
  refine setIntegral_congr_fun (measurableSet_halfBall ν z s) fun y hy ↦ ?_
  rw [hgψ y, show halfBall ν z s = B from rfl, hgw y hy]

/-! ### The chord coefficient -/

/-- The chord coefficient `∫₀¹ DΦ(q + t (p - q)) dt`, so that
`Φ p - Φ q = chordCoeff Φ p q (p - q)` (`sub_eq_chordCoeff_apply`). -/
@[expose] noncomputable def chordCoeff (Φ : E → E) (p q : E) : E →L[ℝ] E :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ Φ (q + t • (p - q))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The defining formula of `chordCoeff`. -/
theorem chordCoeff_eq (Φ : E → E) (p q : E) :
    chordCoeff Φ p q = ∫ t in (0 : ℝ)..1, fderiv ℝ Φ (q + t • (p - q)) := by
  rw [chordCoeff]

section Chord

variable {Φ : E → E} {U : Set E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chord_mem {K : Set E} (hK : Convex ℝ K) {p q : E} (hp : p ∈ K) (hq : q ∈ K) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : q + t • (p - q) ∈ K :=
  hK.add_smul_sub_mem hq hp ht

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem continuousOn_chord (hU : IsOpen U) (hUc : Convex ℝ U) (hΦ : ContDiffOn ℝ 1 Φ U)
    {p q : E} (hp : p ∈ U) (hq : q ∈ U) :
    ContinuousOn (fun t : ℝ ↦ fderiv ℝ Φ (q + t • (p - q))) (Icc 0 1) :=
  (hΦ.continuousOn_fderiv_of_isOpen hU le_rfl).comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    fun _ ht ↦ chord_mem hUc hp hq ht

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem intervalIntegrable_chord (hU : IsOpen U) (hUc : Convex ℝ U)
    (hΦ : ContDiffOn ℝ 1 Φ U) {p q : E} (hp : p ∈ U) (hq : q ∈ U) :
    IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ Φ (q + t • (p - q))) volume 0 1 :=
  (continuousOn_chord hU hUc hΦ hp hq).intervalIntegrable_of_Icc zero_le_one

omit [MeasurableSpace E] [BorelSpace E] in
/-- `Φ p - Φ q = chordCoeff Φ p q (p - q)` (fundamental theorem of calculus on the chord). -/
theorem sub_eq_chordCoeff_apply (hU : IsOpen U) (hUc : Convex ℝ U) (hΦ : ContDiffOn ℝ 1 Φ U)
    {p q : E} (hp : p ∈ U) (hq : q ∈ U) : Φ p - Φ q = chordCoeff Φ p q (p - q) := by
  rw [chordCoeff, ContinuousLinearMap.intervalIntegral_apply
    (intervalIntegrable_chord hU hUc hΦ hp hq)]
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ ↦ Φ (q + t • (p - q)))
      (fderiv ℝ Φ (q + t • (p - q)) (p - q)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hd : DifferentiableAt ℝ Φ (q + t • (p - q)) :=
      (hΦ.differentiableOn one_ne_zero _ (chord_mem hUc hp hq ht)).differentiableAt
        (hU.mem_nhds (chord_mem hUc hp hq ht))
    have hl : HasDerivAt (fun t : ℝ ↦ q + t • (p - q)) (p - q) t := by
      simpa using ((hasDerivAt_id t).smul_const (p - q)).const_add q
    exact hd.hasFDerivAt.comp_hasDerivAt t hl
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((continuousOn_chord hU hUc hΦ hp hq).clm_apply continuousOn_const
      |>.intervalIntegrable_of_Icc zero_le_one)]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
private theorem inner_chordCoeff_apply (hU : IsOpen U) (hUc : Convex ℝ U)
    (hΦ : ContDiffOn ℝ 1 Φ U) {p q : E} (hp : p ∈ U) (hq : q ∈ U) (ξ η : E) :
    ⟪chordCoeff Φ p q ξ, η⟫ = ∫ t in (0 : ℝ)..1, ⟪fderiv ℝ Φ (q + t • (p - q)) ξ, η⟫ := by
  have hi := intervalIntegrable_chord hU hUc hΦ hp hq
  rw [chordCoeff, ContinuousLinearMap.intervalIntegral_apply hi, real_inner_comm]
  have hi' : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ Φ (q + t • (p - q)) ξ) volume 0 1 :=
    (continuousOn_chord hU hUc hΦ hp hq).clm_apply continuousOn_const
      |>.intervalIntegrable_of_Icc zero_le_one
  have := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ η) hi'
  simp only [innerSL_apply_apply] at this
  rw [← this]
  exact intervalIntegral.integral_congr fun t _ ↦ real_inner_comm _ _

omit [MeasurableSpace E] [BorelSpace E] in
/-- The chord coefficient of a field with symmetric derivative is symmetric. -/
theorem isSymmetric_chordCoeff (hU : IsOpen U) (hUc : Convex ℝ U) (hΦ : ContDiffOn ℝ 1 Φ U)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric) {p q : E} (hp : p ∈ U)
    (hq : q ∈ U) : (chordCoeff Φ p q : E →ₗ[ℝ] E).IsSymmetric := by
  intro ξ η
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_chordCoeff_apply hU hUc hΦ hp hq, real_inner_comm (chordCoeff Φ p q η) ξ,
    inner_chordCoeff_apply hU hUc hΦ hp hq]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  have := hsym _ (chord_mem hUc hp hq ht) ξ η
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this, real_inner_comm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Ellipticity of the chord coefficient. -/
theorem le_inner_chordCoeff (hU : IsOpen U) (hUc : Convex ℝ U) (hΦ : ContDiffOn ℝ 1 Φ U)
    {lam : ℝ} (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫) {p q : E}
    (hp : p ∈ U) (hq : q ∈ U) (ξ : E) : lam * ‖ξ‖ ^ 2 ≤ ⟪chordCoeff Φ p q ξ, ξ⟫ := by
  rw [inner_chordCoeff_apply hU hUc hΦ hp hq]
  have hi : IntervalIntegrable (fun t : ℝ ↦ ⟪fderiv ℝ Φ (q + t • (p - q)) ξ, ξ⟫) volume 0 1 :=
    ((continuousOn_chord hU hUc hΦ hp hq).clm_apply continuousOn_const).inner continuousOn_const
      |>.intervalIntegrable_of_Icc zero_le_one
  have := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hi
    fun t ht ↦ hell _ (chord_mem hUc hp hq ht) ξ
  simpa using this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Norm bound for the chord coefficient. -/
theorem norm_chordCoeff_le {K : Set E} (hK : Convex ℝ K) {Λ : ℝ}
    (hΛ : ∀ p ∈ K, ‖fderiv ℝ Φ p‖ ≤ Λ) {p q : E} (hp : p ∈ K) (hq : q ∈ K) :
    ‖chordCoeff Φ p q‖ ≤ Λ := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ ↦ fderiv ℝ Φ (q + t • (p - q))) (C := Λ)
    fun t ht ↦ hΛ _ (chord_mem hK hp hq (Ioc_subset_Icc_self (by simpa using ht)))
  simpa [chordCoeff] using this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Lipschitz bound for the chord coefficient, from a Lipschitz bound for `DΦ` on a convex
`K ⊆ U`. -/
theorem norm_chordCoeff_sub_le (hU : IsOpen U) (hUc : Convex ℝ U) (hΦ : ContDiffOn ℝ 1 Φ U)
    {K : Set E} (hK : Convex ℝ K) (hKU : K ⊆ U) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ a ∈ K, ∀ b ∈ K, ‖fderiv ℝ Φ a - fderiv ℝ Φ b‖ ≤ L * ‖a - b‖) {p q p' q' : E}
    (hp : p ∈ K) (hq : q ∈ K) (hp' : p' ∈ K) (hq' : q' ∈ K) :
    ‖chordCoeff Φ p q - chordCoeff Φ p' q'‖ ≤ L * (‖p - p'‖ + ‖q - q'‖) := by
  rw [chordCoeff, chordCoeff, ← intervalIntegral.integral_sub
    (intervalIntegrable_chord hU hUc hΦ (hKU hp) (hKU hq))
    (intervalIntegrable_chord hU hUc hΦ (hKU hp') (hKU hq'))]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ ↦ fderiv ℝ Φ (q + t • (p - q)) - fderiv ℝ Φ (q' + t • (p' - q')))
    (C := L * (‖p - p'‖ + ‖q - q'‖)) fun t ht ↦ by
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using ht)
      refine (hL _ (chord_mem hK hp hq ht') _ (chord_mem hK hp' hq' ht')).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hL0
      have e : q + t • (p - q) - (q' + t • (p' - q')) = (1 - t) • (q - q') + t • (p - p') := by
        simp only [smul_sub, sub_smul, one_smul]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht'.2]),
        Real.norm_of_nonneg ht'.1]
      nlinarith [norm_nonneg (q - q'), norm_nonneg (p - p'), ht'.1, ht'.2]
  simpa using this

end Chord

/-! ### The difference-quotient weak identity -/

/-- **The difference-quotient weak identity**. If `w₁`, `w₂` are quasilinear conormal
solutions on the same half ball, with within-gradients in the open convex set `U` on which `Φ` is
`C¹`, then `w₁ - w₂` is a linear conormal solution (no data) with coefficient
`a(y) = chordCoeff Φ (∇w₁ y) (∇w₂ y) = ∫₀¹ DΦ(∇w₂ + t (∇w₁ - ∇w₂)) dt`:
`∫_{B⁺} ⟪a ∇(w₁ - w₂), ∇φ⟫ = 0` for `φ ∈ C¹_c(B)`. -/
theorem IsQuasilinearConormalSolOn.sub {ν : E} {Φ : E → E} {z : E} {s : ℝ} {U : Set E}
    {w₁ w₂ : E → ℝ} (hν : ‖ν‖ = 1) (hs : 0 < s) (hz : -s < ⟪z, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hΦ : ContDiffOn ℝ 1 Φ U) (h₁ : IsQuasilinearConormalSolOn ν Φ z s w₁)
    (h₂ : IsQuasilinearConormalSolOn ν Φ z s w₂)
    (hU₁ : ∀ y ∈ halfBall ν z s, gradientWithin w₁ (halfBall ν z s) y ∈ U)
    (hU₂ : ∀ y ∈ halfBall ν z s, gradientWithin w₂ (halfBall ν z s) y ∈ U) :
    IsConormalSolOn ν (fun y ↦ chordCoeff Φ (gradientWithin w₁ (halfBall ν z s) y)
      (gradientWithin w₂ (halfBall ν z s) y)) 0 0 z s (fun y ↦ w₁ y - w₂ y) := by
  set B := halfBall ν z s with hB
  have hBu := uniqueDiffOn_halfBall hν hs hz
  have hBc : IsCompact B := isCompact_halfBall ν z s
  have hBm : MeasurableSet B := measurableSet_halfBall ν z s
  refine ⟨h₁.1.sub h₂.1, fun φ hφ ↦ ?_⟩
  have hφc : Continuous (∇ φ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ.1.continuous_fderiv one_ne_zero)
  have hgr : ∀ y ∈ B, gradientWithin (fun y ↦ w₁ y - w₂ y) B y =
      gradientWithin w₁ B y - gradientWithin w₂ B y := fun y hy ↦ by
    rw [gradientWithin, gradientWithin, gradientWithin,
      fderivWithin_fun_sub (hBu y hy) ((h₁.1.differentiableOn one_ne_zero) y hy)
        ((h₂.1.differentiableOn one_ne_zero) y hy), map_sub]
  have hcont : ∀ {w : E → ℝ}, IsQuasilinearConormalSolOn ν Φ z s w →
      (∀ y ∈ B, gradientWithin w B y ∈ U) →
      IntegrableOn (fun y ↦ ⟪Φ (gradientWithin w B y), ∇ φ y⟫) B := fun {w} hw hwU ↦
    ContinuousOn.integrableOn_compact hBc
      (((hΦ.continuousOn).comp (continuousOn_gradientWithin_halfBall hν hs hz hw.1) hwU).inner
        hφc.continuousOn)
  have e1 : ∫ y in B, ⟪chordCoeff Φ (gradientWithin w₁ B y) (gradientWithin w₂ B y)
        (gradientWithin (fun y ↦ w₁ y - w₂ y) B y), ∇ φ y⟫ =
      (∫ y in B, ⟪Φ (gradientWithin w₁ B y), ∇ φ y⟫) -
        ∫ y in B, ⟪Φ (gradientWithin w₂ B y), ∇ φ y⟫ := by
    rw [← integral_sub (hcont h₁ hU₁) (hcont h₂ hU₂)]
    refine setIntegral_congr_fun hBm fun y hy ↦ ?_
    rw [hgr y hy, ← sub_eq_chordCoeff_apply hU hUc hΦ (hU₁ y hy) (hU₂ y hy), inner_sub_left]
  change ∫ y in B, ⟪chordCoeff Φ (gradientWithin w₁ B y) (gradientWithin w₂ B y)
        (gradientWithin (fun y ↦ w₁ y - w₂ y) B y), ∇ φ y⟫ =
      (∫ y in B, ⟪(0 : E → E) y, ∇ φ y⟫) + ∫ y in B, (0 : E → ℝ) y * φ y
  rw [e1, h₁.2 φ hφ, h₂.2 φ hφ]
  simp

end BasicElliptic.Div
