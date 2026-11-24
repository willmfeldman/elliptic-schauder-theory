/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Three.UniformHolder
public import BasicElliptic.Div.Quasilinear.Estimate
import BasicElliptic.Div.Boundary.Main
import BasicElliptic.Holder.Algebra

/-!
# The first-order estimate with a constant flux, uniform in the structure

* `Div.StructureBounds Φ lam M δ`: `Φ ∈ C³(ball 0 δ)`, `DΦ` symmetric and `lam`-elliptic there,
  `‖DΦ‖, ‖D²Φ‖, ‖D³Φ‖ ≤ M`.
* `Div.exists_c1_estimate_flux`: the scaled linear conormal estimate with flux and no source,
  together with the finiteness of the Hölder seminorm.
* `Div.first_order_estimate_flux`: if `w` is a quasilinear conormal solution on
  `B = halfBall ν x r` with `‖∇w‖ ≤ η` and `Φ(0) - c` has no weak divergence on `B`, then
  `κ r ‖Dw(x)‖ + (κ r)^{3/2} [Dw]_{1/2, halfBall ν x (κ r / 2)} ≤ C (osc_B w + r ‖c‖)`, with
  `η, κ, C` depending only on `E`, `ν`, `lam`, `M`, `δ`.
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace
open scoped NNReal Gradient ContDiff

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The structure bounds -/

/-- The structure hypotheses of the uniform third-order estimate. -/
structure StructureBounds (Φ : E → E) (lam M δ : ℝ) : Prop where
  lam_pos : 0 < lam
  δ_pos : 0 < δ
  contDiffOn : ContDiffOn ℝ 3 Φ (ball 0 δ)
  ell : ∀ p ∈ ball (0 : E) δ, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫
  sym : ∀ p ∈ ball (0 : E) δ, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric
  bound : ∀ p ∈ ball (0 : E) δ, ‖fderiv ℝ Φ p‖ ≤ M ∧ ‖iteratedFDeriv ℝ 2 Φ p‖ ≤ M ∧
    ‖iteratedFDeriv ℝ 3 Φ p‖ ≤ M

namespace StructureBounds

variable {Φ : E → E} {lam M δ : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem M_nonneg (hS : StructureBounds Φ lam M δ) : 0 ≤ M :=
  (norm_nonneg _).trans (hS.bound 0 (mem_ball_self hS.δ_pos)).1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiffOn_one (hS : StructureBounds Φ lam M δ) : ContDiffOn ℝ 1 Φ (ball 0 δ) :=
  hS.contDiffOn.of_le (by norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiffOn_two (hS : StructureBounds Φ lam M δ) : ContDiffOn ℝ 2 Φ (ball 0 δ) :=
  hS.contDiffOn.of_le (by norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `DΦ` is `C²` on the ball. -/
theorem contDiffOn_fderiv (hS : StructureBounds Φ lam M δ) :
    ContDiffOn ℝ 2 (fderiv ℝ Φ) (ball 0 δ) :=
  hS.contDiffOn.fderiv_of_isOpen isOpen_ball (by norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `D²Φ = D(DΦ)` is `C¹` on the ball. -/
theorem contDiffOn_fderiv_fderiv (hS : StructureBounds Φ lam M δ) :
    ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ Φ)) (ball 0 δ) :=
  hS.contDiffOn_fderiv.fderiv_of_isOpen isOpen_ball (by norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_fderiv_fderiv_le (hS : StructureBounds Φ lam M δ) {p : E}
    (hp : p ∈ ball (0 : E) δ) : ‖fderiv ℝ (fderiv ℝ Φ) p‖ ≤ M := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact (hS.bound p hp).2.1

set_option maxSynthPendingDepth 6 in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_fderiv_fderiv_fderiv_le (hS : StructureBounds Φ lam M δ) {p : E}
    (hp : p ∈ ball (0 : E) δ) : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ Φ)) p‖ ≤ M := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  exact (hS.bound p hp).2.2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `DΦ` is `M`-Lipschitz on the ball. -/
theorem norm_fderiv_sub_le (hS : StructureBounds Φ lam M δ) {p q : E}
    (hp : p ∈ ball (0 : E) δ) (hq : q ∈ ball (0 : E) δ) :
    ‖fderiv ℝ Φ p - fderiv ℝ Φ q‖ ≤ M * ‖p - q‖ := by
  have hd : ∀ z ∈ ball (0 : E) δ,
      HasFDerivWithinAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) z) (ball 0 δ) z := fun z hz ↦
    (((hS.contDiffOn_fderiv.differentiableOn (by norm_num)) z hz).differentiableAt
      (isOpen_ball.mem_nhds hz)).hasFDerivAt.hasFDerivWithinAt
  exact (convex_ball _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le hd
    (fun z hz ↦ hS.norm_fderiv_fderiv_le hz) hq hp

set_option maxSynthPendingDepth 6 in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `D²Φ` is `M`-Lipschitz on the ball. -/
theorem norm_fderiv_fderiv_sub_le (hS : StructureBounds Φ lam M δ) {p q : E}
    (hp : p ∈ ball (0 : E) δ) (hq : q ∈ ball (0 : E) δ) :
    ‖fderiv ℝ (fderiv ℝ Φ) p - fderiv ℝ (fderiv ℝ Φ) q‖ ≤ M * ‖p - q‖ := by
  have hd : ∀ z ∈ ball (0 : E) δ, HasFDerivWithinAt (fderiv ℝ (fderiv ℝ Φ))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ Φ)) z) (ball 0 δ) z := fun z hz ↦
    (((hS.contDiffOn_fderiv_fderiv.differentiableOn one_ne_zero) z hz).differentiableAt
      (isOpen_ball.mem_nhds hz)).hasFDerivAt.hasFDerivWithinAt
  exact (convex_ball _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le hd
    (fun z hz ↦ hS.norm_fderiv_fderiv_fderiv_le hz) hq hp

end StructureBounds

/-! ### Auxiliary facts -/

/-- Replacing a constant flux by another one with the same weak divergence. -/
theorem IsConormalSolOn.congr_const_flux {ν x : E} {r : ℝ} {a : E → E →L[ℝ] E} {c c' : E}
    {u : E → ℝ} (h : IsConormalSolOn ν a (fun _ ↦ c) 0 x r u)
    (hc : ∀ φ, IsTestFn (ball x r) φ → ∫ y in halfBall ν x r, ⟪c - c', ∇ φ y⟫ = 0) :
    IsConormalSolOn ν a (fun _ ↦ c') 0 x r u := by
  refine ⟨h.1, fun φ hφ ↦ ?_⟩
  have hφc : Continuous (∇ φ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ.1.continuous_fderiv one_ne_zero)
  have hi : ∀ v : E, IntegrableOn (fun y ↦ ⟪v, ∇ φ y⟫) (halfBall ν x r) := fun v ↦
    (continuous_const.inner hφc).continuousOn.integrableOn_compact (isCompact_halfBall ν x r)
  have key := h.2 φ hφ
  have hsplit : ∫ y in halfBall ν x r, ⟪c, ∇ φ y⟫ =
      (∫ y in halfBall ν x r, ⟪c', ∇ φ y⟫) + ∫ y in halfBall ν x r, ⟪c - c', ∇ φ y⟫ := by
    rw [← integral_add (hi c') (hi (c - c'))]
    congr 1; funext y; rw [← inner_add_left, add_sub_cancel]
  simp only [Pi.zero_apply, zero_mul, integral_zero, add_zero] at key ⊢
  rw [key, hsplit, hc φ hφ, add_zero]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Hölder seminorm only depends on the values on the set. -/
theorem eHolderSeminormOn_congr {F : Type*} [NormedAddCommGroup F] {α : ℝ≥0} {f g : E → F}
    {s : Set E} (hfg : EqOn f g s) : eHolderSeminormOn α f s = eHolderSeminormOn α g s := by
  have : ∀ C : ℝ≥0, HolderOnWith C α f s ↔ HolderOnWith C α g s := fun C ↦ by
    constructor
    · intro hf x hx y hy; rw [← hfg hx, ← hfg hy]; exact hf x hx y hy
    · intro hg x hx y hy; rw [hfg hx, hfg hy]; exact hg x hx y hy
  simp only [eHolderSeminormOn, this]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem holderSeminormOn_congr {F : Type*} [NormedAddCommGroup F] {α : ℝ≥0} {f g : E → F}
    {s : Set E} (hfg : EqOn f g s) : holderSeminormOn α f s = holderSeminormOn α g s := by
  rw [holderSeminormOn, holderSeminormOn, eHolderSeminormOn_congr hfg]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Within-derivatives on two half balls agree where the smaller one is inside the larger. -/
theorem fderivWithin_halfBall_eqOn {ν x x' : E} {r r' : ℝ} (hν : ‖ν‖ = 1) (hr' : 0 < r')
    (hx' : -r' < ⟪x', ν⟫) (hsub : halfBall ν x' r' ⊆ halfBall ν x r) {w : E → ℝ}
    (hw : DifferentiableOn ℝ w (halfBall ν x r)) :
    EqOn (fderivWithin ℝ w (halfBall ν x' r')) (fderivWithin ℝ w (halfBall ν x r))
      (halfBall ν x' r') := fun y hy ↦
  fderivWithin_subset hsub (uniqueDiffOn_halfBall hν hr' hx' y hy) (hw y (hsub hy))

/-! ### The linear estimate with flux -/

variable (E) in
/-- The scaled linear conormal estimate (`Div.c1Holder_halfBall_estimate`) with a Hölder flux and
no source, together with the finiteness of the Hölder seminorm. -/
theorem exists_c1_estimate_flux {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Λ Kc : ℝ}
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν p : E) (ρ : ℝ) (Ka KG : ℝ≥0) (MG : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (u : E → ℝ),
      ‖ν‖ = 1 → 0 < ρ → 0 ≤ ⟪p, ν⟫ → IsUniformlyElliptic lam Λ a (halfBall ν p ρ) →
      IsSymmetricOn a (halfBall ν p ρ) → HolderOnWith Ka α a (halfBall ν p ρ) →
      (Ka : ℝ) * ρ ^ (α : ℝ) ≤ Kc → HolderOnWith KG α G (halfBall ν p ρ) →
      (∀ y ∈ halfBall ν p ρ, ‖G y‖ ≤ MG) → IsConormalSolOn ν a G 0 p ρ u →
      eHolderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≠ ⊤ ∧
      ρ * ‖fderivWithin ℝ u (halfBall ν p ρ) p‖ + ρ ^ (1 + (α : ℝ)) *
          holderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≤
        C * (regionOsc u (halfBall ν p ρ) + ρ ^ (1 + (α : ℝ)) * KG + ρ * MG) := by
  obtain ⟨C, hC⟩ := Div.c1Holder_halfBall_estimate E α hα hα1 lam Λ Kc hlam
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ν p ρ Ka KG MG a G u hν hρ hp hell hsym ha hKa hG hMG hu
  have hp' : -ρ < ⟪p, ν⟫ := by linarith
  have hfm : AEStronglyMeasurable (0 : E → ℝ) (volume.restrict (halfBall ν p ρ)) :=
    aestronglyMeasurable_const
  constructor
  · obtain ⟨-, Cq, hq⟩ := Div.contDiffHolderOn_one_halfBall_of_isConormalSolution E α hα hα1 ν p
      ρ lam Λ Ka KG 0 a G 0 u hν hρ hp' hlam hell hsym ha hG hfm (fun y _ ↦ by simp) hu
    have huS : UniqueDiffOn ℝ (halfBall ν p (ρ / 2)) :=
      uniqueDiffOn_halfBall hν (by positivity) (by linarith)
    have hsub : halfBall ν p (ρ / 2) ⊆ halfBall ν p ρ := halfBall_mono ν p (by linarith)
    refine (eHolderSeminormOn_lt_top_of_holderOnWith (C := Cq)
      (holderOnWith_iff_dist_le.2 fun a' ha' b' hb' ↦ ?_)).ne
    rw [← fderivWithin_subset hsub (huS a' ha') ((hu.1.differentiableOn one_ne_zero) a'
        (hsub ha')),
      ← fderivWithin_subset hsub (huS b' hb') ((hu.1.differentiableOn one_ne_zero) b'
        (hsub hb')),
      ← dist_iteratedFDerivWithin_one u u (huS a' ha') (huS b' hb')]
    exact hq.dist_le ha' hb'
  · have h := hC ν p ρ Ka KG MG 0 a G 0 u hν hρ hp' hell hsym ha hKa hG hMG hfm
      (fun y _ ↦ by simp) hu
    simp only [mul_zero, add_zero] at h
    have hpB : p ∈ halfBall ν p ρ := ⟨mem_closedBall_self hρ.le, hp⟩
    obtain ⟨c, hc⟩ := (isCompact_halfBall ν p ρ).exists_bound_of_continuousOn
      (hu.1.continuousOn)
    have hosc := regionOsc_nonneg_of_abs_le ⟨p, hpB⟩ (fun y hy ↦ (Real.norm_eq_abs _).symm.le.trans
      (hc y hy))
    have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG p hpB)
    have hs0 : 0 ≤ regionOsc u (halfBall ν p ρ) + ρ ^ (1 + (α : ℝ)) * KG + ρ * MG := by
      positivity
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs0)

/-! ### The first-order estimate -/

variable (E) in
/-- **First-order estimate with a constant flux, uniform in the structure.** -/
theorem first_order_estimate_flux {ν : E} (hν : ‖ν‖ = 1) {lam M δ : ℝ} (hlam : 0 < lam)
    (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ η > 0, ∃ κ > 0, κ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → E),
      StructureBounds Φ lam M δ → ∀ (x : E) (r : ℝ) (w : E → ℝ) (c : E), 0 < r →
      0 ≤ ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x r w →
      (∀ y ∈ halfBall ν x r, ‖gradientWithin w (halfBall ν x r) y‖ ≤ η) →
      (∀ φ, IsTestFn (ball x r) φ → ∫ y in halfBall ν x r, ⟪Φ 0 - c, ∇ φ y⟫ = 0) →
      eHolderSeminormOn (1 / 2) (fderivWithin ℝ w (halfBall ν x r))
          (halfBall ν x (κ * r / 2)) ≠ ⊤ ∧
      κ * r * ‖fderivWithin ℝ w (halfBall ν x r) x‖ + (κ * r) ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) *
          holderSeminormOn (1 / 2) (fderivWithin ℝ w (halfBall ν x r))
            (halfBall ν x (κ * r / 2)) ≤
        C * (regionOsc w (halfBall ν x r) + r * ‖c‖) := by
  have : Nontrivial E := ⟨⟨ν, 0, by rintro rfl; simp at hν⟩⟩
  set η₀ := δ / 2 with hη₀
  have hη₀0 : 0 < η₀ := by positivity
  obtain ⟨ηG, hηG, c₁, hc₁, C₁, hC₁, hGL⟩ :=
    exists_holderOnWith_gradientWithin_unif E hν (Λ := M) hlam hM hδ
  set η := min η₀ ηG with hηdef
  have hη : 0 < η := lt_min hη₀0 hηG
  set c := min c₁ 1 with hcdef
  have hc0 : 0 < c := lt_min hc₁ one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  obtain ⟨CT, hCT0, hCT⟩ := exists_c1_estimate_flux E (α := 1 / 2) (by norm_num) (by norm_num)
    (lam := lam) (Λ := M) (Kc := 2 * M * C₁) hlam
  refine ⟨η, hη, c / 2, by positivity, by linarith, CT, hCT0, ?_⟩
  intro Φ hS x r w c' hr hx0 h hgrad hflux
  set U₀ := ball (0 : E) δ with hU₀
  have hU₀o : IsOpen U₀ := isOpen_ball
  have hU₀c : Convex ℝ U₀ := convex_ball _ _
  have hΦ₁ : ContDiffOn ℝ 1 Φ U₀ := hS.contDiffOn_one
  set K₀ := closedBall (0 : E) η₀ with hK₀
  have hK₀U : K₀ ⊆ U₀ := closedBall_subset_ball (by linarith)
  have hK₀c : Convex ℝ K₀ := convex_closedBall _ _
  have h0U₀ : (0 : E) ∈ U₀ := mem_ball_self hδ
  have h0K₀ : (0 : E) ∈ K₀ := mem_closedBall_self hη₀0.le
  have hΛ : ∀ p ∈ K₀, ‖fderiv ℝ Φ p‖ ≤ M := fun p hp ↦ (hS.bound p (hK₀U hp)).1
  have hL : ∀ a ∈ K₀, ∀ b ∈ K₀, ‖fderiv ℝ Φ a - fderiv ℝ Φ b‖ ≤ M * ‖a - b‖ :=
    fun a ha b hb ↦ hS.norm_fderiv_sub_le (hK₀U ha) (hK₀U hb)
  set B := halfBall ν x r with hBdef
  set g := gradientWithin w B with hgdef
  have hx : -r < ⟪x, ν⟫ := by linarith
  have hgK : ∀ y ∈ B, g y ∈ K₀ := fun y hy ↦
    mem_closedBall_zero_iff.2 ((hgrad y hy).trans (min_le_left _ _))
  have hgU : ∀ y ∈ B, g y ∈ U₀ := fun y hy ↦ hK₀U (hgK y hy)
  have hgc : ContinuousOn g B := continuousOn_gradientWithin_halfBall hν hr hx h.1
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hBc : IsCompact B := isCompact_halfBall ν x r
  obtain ⟨cw, hcw⟩ := hBc.exists_bound_of_continuousOn h.1.continuousOn
  have hcw' : ∀ y ∈ B, |w y| ≤ cw := fun y hy ↦ (Real.norm_eq_abs _).symm.le.trans (hcw y hy)
  have hbddA : BddAbove (w '' B) :=
    ⟨cw, by rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (hcw' y hy)⟩
  have hbddB : BddBelow (w '' B) :=
    ⟨-cw, by rintro _ ⟨y, hy, rfl⟩; exact neg_le_of_abs_le (hcw' y hy)⟩
  -- the linear problem
  set a : E → E →L[ℝ] E := fun y ↦ chordCoeff Φ (g y) 0 with ha
  have hΦc : ContinuousOn (fun y ↦ Φ (g y)) B := hΦ₁.continuousOn.comp hgc fun y hy ↦ hgU y hy
  have hlin0 := h.isConormalSolOn_sub_inner hν hr hx hΦc (a := a) (G := fun _ ↦ -Φ 0) 0
    continuousOn_const fun y hy ↦ by
      change chordCoeff Φ (g y) 0 (g y - 0) = _
      rw [← sub_eq_chordCoeff_apply hU₀o hU₀c hΦ₁ (hgU y hy) h0U₀]
      abel
  have hw0 : (fun y ↦ w y - ⟪(0 : E), y⟫) = w := funext fun y ↦ by simp
  rw [hw0] at hlin0
  have hlin : IsConormalSolOn ν a (fun _ ↦ -c') 0 x r w :=
    hlin0.congr_const_flux fun φ hφ ↦ by
      have := hflux φ hφ
      have e : ∀ y, ⟪-Φ 0 - -c', ∇ φ y⟫ = -⟪Φ 0 - c', ∇ φ y⟫ := fun y ↦ by
        rw [← inner_neg_left]; congr 1; abel
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_neg, this, neg_zero]
  -- the a priori Hölder bound for `∇w`
  have hHol := hGL Φ hΦ₁ (hS.ell 0 h0U₀) (hS.sym 0 h0U₀) (hS.bound 0 h0U₀).1
    (fun p hp ↦ by simpa using hS.norm_fderiv_sub_le hp h0U₀) x r w x (r / 2) hr hx h
    (half_pos hr) hx0 (closedBall_subset_ball (half_lt_self hr)) fun z hz ↦
      (hgrad z (halfBall_mono ν x (by linarith) hz)).trans (min_le_right _ _)
  set r₂ := c * (r / 2) with hr₂def
  have hr₂ : 0 < r₂ := by positivity
  have hr₂r : r₂ ≤ r / 2 := mul_le_of_le_one_left (by positivity) hc1
  have hr₂B : halfBall ν x r₂ ⊆ B := halfBall_mono ν x (by linarith)
  set Hg := Real.toNNReal (C₁ / √(r / 2)) with hHgdef
  have hHgv : (Hg : ℝ) = C₁ / √(r / 2) := Real.coe_toNNReal _ (by positivity)
  have hHg : HolderOnWith Hg (1 / 2) g (halfBall ν x r₂) :=
    hHol.mono (halfBall_mono ν x (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (by positivity)))
  have hsqrt : √r₂ ≤ √(r / 2) := Real.sqrt_le_sqrt hr₂r
  have hHgC : (Hg : ℝ) * √r₂ ≤ C₁ := by
    rw [hHgv]
    calc C₁ / √(r / 2) * √r₂ ≤ C₁ / √(r / 2) * √(r / 2) := by gcongr
      _ = C₁ := by field_simp
  have hgr : ∀ y ∈ halfBall ν x r₂, ∀ y' ∈ halfBall ν x r₂,
      ‖g y - g y'‖ ≤ Hg * dist y y' ^ (1 / 2 : ℝ) := fun y hy y' hy' ↦ by
    have := (holderOnWith_iff_dist_le.1 hHg) y hy y' hy'
    rwa [dist_eq_norm, show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num] at this
  have hell_a : IsUniformlyElliptic lam M a (halfBall ν x r₂) := fun y hy ↦
    ⟨le_inner_chordCoeff hU₀o hU₀c hΦ₁ hS.ell (hgU y (hr₂B hy)) h0U₀,
      norm_chordCoeff_le hK₀c hΛ (hgK y (hr₂B hy)) h0K₀⟩
  have hsym_a : IsSymmetricOn a (halfBall ν x r₂) := fun y hy ↦
    isSymmetric_chordCoeff hU₀o hU₀c hΦ₁ hS.sym (hgU y (hr₂B hy)) h0U₀
  have hKa : HolderOnWith (Real.toNNReal (M * Hg)) (1 / 2) a (halfBall ν x r₂) := by
    refine holderOnWith_iff_dist_le.2 fun y hy y' hy' ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm,
      show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num]
    refine (norm_chordCoeff_sub_le hU₀o hU₀c hΦ₁ hK₀c hK₀U hM hL (hgK y (hr₂B hy)) h0K₀
      (hgK y' (hr₂B hy')) h0K₀).trans ?_
    rw [sub_self, norm_zero, add_zero, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hgr y hy y' hy') hM
  have hKaC : (Real.toNNReal (M * Hg) : ℝ) * r₂ ^ ((1 / 2 : ℝ≥0) : ℝ) ≤ 2 * M * C₁ := by
    rw [Real.coe_toNNReal _ (by positivity), show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, mul_assoc]
    calc M * (Hg * √r₂) ≤ M * C₁ := by gcongr
      _ ≤ 2 * M * C₁ := by nlinarith [mul_nonneg hM hC₁]
  have hxr₂ : -r₂ < ⟪x, ν⟫ := by linarith
  have hlin₂ := hlin.restrict_halfBall hν hr₂ hxr₂ (closedBall_subset_closedBall (by linarith))
    (ball_subset_ball (by linarith))
  have hG0 : HolderOnWith 0 (1 / 2) (fun _ ↦ -c' : E → E) (halfBall ν x r₂) :=
    holderOnWith_const _ 0 _ _
  obtain ⟨hfin, hT⟩ := hCT ν x r₂ _ 0 ‖c'‖ a (fun _ ↦ -c') w hν hr₂ hx0 hell_a hsym_a hKa hKaC
    hG0 (fun y _ ↦ by rw [norm_neg]) hlin₂
  have hxr₂B : x ∈ halfBall ν x r₂ := ⟨mem_closedBall_self hr₂.le, hx0⟩
  have hosc₂ : regionOsc w (halfBall ν x r₂) ≤ regionOsc w B :=
    regionOsc_mono hr₂B ⟨x, hxr₂B⟩ hbddA hbddB
  have hD₂ := fderivWithin_halfBall_eqOn hν hr₂ hxr₂ hr₂B hwB
  have hr₂κ : c / 2 * r = r₂ := by rw [hr₂def]; ring
  have hsubH : halfBall ν x (r₂ / 2) ⊆ halfBall ν x r₂ := halfBall_mono ν x (by linarith)
  rw [hr₂κ, ← hD₂ hxr₂B, ← holderSeminormOn_congr (hD₂.mono hsubH),
    ← eHolderSeminormOn_congr (hD₂.mono hsubH)]
  refine ⟨hfin, hT.trans ?_⟩
  simp only [NNReal.coe_zero, mul_zero, add_zero]
  gcongr
  linarith

end BasicElliptic.Div
