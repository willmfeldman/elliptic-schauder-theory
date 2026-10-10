/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Div
import BasicElliptic.Div.Boundary.LocalHolder
import BasicElliptic.Div.Boundary.Estimate
import BasicElliptic.Holder.Algebra
import BasicElliptic.Common.WithinDeriv

/-!
# Conormal flat-boundary `C^{1,α}` regularity in divergence form

`Div.contDiffHolderOn_one_halfBall_of_isConormalSolution` and `Div.c1Holder_halfBall_estimate`
prove `Div.C1HolderHalfBallStatement` and `Div.C1HolderHalfBallEstimateStatement`.

## Qualitative regularity

Let `S = halfBall ν x (r/2)`, `h = ⟪x, ν⟫ > -r`.
* If `h ≤ -r/2`, `S` has at most one point.
* If `h ≥ 0`, apply the local bound `dist_gradientWithin_le_of_isConormalSolOn` with centre `x`,
  `ρ = δ = r/2`, `R = r`.
* If `-r/2 < h < 0`, move the centre to the foot point `x' = x - h ν`:
  `S ⊆ halfBall ν x' ρ`, `ρ = √(r²/4 - h²)`, and `halfBall ν x' (r + h) ⊆ halfBall ν x r`, with
  room `r + h - ρ > 0` (`(r + h)² - ρ² = 2 (h + r/2)² + r²/4`).

In both cases the bounds `M₀ = sup ‖∇w‖`, `M_G = sup ‖G‖` on the (compact) half ball are finite,
the gradient is Hölder on `S`, and `D¹w = Dw` on `S` (unique differentiability).
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient NNReal

public section

namespace BasicElliptic

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Div

variable {E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `⟪x, ν⟫ ≤ -r`, then `halfBall ν x r` has at most one point. -/
theorem halfBall_subsingleton {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hr : 0 ≤ r)
    (hx : ⟪x, ν⟫ ≤ -r) :
    (halfBall ν x r).Subsingleton := by
  have key : ∀ y ∈ halfBall ν x r, y = x + r • ν := by
    intro y hy
    have h1 : ‖y - x‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy.1
    have h2 : r ≤ ⟪y - x, ν⟫ := by
      rw [inner_sub_left]; linarith [mem_halfSpace.1 hy.2]
    have h3 : ‖y - x - r • ν‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hν, Real.norm_eq_abs, mul_one,
        sq_abs]
      have h4 : ⟪y - x, ν⟫ ≤ ‖y - x‖ := by
        simpa [hν] using real_inner_le_norm (y - x) ν
      nlinarith [norm_nonneg (y - x)]
    have : ‖y - x - r • ν‖ = 0 := by nlinarith [norm_nonneg (y - x - r • ν)]
    rw [norm_eq_zero, sub_sub, sub_eq_zero] at this
    exact this
  exact fun p hp q hq ↦ (key p hp).trans (key q hq).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Choice of centre** (see the module docstring). -/
private theorem exists_flat_centre {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r)
    (hx : -(r / 2) < ⟪x, ν⟫) :
    ∃ z : E, ∃ ρ R δ : ℝ, 0 ≤ ⟪z, ν⟫ ∧ 0 < δ ∧ δ ≤ ρ ∧ ρ + δ ≤ R ∧
      halfBall ν x (r / 2) ⊆ halfBall ν z ρ ∧ closedBall z R ⊆ closedBall x r ∧
      ball z R ⊆ ball x r := by
  rcases le_or_gt 0 ⟪x, ν⟫ with h0 | h0
  · exact ⟨x, r / 2, r, r / 2, h0, by positivity, le_rfl, by linarith, subset_rfl, subset_rfl,
      subset_rfl⟩
  set h := ⟪x, ν⟫ with hh
  set z := x - h • ν with hz
  have hzν : ⟪z, ν⟫ = 0 := by
    rw [hz, inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν]; ring
  have hdz : dist z x = -h := by
    rw [hz, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
      Real.norm_eq_abs, abs_of_neg h0]
  set ρ := √(r ^ 2 / 4 - h ^ 2) with hρ
  have hρ2 : 0 < r ^ 2 / 4 - h ^ 2 := by nlinarith
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hρ2
  have hρsq : ρ ^ 2 = r ^ 2 / 4 - h ^ 2 := Real.sq_sqrt hρ2.le
  set R := r + h with hR
  have hR0 : 0 < R := by linarith
  have hRρ : ρ < R := by
    have : ρ ^ 2 < R ^ 2 := by rw [hρsq, hR]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hR0.le this
  refine ⟨z, ρ, R, min ρ (R - ρ), hzν.ge, lt_min hρ0 (by linarith), min_le_left _ _,
    by linarith [min_le_right ρ (R - ρ)], ?_, ?_, ?_⟩
  · rintro y ⟨hy, hyH⟩
    refine ⟨?_, hyH⟩
    rw [mem_closedBall, dist_eq_norm]
    have hyx : ‖y - x‖ ≤ r / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
    have e : y - z = (y - x) + h • ν := by rw [hz]; abel
    have hsq : ‖y - z‖ ^ 2 ≤ ρ ^ 2 := by
      rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul, hν, Real.norm_eq_abs, mul_one,
        sq_abs, hρsq, inner_sub_left]
      have hy0 : 0 ≤ ⟪y, ν⟫ := mem_halfSpace.1 hyH
      have : ‖y - x‖ ^ 2 ≤ r ^ 2 / 4 := by nlinarith [norm_nonneg (y - x)]
      nlinarith
    exact pow_le_pow_iff_left₀ (norm_nonneg _) hρ0.le two_ne_zero |>.1 hsq
  · intro y hy
    rw [mem_closedBall] at hy ⊢
    linarith [dist_triangle y z x]
  · intro y hy
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y z x]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For a centre below the plane (`-r/2 < h < 0`), the cap `halfBall ν x (r/2)` lies in
`halfBall ν x' (3 (r + h) / 4)`, `x' = x - h ν`, and `halfBall ν x' (r + h) ⊆ halfBall ν x r`. -/
private theorem cap_subset {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1) (hx : -(r / 2) < ⟪x, ν⟫)
    (h0 : ⟪x, ν⟫ < 0) :
    0 ≤ ⟪x - ⟪x, ν⟫ • ν, ν⟫ ∧
      halfBall ν x (r / 2) ⊆ halfBall ν (x - ⟪x, ν⟫ • ν) (3 * (r + ⟪x, ν⟫) / 4) ∧
      closedBall (x - ⟪x, ν⟫ • ν) (r + ⟪x, ν⟫) ⊆ closedBall x r ∧
      ball (x - ⟪x, ν⟫ • ν) (r + ⟪x, ν⟫) ⊆ ball x r := by
  set h := ⟪x, ν⟫ with hh
  set z := x - h • ν with hz
  have hzν : ⟪z, ν⟫ = 0 := by
    rw [hz, inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν]; ring
  have hdz : dist z x = -h := by
    rw [hz, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
      Real.norm_eq_abs, abs_of_neg h0]
  refine ⟨hzν.ge, ?_, ?_, ?_⟩
  · rintro y ⟨hy, hyH⟩
    refine ⟨?_, hyH⟩
    rw [mem_closedBall, dist_eq_norm]
    have hyx : ‖y - x‖ ≤ r / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
    have e : y - z = (y - x) + h • ν := by rw [hz]; abel
    have hpos : 0 ≤ 3 * (r + h) / 4 := by linarith
    have hsq : ‖y - z‖ ^ 2 ≤ (3 * (r + h) / 4) ^ 2 := by
      rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul, hν, Real.norm_eq_abs, mul_one,
        sq_abs, inner_sub_left]
      have hy0 : 0 ≤ ⟪y, ν⟫ := mem_halfSpace.1 hyH
      have : ‖y - x‖ ^ 2 ≤ r ^ 2 / 4 := by nlinarith [norm_nonneg (y - x)]
      nlinarith [sq_nonneg (25 * h + 9 * r)]
    exact pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero |>.1 hsq
  · intro y hy
    rw [mem_closedBall] at hy ⊢
    linarith [dist_triangle y z x]
  · intro y hy
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y z x]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Oscillation bound from `regionOsc` for a function continuous on a closed half ball. -/
private theorem abs_sub_le_regionOsc_halfBall {ν x : E} {r : ℝ} {w : E → ℝ}
    (hw : ContinuousOn w (halfBall ν x r)) {p q : E} (hp : p ∈ halfBall ν x r)
    (hq : q ∈ halfBall ν x r) : |w p - w q| ≤ regionOsc w (halfBall ν x r) := by
  have hc := (isCompact_halfBall ν x r).image_of_continuousOn hw
  have h1 : ∀ y ∈ halfBall ν x r, w y ≤ sSup (w '' halfBall ν x r) := fun y hy ↦
    le_csSup hc.bddAbove (mem_image_of_mem w hy)
  have h2 : ∀ y ∈ halfBall ν x r, sInf (w '' halfBall ν x r) ≤ w y := fun y hy ↦
    csInf_le hc.bddBelow (mem_image_of_mem w hy)
  rw [regionOsc_def, abs_le]
  constructor <;> linarith [h1 p hp, h1 q hq, h2 p hp, h2 q hq]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Hölder seminorms only depend on the values on the set. -/
private theorem holderSeminormOn_congr {α : ℝ≥0} {F F' : E → E →L[ℝ] ℝ} {S : Set E}
    (h : EqOn F F' S) : holderSeminormOn α F S = holderSeminormOn α F' S := by
  have hiff : ∀ C : ℝ≥0, HolderOnWith C α F S ↔ HolderOnWith C α F' S := fun C ↦ by
    simp only [holderOnWith_iff_dist_le]
    constructor
    · intro hF p hp q hq; rw [← h hp, ← h hq]; exact hF p hp q hq
    · intro hF p hp q hq; rw [h hp, h hq]; exact hF p hp q hq
  simp only [holderSeminormOn, eHolderSeminormOn, hiff]

end Div

/-- **Conormal flat-boundary `C^{1,α}` regularity** (`Div.C1HolderHalfBallStatement`). -/
theorem Div.contDiffHolderOn_one_halfBall_of_isConormalSolution :
    Div.C1HolderHalfBallStatement E := by
  intro α hα hα1 ν x r lam Λ Ka KG Mf a G f w hν hr hx hlam hell hsym ha hG hfm hfb hw
  set S := halfBall ν x (r / 2) with hS
  have hSB : S ⊆ halfBall ν x r := halfBall_mono ν x (by linarith)
  refine ⟨hw.1.mono hSB, ?_⟩
  rcases le_or_gt ⟪x, ν⟫ (-(r / 2)) with hxs | hxs
  · refine ⟨0, holderOnWith_iff_dist_le.2 fun p hp q hq ↦ ?_⟩
    rw [Div.halfBall_subsingleton hν (by linarith) hxs hp hq, dist_self]; positivity
  obtain ⟨z, ρ, R, δ, hz, hδ, hδρ, hρR, hSsub, hcl, hball⟩ := Div.exists_flat_centre hν hr hxs
  obtain ⟨C₁, hC₁, hloc⟩ := Div.dist_gradientWithin_le_of_isConormalSolOn E hα hα1 hlam
  set D := halfBall ν z R with hD
  have hDB : D ⊆ halfBall ν x r := inter_subset_inter_left _ hcl
  have hR : 0 < R := by linarith
  have hzR : -R < ⟪z, ν⟫ := by linarith
  have hwD := hw.restrict_halfBall hν hR hzR hcl hball
  have hgc := continuousOn_gradientWithin_halfBall hν hR hzR hwD.1
  obtain ⟨M₀, hM₀⟩ := (isCompact_halfBall ν z R).exists_bound_of_continuousOn hgc
  obtain ⟨MG, hMG⟩ := (isCompact_halfBall ν z R).exists_bound_of_continuousOn
    ((hG.continuousOn hα).mono hDB)
  have h := hloc ν z Ka KG Mf M₀ MG R δ ρ a G f w hν hz hδ hδρ hρR (hell.mono hDB)
    (fun y hy ↦ hsym y (hDB hy)) (ha.mono hDB) (hG.mono hDB) hMG
    (hfm.mono_measure (Measure.restrict_mono hDB le_rfl)) (fun y hy ↦ hfb y (hDB hy)) hwD hM₀
  have hzD : z ∈ D := ⟨mem_closedBall_self hR.le, hz⟩
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ z hzD)
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG z hzD)
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb z (hDB hzD))
  have hY : 0 ≤ C₁ * ((M₀ + MG) * δ ^ (-(α : ℝ)) + Ka * (M₀ + MG) + KG +
      Mf * δ ^ (1 - (α : ℝ))) := by
    have := Real.rpow_nonneg hδ.le (-(α : ℝ))
    have := Real.rpow_nonneg hδ.le (1 - (α : ℝ))
    positivity
  have huS : UniqueDiffOn ℝ S := uniqueDiffOn_halfBall hν (by linarith) hxs
  have hSD : S ⊆ D := hSsub.trans (halfBall_mono ν z (by linarith))
  refine ⟨_, holderOnWith_of_dist_le hY fun p hp q hq ↦ ?_⟩
  rw [dist_iteratedFDerivWithin_one w w (huS p hp) (huS q hq),
    fderivWithin_subset hSD (huS p hp) (hwD.1.differentiableOn one_ne_zero p (hSD hp)),
    fderivWithin_subset hSD (huS q hq) (hwD.1.differentiableOn one_ne_zero q (hSD hq))]
  have h' := h p (hSsub hp) q (hSsub hq)
  have e : dist (gradientWithin w D p) (gradientWithin w D q) =
      dist (fderivWithin ℝ w D p) (fderivWithin ℝ w D q) := by
    simp only [gradientWithin, LinearIsometryEquiv.dist_map]
  rwa [e] at h'

/-- **Scaled conormal flat-boundary `C^{1,α}` estimate**
(`Div.C1HolderHalfBallEstimateStatement`). -/
theorem Div.c1Holder_halfBall_estimate : Div.C1HolderHalfBallEstimateStatement E := by
  intro α hα hα1 lam Λ K hlam
  obtain ⟨C₀, hC₀, hcore⟩ := Div.c1Holder_halfBall_estimate_core E hα hα1 (K := K) hlam
  have h2α : 0 ≤ (2 : ℝ) ^ (1 + (α : ℝ)) := by positivity
  refine ⟨2 ^ (1 + (α : ℝ)) * C₀ + C₀, ?_⟩
  intro ν x r Ka KG MG Mf a G f w hν hr hx hell hsym ha hKa hG hMG hfm hfb hw
  set B := halfBall ν x r with hB
  set O := regionOsc w B with hOdef
  have hO : ∀ p ∈ B, ∀ q ∈ B, |w p - w q| ≤ O := fun p hp q hq ↦
    Div.abs_sub_le_regionOsc_halfBall hw.1.continuousOn hp hq
  -- a point of `B`
  set p₀ := x - min ⟪x, ν⟫ 0 • ν with hp₀
  have hp₀B : p₀ ∈ B := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, hp₀, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hν,
        mul_one, Real.norm_eq_abs, abs_of_nonpos (min_le_right _ _)]
      have := min_le_left ⟪x, ν⟫ 0
      have : -r < min ⟪x, ν⟫ 0 := lt_min hx (by linarith)
      linarith
    · rw [mem_halfSpace, hp₀, inner_sub_left, real_inner_smul_left,
        real_inner_self_of_norm_eq_one hν, mul_one]
      linarith [min_le_left ⟪x, ν⟫ 0]
  have hO0 : 0 ≤ O := (abs_nonneg _).trans (hO p₀ hp₀B p₀ hp₀B)
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG p₀ hp₀B)
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb p₀ hp₀B)
  set Z := O + r ^ (1 + (α : ℝ)) * KG + r * MG + r ^ 2 * Mf with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hfinal : C₀ * Z ≤ (2 ^ (1 + (α : ℝ)) * C₀ + C₀) * Z := by
    nlinarith [mul_nonneg (mul_nonneg h2α hC₀) hZ0]
  rw [Div.holderSeminormOn_fderivWithin_eq]
  rcases le_or_gt 0 ⟪x, ν⟫ with hx0 | hx0
  · -- centre in the closed half space
    have h := hcore ν x r Ka KG MG Mf O a G f w hν hx0 hr hell hsym ha hKa hG hMG hfm hfb hw hO
      (halfBall ν x (r / 2)) (halfBall_mono ν x (by linarith))
    have hng : ‖fderivWithin ℝ w B x‖ = ‖gradientWithin w B x‖ := by
      simp only [gradientWithin, LinearIsometryEquiv.norm_map]
    rw [hng]
    exact h.trans hfinal
  -- centre below the plane: `x ∉ B`, so the derivative at `x` vanishes
  have hxB : x ∉ closure B := by
    rw [(isClosed_halfBall ν x r).closure_eq]
    exact fun h ↦ absurd (mem_halfSpace.1 h.2) (not_le.2 hx0)
  rw [fderivWithin_zero_of_notMem_closure hxB, norm_zero, mul_zero, zero_add]
  rcases le_or_gt ⟪x, ν⟫ (-(r / 2)) with hxs | hxs
  · -- the cap has at most one point
    have hsub := Div.halfBall_subsingleton (r := r / 2) hν (by linarith) hxs
    have h0 : holderSeminormOn α (gradientWithin w B) (halfBall ν x (r / 2)) ≤ 0 :=
      holderSeminormOn_le_of_dist_le le_rfl fun p hp q hq ↦ by
        rw [hsub hp hq, dist_self, zero_mul]
    have hrα : 0 ≤ r ^ (1 + (α : ℝ)) := by positivity
    nlinarith [mul_nonneg (add_nonneg (mul_nonneg h2α hC₀) hC₀) hZ0]
  obtain ⟨hz, hS, hcl, hbl⟩ := Div.cap_subset hν hxs hx0
  set z := x - ⟪x, ν⟫ • ν
  set R := r + ⟪x, ν⟫ with hR
  have hR0 : 0 < R := by linarith
  have hRr : R ≤ r := by linarith
  have hr2R : r ≤ 2 * R := by linarith
  set D := halfBall ν z R with hD
  have hDB : D ⊆ B := inter_subset_inter_left _ hcl
  have hwD := hw.restrict_halfBall hν hR0 (by linarith) hcl hbl
  have hKaR : (Ka : ℝ) * R ^ (α : ℝ) ≤ K :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR0.le hRr α.2) Ka.2).trans hKa
  have h := hcore ν z R Ka KG MG Mf O a G f w hν hz hR0 (hell.mono hDB)
    (fun y hy ↦ hsym y (hDB hy)) (ha.mono hDB) hKaR (hG.mono hDB) (fun y hy ↦ hMG y (hDB hy))
    (hfm.mono_measure (Measure.restrict_mono hDB le_rfl)) (fun y hy ↦ hfb y (hDB hy)) hwD
    (fun p hp q hq ↦ hO p (hDB hp) q (hDB hq)) (halfBall ν x (r / 2)) hS
  -- the gradients within `D` and `B` agree on the cap
  have huD := uniqueDiffOn_halfBall hν hR0 (by linarith : -R < ⟪z, ν⟫)
  have hSD : halfBall ν x (r / 2) ⊆ D := hS.trans (halfBall_mono ν z (by linarith))
  have heq : EqOn (fderivWithin ℝ w D) (fderivWithin ℝ w B) (halfBall ν x (r / 2)) :=
    fun p hp ↦ fderivWithin_subset hDB (huD p (hSD hp))
      (hw.1.differentiableOn one_ne_zero p (hDB (hSD hp)))
  have hsem : holderSeminormOn α (gradientWithin w B) (halfBall ν x (r / 2)) =
      holderSeminormOn α (gradientWithin w D) (halfBall ν x (r / 2)) := by
    rw [← Div.holderSeminormOn_fderivWithin_eq, ← Div.holderSeminormOn_fderivWithin_eq,
      Div.holderSeminormOn_congr heq]
  rw [hsem]
  set Hs := holderSeminormOn α (gradientWithin w D) (halfBall ν x (r / 2))
  have hHs : 0 ≤ Hs := holderSeminormOn_nonneg _ _ _
  have hZR : O + R ^ (1 + (α : ℝ)) * KG + R * MG + R ^ 2 * Mf ≤ Z := by
    have e1 : R ^ (1 + (α : ℝ)) ≤ r ^ (1 + (α : ℝ)) :=
      Real.rpow_le_rpow hR0.le hRr (by positivity)
    have e2 : R ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hR0.le hRr 2
    have k1 := mul_le_mul_of_nonneg_right e1 KG.2
    have k2 := mul_le_mul_of_nonneg_right hRr hMG0
    have k3 := mul_le_mul_of_nonneg_right e2 hMf
    rw [hZ]
    exact add_le_add (add_le_add (add_le_add le_rfl k1) k2) k3
  have hRH : R ^ (1 + (α : ℝ)) * Hs ≤ C₀ * Z :=
    calc R ^ (1 + (α : ℝ)) * Hs ≤ R * ‖gradientWithin w D z‖ + R ^ (1 + (α : ℝ)) * Hs :=
          le_add_of_nonneg_left (mul_nonneg hR0.le (norm_nonneg _))
      _ ≤ C₀ * (O + R ^ (1 + (α : ℝ)) * KG + R * MG + R ^ 2 * Mf) := h
      _ ≤ C₀ * Z := mul_le_mul_of_nonneg_left hZR hC₀
  have hr1 : r ^ (1 + (α : ℝ)) ≤ 2 ^ (1 + (α : ℝ)) * R ^ (1 + (α : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num) hR0.le]
    exact Real.rpow_le_rpow hr.le hr2R (by positivity)
  calc r ^ (1 + (α : ℝ)) * Hs ≤ 2 ^ (1 + (α : ℝ)) * R ^ (1 + (α : ℝ)) * Hs :=
        mul_le_mul_of_nonneg_right hr1 hHs
    _ = 2 ^ (1 + (α : ℝ)) * (R ^ (1 + (α : ℝ)) * Hs) := by ring
    _ ≤ 2 ^ (1 + (α : ℝ)) * (C₀ * Z) := mul_le_mul_of_nonneg_left hRH h2α
    _ ≤ (2 ^ (1 + (α : ℝ)) * C₀ + C₀) * Z := by nlinarith [mul_nonneg hC₀ hZ0]

end BasicElliptic
