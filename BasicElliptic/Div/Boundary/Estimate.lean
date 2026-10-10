/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Boundary.LocalHolder
public import BasicElliptic.Defs.Holder
import BasicElliptic.Holder.Interpolation
import BasicElliptic.Holder.Algebra
import BasicElliptic.Common.Absorption
import BasicElliptic.Common.WithinDeriv
import BasicElliptic.Normalize.ChangeOfVariables

/-!
# Scaled conormal `C^{1,α}` estimate at a centre in the closed half space

`BasicElliptic.Div.c1Holder_halfBall_estimate_core`: for a conormal solution on
`B = halfBall ν z R` with `⟪z, ν⟫ ≥ 0`, data as in `Div.C1HolderHalfBallEstimateStatement`
(`K_a R^α ≤ K`, `‖G‖ ≤ M_G`, `|w(p) - w(q)| ≤ O` on `B`),

`R |∇w(z)| + R^{1+α} [∇w]_{α, halfBall ν z (3R/4)} ≤ C (O + R^{1+α} K_G + R M_G + R² M_f)`.

## Proof (hole filling, as in the interior estimate)

Let `H(t) = [∇w]_{α, halfBall ν z t}`, finite on `[3R/4, 7R/8]` by the local bound
`dist_gradientWithin_le_of_isConormalSolOn`. For `3R/4 ≤ ρ < ρ' ≤ 7R/8`, `δ = (ρ' - ρ)/2`,
interpolation on the half balls `halfBall ν y δ`, `y ∈ halfBall ν z (ρ + δ)`
(`norm_fderivWithin_halfBall_le`; their centres lie in the closed half space) bounds
`‖∇w‖ ≤ M₀ = ε δ^α H(ρ') + C_ε δ⁻¹ O` on `halfBall ν z (ρ + δ)`, and the local bound gives

`H(ρ) ≤ ½ H(ρ') + A (O + R M_G) (ρ' - ρ)^{-(1+α)} + C₁ (K_G + M_f R^{1-α} + K R^{-α} M_G)`

(the new terms: `M_G δ^{-α} ≤ 2^{1+α} R M_G (ρ' - ρ)^{-(1+α)}` and `K_a M_G ≤ K R^{-α} M_G`).
Absorption (`le_of_absorption`, shifted) bounds `R^{1+α} H(3R/4)`, and interpolation on
`halfBall ν z (R/2)` with `ε = 1` bounds `R |∇w(z)|`.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient NNReal

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The conclusion of `dist_gradientWithin_le_of_isConormalSolOn` with constant `C₁`. -/
private def LocalBoundB (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α : ℝ≥0) (lam Λ C₁ : ℝ) :
    Prop :=
  ∀ (ν z : E) (Ka KG : ℝ≥0) (Mf M₀ MG R δ ρ : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 ≤ ⟪z, ν⟫ → 0 < δ → δ ≤ ρ → ρ + δ ≤ R →
      IsUniformlyElliptic lam Λ a (halfBall ν z R) → IsSymmetricOn a (halfBall ν z R) →
      HolderOnWith Ka α a (halfBall ν z R) → HolderOnWith KG α G (halfBall ν z R) →
      (∀ y ∈ halfBall ν z R, ‖G y‖ ≤ MG) →
      AEStronglyMeasurable f (volume.restrict (halfBall ν z R)) →
      (∀ y ∈ halfBall ν z R, |f y| ≤ Mf) → IsConormalSolOn ν a G f z R w →
      (∀ y ∈ halfBall ν z R, ‖gradientWithin w (halfBall ν z R) y‖ ≤ M₀) →
      ∀ p ∈ halfBall ν z ρ, ∀ q ∈ halfBall ν z ρ,
        dist (gradientWithin w (halfBall ν z R) p) (gradientWithin w (halfBall ν z R) q) ≤
          C₁ * ((M₀ + MG) * δ ^ (-(α : ℝ)) + Ka * (M₀ + MG) + KG + Mf * δ ^ (1 - (α : ℝ))) *
            dist p q ^ (α : ℝ)

/-- The algebra of `hole_filling_b`. -/
private theorem hole_algebra {α C₁ δ R ρ ρ' M₀ ε Hp Cε O MG Mf Ka KG K : ℝ} (hα' : 0 < α)
    (hα1' : α ≤ 1) (hC₁ : 0 ≤ C₁) (hδ : 0 < δ) (hδr : δ ≤ R) (hR : 0 < R) (hρρ' : ρ < ρ')
    (hδdef : δ = (ρ' - ρ) / 2) (hM₀def : M₀ = ε * δ ^ α * Hp + Cε * δ⁻¹ * O) (hHp : 0 ≤ Hp)
    (hO0 : 0 ≤ O) (hMG0 : 0 ≤ MG) (hMf : 0 ≤ Mf) (hCε : 0 ≤ Cε) (hε : 0 < ε)
    (hεdef : ε = 1 / (2 * (C₁ * (1 + max K 0) + 1))) (hKa : Ka * R ^ α ≤ K) (hKa0 : 0 ≤ Ka) :
    C₁ * ((M₀ + MG) * δ ^ (-α) + Ka * (M₀ + MG) + KG + Mf * δ ^ (1 - α)) ≤
      1 / 2 * Hp + C₁ * (1 + max K 0) * (Cε + 1) * 2 ^ (1 + α) * (O + R * MG) *
          (ρ' - ρ) ^ (-(1 + α)) +
        (C₁ * KG + C₁ * Mf * R ^ (1 - α) + C₁ * max K 0 * R ^ (-α) * MG) := by
  set Kp := max K 0
  have hKp : 0 ≤ Kp := le_max_right _ _
  -- algebra
  have hδα : δ ^ α * δ ^ (-α) = 1 := by
    rw [← Real.rpow_add hδ]; simp
  have hKaδ : Ka * δ ^ α ≤ Kp :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδr hα'.le) hKa0).trans
      (hKa.trans (le_max_left _ _))
  have hKaR : Ka ≤ Kp * R ^ (-α) := by
    have hRα : 0 < R ^ α := Real.rpow_pos_of_pos hR _
    rw [Real.rpow_neg hR.le, ← div_eq_mul_inv, le_div_iff₀ hRα]
    exact hKa.trans (le_max_left _ _)
  have hδ1 : δ⁻¹ * δ ^ (-α) = 2 ^ (1 + α) * (ρ' - ρ) ^ (-(1 + α)) := by
    rw [hδdef, Real.rpow_neg (by positivity), Real.rpow_neg (by linarith),
      Real.div_rpow (by linarith) (by norm_num), Real.rpow_add (by linarith : (0 : ℝ) < ρ' - ρ),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_one]
    field_simp
  have hδr' : δ ^ (1 - α) ≤ R ^ (1 - α) :=
    Real.rpow_le_rpow hδ.le hδr (by linarith)
  set P := (ρ' - ρ) ^ (-(1 + α))
  have hP : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  have h2α : 0 ≤ (2 : ℝ) ^ (1 + α) := by positivity
  have e1 : M₀ * δ ^ (-α) = ε * Hp + Cε * 2 ^ (1 + α) * O * P := by
    rw [hM₀def, add_mul, show ε * δ ^ α * Hp * δ ^ (-α) =
      ε * Hp * (δ ^ α * δ ^ (-α)) by ring, hδα,
      show Cε * δ⁻¹ * O * δ ^ (-α) = Cε * O * (δ⁻¹ * δ ^ (-α)) by ring, hδ1]
    ring
  have eG : MG * δ ^ (-α) ≤ 2 ^ (1 + α) * (R * MG) * P := by
    have : δ ^ (-α) = δ * (δ⁻¹ * δ ^ (-α)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
    rw [this, hδ1]
    have := mul_le_mul_of_nonneg_right hδr (mul_nonneg h2α hP)
    nlinarith [mul_le_mul_of_nonneg_left this hMG0]
  have e2 : Ka * M₀ = (Ka * δ ^ α) * (M₀ * δ ^ (-α)) := by
    rw [show Ka * δ ^ α * (M₀ * δ ^ (-α)) =
      Ka * M₀ * (δ ^ α * δ ^ (-α)) by ring, hδα, mul_one]
  have hT0 : 0 ≤ ε * Hp + Cε * 2 ^ (1 + α) * O * P := by positivity
  have hKaM : Ka * M₀ ≤ Kp * (ε * Hp + Cε * 2 ^ (1 + α) * O * P) := by
    rw [e2, e1]; exact mul_le_mul_of_nonneg_right hKaδ hT0
  have hKaMG : Ka * MG ≤ Kp * R ^ (-α) * MG := mul_le_mul_of_nonneg_right hKaR hMG0
  have hεC : C₁ * (1 + Kp) * ε ≤ 1 / 2 := by
    rw [hεdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hC₁ (by linarith : (0 : ℝ) ≤ 1 + Kp)]
  have hMfδ : Mf * δ ^ (1 - α) ≤ Mf * R ^ (1 - α) :=
    mul_le_mul_of_nonneg_left hδr' hMf
  have hA1 : C₁ * (1 + Kp) * Cε * 2 ^ (1 + α) * O * P + C₁ * (2 ^ (1 + α) *
      (R * MG) * P) ≤ C₁ * (1 + Kp) * (Cε + 1) * 2 ^ (1 + α) * (O + R * MG) * P := by
    have hRM : 0 ≤ R * MG := by positivity
    have k1 : 0 ≤ C₁ * Kp * 2 ^ (1 + α) * (R * MG) * P := by positivity
    have k2 : 0 ≤ C₁ * (1 + Kp) * Cε * 2 ^ (1 + α) * (R * MG) * P := by positivity
    have k3 : 0 ≤ C₁ * (1 + Kp) * 2 ^ (1 + α) * O * P := by positivity
    nlinarith
  calc C₁ * ((M₀ + MG) * δ ^ (-α) + Ka * (M₀ + MG) + KG + Mf * δ ^ (1 - α))
      = C₁ * (M₀ * δ ^ (-α) + MG * δ ^ (-α) + Ka * M₀ + Ka * MG + KG +
          Mf * δ ^ (1 - α)) := by ring
    _ ≤ C₁ * ((ε * Hp + Cε * 2 ^ (1 + α) * O * P) + 2 ^ (1 + α) * (R * MG) * P +
          Kp * (ε * Hp + Cε * 2 ^ (1 + α) * O * P) + Kp * R ^ (-α) * MG + KG +
          Mf * R ^ (1 - α)) := by
        rw [e1]; gcongr
    _ = C₁ * (1 + Kp) * ε * Hp + (C₁ * (1 + Kp) * Cε * 2 ^ (1 + α) * O * P +
          C₁ * (2 ^ (1 + α) * (R * MG) * P)) +
          (C₁ * KG + C₁ * Mf * R ^ (1 - α) + C₁ * Kp * R ^ (-α) * MG) := by ring
    _ ≤ 1 / 2 * Hp + C₁ * (1 + Kp) * (Cε + 1) * 2 ^ (1 + α) * (O + R * MG) * P +
          (C₁ * KG + C₁ * Mf * R ^ (1 - α) + C₁ * Kp * R ^ (-α) * MG) := by
        gcongr


/-- **Hole filling** at a centre in the closed half space (see the module docstring). -/
private theorem hole_filling_b {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Λ K C₁ : ℝ}
    (hloc : LocalBoundB E α lam Λ C₁) (hC₁ : 0 ≤ C₁) {ν z : E} {R : ℝ} {Ka KG : ℝ≥0}
    {Mf MG O : ℝ} {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1)
    (hz : 0 ≤ ⟪z, ν⟫) (hR : 0 < R)
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν z R)) (hsym : IsSymmetricOn a (halfBall ν z R))
    (ha : HolderOnWith Ka α a (halfBall ν z R)) (hKa : (Ka : ℝ) * R ^ (α : ℝ) ≤ K)
    (hG : HolderOnWith KG α G (halfBall ν z R)) (hMG : ∀ y ∈ halfBall ν z R, ‖G y‖ ≤ MG)
    (hfm : AEStronglyMeasurable f (volume.restrict (halfBall ν z R)))
    (hfb : ∀ y ∈ halfBall ν z R, |f y| ≤ Mf) (hw : IsConormalSolOn ν a G f z R w)
    (hfin : eHolderSeminormOn α (gradientWithin w (halfBall ν z R))
      (halfBall ν z (7 * R / 8)) ≠ ⊤)
    (hO : ∀ p ∈ halfBall ν z R, ∀ q ∈ halfBall ν z R, |w p - w q| ≤ O) (hO0 : 0 ≤ O)
    (hMG0 : 0 ≤ MG) :
    ∀ ρ ρ', 3 * R / 4 ≤ ρ → ρ < ρ' → ρ' ≤ 7 * R / 8 →
      holderSeminormOn α (gradientWithin w (halfBall ν z R)) (halfBall ν z ρ) ≤
        1 / 2 * holderSeminormOn α (gradientWithin w (halfBall ν z R)) (halfBall ν z ρ') +
          C₁ * (1 + max K 0) *
            (max (interpConst (1 / (2 * (C₁ * (1 + max K 0) + 1))) α) 0 + 1) *
              2 ^ (1 + (α : ℝ)) * (O + R * MG) * (ρ' - ρ) ^ (-(1 + (α : ℝ))) +
          (C₁ * KG + C₁ * Mf * R ^ (1 - (α : ℝ)) + C₁ * max K 0 * R ^ (-(α : ℝ)) * MG) := by
  intro ρ ρ' hρ hρρ' hρ'
  set B := halfBall ν z R with hB
  set gW := gradientWithin w B with hgW
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1.le
  set Kp := max K 0
  have hKp : 0 ≤ Kp := le_max_right _ _
  set ε := 1 / (2 * (C₁ * (1 + Kp) + 1)) with hεdef
  have hε : 0 < ε := by positivity
  set Cε := max (interpConst ε α) 0
  have hCε : 0 ≤ Cε := le_max_right _ _
  set δ := (ρ' - ρ) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδr : δ ≤ R := by rw [hδdef]; linarith
  have hδρ : δ ≤ ρ := by rw [hδdef]; linarith
  have hzB : z ∈ B := ⟨mem_closedBall_self hR.le, hz⟩
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb z hzB)
  set Hp := holderSeminormOn α gW (halfBall ν z ρ')
  have hHp : 0 ≤ Hp := holderSeminormOn_nonneg _ _ _
  have hfin' : eHolderSeminormOn α gW (halfBall ν z ρ') ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eHolderSeminormOn_mono (halfBall_mono ν z hρ'))
  have hρ'B : halfBall ν z ρ' ⊆ B := halfBall_mono ν z (by linarith)
  -- interpolation: `‖∇w‖ ≤ M₀` on `halfBall ν z (ρ + δ)`
  set M₀ := ε * δ ^ (α : ℝ) * Hp + Cε * δ⁻¹ * O with hM₀def
  have hM₀ : ∀ y ∈ halfBall ν z (ρ + δ), ‖gW y‖ ≤ M₀ := by
    intro y hy
    have hy0 : 0 ≤ ⟪y, ν⟫ := hy.2
    have hyB : halfBall ν y δ ⊆ halfBall ν z ρ' := fun p hp ↦ by
      refine ⟨?_, hp.2⟩
      have h1 := mem_closedBall.1 hp.1
      have h2 := mem_closedBall.1 hy.1
      rw [mem_closedBall]
      linarith [dist_triangle p y z]
    have hu : UniqueDiffOn ℝ (halfBall ν y δ) := uniqueDiffOn_halfBall hν hδ (by linarith)
    have hfw : ∀ p ∈ halfBall ν y δ, fderivWithin ℝ w (halfBall ν y δ) p =
        fderivWithin ℝ w B p := fun p hp ↦
      fderivWithin_subset (hyB.trans hρ'B) (hu p hp)
        (hw.1.differentiableOn one_ne_zero p (hρ'B (hyB hp)))
    have hint := norm_fderivWithin_halfBall_le hν hδ hy0 (u := w)
      ((hw.1.differentiableOn one_ne_zero).mono (hyB.trans hρ'B)) hα' hα1' hHp hε
      (fun p hp q hq ↦ by
        rw [hfw p hp, hfw q hq, ← dist_eq_norm]
        have e : dist (gW p) (gW q) = dist (fderivWithin ℝ w B p) (fderivWithin ℝ w B q) := by
          simp only [hgW, gradientWithin, LinearIsometryEquiv.dist_map]
        rw [← e]
        exact dist_le_holderSeminormOn_mul hfin' (hyB hp) (hyB hq))
      (fun p hp q hq ↦ by
        rw [Real.norm_eq_abs]
        exact hO p (hρ'B (hyB hp)) q (hρ'B (hyB hq)))
      y ⟨mem_closedBall_self hδ.le, hy0⟩
    rw [hfw y ⟨mem_closedBall_self hδ.le, hy0⟩] at hint
    have hng : ‖gW y‖ = ‖fderivWithin ℝ w B y‖ := by
      simp only [hgW, gradientWithin, LinearIsometryEquiv.norm_map]
    rw [hng]
    refine hint.trans (add_le_add le_rfl ?_)
    have : 0 ≤ δ⁻¹ * O := by positivity
    calc interpConst ε α * δ⁻¹ * O = interpConst ε α * (δ⁻¹ * O) := by ring
      _ ≤ Cε * (δ⁻¹ * O) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = Cε * δ⁻¹ * O := by ring
  -- the local Hölder bound on `halfBall ν z ρ`, solution restricted to `halfBall ν z (ρ + δ)`
  have hsub : halfBall ν z (ρ + δ) ⊆ B := halfBall_mono ν z (by linarith)
  have hcl : closedBall z (ρ + δ) ⊆ closedBall z R := closedBall_subset_closedBall (by linarith)
  have hbl : ball z (ρ + δ) ⊆ ball z R := ball_subset_ball (by linarith)
  have hρδ0 : 0 < ρ + δ := by linarith
  have hw' := hw.restrict_halfBall hν hρδ0 (by linarith) hcl hbl
  have hu' := uniqueDiffOn_halfBall hν hρδ0 (by linarith : -(ρ + δ) < ⟪z, ν⟫)
  have hgeq : ∀ y ∈ halfBall ν z (ρ + δ),
      gradientWithin w (halfBall ν z (ρ + δ)) y = gW y := fun y hy ↦
    gradientWithin_eq_of_subset hsub (hu' y hy) (hw.1.differentiableOn one_ne_zero y (hsub hy))
  have hloc' := hloc ν z Ka KG Mf M₀ MG (ρ + δ) δ ρ a G f w hν hz hδ hδρ le_rfl (hell.mono hsub)
    (fun y hy ↦ hsym y (hsub hy)) (ha.mono hsub) (hG.mono hsub) (fun y hy ↦ hMG y (hsub hy))
    (hfm.mono_measure (Measure.restrict_mono hsub le_rfl)) (fun y hy ↦ hfb y (hsub hy)) hw'
    (fun y hy ↦ by rw [hgeq y hy]; exact hM₀ y hy)
  have hρsub : halfBall ν z ρ ⊆ halfBall ν z (ρ + δ) := halfBall_mono ν z (by linarith)
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hY0 : 0 ≤ C₁ * ((M₀ + MG) * δ ^ (-(α : ℝ)) + Ka * (M₀ + MG) + KG +
      Mf * δ ^ (1 - (α : ℝ))) := by
    have := Real.rpow_nonneg hδ.le (-(α : ℝ))
    have := Real.rpow_nonneg hδ.le (1 - (α : ℝ))
    positivity
  refine (holderSeminormOn_le_of_dist_le hY0 fun p hp q hq ↦ ?_).trans ?_
  · have h := hloc' p hp q hq
    rwa [hgeq p (hρsub hp), hgeq q (hρsub hq)] at h
  exact hole_algebra hα' hα1' hC₁ hδ hδr hR hρρ' hδdef hM₀def hHp hO0 hMG0 hMf hCε hε
    hεdef hKa Ka.2

/-- The algebra after absorption in `c1Holder_halfBall_estimate_core`. -/
private theorem main_algebra {R α C₁ Kp A₀ Cab O Mf MG KG Hh : ℝ} (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hKp : 0 ≤ Kp) (hA₀ : 0 ≤ A₀) (hCab : 1 ≤ Cab)
    (hO0 : 0 ≤ O) (hMf : 0 ≤ Mf) (hMG0 : 0 ≤ MG) (hKG : 0 ≤ KG)
    (habs : Hh ≤ Cab * (A₀ * (O + R * MG) * (R / 4) ^ (-(1 + α)) +
      (C₁ * KG + C₁ * Mf * R ^ (1 - α) + C₁ * Kp * R ^ (-α) * MG))) :
    R ^ (1 + α) * Hh ≤ Cab * (A₀ * 4 ^ (1 + α) + C₁ * (1 + Kp)) *
      (O + R ^ (1 + α) * KG + R * MG + R ^ 2 * Mf) := by
  set Bc := C₁ * KG + C₁ * Mf * R ^ (1 - α) + C₁ * Kp * R ^ (-α) * MG
  set C₀ := Cab * (A₀ * 4 ^ (1 + α) + C₁ * (1 + Kp))
  have hr1 : R ^ (1 + α) * (R / 4) ^ (-(1 + α)) = 4 ^ (1 + α) := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hR.le (by norm_num)]
    field_simp
  have hr2 : R ^ (1 - α) * R ^ (1 + α) = R ^ 2 := by
    rw [← Real.rpow_add hR, ← Real.rpow_natCast]; congr 1; push_cast; ring
  have hr3 : R ^ (-α) * R ^ (1 + α) = R := by
    rw [← Real.rpow_add hR]; simp
  have hrα : 0 ≤ R ^ (1 + α) := Real.rpow_nonneg hR.le _
  set Z := O + R ^ (1 + α) * KG + R * MG + R ^ 2 * Mf with hZ
  have hmain : R ^ (1 + α) * Hh ≤ C₀ * Z := by
    calc R ^ (1 + α) * Hh
        ≤ R ^ (1 + α) * (Cab * (A₀ * (O + R * MG) * (R / 4) ^ (-(1 + α)) + Bc)) :=
          mul_le_mul_of_nonneg_left habs hrα
      _ = Cab * (A₀ * (O + R * MG) * (R ^ (1 + α) * (R / 4) ^ (-(1 + α))) +
            (C₁ * (R ^ (1 + α) * KG) + C₁ * Mf * (R ^ (1 - α) *
              R ^ (1 + α)) + C₁ * Kp * MG * (R ^ (-α) * R ^ (1 + α)))) := by
          ring
      _ = Cab * (A₀ * 4 ^ (1 + α) * (O + R * MG) +
            C₁ * (R ^ (1 + α) * KG + R ^ 2 * Mf + Kp * (R * MG))) := by
          rw [hr1, hr2, hr3]; ring
      _ ≤ C₀ * Z := by
          have h2 : 0 ≤ A₀ * 4 ^ (1 + α) := by positivity
          have h3 : 0 ≤ R ^ (1 + α) * KG := by positivity
          have h4 : 0 ≤ R ^ 2 * Mf := by positivity
          have h5 : 0 ≤ R * MG := by positivity
          have h6 : 0 ≤ Cab := by linarith
          have e : C₀ * Z = Cab * (A₀ * 4 ^ (1 + α) * Z + C₁ * (1 + Kp) * Z) := by
            rw [hZ]; ring
          rw [e]
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) h6
          · exact mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) h2
          · have : R ^ (1 + α) * KG + R ^ 2 * Mf + Kp * (R * MG) ≤ (1 + Kp) * Z := by
              rw [hZ]; nlinarith [mul_nonneg hKp h3, mul_nonneg hKp h4, mul_nonneg hKp hO0]
            calc C₁ * (R ^ (1 + α) * KG + R ^ 2 * Mf + Kp * (R * MG))
                ≤ C₁ * ((1 + Kp) * Z) := mul_le_mul_of_nonneg_left this hC₁
              _ = C₁ * (1 + Kp) * Z := by ring
  exact hmain

omit [MeasurableSpace E] [BorelSpace E] in
/-- The gradient at the centre (interpolation on `halfBall ν z (R/2)` with `ε = 1`). -/
private theorem centre_bound {ν z : E} {R O : ℝ} {α : ℝ≥0} {w : E → ℝ} (hν : ‖ν‖ = 1)
    (hz : 0 ≤ ⟪z, ν⟫) (hR : 0 < R) (hw : ContDiffOn ℝ 1 w (halfBall ν z R))
    (hfin2 : eHolderSeminormOn α (gradientWithin w (halfBall ν z R)) (halfBall ν z (3 * R / 4))
      ≠ ⊤)
    (hO : ∀ p ∈ halfBall ν z R, ∀ q ∈ halfBall ν z R, |w p - w q| ≤ O) (hO0 : 0 ≤ O)
    (hα' : (0 : ℝ) < α) (hα1' : (α : ℝ) ≤ 1) :
    R * ‖gradientWithin w (halfBall ν z R) z‖ ≤
      R ^ (1 + (α : ℝ)) * holderSeminormOn α (gradientWithin w (halfBall ν z R))
        (halfBall ν z (3 * R / 4)) + 2 * max (interpConst 1 α) 0 * O := by
  set B := halfBall ν z R with hB
  set gW := gradientWithin w B with hgW
  set Hh := holderSeminormOn α gW (halfBall ν z (3 * R / 4))
  have hHh : 0 ≤ Hh := holderSeminormOn_nonneg _ _ _
  set Ci := max (interpConst 1 α) 0
  have hsub2 : halfBall ν z (R / 2) ⊆ B := halfBall_mono ν z (by linarith)
  have hsub3 : halfBall ν z (R / 2) ⊆ halfBall ν z (3 * R / 4) := halfBall_mono ν z (by linarith)
  have hu : UniqueDiffOn ℝ (halfBall ν z (R / 2)) :=
    uniqueDiffOn_halfBall hν (by positivity) (by linarith)
  have hfw : ∀ p ∈ halfBall ν z (R / 2), fderivWithin ℝ w (halfBall ν z (R / 2)) p =
      fderivWithin ℝ w B p := fun p hp ↦
    fderivWithin_subset hsub2 (hu p hp) (hw.differentiableOn one_ne_zero p (hsub2 hp))
  have hzR2 : z ∈ halfBall ν z (R / 2) := ⟨mem_closedBall_self (by positivity), hz⟩
  have hint := norm_fderivWithin_halfBall_le hν (R := R / 2) (by positivity) hz (u := w)
    ((hw.differentiableOn one_ne_zero).mono hsub2) hα' hα1' hHh one_pos
    (fun p hp q hq ↦ by
      rw [hfw p hp, hfw q hq, ← dist_eq_norm]
      have e : dist (gW p) (gW q) = dist (fderivWithin ℝ w B p) (fderivWithin ℝ w B q) := by
        simp only [hgW, gradientWithin, LinearIsometryEquiv.dist_map]
      rw [← e]
      exact dist_le_holderSeminormOn_mul hfin2 (hsub3 hp) (hsub3 hq))
    (fun p hp q hq ↦ by
      rw [Real.norm_eq_abs]
      exact hO p (hsub2 hp) q (hsub2 hq))
    z hzR2
  rw [hfw z hzR2] at hint
  have hng : ‖gW z‖ = ‖fderivWithin ℝ w B z‖ := by
    simp only [hgW, gradientWithin, LinearIsometryEquiv.norm_map]
  rw [hng]
  have h1 : interpConst 1 α * (R / 2)⁻¹ * O ≤ Ci * (R / 2)⁻¹ * O := by
    have : 0 ≤ (R / 2)⁻¹ * O := by positivity
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left (interpConst 1 α) 0) this
  have h2 : (R / 2) ^ (α : ℝ) ≤ R ^ (α : ℝ) := Real.rpow_le_rpow (by positivity)
    (by linarith) α.2
  have h3 : R * R ^ (α : ℝ) = R ^ (1 + (α : ℝ)) := by
    rw [Real.rpow_add hR, Real.rpow_one]
  calc R * ‖fderivWithin ℝ w B z‖ ≤ R * (1 * (R / 2) ^ (α : ℝ) * Hh + Ci * (R / 2)⁻¹ * O) :=
        mul_le_mul_of_nonneg_left (hint.trans (add_le_add le_rfl h1)) hR.le
    _ = R * (R / 2) ^ (α : ℝ) * Hh + 2 * Ci * O := by field_simp
    _ ≤ R * R ^ (α : ℝ) * Hh + 2 * Ci * O := by gcongr
    _ = R ^ (1 + (α : ℝ)) * Hh + 2 * Ci * O := by rw [h3]


variable (E) in
/-- **Scaled conormal `C^{1,α}` estimate at a centre in the closed half space** (see the module
docstring). -/
theorem c1Holder_halfBall_estimate_core {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Λ K : ℝ}
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν z : E) (R : ℝ) (Ka KG : ℝ≥0) (MG Mf O : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 ≤ ⟪z, ν⟫ → 0 < R →
      IsUniformlyElliptic lam Λ a (halfBall ν z R) → IsSymmetricOn a (halfBall ν z R) →
      HolderOnWith Ka α a (halfBall ν z R) → (Ka : ℝ) * R ^ (α : ℝ) ≤ K →
      HolderOnWith KG α G (halfBall ν z R) → (∀ y ∈ halfBall ν z R, ‖G y‖ ≤ MG) →
      AEStronglyMeasurable f (volume.restrict (halfBall ν z R)) →
      (∀ y ∈ halfBall ν z R, |f y| ≤ Mf) → IsConormalSolOn ν a G f z R w →
      (∀ p ∈ halfBall ν z R, ∀ q ∈ halfBall ν z R, |w p - w q| ≤ O) →
      ∀ S ⊆ halfBall ν z (3 * R / 4),
      R * ‖gradientWithin w (halfBall ν z R) z‖ +
          R ^ (1 + (α : ℝ)) * holderSeminormOn α (gradientWithin w (halfBall ν z R)) S ≤
        C * (O + R ^ (1 + (α : ℝ)) * KG + R * MG + R ^ 2 * Mf) := by
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1.le
  obtain ⟨C₁, hC₁, hloc⟩ := dist_gradientWithin_le_of_isConormalSolOn E hα hα1 hlam
  set Kp := max K 0
  have hKp : 0 ≤ Kp := le_max_right _ _
  set Cε := max (interpConst (1 / (2 * (C₁ * (1 + Kp) + 1))) α) 0
  have hCε : 0 ≤ Cε := le_max_right _ _
  set A₀ := C₁ * (1 + Kp) * (Cε + 1) * 2 ^ (1 + (α : ℝ))
  have hA₀ : 0 ≤ A₀ := by positivity
  set Cab := absorbConst (1 / 2) (1 + (α : ℝ))
  have hCab : 1 ≤ Cab := one_le_absorbConst (by norm_num) (by norm_num) (by positivity)
  set Ci := max (interpConst 1 α) 0
  have hCi : 0 ≤ Ci := le_max_right _ _
  set C₀ := Cab * (A₀ * 4 ^ (1 + (α : ℝ)) + C₁ * (1 + Kp))
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨2 * C₀ + 2 * Ci, by positivity, ?_⟩
  intro ν z R Ka KG MG Mf O a G f w hν hz hR hell hsym ha hKa hG hMG hfm hfb hw hO S hS
  set B := halfBall ν z R with hB
  set gW := gradientWithin w B with hgW
  have hzB : z ∈ B := ⟨mem_closedBall_self hR.le, hz⟩
  have hO0 : 0 ≤ O := (abs_nonneg _).trans (hO z hzB z hzB)
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb z hzB)
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG z hzB)
  -- finiteness on `halfBall ν z (7R/8)`
  have hgc := continuousOn_gradientWithin_halfBall hν hR (by linarith) hw.1
  obtain ⟨M₀, hM₀⟩ := (isCompact_halfBall ν z R).exists_bound_of_continuousOn hgc
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ z hzB)
  have hfinH := hloc ν z Ka KG Mf M₀ MG R (R / 8) (7 * R / 8) a G f w hν hz (by positivity)
    (by linarith) (by linarith) hell hsym ha hG hMG hfm hfb hw hM₀
  have hY : 0 ≤ C₁ * ((M₀ + MG) * (R / 8) ^ (-(α : ℝ)) + Ka * (M₀ + MG) + KG +
      Mf * (R / 8) ^ (1 - (α : ℝ))) := by
    have := Real.rpow_nonneg (by positivity : 0 ≤ R / 8) (-(α : ℝ))
    have := Real.rpow_nonneg (by positivity : 0 ≤ R / 8) (1 - (α : ℝ))
    positivity
  have hfin : eHolderSeminormOn α gW (halfBall ν z (7 * R / 8)) ≠ ⊤ :=
    (eHolderSeminormOn_lt_top_of_holderOnWith (holderOnWith_of_dist_le hY hfinH)).ne
  set H : ℝ → ℝ := fun t ↦ holderSeminormOn α gW (halfBall ν z t) with hHdef
  have hHmono : ∀ t ≤ 7 * R / 8, H t ≤ H (7 * R / 8) := fun t ht ↦
    ENNReal.toReal_mono hfin (eHolderSeminormOn_mono (halfBall_mono ν z ht))
  set Bc := C₁ * KG + C₁ * Mf * R ^ (1 - (α : ℝ)) + C₁ * Kp * R ^ (-(α : ℝ)) * MG
  have hBc : 0 ≤ Bc := by
    have := Real.rpow_nonneg hR.le (1 - (α : ℝ))
    have := Real.rpow_nonneg hR.le (-(α : ℝ))
    positivity
  have hhf := hole_filling_b hα hα1 hloc hC₁ hν hz hR hell hsym ha hKa hG hMG hfm hfb hw hfin hO
    hO0 hMG0
  have habs := le_of_absorption_shift (Q := H) (s := 3 * R / 4) (T := 7 * R / 8)
    (θ := 1 / 2) (γ := 1 + (α : ℝ)) (A := A₀ * (O + R * MG)) (B := Bc) (by norm_num)
    (by norm_num) (by positivity) (by linarith) (by positivity) hBc hhf
    ⟨H (7 * R / 8), by rintro _ ⟨t, ht, rfl⟩; exact hHmono t ht.2⟩
    (fun t _ ↦ holderSeminormOn_nonneg _ _ _)
  rw [show 2 * (7 * R / 8 - 3 * R / 4) = R / 4 by ring] at habs
  set Hh := H (3 * R / 4)
  have hHh : 0 ≤ Hh := holderSeminormOn_nonneg _ _ _
  set Z := O + R ^ (1 + (α : ℝ)) * KG + R * MG + R ^ 2 * Mf with hZ
  have hmain : R ^ (1 + (α : ℝ)) * Hh ≤ C₀ * Z :=
    main_algebra hR hC₁ hKp hA₀ hCab hO0 hMf hMG0 KG.2 habs
  have hfin2 : eHolderSeminormOn α gW (halfBall ν z (3 * R / 4)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eHolderSeminormOn_mono (halfBall_mono ν z (by linarith)))
  have hcentre : R * ‖gW z‖ ≤ R ^ (1 + (α : ℝ)) * Hh + 2 * Ci * O :=
    centre_bound hν hz hR hw.1 hfin2 hO hO0 hα' hα1'
  have hZO : O ≤ Z := by
    have : 0 ≤ R ^ (1 + (α : ℝ)) * KG := by positivity
    have : 0 ≤ R * MG := by positivity
    have : 0 ≤ R ^ 2 * Mf := by positivity
    rw [hZ]; linarith
  have hHS : holderSeminormOn α gW S ≤ Hh :=
    ENNReal.toReal_mono hfin2 (eHolderSeminormOn_mono hS)
  calc R * ‖gW z‖ + R ^ (1 + (α : ℝ)) * holderSeminormOn α gW S
      ≤ R * ‖gW z‖ + R ^ (1 + (α : ℝ)) * Hh := by gcongr
    _ ≤ 2 * (C₀ * Z) + 2 * Ci * O := by linarith
    _ ≤ 2 * (C₀ * Z) + 2 * Ci * Z := by gcongr
    _ = (2 * C₀ + 2 * Ci) * Z := by ring

end BasicElliptic.Div
