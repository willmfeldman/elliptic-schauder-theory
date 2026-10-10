/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Interior.GradientCampanato
public import BasicElliptic.Campanato.Holder
import BasicElliptic.Campanato.Density
import BasicElliptic.Common.RealArith

/-!
# Quantitative local Hölder bound for `∇w`

`BasicElliptic.Div.dist_gradient_le_of_isWeakSolOn`: there is `C = C(E, α, lam, Λ)` such that,
for a weak solution `w ∈ C¹(U)` as in `gradient_campanato_at_point`, a closed ball
`closedBall z (ρ + δ) ⊆ U` with `0 < δ ≤ ρ` and `‖∇w‖ ≤ M₀` on it,

`|∇w(p) - ∇w(q)| ≤ C (M₀ δ^{-α} + K_a M₀ + K_G + M_f δ^{1-α}) |p - q|^α`
for `p, q ∈ closedBall z ρ`.

## Proof

For `x₀ ∈ S = closedBall z ρ`, `B_δ(x₀) ⊆ closedBall z (ρ + δ)`, so
`gradient_campanato_at_point` gives `⨍_{B_r(x₀) ∩ S} ‖∇w - (∇w)_{B_r(x₀) ∩ S}‖² ≤ M'² r^{2α}`
for `r ≤ ρ₀ = √(lam/Λ) δ` (`≤ ρ`), with `M'² = C X / c₀`,
`X = M₀² δ^{-2α} + K_a² M₀² + K_G² + M_f² δ^{2-2α} ≤ Y²`, `Y` the bracket above, and `c₀` the
density constant of closed balls. Campanato's characterization gives the bound for
`|p - q| < ρ₀ / 2`; for the other pairs `|∇w(p) - ∇w(q)| ≤ 2 M₀ ≤ 2 M₀ (ρ₀/2)^{-α} |p - q|^α`.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient NNReal

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `lam ≤ Λ` for a uniformly elliptic field on a nonempty set in a nontrivial space. -/
theorem lam_le_of_isUniformlyElliptic [Nontrivial E] {lam Λ : ℝ} {a : E → E →L[ℝ] E}
    {U : Set E} (hell : IsUniformlyElliptic lam Λ a U) {x₀ : E} (hx₀ : x₀ ∈ U) : lam ≤ Λ := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  have hξ0 : 0 < ‖ξ‖ ^ 2 := by positivity
  have h1 := (hell x₀ hx₀).1 ξ
  have h2 : ⟪a x₀ ξ, ξ⟫ ≤ Λ * ‖ξ‖ ^ 2 :=
    (real_inner_le_norm _ _).trans (by
      calc ‖a x₀ ξ‖ * ‖ξ‖ ≤ ‖a x₀‖ * ‖ξ‖ * ‖ξ‖ :=
            mul_le_mul_of_nonneg_right ((a x₀).le_opNorm ξ) (norm_nonneg _)
        _ ≤ Λ * ‖ξ‖ * ‖ξ‖ := by
            gcongr; exact (hell x₀ hx₀).2
        _ = Λ * ‖ξ‖ ^ 2 := by ring)
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- `∇w` is continuous on an open set where `w` is `C¹`. -/
theorem continuousOn_gradient_of_contDiffOn {U : Set E} {w : E → ℝ} (hU : IsOpen U)
    (hw : ContDiffOn ℝ 1 w U) : ContinuousOn (∇ w) U :=
  (toDual ℝ E).symm.continuous.comp_continuousOn (hw.continuousOn_fderiv_of_isOpen hU le_rfl)

variable (E) in
/-- **Quantitative local Hölder bound for `∇w`** (see the module docstring). -/
theorem dist_gradient_le_of_isWeakSolOn {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set E) (Ka KG : ℝ≥0) (Mf M₀ δ ρ : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ) (z : E),
      IsOpen U → IsUniformlyElliptic lam Λ a U → HolderOnWith Ka α a U →
      HolderOnWith KG α G U → (∀ y ∈ U, |f y| ≤ Mf) → IsWeakSolOn a G f U w →
      0 < δ → δ ≤ ρ → closedBall z (ρ + δ) ⊆ U → (∀ y ∈ closedBall z (ρ + δ), ‖∇ w y‖ ≤ M₀) →
      ∀ p ∈ closedBall z ρ, ∀ q ∈ closedBall z ρ,
        dist (∇ w p) (∇ w q) ≤
          C * (M₀ * δ ^ (-(α : ℝ)) + Ka * M₀ + KG + Mf * δ ^ (1 - (α : ℝ))) *
            dist p q ^ (α : ℝ) := by
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1.le
  obtain ⟨C, hC0, hcamp⟩ := gradient_campanato_at_point E hα hα1 hlam
  set c₀ := unitBallVolume E * (1 / 4) ^ finrank ℝ E
  have hc₀ : 0 < c₀ := mul_pos unitBallVolume_pos (by positivity)
  set κ := √(lam / Λ)
  set Kc := campanatoHolderConst E c₀ α
  have hKc : 0 ≤ Kc := campanatoHolderConst_nonneg hα'
  refine ⟨Kc * √(C / c₀) + 2 * (κ / 2) ^ (-(α : ℝ)), by
    have := Real.rpow_nonneg (by positivity : 0 ≤ κ / 2) (-(α : ℝ)); positivity, ?_⟩
  intro U Ka KG Mf M₀ δ ρ a G f w z hU hell ha hG hfb hw hδ hδρ hsub hM₀ p hp q hq
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hzU : z ∈ U := hsub (mem_closedBall_self (by positivity))
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ z (mem_closedBall_self (by positivity)))
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb z hzU)
  set Y := M₀ * δ ^ (-(α : ℝ)) + Ka * M₀ + KG + Mf * δ ^ (1 - (α : ℝ)) with hY
  have hδa : 0 ≤ δ ^ (-(α : ℝ)) := Real.rpow_nonneg hδ.le _
  have hδb : 0 ≤ δ ^ (1 - (α : ℝ)) := Real.rpow_nonneg hδ.le _
  have hY0 : 0 ≤ Y := by positivity
  have hpq : 0 ≤ dist p q ^ (α : ℝ) := Real.rpow_nonneg dist_nonneg _
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [Subsingleton.elim p q, dist_self]
    have := Real.rpow_nonneg (by positivity : 0 ≤ κ / 2) (-(α : ℝ))
    positivity
  set S := closedBall z ρ
  have hlamΛ := lam_le_of_isUniformlyElliptic hell hzU
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  have hκ : 0 < κ := Real.sqrt_pos.2 (div_pos hlam hΛ)
  have hκ1 : κ ≤ 1 := Real.sqrt_le_one.2 ((div_le_one hΛ).2 hlamΛ)
  set ρ₀ := κ * δ
  have hρ₀ : 0 < ρ₀ := mul_pos hκ hδ
  have hρ₀ρ : ρ₀ ≤ ρ := (mul_le_of_le_one_left hδ.le hκ1).trans hδρ
  have hgradc := continuousOn_gradient_of_contDiffOn hU hw.1
  have hballU : ∀ x₀ ∈ S, ball x₀ δ ⊆ closedBall z (ρ + δ) := fun x₀ hx₀ y hy ↦ by
    rw [mem_closedBall] at hx₀ ⊢
    rw [mem_ball] at hy
    linarith [dist_triangle y x₀ z]
  -- the uniform Campanato bound
  set X := M₀ ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * M₀ ^ 2 + (KG : ℝ) ^ 2 +
    Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) with hX
  have hX0 : 0 ≤ X := by
    have := Real.rpow_nonneg hδ.le (-(2 * (α : ℝ)))
    have := Real.rpow_nonneg hδ.le (2 - 2 * (α : ℝ))
    positivity
  have hdens : HasDensity S c₀ ρ₀ := (closedBall_density hρ).mono_scale hρ₀ρ
  set M' := √(C * X / c₀)
  have hM' : 0 ≤ M' := Real.sqrt_nonneg _
  have hcampS : IsCampanatoOn S (∇ w) α M' ρ₀ := by
    intro x₀ hx₀ r hr
    have hr0 := hr.1
    have hint := hcamp U Ka KG Mf M₀ δ a G f w x₀ hU hell ha hG hfb hw hδ
      ((hballU x₀ hx₀).trans hsub) (fun y hy ↦ hM₀ y (hballU x₀ hx₀ hy)) S r hr0 hr.2
    have hvol : c₀ * r ^ finrank ℝ E ≤ volume.real (ball x₀ r ∩ S) := hdens x₀ hx₀ r hr
    have hvol0 : 0 < c₀ * r ^ finrank ℝ E := by positivity
    rw [setAverage_eq, smul_eq_mul]
    have hI0 : 0 ≤ ∫ y in ball x₀ r ∩ S, ‖∇ w y - ⨍ z in ball x₀ r ∩ S, ∇ w z‖ ^ 2 :=
      integral_nonneg fun _ ↦ sq_nonneg _
    have hrb : r ^ ((finrank ℝ E : ℝ) + 2 * α) = r ^ finrank ℝ E * r ^ (2 * (α : ℝ)) := by
      rw [Real.rpow_add hr0, Real.rpow_natCast]
    calc (volume.real (ball x₀ r ∩ S))⁻¹ *
          ∫ y in ball x₀ r ∩ S, ‖∇ w y - ⨍ z in ball x₀ r ∩ S, ∇ w z‖ ^ 2
        ≤ (c₀ * r ^ finrank ℝ E)⁻¹ * (C * r ^ ((finrank ℝ E : ℝ) + 2 * α) * X) := by
          gcongr
      _ = M' ^ 2 * r ^ (2 * (α : ℝ)) := by
          rw [Real.sq_sqrt (by positivity), hrb]
          field_simp
  have hM'Y : M' ≤ √(C / c₀) * Y := by
    have hXY : √X ≤ Y := by
      have e1 : (M₀ * δ ^ (-(α : ℝ))) ^ 2 = M₀ ^ 2 * δ ^ (-(2 * (α : ℝ))) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hδ.le]; congr 2; push_cast; ring
      have e2 : (Mf * δ ^ (1 - (α : ℝ))) ^ 2 = Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hδ.le]; congr 2; push_cast; ring
      have e3 : ((Ka : ℝ) * M₀) ^ 2 = (Ka : ℝ) ^ 2 * M₀ ^ 2 := by ring
      have := sqrt_sum_four_sq_le (by positivity : 0 ≤ M₀ * δ ^ (-(α : ℝ)))
        (by positivity : 0 ≤ (Ka : ℝ) * M₀) (KG.2) (by positivity : 0 ≤ Mf * δ ^ (1 - (α : ℝ)))
      rwa [e1, e2, e3] at this
    calc M' = √(C / c₀) * √X := by
          rw [← Real.sqrt_mul (by positivity)]
          exact congrArg Real.sqrt (by ring)
      _ ≤ √(C / c₀) * Y := mul_le_mul_of_nonneg_left hXY (Real.sqrt_nonneg _)
  have hSc : IsCompact S := isCompact_closedBall z ρ
  have hgS : ContinuousOn (∇ w) S :=
    hgradc.mono ((closedBall_subset_closedBall (by linarith)).trans hsub)
  rcases lt_or_ge (dist p q) (ρ₀ / 2) with hnear | hfar
  · rw [dist_eq_norm]
    refine (norm_sub_le_of_campanato hα' hα1' hM' hc₀ hSc hdens hgS hcampS hp hq
      hnear.le).trans ?_
    have h2 : 0 ≤ 2 * (κ / 2) ^ (-(α : ℝ)) * Y :=
      mul_nonneg (mul_nonneg zero_le_two (Real.rpow_nonneg (by positivity) _)) hY0
    calc Kc * M' * dist p q ^ (α : ℝ) ≤ Kc * (√(C / c₀) * Y) * dist p q ^ (α : ℝ) := by
          gcongr
      _ ≤ (Kc * √(C / c₀) + 2 * (κ / 2) ^ (-(α : ℝ))) * Y * dist p q ^ (α : ℝ) := by
          rw [add_mul, add_mul]
          nlinarith [mul_nonneg h2 hpq]
  · have hpS : p ∈ closedBall z (ρ + δ) := closedBall_subset_closedBall (by linarith) hp
    have hqS : q ∈ closedBall z (ρ + δ) := closedBall_subset_closedBall (by linarith) hq
    have h1 : dist (∇ w p) (∇ w q) ≤ 2 * M₀ := by
      rw [dist_eq_norm]
      linarith [norm_sub_le (∇ w p) (∇ w q), hM₀ p hpS, hM₀ q hqS]
    have h2 : 1 ≤ (ρ₀ / 2) ^ (-(α : ℝ)) * dist p q ^ (α : ℝ) := by
      rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
        le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _), one_mul]
      exact Real.rpow_le_rpow (by positivity) hfar α.2
    have h3 : (ρ₀ / 2) ^ (-(α : ℝ)) = (κ / 2) ^ (-(α : ℝ)) * δ ^ (-(α : ℝ)) := by
      rw [show ρ₀ / 2 = κ / 2 * δ by ring, Real.mul_rpow (by positivity) hδ.le]
    have h4 : M₀ * δ ^ (-(α : ℝ)) ≤ Y := by
      have : 0 ≤ (Ka : ℝ) * M₀ := by positivity
      have : 0 ≤ Mf * δ ^ (1 - (α : ℝ)) := by positivity
      rw [hY]
      linarith [NNReal.coe_nonneg KG]
    have h5 : 0 ≤ Kc * √(C / c₀) * Y * dist p q ^ (α : ℝ) := by positivity
    have hκα : 0 ≤ (κ / 2) ^ (-(α : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc dist (∇ w p) (∇ w q) ≤ 2 * M₀ * ((ρ₀ / 2) ^ (-(α : ℝ)) * dist p q ^ (α : ℝ)) :=
          h1.trans (le_mul_of_one_le_right (by positivity) h2)
      _ = 2 * (κ / 2) ^ (-(α : ℝ)) * (M₀ * δ ^ (-(α : ℝ))) * dist p q ^ (α : ℝ) := by
          rw [h3]; ring
      _ ≤ 2 * (κ / 2) ^ (-(α : ℝ)) * Y * dist p q ^ (α : ℝ) := by gcongr
      _ ≤ _ := by rw [add_mul, add_mul]; linarith

end BasicElliptic.Div
