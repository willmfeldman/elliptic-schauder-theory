/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Div
import BasicElliptic.Div.Interior.LocalHolder
import BasicElliptic.Holder.Interpolation
import BasicElliptic.Common.Absorption
import BasicElliptic.Campanato.Holder
import BasicElliptic.Campanato.Density
import BasicElliptic.Holder.Algebra

/-!
# Interior `C^{1,α}` regularity in divergence form

`Div.contDiffHolderOn_one_of_isWeakSolution` and `Div.c1Holder_ball_estimate` prove
`Div.C1HolderBallStatement` and `Div.C1HolderBallEstimateStatement`.

## Qualitative regularity

Let `closedBall z ρ ⊆ U`, `ρ > 0`. Choose `δ > 0` with `closedBall z (ρ + δ) ⊆ U` and let `M₀`
bound `‖∇w‖` there (`w ∈ C¹(U)`, a compact set). For every `x₀ ∈ S = closedBall z ρ`,
`B_δ(x₀) ⊆ U`, so `gradient_campanato_at_point` gives the Campanato bound
`⨍_{B_r(x₀) ∩ S} ‖∇w - (∇w)_{B_r(x₀) ∩ S}‖² ≤ M'² r^{2α}` for `r ≤ ρ₀ = min ρ (√(lam/Λ) δ)`,
uniformly in `x₀` (closed balls have density `|B_1| 4^{-d}`, `closedBall_density`). Campanato's
characterization (`norm_sub_le_of_campanato`, continuity of `∇w` on `S`) gives the Hölder bound
for pairs at distance `≤ ρ₀ / 2`, and `‖∇w‖ ≤ M₀` handles the far pairs
(`holderOnWith_of_near_far`). Finally `dist (D¹w(x), D¹w(y)) = dist (∇w(x), ∇w(y))` for the
within-derivatives on the closed ball (unique differentiability; `w` is differentiable at the
points of the open `U`; the Riesz map is an isometry).

Both use the quantitative local bound `dist_gradient_le_of_isWeakSolOn`
(`Div/Interior/LocalHolder.lean`):
`[∇w]_{α, B_ρ} ≤ C₁ (M₀ δ^{-α} + K_a M₀ + K_G + M_f δ^{1-α})` when `‖∇w‖ ≤ M₀` on `B_{ρ+δ}`,
`δ ≤ ρ`.

## Scaled estimate (hole filling)

Let `H(t) = [∇w]_{α, B̄_t(x)}` and `O = osc_{B̄_r(x)} w`. `H` is finite on `[r/2, 3r/4]` by the
qualitative step (applied on `B̄_{3r/4} ⊆ B_r`). For `r/2 ≤ ρ < ρ' ≤ 3r/4` put `δ = (ρ' - ρ)/2`.
Interpolation on the balls `B̄_δ(y)`, `y ∈ B̄_{ρ+δ}` (`norm_fderivWithin_closedBall_le`), gives
`‖∇w‖ ≤ M₀ := ε δ^α H(ρ') + C_ε δ^{-1} O` on `B̄_{ρ+δ}`. The local bound and `K_a δ^α ≤ K`
(`δ ≤ r`) give
`H(ρ) ≤ C₁ (1 + K) ε H(ρ') + C₁ (1 + K) C_ε δ^{-1-α} O + C₁ K_G + C₁ M_f r^{1-α}`,
and `ε = 1 / (2 (C₁ (1 + K) + 1))` makes the first coefficient `≤ 1/2`. The absorption lemma
(`le_of_absorption`, shifted to `[r/2, 3r/4]`) gives
`r^{1+α} H(r/2) ≤ C (O + r^{1+α} K_G + r² M_f)`. Finally interpolation on `B̄_{r/2}(x)` with
`ε = 1` bounds `r ‖∇w(x)‖ ≤ r^{1+α} H(r/2) + 2 C_1 O`. The finiteness used in the absorption is
proved (qualitative step), not assumed.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient NNReal

public section

namespace BasicElliptic

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Div

variable {E}

/-- The local bound of `dist_gradient_le_of_isWeakSolOn` with constant `C₁`, as a predicate. -/
private def LocalBound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α : ℝ≥0) (lam Λ C₁ : ℝ) :
    Prop :=
  ∀ (U : Set E) (Ka KG : ℝ≥0) (Mf M₀ δ ρ : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ) (z : E),
      IsOpen U → IsUniformlyElliptic lam Λ a U → HolderOnWith Ka α a U →
      HolderOnWith KG α G U → (∀ y ∈ U, |f y| ≤ Mf) → IsWeakSolOn a G f U w →
      0 < δ → δ ≤ ρ → closedBall z (ρ + δ) ⊆ U → (∀ y ∈ closedBall z (ρ + δ), ‖∇ w y‖ ≤ M₀) →
      ∀ p ∈ closedBall z ρ, ∀ q ∈ closedBall z ρ,
        dist (∇ w p) (∇ w q) ≤
          C₁ * (M₀ * δ ^ (-(α : ℝ)) + Ka * M₀ + KG + Mf * δ ^ (1 - (α : ℝ))) *
            dist p q ^ (α : ℝ)

/-- **Finiteness** (the qualitative step): `∇w` is Hölder on every closed ball `B̄_ρ(z) ⊆ U`,
`ρ > 0`. -/
private theorem exists_holderOnWith_gradient {α : ℝ≥0} {lam Λ C₁ : ℝ}
    (hloc : LocalBound E α lam Λ C₁) (hC₁ : 0 ≤ C₁)
    {U : Set E} {Ka KG : ℝ≥0} {Mf : ℝ} {a : E → E →L[ℝ] E} {G : E → E}
    {f : E → ℝ} {w : E → ℝ} (hU : IsOpen U)
    (hell : IsUniformlyElliptic lam Λ a U) (ha : HolderOnWith Ka α a U)
    (hG : HolderOnWith KG α G U) (hfb : ∀ y ∈ U, |f y| ≤ Mf) (hw : IsWeakSolOn a G f U w)
    {z : E} {ρ : ℝ} (hρ : 0 < ρ) (hsub : closedBall z ρ ⊆ U) :
    ∃ C : ℝ≥0, HolderOnWith C α (∇ w) (closedBall z ρ) := by
  obtain ⟨δ₁, hδ₁, hδU⟩ := (isCompact_closedBall z ρ).exists_cthickening_subset_open hU hsub
  rw [cthickening_closedBall hδ₁.le hρ.le] at hδU
  set δ := min δ₁ ρ
  have hδ : 0 < δ := lt_min hδ₁ hρ
  have hsub' : closedBall z (ρ + δ) ⊆ U :=
    (closedBall_subset_closedBall (by linarith [min_le_left δ₁ ρ])).trans hδU
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall z (ρ + δ)).exists_bound_of_continuousOn
    ((continuousOn_gradient_of_contDiffOn hU hw.1).mono hsub')
  have h := hloc U Ka KG Mf M₀ δ ρ a G f w z hU hell ha hG hfb hw hδ (min_le_right _ _) hsub' hM₀
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ z (mem_closedBall_self (by positivity)))
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb z (hsub (mem_closedBall_self hρ.le)))
  have hY : 0 ≤ C₁ * (M₀ * δ ^ (-(α : ℝ)) + Ka * M₀ + KG + Mf * δ ^ (1 - (α : ℝ))) := by
    have := Real.rpow_nonneg hδ.le (-(α : ℝ))
    have := Real.rpow_nonneg hδ.le (1 - (α : ℝ))
    positivity
  exact ⟨_, holderOnWith_of_dist_le hY h⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- The Hölder seminorms of `Dw` and `∇w` agree (the Riesz map is an isometry). -/
private theorem eHolderSeminormOn_fderiv_eq (α : ℝ≥0) (w : E → ℝ) (s : Set E) :
    eHolderSeminormOn α (fderiv ℝ w) s = eHolderSeminormOn α (∇ w) s := by
  have e : ∀ x y, dist (∇ w x) (∇ w y) = dist (fderiv ℝ w x) (fderiv ℝ w y) := fun x y ↦ by
    simp only [gradient, LinearIsometryEquiv.dist_map]
  have hiff : ∀ C : ℝ≥0, HolderOnWith C α (fderiv ℝ w) s ↔ HolderOnWith C α (∇ w) s :=
    fun C ↦ by simp only [holderOnWith_iff_dist_le, e]
  simp only [eHolderSeminormOn, hiff]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Oscillation bound from `regionOsc` for a function continuous on a closed ball. -/
private theorem abs_sub_le_regionOsc {w : E → ℝ} {x : E} {r : ℝ}
    (hw : ContinuousOn w (closedBall x r)) {p q : E} (hp : p ∈ closedBall x r)
    (hq : q ∈ closedBall x r) : |w p - w q| ≤ regionOsc w (closedBall x r) := by
  have hc := (isCompact_closedBall x r).image_of_continuousOn hw
  have h1 : ∀ y ∈ closedBall x r, w y ≤ sSup (w '' closedBall x r) := fun y hy ↦
    le_csSup hc.bddAbove (mem_image_of_mem w hy)
  have h2 : ∀ y ∈ closedBall x r, sInf (w '' closedBall x r) ≤ w y := fun y hy ↦
    csInf_le hc.bddBelow (mem_image_of_mem w hy)
  rw [regionOsc_def, abs_le]
  constructor <;> linarith [h1 p hp, h1 q hq, h2 p hp, h2 q hq]

/-- **Hole filling** (see the module docstring): `H(ρ) ≤ H(ρ')/2 + A (ρ' - ρ)^{-(1+α)} + B`. -/
private theorem hole_filling {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Λ K C₁ : ℝ}
    (hloc : LocalBound E α lam Λ C₁) (hC₁ : 0 ≤ C₁) {x : E} {r : ℝ} {Ka KG : ℝ≥0} {Mf O : ℝ}
    {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ} (hr : 0 < r)
    (hell : IsUniformlyElliptic lam Λ a (ball x r)) (ha : HolderOnWith Ka α a (ball x r))
    (hKa : (Ka : ℝ) * r ^ (α : ℝ) ≤ K) (hG : HolderOnWith KG α G (ball x r))
    (hfb : ∀ y ∈ ball x r, |f y| ≤ Mf) (hw : IsWeakSolOn a G f (ball x r) w)
    (hfin : eHolderSeminormOn α (∇ w) (closedBall x (3 * r / 4)) ≠ ⊤)
    (hO : ∀ p ∈ closedBall x r, ∀ q ∈ closedBall x r, |w p - w q| ≤ O) (hO0 : 0 ≤ O) :
    ∀ ρ ρ', r / 2 ≤ ρ → ρ < ρ' → ρ' ≤ 3 * r / 4 →
      holderSeminormOn α (∇ w) (closedBall x ρ) ≤
        1 / 2 * holderSeminormOn α (∇ w) (closedBall x ρ') +
          C₁ * (1 + max K 0) *
            max (interpConst (1 / (2 * (C₁ * (1 + max K 0) + 1))) α) 0 *
              2 ^ (1 + (α : ℝ)) * O * (ρ' - ρ) ^ (-(1 + (α : ℝ))) +
          (C₁ * KG + C₁ * Mf * r ^ (1 - (α : ℝ))) := by
  intro ρ ρ' hρ hρρ' hρ'
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
  have hδr : δ ≤ r := by rw [hδdef]; linarith
  have hδρ : δ ≤ ρ := by rw [hδdef]; linarith
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb x (mem_ball_self hr))
  set Hp := holderSeminormOn α (∇ w) (closedBall x ρ')
  have hHp : 0 ≤ Hp := holderSeminormOn_nonneg _ _ _
  have hfin' : eHolderSeminormOn α (∇ w) (closedBall x ρ') ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eHolderSeminormOn_mono (closedBall_subset_closedBall hρ'))
  have hρ'r : closedBall x ρ' ⊆ ball x r :=
    closedBall_subset_ball (by linarith)
  have hdiff : ∀ y ∈ ball x r, DifferentiableAt ℝ w y := fun y hy ↦
    (hw.1.differentiableOn one_ne_zero y hy).differentiableAt (isOpen_ball.mem_nhds hy)
  -- interpolation: `‖∇w‖ ≤ M₀` on `B̄_{ρ+δ}`
  set M₀ := ε * δ ^ (α : ℝ) * Hp + Cε * δ⁻¹ * O with hM₀def
  have hM₀ : ∀ y ∈ closedBall x (ρ + δ), ‖∇ w y‖ ≤ M₀ := by
    intro y hy
    have hyB : closedBall y δ ⊆ closedBall x ρ' := fun p hp ↦ by
      rw [mem_closedBall] at hp hy ⊢
      linarith [dist_triangle p y x]
    have hu : UniqueDiffOn ℝ (closedBall y δ) :=
      uniqueDiffOn_convex (convex_closedBall y δ)
        (by rw [interior_closedBall y hδ.ne']; exact nonempty_ball.2 hδ)
    have hfw : ∀ p ∈ closedBall y δ, fderivWithin ℝ w (closedBall y δ) p = fderiv ℝ w p :=
      fun p hp ↦ fderivWithin_eq_fderiv (hu p hp) (hdiff p (hρ'r (hyB hp)))
    have hint := norm_fderivWithin_closedBall_le (x₀ := y) hδ (u := w)
      (fun p hp ↦ (hdiff p (hρ'r (hyB hp))).differentiableWithinAt) hα' hα1' hHp hε
      (fun p hp q hq ↦ by
        rw [hfw p hp, hfw q hq, ← dist_eq_norm]
        have e : dist (∇ w p) (∇ w q) = dist (fderiv ℝ w p) (fderiv ℝ w q) := by
          simp only [gradient, LinearIsometryEquiv.dist_map]
        rw [← e]
        exact dist_le_holderSeminormOn_mul hfin' (hyB hp) (hyB hq))
      (fun p hp q hq ↦ by
        rw [Real.norm_eq_abs]
        exact hO p ((hyB.trans (hρ'r.trans ball_subset_closedBall)) hp)
          q ((hyB.trans (hρ'r.trans ball_subset_closedBall)) hq))
      y (mem_closedBall_self hδ.le)
    rw [hfw y (mem_closedBall_self hδ.le)] at hint
    have hng : ‖∇ w y‖ = ‖fderiv ℝ w y‖ := by
      simp only [gradient, LinearIsometryEquiv.norm_map]
    rw [hng]
    refine hint.trans (add_le_add le_rfl ?_)
    have : 0 ≤ δ⁻¹ * O := by positivity
    calc interpConst ε α * δ⁻¹ * O = interpConst ε α * (δ⁻¹ * O) := by ring
      _ ≤ Cε * (δ⁻¹ * O) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = Cε * δ⁻¹ * O := by ring
  -- the local Hölder bound
  have hsubU : closedBall x (ρ + δ) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hloc' := hloc (ball x r) Ka KG Mf M₀ δ ρ a G f w x isOpen_ball hell ha hG hfb hw hδ hδρ
    hsubU hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hY0 : 0 ≤ C₁ * (M₀ * δ ^ (-(α : ℝ)) + Ka * M₀ + KG + Mf * δ ^ (1 - (α : ℝ))) := by
    have := Real.rpow_nonneg hδ.le (-(α : ℝ))
    have := Real.rpow_nonneg hδ.le (1 - (α : ℝ))
    positivity
  refine (holderSeminormOn_le_of_dist_le hY0 hloc').trans ?_
  -- algebra
  have hδα : δ ^ (α : ℝ) * δ ^ (-(α : ℝ)) = 1 := by
    rw [← Real.rpow_add hδ]; simp
  have hKaδ : (Ka : ℝ) * δ ^ (α : ℝ) ≤ Kp :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδr α.2) Ka.2).trans
      (hKa.trans (le_max_left _ _))
  have hδ1 : δ⁻¹ * δ ^ (-(α : ℝ)) = 2 ^ (1 + (α : ℝ)) * (ρ' - ρ) ^ (-(1 + (α : ℝ))) := by
    rw [hδdef, Real.rpow_neg (by positivity), Real.rpow_neg (by linarith),
      Real.div_rpow (by linarith) (by norm_num), Real.rpow_add (by linarith : (0 : ℝ) < ρ' - ρ),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_one]
    field_simp
  have hδ1' : δ⁻¹ = δ ^ (α : ℝ) * (δ⁻¹ * δ ^ (-(α : ℝ))) := by
    rw [mul_comm δ⁻¹, ← mul_assoc, hδα, one_mul]
  have hδr' : δ ^ (1 - (α : ℝ)) ≤ r ^ (1 - (α : ℝ)) :=
    Real.rpow_le_rpow hδ.le hδr (by linarith)
  set P := (ρ' - ρ) ^ (-(1 + (α : ℝ)))
  have hP : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  -- `M₀ δ^{-α} = ε Hp + Cε 2^{1+α} O P` and `Ka M₀ ≤ Kp (ε Hp + Cε 2^{1+α} O P)`
  have e1 : M₀ * δ ^ (-(α : ℝ)) = ε * Hp + Cε * 2 ^ (1 + (α : ℝ)) * O * P := by
    rw [hM₀def, add_mul, show ε * δ ^ (α : ℝ) * Hp * δ ^ (-(α : ℝ)) =
      ε * Hp * (δ ^ (α : ℝ) * δ ^ (-(α : ℝ))) by ring, hδα,
      show Cε * δ⁻¹ * O * δ ^ (-(α : ℝ)) = Cε * O * (δ⁻¹ * δ ^ (-(α : ℝ))) by ring, hδ1]
    ring
  have e2 : (Ka : ℝ) * M₀ = (Ka * δ ^ (α : ℝ)) * (M₀ * δ ^ (-(α : ℝ))) := by
    rw [show (Ka : ℝ) * δ ^ (α : ℝ) * (M₀ * δ ^ (-(α : ℝ))) =
      Ka * M₀ * (δ ^ (α : ℝ) * δ ^ (-(α : ℝ))) by ring, hδα, mul_one]
  have hT0 : 0 ≤ ε * Hp + Cε * 2 ^ (1 + (α : ℝ)) * O * P := by positivity
  have hKaM : (Ka : ℝ) * M₀ ≤ Kp * (ε * Hp + Cε * 2 ^ (1 + (α : ℝ)) * O * P) := by
    rw [e2, e1]; exact mul_le_mul_of_nonneg_right hKaδ hT0
  have hεC : C₁ * (1 + Kp) * ε ≤ 1 / 2 := by
    rw [hεdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hC₁ (by linarith : (0 : ℝ) ≤ 1 + Kp)]
  have hMfδ : Mf * δ ^ (1 - (α : ℝ)) ≤ Mf * r ^ (1 - (α : ℝ)) :=
    mul_le_mul_of_nonneg_left hδr' hMf
  calc C₁ * (M₀ * δ ^ (-(α : ℝ)) + Ka * M₀ + KG + Mf * δ ^ (1 - (α : ℝ)))
      ≤ C₁ * ((ε * Hp + Cε * 2 ^ (1 + (α : ℝ)) * O * P) +
          Kp * (ε * Hp + Cε * 2 ^ (1 + (α : ℝ)) * O * P) + KG + Mf * r ^ (1 - (α : ℝ))) := by
        rw [e1]; gcongr
    _ = C₁ * (1 + Kp) * ε * Hp + C₁ * (1 + Kp) * Cε * 2 ^ (1 + (α : ℝ)) * O * P +
          (C₁ * KG + C₁ * Mf * r ^ (1 - (α : ℝ))) := by ring
    _ ≤ 1 / 2 * Hp + C₁ * (1 + Kp) * Cε * 2 ^ (1 + (α : ℝ)) * O * P +
          (C₁ * KG + C₁ * Mf * r ^ (1 - (α : ℝ))) := by gcongr

end Div

/-- **Interior `C^{1,α}` regularity**, divergence form (`Div.C1HolderBallStatement`). -/
theorem Div.contDiffHolderOn_one_of_isWeakSolution : Div.C1HolderBallStatement E := by
  intro α hα hα1 U lam Λ Ka KG Mf a G f w hU hlam hell ha hG _ hfb hw z ρ hsub
  refine ⟨hw.1.mono hsub, ?_⟩
  rcases le_or_gt ρ 0 with hρ | hρ
  · -- the closed ball has at most one point
    refine ⟨0, holderOnWith_iff_dist_le.2 fun x hx y hy ↦ ?_⟩
    have hx' : x = z := dist_le_zero.1 ((mem_closedBall.1 hx).trans hρ)
    have hy' : y = z := dist_le_zero.1 ((mem_closedBall.1 hy).trans hρ)
    rw [hx', hy', dist_self]; positivity
  obtain ⟨C₁, hC₁, hloc⟩ := dist_gradient_le_of_isWeakSolOn E hα hα1 hlam
  obtain ⟨C, hC⟩ := Div.exists_holderOnWith_gradient hloc hC₁ hU hell ha hG hfb hw hρ hsub
  have hu : UniqueDiffOn ℝ (closedBall z ρ) :=
    uniqueDiffOn_convex (convex_closedBall z ρ)
      (by rw [interior_closedBall z hρ.ne']; exact nonempty_ball.2 hρ)
  have hdiff : ∀ y ∈ closedBall z ρ, DifferentiableAt ℝ w y := fun y hy ↦
    (hw.1.differentiableOn one_ne_zero y (hsub hy)).differentiableAt (hU.mem_nhds (hsub hy))
  refine ⟨C, holderOnWith_iff_dist_le.2 fun x hx y hy ↦ ?_⟩
  rw [dist_iteratedFDerivWithin_one w w (hu x hx) (hu y hy),
    fderivWithin_eq_fderiv (hu x hx) (hdiff x hx), fderivWithin_eq_fderiv (hu y hy) (hdiff y hy)]
  have h := (holderOnWith_iff_dist_le.1 hC) x hx y hy
  have e : dist (∇ w x) (∇ w y) = dist (fderiv ℝ w x) (fderiv ℝ w y) := by
    simp only [gradient, LinearIsometryEquiv.dist_map]
  rwa [e] at h

/-- **Scaled interior `C^{1,α}` estimate**, divergence form
(`Div.C1HolderBallEstimateStatement`). -/
theorem Div.c1Holder_ball_estimate : Div.C1HolderBallEstimateStatement E := by
  intro α hα hα1 lam Λ K hlam
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1.le
  obtain ⟨C₁, hC₁, hloc⟩ := dist_gradient_le_of_isWeakSolOn E hα hα1 hlam
  set Kp := max K 0
  have hKp : 0 ≤ Kp := le_max_right _ _
  set Cε := max (interpConst (1 / (2 * (C₁ * (1 + Kp) + 1))) α) 0
  have hCε : 0 ≤ Cε := le_max_right _ _
  set A₀ := C₁ * (1 + Kp) * Cε * 2 ^ (1 + (α : ℝ))
  have hA₀ : 0 ≤ A₀ := by positivity
  set Cab := absorbConst (1 / 2) (1 + (α : ℝ))
  have hCab : 1 ≤ Cab := one_le_absorbConst (by norm_num) (by norm_num) (by positivity)
  set Ci := max (interpConst 1 α) 0
  have hCi : 0 ≤ Ci := le_max_right _ _
  refine ⟨2 * Cab * (A₀ * 2 ^ (1 + (α : ℝ)) + C₁) + 2 * Ci, ?_⟩
  intro x r Ka KG Mf a G f w hr hell ha hKa hG _ hfb hcont hw
  set O := regionOsc w (closedBall x r)
  have hO : ∀ p ∈ closedBall x r, ∀ q ∈ closedBall x r, |w p - w q| ≤ O :=
    fun p hp q hq ↦ Div.abs_sub_le_regionOsc hcont hp hq
  have hxr : x ∈ closedBall x r := mem_closedBall_self hr.le
  have hO0 : 0 ≤ O := (abs_nonneg _).trans (hO x hxr x hxr)
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb x (mem_ball_self hr))
  -- finiteness on `B̄_{3r/4}` (qualitative step)
  obtain ⟨C3, hC3⟩ := Div.exists_holderOnWith_gradient hloc hC₁ isOpen_ball hell ha hG hfb hw
    (z := x) (ρ := 3 * r / 4) (by positivity) (closedBall_subset_ball (by linarith))
  have hfin : eHolderSeminormOn α (∇ w) (closedBall x (3 * r / 4)) ≠ ⊤ :=
    (eHolderSeminormOn_lt_top_of_holderOnWith hC3).ne
  set H : ℝ → ℝ := fun t ↦ holderSeminormOn α (∇ w) (closedBall x t) with hHdef
  have hHmono : ∀ t ≤ 3 * r / 4, H t ≤ H (3 * r / 4) := fun t ht ↦
    ENNReal.toReal_mono hfin (eHolderSeminormOn_mono (closedBall_subset_closedBall ht))
  set B := C₁ * KG + C₁ * Mf * r ^ (1 - (α : ℝ))
  have hB : 0 ≤ B := by
    have := Real.rpow_nonneg hr.le (1 - (α : ℝ)); positivity
  have hhf := Div.hole_filling hα hα1 hloc hC₁ hr hell ha hKa hG hfb hw hfin hO hO0
  have habs := le_of_absorption_shift (Q := H) (s := r / 2) (T := 3 * r / 4)
    (θ := 1 / 2) (γ := 1 + (α : ℝ)) (A := A₀ * O) (B := B) (by norm_num) (by norm_num)
    (by positivity) (by linarith) (by positivity) hB hhf
    ⟨H (3 * r / 4), by rintro _ ⟨t, ht, rfl⟩; exact hHmono t ht.2⟩
    (fun t _ ↦ holderSeminormOn_nonneg _ _ _)
  rw [show 2 * (3 * r / 4 - r / 2) = r / 2 by ring] at habs
  set Hh := H (r / 2)
  have hHh : 0 ≤ Hh := holderSeminormOn_nonneg _ _ _
  have hr1 : r ^ (1 + (α : ℝ)) * (r / 2) ^ (-(1 + (α : ℝ))) = 2 ^ (1 + (α : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hr.le (by norm_num)]
    field_simp
  have hr2 : r ^ (1 - (α : ℝ)) * r ^ (1 + (α : ℝ)) = r ^ 2 := by
    rw [← Real.rpow_add hr, ← Real.rpow_natCast]; congr 1; push_cast; ring
  have hrα : 0 ≤ r ^ (1 + (α : ℝ)) := Real.rpow_nonneg hr.le _
  have hmain : r ^ (1 + (α : ℝ)) * Hh ≤
      Cab * (A₀ * 2 ^ (1 + (α : ℝ)) + C₁) * (O + r ^ (1 + (α : ℝ)) * KG + r ^ 2 * Mf) := by
    calc r ^ (1 + (α : ℝ)) * Hh
        ≤ r ^ (1 + (α : ℝ)) * (Cab * (A₀ * O * (r / 2) ^ (-(1 + (α : ℝ))) + B)) :=
          mul_le_mul_of_nonneg_left habs hrα
      _ = Cab * (A₀ * O * (r ^ (1 + (α : ℝ)) * (r / 2) ^ (-(1 + (α : ℝ)))) +
            (C₁ * (r ^ (1 + (α : ℝ)) * KG) + C₁ * Mf * (r ^ (1 - (α : ℝ)) *
              r ^ (1 + (α : ℝ))))) := by ring
      _ = Cab * (A₀ * 2 ^ (1 + (α : ℝ)) * O + C₁ * (r ^ (1 + (α : ℝ)) * KG + r ^ 2 * Mf)) := by
          rw [hr1, hr2]; ring
      _ ≤ Cab * (A₀ * 2 ^ (1 + (α : ℝ)) + C₁) * (O + r ^ (1 + (α : ℝ)) * KG + r ^ 2 * Mf) := by
          have h2 : 0 ≤ A₀ * 2 ^ (1 + (α : ℝ)) := by positivity
          have h3 : 0 ≤ r ^ (1 + (α : ℝ)) * KG := by positivity
          have h4 : 0 ≤ r ^ 2 * Mf := by positivity
          have h5 : 0 ≤ Cab := by linarith
          nlinarith [mul_nonneg h5 (mul_nonneg h2 (add_nonneg h3 h4)),
            mul_nonneg h5 (mul_nonneg hC₁ hO0)]
  -- the gradient at the centre (interpolation on `B̄_{r/2}(x)` with `ε = 1`)
  have hdiff : ∀ y ∈ ball x r, DifferentiableAt ℝ w y := fun y hy ↦
    (hw.1.differentiableOn one_ne_zero y hy).differentiableAt (isOpen_ball.mem_nhds hy)
  have hsub2 : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hfin2 : eHolderSeminormOn α (∇ w) (closedBall x (r / 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eHolderSeminormOn_mono (closedBall_subset_closedBall
      (by linarith)))
  have hu : UniqueDiffOn ℝ (closedBall x (r / 2)) :=
    uniqueDiffOn_convex (convex_closedBall x (r / 2))
      (by rw [interior_closedBall x (by positivity)]; exact nonempty_ball.2 (by positivity))
  have hfw : ∀ p ∈ closedBall x (r / 2), fderivWithin ℝ w (closedBall x (r / 2)) p =
      fderiv ℝ w p := fun p hp ↦ fderivWithin_eq_fderiv (hu p hp) (hdiff p (hsub2 hp))
  have hint := norm_fderivWithin_closedBall_le (x₀ := x) (R := r / 2) (by positivity) (u := w)
    (fun p hp ↦ (hdiff p (hsub2 hp)).differentiableWithinAt) hα' hα1' hHh one_pos
    (fun p hp q hq ↦ by
      rw [hfw p hp, hfw q hq, ← dist_eq_norm]
      have e : dist (∇ w p) (∇ w q) = dist (fderiv ℝ w p) (fderiv ℝ w q) := by
        simp only [gradient, LinearIsometryEquiv.dist_map]
      rw [← e]
      exact dist_le_holderSeminormOn_mul hfin2 hp hq)
    (fun p hp q hq ↦ by
      rw [Real.norm_eq_abs]
      exact hO p (closedBall_subset_closedBall (by linarith) hp) q
        (closedBall_subset_closedBall (by linarith) hq))
    x (mem_closedBall_self (by positivity))
  rw [hfw x (mem_closedBall_self (by positivity))] at hint
  have hcentre : r * ‖fderiv ℝ w x‖ ≤ r ^ (1 + (α : ℝ)) * Hh + 2 * Ci * O := by
    have h1 : interpConst 1 α * (r / 2)⁻¹ * O ≤ Ci * (r / 2)⁻¹ * O := by
      have : 0 ≤ (r / 2)⁻¹ * O := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left (interpConst 1 α) 0) this]
    have h2 : (r / 2) ^ (α : ℝ) ≤ r ^ (α : ℝ) := Real.rpow_le_rpow (by positivity)
      (by linarith) α.2
    have h3 : r * r ^ (α : ℝ) = r ^ (1 + (α : ℝ)) := by
      rw [Real.rpow_add hr, Real.rpow_one]
    calc r * ‖fderiv ℝ w x‖ ≤ r * (1 * (r / 2) ^ (α : ℝ) * Hh + Ci * (r / 2)⁻¹ * O) :=
          mul_le_mul_of_nonneg_left (hint.trans (add_le_add le_rfl h1)) hr.le
      _ = r * (r / 2) ^ (α : ℝ) * Hh + 2 * Ci * O := by field_simp
      _ ≤ r * r ^ (α : ℝ) * Hh + 2 * Ci * O := by gcongr
      _ = r ^ (1 + (α : ℝ)) * Hh + 2 * Ci * O := by rw [h3]
  -- conclusion
  have hsemi : holderSeminormOn α (fderiv ℝ w) (closedBall x (r / 2)) = Hh := by
    simp only [holderSeminormOn, Div.eHolderSeminormOn_fderiv_eq, Hh, hHdef]
  rw [hsemi]
  have h3 : 0 ≤ r ^ (1 + (α : ℝ)) * KG := by positivity
  have h4 : 0 ≤ r ^ 2 * Mf := by positivity
  have hX : O ≤ O + r ^ (1 + (α : ℝ)) * KG + r ^ 2 * Mf := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 2 * Ci)]

end BasicElliptic
