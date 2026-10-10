/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Boundary.Patch
public import BasicElliptic.Campanato.Holder
import BasicElliptic.Campanato.Density
import BasicElliptic.Div.Interior.LocalHolder
import BasicElliptic.Common.RealArith

/-!
# Quantitative local Hölder bound for `∇w` up to the flat part

`BasicElliptic.Div.dist_gradientWithin_le_of_isConormalSolOn`: there is `C = C(E, α, lam, Λ)`
such that, for a conormal solution on `D = halfBall ν z R` (data as in `campanato_patch`), a
centre with `⟪z, ν⟫ ≥ 0`, `0 < δ ≤ ρ`, `ρ + δ ≤ R`, `‖∇w‖ ≤ M₀` on `D` and `‖G‖ ≤ M_G`,

`|∇w(p) - ∇w(q)| ≤ C ((M₀ + M_G) δ^{-α} + K_a (M₀ + M_G) + K_G + M_f δ^{1-α}) |p - q|^α`
for `p, q ∈ halfBall ν z ρ` (`∇w` the within-gradient on `D`).

## Proof

As `dist_gradient_le_of_isWeakSolOn` (`Div/Interior/LocalHolder.lean`): `campanato_patch` gives the
Campanato bound at every point of `S = halfBall ν z ρ` up to scale `ρ₀ = (lam/Λ) δ / 4`; half balls
with `⟪z, ν⟫ ≥ 0` have uniform
density (`halfBall_density`), so Campanato's characterization
(`norm_sub_le_of_campanato`) handles `|p - q| < ρ₀ / 2`, and `‖∇w‖ ≤ M₀` the other pairs.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient NNReal

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Near pairs from Campanato, far pairs from the sup bound. -/
private theorem near_far_bound {S : Set E} {F : E → E} {α Kc M' A Y θ δ M₀ : ℝ} (hα : 0 < α)
    (hKc : 0 ≤ Kc) (hM' : 0 ≤ M') (hY0 : 0 ≤ Y) (hθ : 0 < θ)
    (hδ : 0 < δ) (hM₀0 : 0 ≤ M₀)
    (hnear : ∀ p ∈ S, ∀ q ∈ S, dist p q ≤ θ * δ / 2 → dist (F p) (F q) ≤ Kc * M' * dist p q ^ α)
    (hM'Y : M' ≤ A * Y) (hM₀ : ∀ y ∈ S, ‖F y‖ ≤ M₀) (h4 : M₀ * δ ^ (-α) ≤ Y) :
    ∀ p ∈ S, ∀ q ∈ S, dist (F p) (F q) ≤ (Kc * A + 2 * (θ / 2) ^ (-α)) * Y * dist p q ^ α := by
  intro p hp q hq
  have hpq : 0 ≤ dist p q ^ α := Real.rpow_nonneg dist_nonneg _
  rcases lt_or_ge (dist p q) (θ * δ / 2) with hnear' | hfar
  · refine (hnear p hp q hq hnear'.le).trans ?_
    have h2 : 0 ≤ 2 * (θ / 2) ^ (-α) * Y * dist p q ^ α := by positivity
    calc Kc * M' * dist p q ^ α ≤ Kc * (A * Y) * dist p q ^ α := by gcongr
      _ = Kc * A * Y * dist p q ^ α := by ring
      _ ≤ (Kc * A + 2 * (θ / 2) ^ (-α)) * Y * dist p q ^ α := by
          rw [add_mul, add_mul]; linarith
  · have h1 : dist (F p) (F q) ≤ 2 * M₀ := by
      rw [dist_eq_norm]
      linarith [norm_sub_le (F p) (F q), hM₀ p hp, hM₀ q hq]
    have h2 : 1 ≤ (θ * δ / 2) ^ (-α) * dist p q ^ α := by
      rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
        le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _), one_mul]
      exact Real.rpow_le_rpow (by positivity) hfar hα.le
    have h3 : (θ * δ / 2) ^ (-α) = (θ / 2) ^ (-α) * δ ^ (-α) := by
      rw [show θ * δ / 2 = θ / 2 * δ by ring, Real.mul_rpow (by positivity) hδ.le]
    have hMY : 0 ≤ Kc * A * Y * dist p q ^ α := by
      have : 0 ≤ A * Y := hM'.trans hM'Y
      have : 0 ≤ Kc * (A * Y) := mul_nonneg hKc this
      calc (0 : ℝ) ≤ Kc * (A * Y) * dist p q ^ α := mul_nonneg this hpq
        _ = Kc * A * Y * dist p q ^ α := by ring
    calc dist (F p) (F q) ≤ 2 * M₀ * ((θ * δ / 2) ^ (-α) * dist p q ^ α) :=
          h1.trans (le_mul_of_one_le_right (by positivity) h2)
      _ = 2 * (θ / 2) ^ (-α) * (M₀ * δ ^ (-α)) * dist p q ^ α := by
          rw [h3]; ring
      _ ≤ 2 * (θ / 2) ^ (-α) * Y * dist p q ^ α := by gcongr
      _ ≤ _ := by rw [add_mul, add_mul]; linarith

variable (E) in
/-- **Quantitative local Hölder bound for `∇w` up to the flat part** (see the module
docstring). -/
theorem dist_gradientWithin_le_of_isConormalSolOn {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {lam Λ : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν z : E) (Ka KG : ℝ≥0) (Mf M₀ MG R δ ρ : ℝ) (a : E → E →L[ℝ] E)
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
          C * ((M₀ + MG) * δ ^ (-(α : ℝ)) + Ka * (M₀ + MG) + KG + Mf * δ ^ (1 - (α : ℝ))) *
            dist p q ^ (α : ℝ) := by
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1.le
  obtain ⟨C, hC0, hcamp⟩ := campanato_patch E hα hα1 hlam
  set c₀ := halfBallDensityConst E
  have hc₀ : 0 < c₀ := halfBallDensityConst_pos
  set κ := √(lam / Λ) with hκ
  set θ := κ ^ 2 / 4 with hθ
  set Kc := campanatoHolderConst E c₀ α
  have hKc : 0 ≤ Kc := campanatoHolderConst_nonneg hα'
  have hθα : 0 ≤ (θ / 2) ^ (-(α : ℝ)) := Real.rpow_nonneg (by positivity) _
  refine ⟨Kc * √(C / c₀) + 2 * (θ / 2) ^ (-(α : ℝ)), by positivity, ?_⟩
  intro ν z Ka KG Mf M₀ MG R δ ρ a G f w hν hz hδ hδρ hρR hell hsym ha hG hMG hfm hfb hw hM₀
    p hp q hq
  set D := halfBall ν z R with hD
  set gW := gradientWithin w D with hgW
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hzD : z ∈ D := ⟨mem_closedBall_self (by linarith), hz⟩
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ z hzD)
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG z hzD)
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb z hzD)
  set N := M₀ + MG with hN
  have hN0 : 0 ≤ N := by positivity
  set Y := N * δ ^ (-(α : ℝ)) + Ka * N + KG + Mf * δ ^ (1 - (α : ℝ)) with hY
  have hδa : 0 ≤ δ ^ (-(α : ℝ)) := Real.rpow_nonneg hδ.le _
  have hδb : 0 ≤ δ ^ (1 - (α : ℝ)) := Real.rpow_nonneg hδ.le _
  have hY0 : 0 ≤ Y := by positivity
  have hpq : 0 ≤ dist p q ^ (α : ℝ) := Real.rpow_nonneg dist_nonneg _
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have : Nontrivial E := ⟨⟨ν, 0, hν0⟩⟩
  set S := halfBall ν z ρ with hS
  have hlamΛ := lam_le_of_isUniformlyElliptic hell hzD
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  have hκsq : κ ^ 2 = lam / Λ := Real.sq_sqrt (by positivity)
  have hκpos : 0 < κ := Real.sqrt_pos.2 (div_pos hlam hΛ)
  have hκ1 : κ ≤ 1 := Real.sqrt_le_one.2 ((div_le_one hΛ).2 hlamΛ)
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    have : κ ^ 2 ≤ 1 := by nlinarith
    rw [hθ]; linarith
  set ρ₀ := θ * δ with hρ₀def
  have hρ₀ : 0 < ρ₀ := mul_pos hθpos hδ
  have hρ₀ρ : ρ₀ ≤ ρ := (mul_le_of_le_one_left hδ.le hθ1).trans hδρ
  have hSD : S ⊆ D := inter_subset_inter_left _ (closedBall_subset_closedBall (by linarith))
  have hxR : -R < ⟪z, ν⟫ := by linarith
  have hgradc : ContinuousOn gW D := continuousOn_gradientWithin_halfBall hν (by linarith) hxR hw.1
  -- the uniform Campanato bound
  set X := N ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * N ^ 2 + (KG : ℝ) ^ 2 +
    Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) with hX
  have hX0 : 0 ≤ X := by
    have := Real.rpow_nonneg hδ.le (-(2 * (α : ℝ)))
    have := Real.rpow_nonneg hδ.le (2 - 2 * (α : ℝ))
    positivity
  have hdens : HasDensity S c₀ ρ₀ := (halfBall_density hν hρ hz).mono_scale hρ₀ρ
  set M' := √(C * X / c₀)
  have hM' : 0 ≤ M' := Real.sqrt_nonneg _
  have hcampS : IsCampanatoOn S gW α M' ρ₀ := by
    intro x₀ hx₀ r hr
    have hr0 := hr.1
    have hx₀D : x₀ ∈ D := hSD hx₀
    have hroom : dist x₀ z + δ ≤ R := by linarith [(mem_halfBall.1 hx₀).1]
    have hrt : r ≤ lam / Λ / 4 * δ := by rw [← hκsq]; exact hr.2
    have hint := hcamp ν z Ka KG Mf M₀ MG R δ a G f w hν hδ hell hsym ha hG hMG hfm hfb hw hM₀
      x₀ hx₀D hroom S (measurableSet_halfBall ν z ρ) (halfBall_subset_halfSpace ν z ρ) r hr0 hrt
    have hvol : c₀ * r ^ finrank ℝ E ≤ volume.real (ball x₀ r ∩ S) := hdens x₀ hx₀ r hr
    have hvol0 : 0 < c₀ * r ^ finrank ℝ E := by positivity
    rw [setAverage_eq, smul_eq_mul]
    have hI0 : 0 ≤ ∫ y in ball x₀ r ∩ S, ‖gW y - ⨍ z in ball x₀ r ∩ S, gW z‖ ^ 2 :=
      integral_nonneg fun _ ↦ sq_nonneg _
    have hrb : r ^ ((finrank ℝ E : ℝ) + 2 * α) = r ^ finrank ℝ E * r ^ (2 * (α : ℝ)) := by
      rw [Real.rpow_add hr0, Real.rpow_natCast]
    calc (volume.real (ball x₀ r ∩ S))⁻¹ *
          ∫ y in ball x₀ r ∩ S, ‖gW y - ⨍ z in ball x₀ r ∩ S, gW z‖ ^ 2
        ≤ (c₀ * r ^ finrank ℝ E)⁻¹ * (C * r ^ ((finrank ℝ E : ℝ) + 2 * α) * X) := by
          gcongr
      _ = M' ^ 2 * r ^ (2 * (α : ℝ)) := by
          rw [Real.sq_sqrt (by positivity), hrb]
          field_simp
  have hM'Y : M' ≤ √(C / c₀) * Y := by
    have hXY : √X ≤ Y := by
      have e1 : (N * δ ^ (-(α : ℝ))) ^ 2 = N ^ 2 * δ ^ (-(2 * (α : ℝ))) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hδ.le]; congr 2; push_cast; ring
      have e2 : (Mf * δ ^ (1 - (α : ℝ))) ^ 2 = Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hδ.le]; congr 2; push_cast; ring
      have e3 : ((Ka : ℝ) * N) ^ 2 = (Ka : ℝ) ^ 2 * N ^ 2 := by ring
      have := sqrt_sum_four_sq_le (by positivity : 0 ≤ N * δ ^ (-(α : ℝ)))
        (by positivity : 0 ≤ (Ka : ℝ) * N) (KG.2) (by positivity : 0 ≤ Mf * δ ^ (1 - (α : ℝ)))
      rwa [e1, e2, e3] at this
    calc M' = √(C / c₀) * √X := by
          rw [← Real.sqrt_mul (by positivity)]
          exact congrArg Real.sqrt (by ring)
      _ ≤ √(C / c₀) * Y := mul_le_mul_of_nonneg_left hXY (Real.sqrt_nonneg _)
  have hSc : IsCompact S := isCompact_halfBall ν z ρ
  have hgS : ContinuousOn gW S := hgradc.mono hSD
  refine near_far_bound hα' hKc hM' hY0 hθpos hδ hM₀0 (fun p hp q hq hpq ↦ by
      rw [dist_eq_norm]
      exact norm_sub_le_of_campanato hα' hα1' hM' hc₀ hSc hdens hgS hcampS hp hq hpq)
    hM'Y (fun y hy ↦ hM₀ y (hSD hy)) ?_ p hp q hq
  have : 0 ≤ (Ka : ℝ) * N := by positivity
  have : 0 ≤ Mf * δ ^ (1 - (α : ℝ)) := by positivity
  have : M₀ * δ ^ (-(α : ℝ)) ≤ N * δ ^ (-(α : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hδa
  rw [hY]
  linarith [NNReal.coe_nonneg KG]

end BasicElliptic.Div
