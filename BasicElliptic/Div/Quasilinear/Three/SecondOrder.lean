/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Three.FlatFlux
public import BasicElliptic.Div.Quasilinear.Three.Canonical
import BasicElliptic.Div.Quasilinear.HigherOrder
import BasicElliptic.Holder.Algebra

/-!
# The second-order estimate, uniform in the structure

Derivatives are taken within the half space `halfSpace ν`; at points of the open ball they agree
with the within-derivatives on the half ball (`Div/Quasilinear/Three/Canonical.lean`).

* `Div.first_order_estimate'`: `Div.first_order_estimate` as pointwise bounds on
  `halfBall ν x (κ r)`.
* `Div.second_order_estimate`: `r² ‖D²w‖ ≤ C osc w` and
  `r^{5/2} ‖D²w(y) - D²w(y')‖ ≤ C osc w |y - y'|^{1/2}` on `halfBall ν x (κ r)`. For tangential
  `e`, `∂_e w` solves the linear conormal problem with coefficient `DΦ(∇w)`, which is `1/2`-Hölder
  with a scale-invariant constant by the first-order estimate; the linear `C^{1,1/2}` estimate
  bounds the tangential rows of `D²w` and their Hölder quotients, and the equation
  `Σ_j D²w(b_j, DΦ(∇w) b_j) = 0` bounds the normal–normal entry
  (`Div.norm_le_of_tangential_approx`).
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace Module
open scoped NNReal Gradient ContDiff

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (E) in
/-- **The first-order estimate, pointwise form.** -/
theorem first_order_estimate' {ν : E} (hν : ‖ν‖ = 1) {lam M δ : ℝ} (hlam : 0 < lam)
    (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ η > 0, ∃ κ > 0, κ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → E),
      StructureBounds Φ lam M δ → ∀ (x : E) (r : ℝ) (w : E → ℝ), 0 < r →
      0 ≤ ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x r w →
      (∀ y ∈ halfBall ν x r, ‖gradientWithin w (halfBall ν x r) y‖ ≤ η) →
      (∀ y ∈ halfBall ν x (κ * r),
        r * ‖fderivWithin ℝ w (halfSpace ν) y‖ ≤ C * regionOsc w (halfBall ν x r)) ∧
      ∀ y ∈ halfBall ν x (κ * r), ∀ y' ∈ halfBall ν x (κ * r),
        r * √r * ‖fderivWithin ℝ w (halfSpace ν) y - fderivWithin ℝ w (halfSpace ν) y'‖ ≤
          C * regionOsc w (halfBall ν x r) * √(dist y y') := by
  obtain ⟨η, hη, κ, hκ, hκ2, C, hC, hP⟩ := first_order_estimate E hν hlam hM hδ
  refine ⟨η, hη, κ, hκ, hκ2, 2 * C, by positivity, ?_⟩
  intro Φ hS x r w hr hx0 h hgrad
  obtain ⟨hfin, hc, hh⟩ := hP Φ hS x r w hr hx0 h hgrad
  set B := halfBall ν x r with hB
  set osc := regionOsc w B with hosc
  have hosc0 : 0 ≤ osc := regionOsc_nonneg_of_compact (isCompact_halfBall ν x r)
    h.1.continuousOn ⟨x, mem_closedBall_self hr.le, hx0⟩
  have hball : ∀ y ∈ halfBall ν x (κ * r), y ∈ ball x r := fun y hy ↦
    mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (by nlinarith))
  have hcan : ∀ y ∈ halfBall ν x (κ * r),
      fderivWithin ℝ w (halfSpace ν) y = fderivWithin ℝ w B y := fun y hy ↦
    (fderivWithin_halfBall_eq w (hball y hy)).symm
  set sem := holderSeminormOn (1 / 2) (fderivWithin ℝ w B) (halfBall ν x (κ * r)) with hsem
  have hsem0 : 0 ≤ sem := holderSeminormOn_nonneg _ _ _
  have hdist : ∀ y ∈ halfBall ν x (κ * r), ∀ y' ∈ halfBall ν x (κ * r),
      ‖fderivWithin ℝ w (halfSpace ν) y - fderivWithin ℝ w (halfSpace ν) y'‖ ≤
        sem * √(dist y y') := fun y hy y' hy' ↦ by
    rw [hcan y hy, hcan y' hy', ← dist_eq_norm, Real.sqrt_eq_rpow]
    have := dist_le_holderSeminormOn_mul hfin hy hy'
    rwa [show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num] at this
  have hsr : 0 ≤ r * √r := by positivity
  have hxR : x ∈ halfBall ν x (κ * r) := ⟨mem_closedBall_self (by positivity), hx0⟩
  refine ⟨fun y hy ↦ ?_, fun y hy y' hy' ↦ ?_⟩
  · have h1 := hdist y hy x hxR
    have hd : √(dist y x) ≤ √r :=
      Real.sqrt_le_sqrt ((mem_closedBall.1 hy.1).trans (by nlinarith))
    have h2 : ‖fderivWithin ℝ w (halfSpace ν) y‖ ≤
        ‖fderivWithin ℝ w (halfSpace ν) x‖ + sem * √r := by
      calc _ ≤ ‖fderivWithin ℝ w (halfSpace ν) x‖ + ‖fderivWithin ℝ w (halfSpace ν) y -
            fderivWithin ℝ w (halfSpace ν) x‖ := norm_le_insert' _ _
        _ ≤ _ := by gcongr; exact h1.trans (by gcongr)
    rw [hcan x hxR] at h2
    calc r * ‖fderivWithin ℝ w (halfSpace ν) y‖
        ≤ r * (‖fderivWithin ℝ w B x‖ + sem * √r) := by gcongr
      _ = r * ‖fderivWithin ℝ w B x‖ + r * √r * sem := by ring
      _ ≤ C * osc + C * osc := add_le_add hc hh
      _ = 2 * C * osc := by ring
  · calc r * √r * ‖fderivWithin ℝ w (halfSpace ν) y - fderivWithin ℝ w (halfSpace ν) y'‖
        ≤ r * √r * (sem * √(dist y y')) := by gcongr; exact hdist y hy y' hy'
      _ = (r * √r * sem) * √(dist y y') := by ring
      _ ≤ (C * osc) * √(dist y y') := by gcongr
      _ ≤ 2 * C * osc * √(dist y y') := by
          gcongr; nlinarith

/-! ### The linear step in pointwise form -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem holderOnWith_of_norm_sub_le_sqrt {F : Type*} [NormedAddCommGroup F] {f : E → F}
    {s : Set E} {K : ℝ} (hK : 0 ≤ K) (h : ∀ y ∈ s, ∀ y' ∈ s, ‖f y - f y'‖ ≤ K * √(dist y y')) :
    HolderOnWith (Real.toNNReal K) (1 / 2) f s := by
  refine holderOnWith_of_dist_le hK fun y hy y' hy' ↦ ?_
  rw [dist_eq_norm, show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact h y hy y' hy'

variable (E) in
/-- **The linear `C^{1,1/2}` step in pointwise form.** -/
theorem linear_step {lam Λ Kc : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν x : E) (ρ Ka KG MG U₀ : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
      (u : E → ℝ), ‖ν‖ = 1 → 0 < ρ → 0 ≤ ⟪x, ν⟫ →
      IsUniformlyElliptic lam Λ a (halfBall ν x ρ) → IsSymmetricOn a (halfBall ν x ρ) →
      0 ≤ Ka → (∀ y ∈ halfBall ν x ρ, ∀ y' ∈ halfBall ν x ρ, ‖a y - a y'‖ ≤ Ka * √(dist y y')) →
      Ka * √ρ ≤ Kc → 0 ≤ KG →
      (∀ y ∈ halfBall ν x ρ, ∀ y' ∈ halfBall ν x ρ, ‖G y - G y'‖ ≤ KG * √(dist y y')) →
      (∀ y ∈ halfBall ν x ρ, ‖G y‖ ≤ MG) → (∀ y ∈ halfBall ν x ρ, |u y| ≤ U₀) →
      IsConormalSolOn ν a G 0 x ρ u →
      ρ * ‖fderivWithin ℝ u (halfBall ν x ρ) x‖ ≤ C * (U₀ + ρ * √ρ * KG + ρ * MG) ∧
      ∀ y ∈ halfBall ν x (ρ / 2), ∀ y' ∈ halfBall ν x (ρ / 2),
        ρ * √ρ * ‖fderivWithin ℝ u (halfBall ν x ρ) y - fderivWithin ℝ u (halfBall ν x ρ) y'‖ ≤
          C * (U₀ + ρ * √ρ * KG + ρ * MG) * √(dist y y') := by
  obtain ⟨C, hC0, hC⟩ := exists_c1_estimate_flux E (α := 1 / 2) (by norm_num) (by norm_num)
    (lam := lam) (Λ := Λ) (Kc := Kc) hlam
  refine ⟨2 * C, by positivity, ?_⟩
  intro ν x ρ Ka KG MG U₀ a G u hν hρ hx0 hell hsym hKa0 hKa hKaC hKG0 hKG hMG hU hu
  have hxB : x ∈ halfBall ν x ρ := ⟨mem_closedBall_self hρ.le, hx0⟩
  have hU0 : 0 ≤ U₀ := (abs_nonneg _).trans (hU x hxB)
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG x hxB)
  have hha := holderOnWith_of_norm_sub_le_sqrt hKa0 hKa
  have hhG := holderOnWith_of_norm_sub_le_sqrt hKG0 hKG
  obtain ⟨hfin, hest⟩ := hC ν x ρ _ _ MG a G u hν hρ hx0 hell hsym hha (by
    rw [Real.coe_toNNReal _ hKa0, show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]; exact hKaC) hhG hMG hu
  rw [Real.coe_toNNReal _ hKG0] at hest
  have h32 : ρ ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) = ρ * √ρ := by
    rw [show (1 + ((1 / 2 : ℝ≥0) : ℝ)) = 1 + 1 / 2 by norm_num, Real.rpow_add hρ,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [h32] at hest
  have hosc : regionOsc u (halfBall ν x ρ) ≤ 2 * U₀ := regionOsc_le_two_mul_of_abs_le ⟨x, hxB⟩ hU
  set sem := holderSeminormOn (1 / 2) (fderivWithin ℝ u (halfBall ν x ρ)) (halfBall ν x (ρ / 2))
  have hsem0 : 0 ≤ sem := holderSeminormOn_nonneg _ _ _
  have hQ : C * (regionOsc u (halfBall ν x ρ) + ρ * √ρ * KG + ρ * MG) ≤
      2 * C * (U₀ + ρ * √ρ * KG + ρ * MG) := by
    have : 0 ≤ ρ * √ρ * KG + ρ * MG := by positivity
    nlinarith
  have hsr : 0 ≤ ρ * √ρ * sem := by positivity
  have hfr : 0 ≤ ρ * ‖fderivWithin ℝ u (halfBall ν x ρ) x‖ := by positivity
  refine ⟨by linarith, fun y hy y' hy' ↦ ?_⟩
  have hd := dist_le_holderSeminormOn_mul hfin hy hy'
  rw [show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, dist_eq_norm] at hd
  calc ρ * √ρ * ‖_‖ ≤ ρ * √ρ * (sem * √(dist y y')) := by gcongr
    _ = (ρ * √ρ * sem) * √(dist y y') := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

omit [MeasurableSpace E] [BorelSpace E] in
theorem fderivWithin_eq_toDual_gradientWithin (f : E → ℝ) (s : Set E) (y : E) :
    fderivWithin ℝ f s y = InnerProductSpace.toDual ℝ E (gradientWithin f s y) := by
  rw [gradientWithin, LinearIsometryEquiv.apply_symm_apply]

/-! ### The second-order estimate -/

set_option maxHeartbeats 1600000 in
-- a long proof with many explicit constants and nonlinear arithmetic
variable (E) in
/-- **The second-order estimate, uniform in the structure.** -/
theorem second_order_estimate {ν : E} (hν : ‖ν‖ = 1) {lam M δ : ℝ} (hlam : 0 < lam)
    (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ η > 0, ∃ κ > 0, κ ≤ 1 / 8 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → E),
      StructureBounds Φ lam M δ → ∀ (x : E) (r : ℝ) (w : E → ℝ), 0 < r →
      0 ≤ ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x r w →
      (∀ y ∈ halfBall ν x r, ‖gradientWithin w (halfBall ν x r) y‖ ≤ η) →
      (∀ y ∈ halfBall ν x (κ * r), r ^ 2 *
        ‖fderivWithin ℝ (fderivWithin ℝ w (halfSpace ν)) (halfSpace ν) y‖ ≤
          C * regionOsc w (halfBall ν x r)) ∧
      ∀ y ∈ halfBall ν x (κ * r), ∀ y' ∈ halfBall ν x (κ * r),
        r ^ 2 * √r * ‖fderivWithin ℝ (fderivWithin ℝ w (halfSpace ν)) (halfSpace ν) y -
          fderivWithin ℝ (fderivWithin ℝ w (halfSpace ν)) (halfSpace ν) y'‖ ≤
          C * regionOsc w (halfBall ν x r) * √(dist y y') := by
  have : Nontrivial E := ⟨⟨ν, 0, by rintro rfl; simp at hν⟩⟩
  obtain ⟨η₁, hη₁, κ₁, hκ₁, hκ₁2, C₁, hC₁, hP1⟩ := first_order_estimate' E hν hlam hM hδ
  set η := min η₁ (δ / 2) with hηdef
  have hη : 0 < η := lt_min hη₁ (by positivity)
  set Kc := 2 * M * C₁ * η with hKc
  obtain ⟨CL, hCL, hL⟩ := linear_step E (lam := lam) (Λ := M) (Kc := Kc) hlam
  set b := stdOrthonormalBasis ℝ E with hb
  set d : ℝ := (Fintype.card (Fin (finrank ℝ E)) : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  set c := κ₁ / 2 with hc
  have hc0 : 0 < c := by positivity
  set lm := 1 + d * M / lam with hlm
  have hlm0 : 0 ≤ lm := by positivity
  set a₀ := CL * C₁ / c with ha₀
  set a₁ := CL * C₁ / (c * √c) with ha₁
  have ha₀0 : 0 ≤ a₀ := by positivity
  have ha₁0 : 0 ≤ a₁ := by positivity
  have hsc : 0 < √c := Real.sqrt_pos.2 hc0
  have ha₁c : a₁ * √c = a₀ := by rw [ha₁, ha₀]; field_simp
  refine ⟨η, hη, κ₁ / 4, by positivity, by linarith,
    4 * a₀ * lm + 2 * a₁ * lm + 8 * d * a₀ * lm * M * C₁ * η / lam, by positivity, ?_⟩
  intro Φ hS x r w hr hx0 h hgrad
  set B := halfBall ν x r with hB
  set g := gradientWithin w B with hg
  have hx : -r < ⟪x, ν⟫ := by linarith
  have hBc : IsCompact B := isCompact_halfBall ν x r
  have hwc : ContinuousOn w B := h.1.continuousOn
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hxB : x ∈ B := ⟨mem_closedBall_self hr.le, hx0⟩
  set osc := regionOsc w B with hosc
  have hosc0 : 0 ≤ osc := regionOsc_nonneg_of_compact hBc hwc ⟨x, hxB⟩
  have hoscη : osc ≤ 2 * r * η := by
    refine regionOsc_le_of_norm_fderivWithin_le (convex_halfBall ν x r) ⟨x, hxB⟩ hwB
      (fun y hy ↦ ?_) (fun a ha b hb ↦ ?_)
    · rw [norm_fderivWithin_eq_norm_gradientWithin]; exact hgrad y hy
    · rw [← dist_eq_norm]
      linarith [dist_triangle a x b, mem_closedBall.1 ha.1, dist_comm b x ▸ mem_closedBall.1 hb.1]
  obtain ⟨hD1c, hD1h⟩ := hP1 Φ hS x r w hr hx0 h fun y hy ↦ (hgrad y hy).trans (min_le_left _ _)
  set D₀ := fderivWithin ℝ w (halfSpace ν) with hD₀
  set ρ := c * r with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r / 2 := by rw [hρ, hc]; nlinarith
  have hρκ : ρ ≤ κ₁ * r := by rw [hρ, hc]; nlinarith
  have hR1 : halfBall ν x ρ ⊆ halfBall ν x (κ₁ * r) := halfBall_mono ν x hρκ
  have hball : ∀ {s : ℝ}, s ≤ r / 2 → ∀ y ∈ halfBall ν x s, y ∈ ball x r := fun hs y hy ↦
    mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (by linarith))
  have hcanD : ∀ y ∈ ball x r, fderivWithin ℝ w B y = D₀ y := fun y hy ↦
    fderivWithin_halfBall_eq w hy
  have hrange : ∀ y ∈ B, g y ∈ ball (0 : E) δ := fun y hy ↦
    mem_ball_zero_iff.2 ((hgrad y hy).trans_lt (by
      have := min_le_right η₁ (δ / 2); linarith))
  -- the coefficient `A = DΦ(∇w)`
  set A : E → E →L[ℝ] E := fun y ↦ fderiv ℝ Φ (g y) with hA
  have hAell : ∀ {S : Set E}, S ⊆ B → IsUniformlyElliptic lam M A S := fun hSB y hy ↦
    ⟨hS.ell _ (hrange y (hSB hy)), (hS.bound _ (hrange y (hSB hy))).1⟩
  have hAsym : ∀ {S : Set E}, S ⊆ B → IsSymmetricOn A S := fun hSB y hy ↦
    hS.sym _ (hrange y (hSB hy))
  set Dh := C₁ * osc / (r * √r) with hDh
  have hsr : 0 < r * √r := by positivity
  have hDh0 : 0 ≤ Dh := by positivity
  have hgh : ∀ y ∈ halfBall ν x ρ, ∀ y' ∈ halfBall ν x ρ,
      ‖g y - g y'‖ ≤ Dh * √(dist y y') := fun y hy y' hy' ↦ by
    have hyb := hball hρr.le y hy
    have hyb' := hball hρr.le y' hy'
    rw [← dist_eq_norm, ← dist_fderivWithin_eq_dist_gradientWithin, dist_eq_norm, hcanD y hyb,
      hcanD y' hyb', hDh, div_mul_eq_mul_div, le_div_iff₀ hsr]
    have := hD1h y (hR1 hy) y' (hR1 hy')
    linarith
  have hρB : halfBall ν x ρ ⊆ B := halfBall_mono ν x (by linarith)
  have hAh : ∀ y ∈ halfBall ν x ρ, ∀ y' ∈ halfBall ν x ρ,
      ‖A y - A y'‖ ≤ M * Dh * √(dist y y') := fun y hy y' hy' ↦ by
    calc ‖A y - A y'‖ ≤ M * ‖g y - g y'‖ :=
          hS.norm_fderiv_sub_le (hrange y (hρB hy)) (hrange y' (hρB hy'))
      _ ≤ M * (Dh * √(dist y y')) := by gcongr; exact hgh y hy y' hy'
      _ = M * Dh * √(dist y y') := by ring
  have hKaC : M * Dh * √ρ ≤ Kc := by
    have hρr' : √ρ ≤ √r := Real.sqrt_le_sqrt (by linarith)
    have hsr0 : 0 < √r := Real.sqrt_pos.2 hr
    calc M * Dh * √ρ ≤ M * Dh * √r := by gcongr
      _ = M * C₁ * (osc / r) := by rw [hDh]; field_simp
      _ ≤ M * C₁ * (2 * η) := by
          gcongr; rw [div_le_iff₀ hr]; linarith
      _ = Kc := by rw [hKc]; ring
  -- `C³` regularity and the within Hessian on `T = halfBall ν x (r / 2)`
  have hr2 : 0 < r / 2 := by positivity
  have hC3 := contDiffOn_three_halfBall_of_quasilinear_conormal hν hr hx isOpen_ball
    (convex_ball _ _) hlam hS.contDiffOn hS.ell hS.sym hrange h
  have hC2 : ContDiffOn ℝ 2 w (halfBall ν x (r / 2)) := hC3.of_le (by norm_num)
  set T := halfBall ν x (r / 2) with hT
  have hTB : T ⊆ B := halfBall_mono ν x (by linarith)
  obtain ⟨hD1, hsymm, hgradu⟩ := hessianWithin_halfBall_data hν hr2 hx0 hTB hwB hC2
  set H := fderivWithin ℝ (fderivWithin ℝ w B) T with hH
  have hcanH : ∀ y ∈ ball x (r / 2),
      H y = fderivWithin ℝ (fderivWithin ℝ w (halfSpace ν)) (halfSpace ν) y := fun y hy ↦
    fderivWithin_fderivWithin_halfBall_eq w (ball_subset_ball (by linarith) hy) hy
  have hρT : halfBall ν x ρ ⊆ T := halfBall_mono ν x hρr.le
  have huT := uniqueDiffOn_halfBall hν hr2 (by linarith : -(r / 2) < ⟪x, ν⟫)
  -- the equation on `T`
  have hclosed : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have heqn : ∀ y ∈ T, ∑ j, H y (b j) (A y (b j)) = 0 := fun y hy ↦ by
    have := sum_hessianWithin_eq_zero hν hr hx isOpen_ball (convex_ball _ _) hlam
      hS.contDiffOn_two hS.ell hS.sym hrange h hx0 hr2 hclosed hC2 b hy
    have hEq : EqOn (fderivWithin ℝ w T) (fderivWithin ℝ w B) T := fun z hz ↦
      fderivWithin_subset hTB (huT z hz) (hwB z (hTB hz))
    rwa [fderivWithin_congr hEq (hEq hy)] at this
  -- the tangential rows
  set R2 := halfBall ν x (ρ / 2) with hR2
  have hR2ρ : R2 ⊆ halfBall ν x ρ := halfBall_mono ν x (by linarith)
  set T₀ := a₀ * osc / r ^ 2 with hT₀
  set T₁ := a₁ * osc / (r ^ 2 * √r) with hT₁
  have hT₀0 : 0 ≤ T₀ := by positivity
  have hT₁0 : 0 ≤ T₁ := by positivity
  have htan : ∀ e : E, ⟪e, ν⟫ = 0 → ‖H x e‖ ≤ T₀ * ‖e‖ ∧
      ∀ y ∈ R2, ∀ y' ∈ R2, ‖H y e - H y' e‖ ≤ T₁ * ‖e‖ * √(dist y y') := by
    intro e he
    have hue := h.isConormalSolOn_fderivWithin_apply hν isOpen_ball hS.contDiffOn_one hrange
      hρ0 hρr hx0 hclosed hC2 he
    set U₀ := C₁ * osc / r * ‖e‖ with hU₀
    have hU : ∀ y ∈ halfBall ν x ρ, |fderivWithin ℝ w B y e| ≤ U₀ := fun y hy ↦ by
      rw [← Real.norm_eq_abs, hcanD y (hball hρr.le y hy)]
      refine ((D₀ y).le_opNorm e).trans ?_
      rw [hU₀]
      gcongr
      rw [le_div_iff₀ hr, mul_comm]
      exact hD1c y (hR1 hy)
    obtain ⟨hLc, hLh⟩ := hL ν x ρ (M * Dh) 0 0 U₀ A 0 _ hν hρ0 hx0 (hAell hρB) (hAsym hρB)
      (by positivity) hAh hKaC le_rfl (fun y _ y' _ ↦ by simp) (fun y _ ↦ by simp) hU hue
    have hDu : ∀ y ∈ halfBall ν x ρ,
        fderivWithin ℝ (fun y ↦ fderivWithin ℝ w B y e) (halfBall ν x ρ) y = H y e :=
      fun y hy ↦ by
        rw [fderivWithin_eq_toDual_gradientWithin, hgradu hρT
          (uniqueDiffOn_halfBall hν hρ0 (by linarith)) e y hy,
          LinearIsometryEquiv.apply_symm_apply]
    have hxρ : x ∈ halfBall ν x ρ := ⟨mem_closedBall_self hρ0.le, hx0⟩
    rw [hDu x hxρ] at hLc
    simp only [mul_zero, add_zero] at hLc hLh
    constructor
    · rw [hT₀, ha₀, mul_comm (CL * C₁ / c * osc / r ^ 2), ← mul_div_assoc, le_div_iff₀
        (by positivity)]
      have : ρ * ‖H x e‖ ≤ CL * (C₁ * osc / r * ‖e‖) := hLc
      rw [hρ] at this
      have e1 : ‖e‖ * (CL * C₁ / c * osc) = CL * (C₁ * osc / r * ‖e‖) * (r / c) := by
        field_simp
      rw [e1]
      calc ‖H x e‖ * r ^ 2 = (c * r * ‖H x e‖) * (r / c) := by field_simp
        _ ≤ _ := by gcongr
    · intro y hy y' hy'
      have := hLh y hy y' hy'
      rw [hDu y (hR2ρ hy), hDu y' (hR2ρ hy')] at this
      have hρs : ρ * √ρ = c * √c * (r * √r) := by
        rw [hρ, Real.sqrt_mul hc0.le]; ring
      rw [hρs] at this
      have hpos : 0 < c * √c * (r * √r) := by positivity
      rw [hT₁, ha₁]
      have e1 : CL * C₁ / (c * √c) * osc / (r ^ 2 * √r) * ‖e‖ * √(dist y y') =
          CL * (C₁ * osc / r * ‖e‖) * √(dist y y') / (c * √c * (r * √r)) := by
        field_simp
      rw [e1, le_div_iff₀ hpos]
      linarith
  -- the Hessian at points of `R2`
  have hR2T : R2 ⊆ T := hR2ρ.trans hρT
  have hxR2 : x ∈ R2 := ⟨mem_closedBall_self (by positivity), hx0⟩
  have hAy : ∀ y ∈ R2, (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪A y ξ, ξ⟫) ∧ ‖A y‖ ≤ M ∧
      (A y : E →ₗ[ℝ] E).IsSymmetric := fun y hy ↦
    ⟨(hAell hρB y (hR2ρ hy)).1, (hAell hρB y (hR2ρ hy)).2, hAsym hρB y (hR2ρ hy)⟩
  have hrowy : ∀ y ∈ R2, ∀ e : E, ⟪e, ν⟫ = 0 → ‖H y e‖ ≤ 2 * T₀ * ‖e‖ := by
    intro y hy e he
    obtain ⟨h1, h2⟩ := htan e he
    have h3 := h2 y hy x hxR2
    have hdx : √(dist y x) ≤ √c * √r := by
      rw [← Real.sqrt_mul hc0.le]
      exact Real.sqrt_le_sqrt ((mem_closedBall.1 hy.1).trans (by rw [hρ]; linarith))
    have hT₁T₀ : T₁ * (√c * √r) = T₀ := by
      rw [hT₁, hT₀, ← ha₁c]
      have : 0 < √r := Real.sqrt_pos.2 hr
      field_simp
    calc ‖H y e‖ ≤ ‖H x e‖ + ‖H y e - H x e‖ := norm_le_insert' _ _
      _ ≤ T₀ * ‖e‖ + T₁ * ‖e‖ * (√c * √r) := by
          gcongr; exact h3.trans (by gcongr)
      _ = 2 * T₀ * ‖e‖ := by rw [mul_right_comm, hT₁T₀]; ring
  have hHs : ∀ y ∈ R2, ‖H y‖ ≤ 4 * T₀ * lm := by
    intro y hy
    obtain ⟨hAe, hAb, hAs⟩ := hAy y hy
    have := norm_le_of_tangential_approx b hν (H y) (hsymm y (hR2T hy)) hAs hlam hAe hAb
      (R := 0) (by rw [heqn y (hR2T hy), abs_zero]) (by positivity) (hrowy y hy)
    rw [zero_div, add_zero] at this
    calc ‖H y‖ ≤ 2 * (2 * T₀) * (1 + Fintype.card (Fin (finrank ℝ E)) * M / lam) := this
      _ = 4 * T₀ * lm := by rw [hlm, hd]; ring
  have hHh : ∀ y ∈ R2, ∀ y' ∈ R2, ‖H y - H y'‖ ≤
      (2 * T₁ * lm + d * (4 * T₀ * lm) * (M * Dh) / lam) * √(dist y y') := by
    intro y hy y' hy'
    obtain ⟨hAe, hAb, hAs⟩ := hAy y hy
    set sd := √(dist y y') with hsd
    have hsd0 : 0 ≤ sd := Real.sqrt_nonneg _
    have hsymK : ∀ u v, (H y - H y') u v = (H y - H y') v u := fun u v ↦ by
      simp only [sub_apply]
      rw [hsymm y (hR2T hy) u v, hsymm y' (hR2T hy') u v]
    have hR : |∑ j, (H y - H y') (b j) (A y (b j))| ≤ d * (4 * T₀ * lm) * (M * Dh) * sd := by
      have e1 : ∑ j, (H y - H y') (b j) (A y (b j)) =
          ∑ j, H y' (b j) ((A y' - A y) (b j)) := by
        have h1 := heqn y (hR2T hy)
        have h2 := heqn y' (hR2T hy')
        simp only [sub_apply, map_sub, Finset.sum_sub_distrib, h1, h2]
      rw [e1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hA' : ‖A y' - A y‖ ≤ M * Dh * sd := by
        rw [hsd, dist_comm]; exact hAh y' (hR2ρ hy') y (hR2ρ hy)
      calc ∑ j, |H y' (b j) ((A y' - A y) (b j))| ≤ ∑ _j : Fin (finrank ℝ E),
            (4 * T₀ * lm) * (M * Dh * sd) := Finset.sum_le_sum fun j _ ↦ by
              rw [← Real.norm_eq_abs]
              calc ‖H y' (b j) ((A y' - A y) (b j))‖
                  ≤ ‖H y' (b j)‖ * ‖(A y' - A y) (b j)‖ := (H y' (b j)).le_opNorm _
                _ ≤ (‖H y'‖ * ‖b j‖) * (‖A y' - A y‖ * ‖b j‖) := by
                    gcongr
                    · exact (H y').le_opNorm _
                    · exact (A y' - A y).le_opNorm _
                _ ≤ (4 * T₀ * lm * 1) * (M * Dh * sd * 1) := by
                    rw [b.orthonormal.1 j]
                    gcongr
                    exact hHs y' hy'
                _ = _ := by ring
        _ = d * (4 * T₀ * lm) * (M * Dh) * sd := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hd]; ring
    have hrowK : ∀ e : E, ⟪e, ν⟫ = 0 → ‖(H y - H y') e‖ ≤ (T₁ * sd) * ‖e‖ := fun e he ↦ by
      rw [sub_apply]
      calc ‖H y e - H y' e‖ ≤ T₁ * ‖e‖ * sd := (htan e he).2 y hy y' hy'
        _ = T₁ * sd * ‖e‖ := by ring
    have := norm_le_of_tangential_approx b hν (H y - H y') hsymK hAs hlam hAe hAb hR
      (by positivity) hrowK
    calc ‖H y - H y'‖ ≤ 2 * (T₁ * sd) * (1 + Fintype.card (Fin (finrank ℝ E)) * M / lam) +
          d * (4 * T₀ * lm) * (M * Dh) * sd / lam := this
      _ = (2 * T₁ * lm + d * (4 * T₀ * lm) * (M * Dh) / lam) * sd := by
          rw [hlm, hd]; ring
  -- back to `halfSpace ν` and to the scale `r`
  have hκρ : κ₁ / 4 * r = ρ / 2 := by rw [hρ, hc]; ring
  rw [hκρ]
  have hR2b : ∀ y ∈ R2, y ∈ ball x (r / 2) := fun y hy ↦
    mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (by linarith))
  have hr2' : 0 < r ^ 2 := by positivity
  refine ⟨fun y hy ↦ ?_, fun y hy y' hy' ↦ ?_⟩
  · rw [← hcanH y (hR2b y hy)]
    have := hHs y hy
    calc r ^ 2 * ‖H y‖ ≤ r ^ 2 * (4 * T₀ * lm) := by gcongr
      _ = 4 * a₀ * lm * osc := by rw [hT₀]; field_simp
      _ ≤ _ := by
          gcongr
          have : 0 ≤ 2 * a₁ * lm + 8 * d * a₀ * lm * M * C₁ * η / lam := by positivity
          linarith
  · rw [← hcanH y (hR2b y hy), ← hcanH y' (hR2b y' hy')]
    have := hHh y hy y' hy'
    have hsq : 0 < √r := Real.sqrt_pos.2 hr
    have key : r ^ 2 * √r * (2 * T₁ * lm + d * (4 * T₀ * lm) * (M * Dh) / lam) ≤
        (4 * a₀ * lm + 2 * a₁ * lm + 8 * d * a₀ * lm * M * C₁ * η / lam) * osc := by
      have e1 : r ^ 2 * √r * (2 * T₁ * lm + d * (4 * T₀ * lm) * (M * Dh) / lam) =
          2 * a₁ * lm * osc + 4 * d * a₀ * lm * M * C₁ * osc * (osc / r) / lam := by
        rw [hT₁, hT₀, hDh]; field_simp
      rw [e1]
      have h1 : osc / r ≤ 2 * η := by rw [div_le_iff₀ hr]; linarith
      have h2 : 4 * d * a₀ * lm * M * C₁ * osc * (osc / r) / lam ≤
          8 * d * a₀ * lm * M * C₁ * η / lam * osc := by
        rw [div_le_iff₀ hlam, div_mul_eq_mul_div, div_mul_cancel₀ _ hlam.ne']
        have : 0 ≤ 4 * d * a₀ * lm * M * C₁ * osc := by positivity
        nlinarith
      have h3 : 0 ≤ 4 * a₀ * lm * osc := by positivity
      linarith
    calc r ^ 2 * √r * ‖H y - H y'‖ ≤ r ^ 2 * √r *
          ((2 * T₁ * lm + d * (4 * T₀ * lm) * (M * Dh) / lam) * √(dist y y')) := by gcongr
      _ = (r ^ 2 * √r * (2 * T₁ * lm + d * (4 * T₀ * lm) * (M * Dh) / lam)) *
          √(dist y y') := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key (Real.sqrt_nonneg _)

end BasicElliptic.Div
