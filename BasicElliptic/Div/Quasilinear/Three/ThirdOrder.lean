/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Three.SecondOrder
public import BasicElliptic.Div.Quasilinear.Three.Tensor
import BasicElliptic.Div.Quasilinear.HigherOrder
import BasicElliptic.Holder.Algebra
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The third-order estimate, uniform in the structure

`Div.third_order_estimate`: at a centre in the closed half space,
`r³ ‖D³w(x)‖ ≤ C osc w`.

For tangential `e, e'`, `v = ∂_{e'} ∂_e w` solves the linear conormal problem with coefficient
`A = DΦ(∇w)` and flux `-(D²Φ(∇w)(∇∂_{e'} w)) ∇∂_e w`
(`Div.IsConormalSolOn.isConormalSolOn_fderivWithin_apply` applied to
`∂_e w`). The first- and second-order estimates bound the coefficient's and the flux's
Hölder quotients with scale-invariant constants (the quadratic terms carry a factor
`osc w / r ≤ 2 η`), and the linear `C^{1,1/2}` estimate bounds `D³w(·, e', e)` at the centre.
The full third derivative is symmetric, and the differentiated equation
`Σ_j D³w(ξ, b_j, A b_j) = -Σ_j D²w(b_j, DA(ξ) b_j)` gives the remaining entries
(`Div.norm_le_of_tangential_three`).
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace Module
open scoped NNReal Gradient ContDiff Topology

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxSynthPendingDepth 6 in
set_option maxHeartbeats 4000000 in
-- a long proof with many explicit constants and nonlinear arithmetic
variable (E) in
/-- **The third-order estimate, uniform in the structure.** -/
theorem third_order_estimate {ν : E} (hν : ‖ν‖ = 1) {lam M δ : ℝ} (hlam : 0 < lam)
    (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ η > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → E),
      StructureBounds Φ lam M δ → ∀ (x : E) (r : ℝ) (w : E → ℝ), 0 < r →
      0 ≤ ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x r w →
      (∀ y ∈ halfBall ν x r, ‖gradientWithin w (halfBall ν x r) y‖ ≤ η) →
      r ^ 3 * ‖iteratedFDerivWithin ℝ 3 w (halfBall ν x r) x‖ ≤
        C * regionOsc w (halfBall ν x r) := by
  have : Nontrivial E := ⟨⟨ν, 0, by rintro rfl; simp at hν⟩⟩
  obtain ⟨η₁, hη₁, κ₁, hκ₁, hκ₁2, C₁, hC₁, hP1⟩ := first_order_estimate' E hν hlam hM hδ
  obtain ⟨η₂, hη₂, κ₂, hκ₂, hκ₂8, C₂, hC₂, hP2⟩ := second_order_estimate E hν hlam hM hδ
  set η := min (min η₁ η₂) (δ / 2) with hηdef
  have hη : 0 < η := lt_min (lt_min hη₁ hη₂) (by positivity)
  have hηη₁ : η ≤ η₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hηη₂ : η ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hηδ : η ≤ δ / 2 := min_le_right _ _
  set Kc := 2 * M * C₁ * η with hKc
  obtain ⟨CL, hCL, hL⟩ := linear_step E (lam := lam) (Λ := M) (Kc := Kc) hlam
  set b := stdOrthonormalBasis ℝ E with hb
  set d : ℝ := (Fintype.card (Fin (finrank ℝ E)) : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  set lm := 1 + d * M / lam with hlm
  have hlm0 : 0 ≤ lm := by positivity
  set c₃ := min (κ₁ / 2) (κ₂ / 2) with hc₃
  have hc₃0 : 0 < c₃ := lt_min (by positivity) (by positivity)
  have hc₃1 : c₃ ≤ κ₁ / 2 := min_le_left _ _
  have hc₃2 : c₃ ≤ κ₂ / 2 := min_le_right _ _
  have hc₃16 : c₃ ≤ 1 / 16 := hc₃2.trans (by linarith)
  have hsc₃ : √c₃ ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  set τc := CL * (C₂ / c₃ + √c₃ * (M * C₁ * C₂ ^ 2 * (2 * η) ^ 2 + 2 * M * C₂ ^ 2 * (2 * η)) +
    M * C₂ ^ 2 * (2 * η)) with hτc
  have hτc0 : 0 ≤ τc := by positivity
  set Rc := d * M * C₂ ^ 2 * (2 * η) with hRc
  have hRc0 : 0 ≤ Rc := by positivity
  refine ⟨η, hη, (2 * τc * lm + Rc / lam) * (1 + 2 * lm) + Rc / lam, by positivity, ?_⟩
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
  set q := osc / r with hq
  have hq0 : 0 ≤ q := by positivity
  have hq2 : q ≤ 2 * η := by rw [hq, div_le_iff₀ hr]; linarith
  have hsr : 0 < √r := Real.sqrt_pos.2 hr
  -- the first- and second-order estimates
  obtain ⟨-, hD1h⟩ := hP1 Φ hS x r w hr hx0 h fun y hy ↦ (hgrad y hy).trans hηη₁
  obtain ⟨hH2c, hH2h⟩ := hP2 Φ hS x r w hr hx0 h fun y hy ↦ (hgrad y hy).trans hηη₂
  -- `C³` on `T`, the within derivatives
  have hrange : ∀ y ∈ B, g y ∈ ball (0 : E) δ := fun y hy ↦
    mem_ball_zero_iff.2 ((hgrad y hy).trans_lt (by linarith))
  have hr2 : 0 < r / 2 := by positivity
  have hC3 := contDiffOn_three_halfBall_of_quasilinear_conormal hν hr hx isOpen_ball
    (convex_ball _ _) hlam hS.contDiffOn hS.ell hS.sym hrange h
  have hC2 : ContDiffOn ℝ 2 w (halfBall ν x (r / 2)) := hC3.of_le (by norm_num)
  set T := halfBall ν x (r / 2) with hT
  have hTB : T ⊆ B := halfBall_mono ν x (by linarith)
  have huT := uniqueDiffOn_halfBall hν hr2 (by linarith : -(r / 2) < ⟪x, ν⟫)
  have hxT : x ∈ T := ⟨mem_closedBall_self hr2.le, hx0⟩
  obtain ⟨-, hsymm, hgradu⟩ := hessianWithin_halfBall_data hν hr2 hx0 hTB hwB hC2
  set D := fderivWithin ℝ w B with hD
  have hDT : ∀ y ∈ T, fderivWithin ℝ w T y = D y := fun y hy ↦
    fderivWithin_subset hTB (huT y hy) (hwB y (hTB hy))
  have hD2 : ContDiffOn ℝ 2 D T :=
    (hC3.fderivWithin huT (by norm_num)).congr fun y hy ↦ (hDT y hy).symm
  set H := fderivWithin ℝ D T with hH
  have hH1 : ContDiffOn ℝ 1 H T := hD2.fderivWithin huT (by norm_num)
  have hDd : ∀ y ∈ T, HasFDerivWithinAt D (H y) T y := fun y hy ↦
    ((hD2.differentiableOn (by norm_num)) y hy).hasFDerivWithinAt
  have hHd : ∀ y ∈ T, HasFDerivWithinAt H (fderivWithin ℝ H T y) T y := fun y hy ↦
    ((hH1.differentiableOn one_ne_zero) y hy).hasFDerivWithinAt
  set T3 := fderivWithin ℝ H T x with hT3
  have hcanH : ∀ y ∈ ball x (r / 2),
      H y = fderivWithin ℝ (fderivWithin ℝ w (halfSpace ν)) (halfSpace ν) y := fun y hy ↦
    fderivWithin_fderivWithin_halfBall_eq w (ball_subset_ball (by linarith) hy) hy
  have hcanD : ∀ y ∈ ball x r, D y = fderivWithin ℝ w (halfSpace ν) y := fun y hy ↦
    fderivWithin_halfBall_eq w hy
  -- `g = Tc ∘ D` and `A = DΦ ∘ g`
  set Tc : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap with hTc
  have hTa : ∀ ℓ, Tc ℓ = (InnerProductSpace.toDual ℝ E).symm ℓ := fun _ ↦ rfl
  have hTcn : ∀ ℓ, ‖Tc ℓ‖ = ‖ℓ‖ := fun ℓ ↦ by rw [hTa, LinearIsometryEquiv.norm_map]
  have hTcN : ‖Tc‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ℓ ↦ by
    rw [hTcn, one_mul]
  have hgD : ∀ y, g y = Tc (D y) := fun y ↦ rfl
  have hgd : ∀ y ∈ T, HasFDerivWithinAt g (Tc ∘L H y) T y := fun y hy ↦ by
    have : g = fun y ↦ Tc (D y) := funext hgD
    rw [this]; exact Tc.hasFDerivAt.comp_hasFDerivWithinAt y (hDd y hy)
  set P : E → E →L[ℝ] E →L[ℝ] E := fun y ↦ fderiv ℝ (fderiv ℝ Φ) (g y) with hP
  set A : E → E →L[ℝ] E := fun y ↦ fderiv ℝ Φ (g y) with hA
  set A' : E → E →L[ℝ] E →L[ℝ] E := fun y ↦ P y ∘L (Tc ∘L H y) with hA'
  have hAd : ∀ y ∈ T, HasFDerivWithinAt A (A' y) T y := fun y hy ↦ by
    have hΦd : HasFDerivAt (fderiv ℝ Φ) (P y) (g y) :=
      ((hS.contDiffOn_fderiv.differentiableOn (by norm_num) _ (hrange y (hTB hy))).differentiableAt
        (isOpen_ball.mem_nhds (hrange y (hTB hy)))).hasFDerivAt
    exact hΦd.comp_hasFDerivWithinAt y (hgd y hy)
  have hg2 : ContDiffOn ℝ 2 g T := by
    have : g = fun y ↦ Tc (D y) := funext hgD
    rw [this]; exact Tc.contDiff.comp_contDiffOn hD2
  have hA1 : ContDiffOn ℝ 1 A T :=
    (hS.contDiffOn_fderiv.of_le (by norm_num)).comp (hg2.of_le (by norm_num))
      fun y hy ↦ hrange y (hTB hy)
  -- the region `R₃ = halfBall ν x ρ₃`
  set ρ₃ := c₃ * r with hρ₃
  have hρ₃0 : 0 < ρ₃ := by positivity
  have hρ₃8 : ρ₃ < r / 8 := by rw [hρ₃]; nlinarith
  set R₃ := halfBall ν x ρ₃ with hR₃
  have hR₃κ₁ : R₃ ⊆ halfBall ν x (κ₁ * r) := halfBall_mono ν x (by rw [hρ₃]; nlinarith)
  have hR₃κ₂ : R₃ ⊆ halfBall ν x (κ₂ * r) := halfBall_mono ν x (by rw [hρ₃]; nlinarith)
  have hR₃T : R₃ ⊆ T := halfBall_mono ν x (by linarith)
  have hR₃B : R₃ ⊆ B := hR₃T.trans hTB
  have hR₃b : ∀ y ∈ R₃, y ∈ ball x (r / 2) := fun y hy ↦
    mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (by linarith))
  have hxR₃ : x ∈ R₃ := ⟨mem_closedBall_self hρ₃0.le, hx0⟩
  -- bounds on `R₃`
  set Hs := C₂ * q / r with hHs
  set Hh := C₂ * q / (r * √r) with hHh
  set Dh := C₁ * q / √r with hDh
  have hHs0 : 0 ≤ Hs := by positivity
  have hHh0 : 0 ≤ Hh := by positivity
  have hDh0 : 0 ≤ Dh := by positivity
  have hHsb : ∀ y ∈ R₃, ‖H y‖ ≤ Hs := fun y hy ↦ by
    rw [hcanH y (hR₃b y hy), hHs, hq]
    have := hH2c y (hR₃κ₂ hy)
    have e : C₂ * (osc / r) / r = C₂ * osc / r ^ 2 := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have hHhb : ∀ y ∈ R₃, ∀ y' ∈ R₃, ‖H y - H y'‖ ≤ Hh * √(dist y y') := fun y hy y' hy' ↦ by
    rw [hcanH y (hR₃b y hy), hcanH y' (hR₃b y' hy')]
    have := hH2h y (hR₃κ₂ hy) y' (hR₃κ₂ hy')
    have hpos : 0 < r ^ 2 * √r := by positivity
    have e : Hh * √(dist y y') = C₂ * osc * √(dist y y') / (r ^ 2 * √r) := by
      rw [hHh, hq]; field_simp
    rw [e, le_div_iff₀ hpos]; linarith
  have hDhb : ∀ y ∈ R₃, ∀ y' ∈ R₃, ‖g y - g y'‖ ≤ Dh * √(dist y y') := fun y hy y' hy' ↦ by
    have hyb : y ∈ ball x r := ball_subset_ball (by linarith) (hR₃b y hy)
    have hyb' : y' ∈ ball x r := ball_subset_ball (by linarith) (hR₃b y' hy')
    rw [← dist_eq_norm, ← dist_fderivWithin_eq_dist_gradientWithin, dist_eq_norm,
      ← hD, hcanD y hyb, hcanD y' hyb']
    have := hD1h y (hR₃κ₁ hy) y' (hR₃κ₁ hy')
    have hpos : 0 < r * √r := by positivity
    have e : Dh * √(dist y y') = C₁ * osc * √(dist y y') / (r * √r) := by
      rw [hDh, hq]; field_simp
    rw [e, le_div_iff₀ hpos]; linarith
  have hPb : ∀ y ∈ B, ‖P y‖ ≤ M := fun y hy ↦ hS.norm_fderiv_fderiv_le (hrange y hy)
  have hAb : ∀ y ∈ B, ‖A y‖ ≤ M := fun y hy ↦ (hS.bound _ (hrange y hy)).1
  have hA'b : ∀ y ∈ R₃, ‖A' y‖ ≤ M * Hs := fun y hy ↦ by
    calc ‖A' y‖ ≤ ‖P y‖ * (‖Tc‖ * ‖H y‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
            gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ M * (1 * Hs) := by
          gcongr
          · exact hPb y (hR₃B hy)
          · exact hHsb y hy
      _ = M * Hs := by ring
  have hAh : ∀ y ∈ R₃, ∀ y' ∈ R₃, ‖A y - A y'‖ ≤ M * Dh * √(dist y y') := fun y hy y' hy' ↦ by
    calc ‖A y - A y'‖ ≤ M * ‖g y - g y'‖ :=
          hS.norm_fderiv_sub_le (hrange y (hR₃B hy)) (hrange y' (hR₃B hy'))
      _ ≤ M * (Dh * √(dist y y')) := by gcongr; exact hDhb y hy y' hy'
      _ = M * Dh * √(dist y y') := by ring
  have hKaC : M * Dh * √ρ₃ ≤ Kc := by
    have e : M * Dh * √ρ₃ = M * C₁ * q * √c₃ := by
      rw [hDh, hρ₃, Real.sqrt_mul hc₃0.le]; field_simp
    rw [e, hKc]
    calc M * C₁ * q * √c₃ ≤ M * C₁ * (2 * η) * 1 := by gcongr
      _ = 2 * M * C₁ * η := by ring
  -- the tangential entries of `D³w(x)`
  set τ := τc * q / r ^ 2 with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  have hhalf : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hentry : ∀ β e e', ⟪e, ν⟫ = 0 → ⟪e', ν⟫ = 0 → |T3 β e e'| ≤ τ * ‖β‖ * ‖e‖ * ‖e'‖ := by
    intro β e e' he he'
    have hs₁ : 0 < r / 4 := by positivity
    have hue := h.isConormalSolOn_fderivWithin_apply hν isOpen_ball hS.contDiffOn_one hrange
      hs₁ (by linarith) hx0 hhalf hC2 he
    set u : E → ℝ := fun y ↦ D y e with hu
    have huC2 : ContDiffOn ℝ 2 u (halfBall ν x (r / 8)) :=
      (hD2.clm_apply contDiffOn_const).mono (halfBall_mono ν x (by linarith))
    have hA1' : ContDiffOn ℝ 1 A (halfBall ν x (r / 8)) :=
      hA1.mono (halfBall_mono ν x (by linarith))
    have hve := hue.isConormalSolOn_fderivWithin_apply hν hs₁ (by linarith) hρ₃0 hρ₃8 hx0
      (closedBall_subset_ball (by linarith)) huC2 hA1' (contDiff_zero_fun.contDiffOn) he'
    set T'' := halfBall ν x (r / 8) with hT''
    have huT'' := uniqueDiffOn_halfBall hν (by positivity : (0 : ℝ) < r / 8)
      (by linarith : -(r / 8) < ⟪x, ν⟫)
    have hT''T : T'' ⊆ T := halfBall_mono ν x (by linarith)
    have hS₁T : halfBall ν x (r / 4) ⊆ T := halfBall_mono ν x (by linarith)
    have huS₁ := uniqueDiffOn_halfBall hν hs₁ (by linarith : -(r / 4) < ⟪x, ν⟫)
    have hR₃S₁ : R₃ ⊆ halfBall ν x (r / 4) := halfBall_mono ν x (by linarith)
    have hR₃T'' : R₃ ⊆ T'' := halfBall_mono ν x (by linarith)
    -- the derivative of `u` and the flux
    have hDu : ∀ y ∈ halfBall ν x (r / 4),
        fderivWithin ℝ u (halfBall ν x (r / 4)) y = H y e := fun y hy ↦ by
      rw [fderivWithin_eq_toDual_gradientWithin, hgradu hS₁T huS₁ e y hy,
        LinearIsometryEquiv.apply_symm_apply]
    have hgu : ∀ y ∈ halfBall ν x (r / 4),
        gradientWithin u (halfBall ν x (r / 4)) y = Tc (H y e) := fun y hy ↦
      hgradu hS₁T huS₁ e y hy
    set G' : E → E := fun y ↦ fderivWithin ℝ (0 : E → E) T'' y e' -
      fderivWithin ℝ A T'' y e' (gradientWithin u (halfBall ν x (r / 4)) y) with hG'
    have hG'eq : ∀ y ∈ R₃, G' y = -(P y (Tc (H y e')) (Tc (H y e))) := fun y hy ↦ by
      simp only [hG', fderivWithin_zero, Pi.zero_apply, zero_apply, zero_sub]
      rw [(hAd y (hR₃T hy)).mono hT''T |>.fderivWithin (huT'' y (hR₃T'' hy)), hgu y (hR₃S₁ hy)]
      rfl
    set v : E → ℝ := fun y ↦ fderivWithin ℝ u (halfBall ν x (r / 4)) y e' with hv
    have hveq : ∀ y ∈ R₃, v y = H y e e' := fun y hy ↦ by
      rw [hv]; simp only; rw [hDu y (hR₃S₁ hy)]
    -- bounds for the linear step
    set U₀ := Hs * ‖e‖ * ‖e'‖ with hU₀
    set KG := (M * Dh * Hs ^ 2 + 2 * M * Hs * Hh) * ‖e‖ * ‖e'‖ with hKG
    set MG := M * Hs ^ 2 * ‖e‖ * ‖e'‖ with hMG
    have hU : ∀ y ∈ R₃, |v y| ≤ U₀ := fun y hy ↦ by
      rw [hveq y hy, ← Real.norm_eq_abs]
      calc ‖H y e e'‖ ≤ ‖H y e‖ * ‖e'‖ := (H y e).le_opNorm e'
        _ ≤ ‖H y‖ * ‖e‖ * ‖e'‖ := by gcongr; exact (H y).le_opNorm e
        _ ≤ U₀ := by rw [hU₀]; gcongr; exact hHsb y hy
    have hHe : ∀ y ∈ R₃, ∀ f : E, ‖Tc (H y f)‖ ≤ Hs * ‖f‖ := fun y hy f ↦ by
      rw [hTcn]; exact ((H y).le_opNorm f).trans (by gcongr; exact hHsb y hy)
    have hMGb : ∀ y ∈ R₃, ‖G' y‖ ≤ MG := fun y hy ↦ by
      rw [hG'eq y hy, norm_neg]
      calc ‖P y (Tc (H y e')) (Tc (H y e))‖
          ≤ ‖P y‖ * ‖Tc (H y e')‖ * ‖Tc (H y e)‖ :=
            ((P y (Tc (H y e'))).le_opNorm _).trans (by gcongr; exact (P y).le_opNorm _)
        _ ≤ M * (Hs * ‖e'‖) * (Hs * ‖e‖) := by
            gcongr
            · exact hPb y (hR₃B hy)
            · exact hHe y hy e'
            · exact hHe y hy e
        _ = MG := by rw [hMG]; ring
    have hKGb : ∀ y ∈ R₃, ∀ y' ∈ R₃, ‖G' y - G' y'‖ ≤ KG * √(dist y y') := fun y hy y' hy' ↦ by
      rw [hG'eq y hy, hG'eq y' hy', neg_sub_neg, norm_sub_rev]
      set sd := √(dist y y') with hsd
      have hsd0 : 0 ≤ sd := Real.sqrt_nonneg _
      refine (norm_apply_sub_apply_le _ _ _ _ _ _).trans ?_
      have h1 : ‖P y - P y'‖ ≤ M * (Dh * sd) :=
        (hS.norm_fderiv_fderiv_sub_le (hrange y (hR₃B hy)) (hrange y' (hR₃B hy'))).trans
          (by gcongr; exact hDhb y hy y' hy')
      have hdif : ∀ f : E, ‖Tc (H y f) - Tc (H y' f)‖ ≤ Hh * sd * ‖f‖ := fun f ↦ by
        rw [← map_sub, hTcn, ← sub_apply]
        exact ((H y - H y').le_opNorm f).trans (by gcongr; exact hHhb y hy y' hy')
      calc ‖P y - P y'‖ * ‖Tc (H y e')‖ * ‖Tc (H y e)‖ +
            ‖P y'‖ * ‖Tc (H y e') - Tc (H y' e')‖ * ‖Tc (H y e)‖ +
            ‖P y'‖ * ‖Tc (H y' e')‖ * ‖Tc (H y e) - Tc (H y' e)‖
          ≤ M * (Dh * sd) * (Hs * ‖e'‖) * (Hs * ‖e‖) + M * (Hh * sd * ‖e'‖) * (Hs * ‖e‖) +
            M * (Hs * ‖e'‖) * (Hh * sd * ‖e‖) := by
            gcongr
            · exact hHe y hy e'
            · exact hHe y hy e
            · exact hPb y' (hR₃B hy')
            · exact hdif e'
            · exact hHe y hy e
            · exact hPb y' (hR₃B hy')
            · exact hHe y' hy' e'
            · exact hdif e
        _ = KG * sd := by rw [hKG]; ring
    have hAell : IsUniformlyElliptic lam M A R₃ := fun y hy ↦
      ⟨hS.ell _ (hrange y (hR₃B hy)), hAb y (hR₃B hy)⟩
    have hAsym : IsSymmetricOn A R₃ := fun y hy ↦ hS.sym _ (hrange y (hR₃B hy))
    obtain ⟨hLc, -⟩ := hL ν x ρ₃ (M * Dh) KG MG U₀ A G' v hν hρ₃0 hx0 hAell hAsym
      (by positivity) hAh hKaC (by positivity) hKGb hMGb hU hve
    -- `Dv(x) = D³w(x)(·, e, e')`
    have hHee : HasFDerivWithinAt (fun y ↦ H y e e')
        ((ContinuousLinearMap.apply ℝ ℝ e') ∘L (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) e) ∘L T3)
        R₃ x := by
      have := ((ContinuousLinearMap.apply ℝ ℝ e') ∘L
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) e)).hasFDerivAt.comp_hasFDerivWithinAt x
          ((hHd x hxT).mono hR₃T)
      exact this
    have huR₃ := uniqueDiffOn_halfBall hν hρ₃0 (by linarith : -ρ₃ < ⟪x, ν⟫)
    have hDv : fderivWithin ℝ v R₃ x =
        (ContinuousLinearMap.apply ℝ ℝ e') ∘L (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) e) ∘L
          T3 := by
      rw [fderivWithin_congr (fun y hy ↦ hveq y hy) (hveq x hxR₃)]
      exact hHee.fderivWithin (huR₃ x hxR₃)
    rw [hDv] at hLc
    have hval : |T3 β e e'| ≤ ‖(ContinuousLinearMap.apply ℝ ℝ e') ∘L
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) e) ∘L T3‖ * ‖β‖ := by
      rw [← Real.norm_eq_abs]
      have h := ((ContinuousLinearMap.apply ℝ ℝ e') ∘L
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) e) ∘L T3).le_opNorm β
      simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.apply_apply] using h
    -- arithmetic
    set N := ‖(ContinuousLinearMap.apply ℝ ℝ e') ∘L
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) e) ∘L T3‖ with hN
    have hNb : N ≤ τ * ‖e‖ * ‖e'‖ := by
      have hρs : ρ₃ * √ρ₃ = c₃ * √c₃ * (r * √r) := by
        rw [hρ₃, Real.sqrt_mul hc₃0.le]; ring
      rw [hρs] at hLc
      have key : CL * (U₀ + c₃ * √c₃ * (r * √r) * KG + ρ₃ * MG) ≤ ρ₃ * (τ * ‖e‖ * ‖e'‖) := by
        rw [hU₀, hKG, hMG, hτdef, hτc, hHs, hHh, hDh, hρ₃]
        have hee : 0 ≤ ‖e‖ * ‖e'‖ := by positivity
        have hqsq : q ^ 2 ≤ (2 * η) ^ 2 := pow_le_pow_left₀ hq0 hq2 2
        have hq3 : q ^ 3 ≤ (2 * η) ^ 2 * q := by
          have := mul_le_mul_of_nonneg_right hqsq hq0; nlinarith
        have hqq : q ^ 2 ≤ (2 * η) * q := by nlinarith
        have hsc0 : 0 ≤ √c₃ := Real.sqrt_nonneg _
        have e1 : CL * (C₂ * q / r * ‖e‖ * ‖e'‖ + c₃ * √c₃ * (r * √r) *
            ((M * (C₁ * q / √r) * (C₂ * q / r) ^ 2 + 2 * M * (C₂ * q / r) *
              (C₂ * q / (r * √r))) * ‖e‖ * ‖e'‖) +
            c₃ * r * (M * (C₂ * q / r) ^ 2 * ‖e‖ * ‖e'‖)) =
            c₃ * r * (CL * (C₂ / c₃ * q + √c₃ * (M * C₁ * C₂ ^ 2 * q ^ 3 +
              2 * M * C₂ ^ 2 * q ^ 2) + M * C₂ ^ 2 * q ^ 2) / r ^ 2 * (‖e‖ * ‖e'‖)) := by
          field_simp
        rw [e1]
        have e2 : c₃ * r * (CL * (C₂ / c₃ + √c₃ * (M * C₁ * C₂ ^ 2 * (2 * η) ^ 2 +
            2 * M * C₂ ^ 2 * (2 * η)) + M * C₂ ^ 2 * (2 * η)) * q / r ^ 2 * ‖e‖ * ‖e'‖) =
            c₃ * r * (CL * (C₂ / c₃ * q + √c₃ * (M * C₁ * C₂ ^ 2 * ((2 * η) ^ 2 * q) +
              2 * M * C₂ ^ 2 * ((2 * η) * q)) + M * C₂ ^ 2 * ((2 * η) * q)) / r ^ 2 *
              (‖e‖ * ‖e'‖)) := by ring
        rw [e2]
        gcongr
      have : ρ₃ * N ≤ ρ₃ * (τ * ‖e‖ * ‖e'‖) := hLc.trans key
      exact le_of_mul_le_mul_left this hρ₃0
    calc |T3 β e e'| ≤ N * ‖β‖ := hval
      _ ≤ τ * ‖e‖ * ‖e'‖ * ‖β‖ := by gcongr
      _ = τ * ‖β‖ * ‖e‖ * ‖e'‖ := by ring
  -- symmetries of `T3`
  have hderiv2 : ∀ u v, HasFDerivWithinAt (fun y ↦ H y u v)
      ((ContinuousLinearMap.apply ℝ ℝ v) ∘L (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u) ∘L T3)
      T x := fun u v ↦
    ((ContinuousLinearMap.apply ℝ ℝ v) ∘L
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u)).hasFDerivAt.comp_hasFDerivWithinAt x
        (hHd x hxT)
  have h23 : ∀ ξ u v, T3 ξ u v = T3 ξ v u := fun ξ u v ↦ by
    have e1 := (hderiv2 u v).fderivWithin (huT x hxT)
    have e2 := (hderiv2 v u).fderivWithin (huT x hxT)
    have e3 : fderivWithin ℝ (fun y ↦ H y u v) T x = fderivWithin ℝ (fun y ↦ H y v u) T x :=
      fderivWithin_congr (fun y hy ↦ hsymm y hy u v) (hsymm x hxT u v)
    rw [e1, e2] at e3
    have := congrArg (fun L ↦ L ξ) e3
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.apply_apply] using this
  have hclT : closure (interior T) = T := by
    rw [(convex_halfBall ν x (r / 2)).closure_interior_eq_closure_of_nonempty_interior
      (interior_halfBall_nonempty hν hr2 (by linarith)), (isClosed_halfBall ν x (r / 2)).closure_eq]
  have h13 : ∀ ξ a b', T3 ξ a b' = T3 b' a ξ := fun ξ a b' ↦ by
    set ua : E → ℝ := fun y ↦ D y a with hua
    have hua2 : ContDiffOn ℝ 2 ua T := hD2.clm_apply contDiffOn_const
    have hfa : ∀ y ∈ T, fderivWithin ℝ ua T y = H y a := fun y hy ↦ by
      have hd : HasFDerivWithinAt ua ((ContinuousLinearMap.apply ℝ ℝ a) ∘L H y) T y :=
        (ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp_hasFDerivWithinAt y (hDd y hy)
      rw [hd.fderivWithin (huT y hy)]
      ext ξ
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.apply_apply]
      exact hsymm y hy ξ a
    have hHa : HasFDerivWithinAt (fun y ↦ H y a)
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a) ∘L T3) T x :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a).hasFDerivAt.comp_hasFDerivWithinAt x
        (hHd x hxT)
    have e1 : fderivWithin ℝ (fderivWithin ℝ ua T) T x =
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a) ∘L T3 := by
      rw [fderivWithin_congr (fun y hy ↦ hfa y hy) (hfa x hxT)]
      exact hHa.fderivWithin (huT x hxT)
    have hcw : ContDiffWithinAt ℝ 2 ua T x := hua2 x hxT
    have hs2 := hcw.isSymmSndFDerivWithinAt (by simp) huT (by rw [hclT]; exact hxT) hxT ξ b'
    rw [e1] at hs2
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.apply_apply] at hs2
    exact hs2
  -- the differentiated equation
  have hclosed : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have heqn : ∀ y ∈ T, ∑ j, H y (b j) (A y (b j)) = 0 := fun y hy ↦ by
    have := sum_hessianWithin_eq_zero hν hr hx isOpen_ball (convex_ball _ _) hlam
      hS.contDiffOn_two hS.ell hS.sym hrange h hx0 hr2 hclosed hC2 b hy
    have hEq : EqOn (fderivWithin ℝ w T) (fderivWithin ℝ w B) T := fun z hz ↦
      fderivWithin_subset hTB (huT z hz) (hwB z (hTB hz))
    rwa [fderivWithin_congr hEq (hEq hy)] at this
  have hterm : ∀ j, HasFDerivWithinAt (fun y ↦ H y (b j) (A y (b j)))
      ((H x (b j)) ∘L ((ContinuousLinearMap.apply ℝ E (b j)) ∘L A' x) +
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b j)) ∘L T3).flip (A x (b j))) T x :=
    fun j ↦ by
      have hc := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b j)).hasFDerivAt.comp_hasFDerivWithinAt
        x (hHd x hxT)
      have hu := (ContinuousLinearMap.apply ℝ E (b j)).hasFDerivAt.comp_hasFDerivWithinAt x
        (hAd x hxT)
      exact hc.clm_apply hu
  have hFd := HasFDerivWithinAt.fun_sum (u := Finset.univ) fun j _ ↦ hterm j
  have hF0 : fderivWithin ℝ (fun y ↦ ∑ j ∈ Finset.univ, H y (b j) (A y (b j))) T x = 0 := by
    rw [fderivWithin_congr (f := fun _ ↦ (0 : ℝ)) (fun y hy ↦ by simpa using heqn y hy)
      (by simpa using heqn x hxT)]
    exact fderivWithin_const_apply _
  rw [hFd.fderivWithin (huT x hxT)] at hF0
  set R := Rc * q / r ^ 2 with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hxR₃' := hxR₃
  have heqξ : ∀ ξ, |∑ j, T3 ξ (b j) (A x (b j))| ≤ R * ‖ξ‖ := by
    intro ξ
    have hξ := congrArg (fun L ↦ L ξ) hF0
    simp only [sum_apply, add_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.flip_apply, zero_apply,
      Finset.sum_add_distrib] at hξ
    have e : ∑ j, T3 ξ (b j) (A x (b j)) = -∑ j, H x (b j) (A' x ξ (b j)) := by linarith
    rw [e, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |H x (b j) (A' x ξ (b j))| ≤ ∑ _j : Fin (finrank ℝ E), Hs * (M * Hs * ‖ξ‖) :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [← Real.norm_eq_abs]
            calc ‖H x (b j) (A' x ξ (b j))‖ ≤ (‖H x‖ * ‖b j‖) * (‖A' x ξ‖ * ‖b j‖) :=
                  ((H x (b j)).le_opNorm _).trans (by
                    gcongr
                    · exact (H x).le_opNorm _
                    · exact (A' x ξ).le_opNorm _)
              _ ≤ (Hs * 1) * ((M * Hs * ‖ξ‖) * 1) := by
                  rw [b.orthonormal.1 j]
                  gcongr
                  · exact hHsb x hxR₃
                  · exact ((A' x).le_opNorm ξ).trans (by gcongr; exact hA'b x hxR₃)
              _ = Hs * (M * Hs * ‖ξ‖) := by ring
      _ = d * M * Hs ^ 2 * ‖ξ‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hd]; ring
      _ ≤ R * ‖ξ‖ := by
          gcongr
          rw [hRdef, hRc, hHs]
          have hqq : q ^ 2 ≤ (2 * η) * q := by nlinarith
          have e1 : d * M * (C₂ * q / r) ^ 2 = d * M * C₂ ^ 2 * q ^ 2 / r ^ 2 := by ring
          rw [e1]
          have h1 : d * M * C₂ ^ 2 * q ^ 2 ≤ d * M * C₂ ^ 2 * (2 * η) * q := by
            have := mul_le_mul_of_nonneg_left hqq (by positivity : 0 ≤ d * M * C₂ ^ 2)
            linarith
          exact div_le_div_of_nonneg_right h1 (by positivity)
  -- the tensor bound
  have hAx := hS.ell _ (hrange x hxB)
  have hT3 := norm_le_of_tangential_three b hν T3 h23 h13 (hS.sym _ (hrange x hxB)) hlam hAx
    (hAb x hxB) hR0 hτ0 heqξ hentry
  -- `‖D³w(x)‖ ≤ ‖T3‖`
  have huB := uniqueDiffOn_halfBall hν hr hx
  have hBT : B =ᶠ[𝓝 x] T :=
    (halfBall_eventuallyEq_halfSpace (mem_ball_self hr)).trans
      (halfBall_eventuallyEq_halfSpace (mem_ball_self hr2)).symm
  have hnorm : ‖iteratedFDerivWithin ℝ 3 w B x‖ ≤ ‖T3‖ := by
    rw [← norm_iteratedFDerivWithin_fderivWithin huB hxB, ← hD,
      iteratedFDerivWithin_congr_set hBT 2]
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m ↦ ?_
    rw [iteratedFDerivWithin_two_apply D huT hxT m, Fin.prod_univ_two]
    calc ‖fderivWithin ℝ (fderivWithin ℝ D T) T x (m 0) (m 1)‖
        ≤ ‖fderivWithin ℝ (fderivWithin ℝ D T) T x (m 0)‖ * ‖m 1‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖T3‖ * ‖m 0‖ * ‖m 1‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖T3‖ * (‖m 0‖ * ‖m 1‖) := by ring
  -- arithmetic
  have hcard : (Fintype.card (Fin (finrank ℝ E)) : ℝ) = d := rfl
  rw [hcard] at hT3
  calc r ^ 3 * ‖iteratedFDerivWithin ℝ 3 w B x‖ ≤ r ^ 3 * ‖T3‖ := by gcongr
    _ ≤ r ^ 3 * ((2 * τ * (1 + d * M / lam) + R / lam) * (1 + 2 * (1 + d * M / lam)) +
          R / lam) := by gcongr
    _ = ((2 * τc * lm + Rc / lam) * (1 + 2 * lm) + Rc / lam) * osc := by
        rw [hτdef, hRdef, hq, hlm]; field_simp

end BasicElliptic.Div
