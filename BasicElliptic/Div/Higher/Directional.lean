/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Higher.Translate
import BasicElliptic.Common.UniformLimit
import BasicElliptic.Div.Boundary.Main
import BasicElliptic.Holder.Algebra

/-!
# Directional second derivatives for the linear conormal problem

`Div.exists_hasFDerivWithinAt_fderivWithin_apply_of_linear`: the linear analogue of
`Div.exists_hasFDerivWithinAt_fderivWithin_apply` (`Div/Quasilinear/Directional.lean`). Let `w`
be `C¹` on `B = halfBall ν x r` with within-gradient `α`-Hölder (constant `H_w`) and bounded by
`M` on `halfBall ν z (4ρ)`, and let `e` (`‖e‖ ≤ 1`) be a direction whose translations preserve the
half space on `closedBall z (2ρ)`. Suppose that for `0 < t ≤ ρ` the difference
`u_t = w (t e + ·) - w` is a conormal solution on `halfBall ν z (2ρ)` with a fixed symmetric,
`(lam, Λ)`-elliptic, `K_a`-Hölder coefficient `a`, no right-hand side, and a flux `G_t` with
`[G_t]_α ≤ t K₁` and `‖G_t‖ ≤ t K₂` (this is what `Div.IsConormalSolOn.translate_sub` provides).
Then `∂_e w = D_B w (·) e` is differentiable within `S = halfBall ν z (ρ/4)` with an `α`-Hölder
derivative.

## Proof

At `q ∈ S` the scaled conormal boundary estimate (`Div.c1Holder_halfBall_estimate`) on
`halfBall ν q ρ` gives
`ρ^{1+α} [D u_t]_{α, halfBall ν q (ρ/2)} ≤ C (osc u_t + ρ^{1+α} t K₁ + ρ t K₂)
  ≤ C t (2 M + ρ^{1+α} K₁ + ρ K₂)`,
the seminorm being finite by the qualitative conormal boundary theorem. Hence the derivatives of
`u_t / t` are uniformly `α`-Hölder on `S`; `u_t / t → ∂_e w` uniformly on `S`, and
`exists_hasFDerivWithinAt_of_tendstoUniformlyOn` concludes along `t_n = ρ / (n + 1)`.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology NNReal

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (E) in
/-- The scaled conormal estimate of `Div/Boundary/` for problems with a flux and no right-hand side,
together with the finiteness of the Hölder seminorm (from the qualitative boundary theorem), at
centres in the closed half space. -/
theorem exists_holderSeminormOn_le_of_isConormalSolOn_flux {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {lam Λ Kc : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν p : E) (ρ : ℝ) (Ka KG : ℝ≥0) (MG : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (u : E → ℝ),
      ‖ν‖ = 1 → 0 < ρ → 0 ≤ ⟪p, ν⟫ → IsUniformlyElliptic lam Λ a (halfBall ν p ρ) →
      IsSymmetricOn a (halfBall ν p ρ) → HolderOnWith Ka α a (halfBall ν p ρ) →
      (Ka : ℝ) * ρ ^ (α : ℝ) ≤ Kc → HolderOnWith KG α G (halfBall ν p ρ) →
      (∀ y ∈ halfBall ν p ρ, ‖G y‖ ≤ MG) → IsConormalSolOn ν a G 0 p ρ u →
      eHolderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≠ ⊤ ∧
      ρ ^ (1 + (α : ℝ)) *
          holderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≤
        C * (regionOsc u (halfBall ν p ρ) + ρ ^ (1 + (α : ℝ)) * KG + ρ * MG) := by
  obtain ⟨C, hC⟩ := Div.c1Holder_halfBall_estimate E α hα hα1 lam Λ Kc hlam
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ν p ρ Ka KG MG a G u hν hρ hp hell hsym ha hKa hG hMG hu
  have hp' : -ρ < ⟪p, ν⟫ := by linarith
  have hfm : AEStronglyMeasurable (0 : E → ℝ) (volume.restrict (halfBall ν p ρ)) :=
    aestronglyMeasurable_const
  have hpB : p ∈ halfBall ν p ρ := ⟨mem_closedBall_self hρ.le, hp⟩
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
    obtain ⟨c, hc⟩ := (isCompact_halfBall ν p ρ).exists_bound_of_continuousOn
      (hu.1.continuousOn)
    have hosc := regionOsc_nonneg_of_abs_le ⟨p, hpB⟩ (fun y hy ↦ (Real.norm_eq_abs _).symm.le.trans
      (hc y hy))
    have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG p hpB)
    have h0 : 0 ≤ ρ * ‖fderivWithin ℝ u (halfBall ν p ρ) p‖ := by positivity
    have hR : 0 ≤ regionOsc u (halfBall ν p ρ) + ρ ^ (1 + (α : ℝ)) * KG + ρ * MG := by positivity
    calc ρ ^ (1 + (α : ℝ)) *
          holderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2))
        ≤ C * (regionOsc u (halfBall ν p ρ) + ρ ^ (1 + (α : ℝ)) * KG + ρ * MG) := by linarith
      _ ≤ max C 0 * (regionOsc u (halfBall ν p ρ) + ρ ^ (1 + (α : ℝ)) * KG + ρ * MG) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hR

/-- **Directional second derivatives, linear case** (see the module docstring). -/
theorem exists_hasFDerivWithinAt_fderivWithin_apply_of_linear {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {ν : E} (hν : ‖ν‖ = 1) {lam Λ : ℝ} (hlam : 0 < lam) {x : E} {r : ℝ}
    {w : E → ℝ} (hw : ContDiffOn ℝ 1 w (halfBall ν x r)) {z : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hz : 0 ≤ ⟪z, ν⟫) (hzr : dist z x + 4 * ρ ≤ r) {a : E → E →L[ℝ] E}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν z (2 * ρ)))
    (hsym : IsSymmetricOn a (halfBall ν z (2 * ρ))) {Ka : ℝ≥0}
    (ha : HolderOnWith Ka α a (halfBall ν z (2 * ρ))) {Hw : ℝ≥0}
    (hHw : HolderOnWith Hw α (gradientWithin w (halfBall ν x r)) (halfBall ν z (4 * ρ)))
    {M : ℝ} (hM : ∀ y ∈ halfBall ν z (4 * ρ), ‖gradientWithin w (halfBall ν x r) y‖ ≤ M)
    {e : E} (he : ‖e‖ ≤ 1)
    (hcompat : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ closedBall z (2 * ρ),
      (0 ≤ ⟪t • e + y, ν⟫ ↔ 0 ≤ ⟪y, ν⟫))
    {Gt : ℝ → E → E} {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁)
    (hGt : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ halfBall ν z (2 * ρ), ∀ y' ∈ halfBall ν z (2 * ρ),
      ‖Gt t y - Gt t y'‖ ≤ t * K₁ * dist y y' ^ (α : ℝ))
    (hGb : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ halfBall ν z (2 * ρ), ‖Gt t y‖ ≤ t * K₂)
    (hlin : ∀ t ∈ Ioc (0 : ℝ) ρ,
      IsConormalSolOn ν a (Gt t) 0 z (2 * ρ) (fun y ↦ w (t • e + y) - w y)) :
    ∃ g : E → E →L[ℝ] ℝ, (∀ y ∈ halfBall ν z (ρ / 4),
      HasFDerivWithinAt (fun y ↦ fderivWithin ℝ w (halfBall ν x r) y e) (g y)
        (halfBall ν z (ρ / 4)) y) ∧
      ∃ H : ℝ, 0 ≤ H ∧ ∀ y ∈ halfBall ν z (ρ / 4), ∀ y' ∈ halfBall ν z (ρ / 4),
        ‖g y - g y'‖ ≤ H * dist y y' ^ (α : ℝ) := by
  set B := halfBall ν x r with hB
  set S4 := halfBall ν z (4 * ρ) with hS4
  set B2 := halfBall ν z (2 * ρ) with hB2
  set S := halfBall ν z (ρ / 4) with hS
  set Kc : ℝ := Ka * ρ ^ (α : ℝ) with hKc
  obtain ⟨C, hC0, hCest⟩ := exists_holderSeminormOn_le_of_isConormalSolOn_flux E hα hα1
    (Λ := Λ) (Kc := Kc) hlam
  have hzS4 : z ∈ S4 := ⟨mem_closedBall_self (by positivity), hz⟩
  have hzB2 : z ∈ B2 := ⟨mem_closedBall_self (by positivity), hz⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hzS4)
  have hρmem : ρ ∈ Ioc (0 : ℝ) ρ := ⟨hρ, le_rfl⟩
  have hK₂ : 0 ≤ K₂ := by
    have := (norm_nonneg _).trans (hGb ρ hρmem z hzB2)
    exact nonneg_of_mul_nonneg_right (by linarith) hρ
  have hball4 : closedBall z (4 * ρ) ⊆ closedBall x r := closedBall_subset_closedBall' (by linarith)
  have hS4B : S4 ⊆ B := inter_subset_inter_left _ hball4
  have hwB : DifferentiableOn ℝ w B := hw.differentiableOn one_ne_zero
  -- the translate stays in `S4`
  have htr : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ B2, t • e + y ∈ S4 := by
    intro t ht y hy
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall]
      have : dist (t • e + y) y ≤ ρ := by
        rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht.1.le]
        nlinarith [ht.2, norm_nonneg e, ht.1]
      linarith [dist_triangle (t • e + y) y z, (mem_closedBall.1 hy.1)]
    · exact (hcompat t ht y hy.1).2 hy.2
  have hB2S4 : B2 ⊆ S4 := halfBall_mono ν z (by linarith)
  have hKaρ : (Ka : ℝ) * ρ ^ (α : ℝ) ≤ Kc := le_rfl
  have hS_B2 : S ⊆ B2 := halfBall_mono ν z (by linarith)
  have huS : UniqueDiffOn ℝ S := uniqueDiffOn_halfBall hν (by positivity) (by linarith)
  set Q : ℝ := C * (2 * M + ρ ^ (1 + (α : ℝ)) * K₁ + ρ * K₂) / ρ ^ (1 + (α : ℝ)) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  -- the uniform Hölder bound for the derivatives of `u_t` on `S`
  have hpair : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ q ∈ S, ∀ q' ∈ S,
      ‖fderivWithin ℝ (fun y ↦ w (t • e + y) - w y) S q -
          fderivWithin ℝ (fun y ↦ w (t • e + y) - w y) S q'‖ ≤
        (t * Q) * dist q q' ^ (α : ℝ) := by
    intro t ht q hq q' hq'
    set u : E → ℝ := fun y ↦ w (t • e + y) - w y with hu
    have hqz : dist q z ≤ ρ / 4 := hq.1
    have hBq : halfBall ν q ρ ⊆ B2 :=
      inter_subset_inter_left _ (closedBall_subset_closedBall' (by linarith))
    have hq0 : 0 ≤ ⟪q, ν⟫ := hq.2
    have hlinq := (hlin t ht).restrict_halfBall (y := q) hν hρ (by linarith)
      (closedBall_subset_closedBall' (by linarith)) (ball_subset_ball' (by linarith))
    set KG : ℝ≥0 := Real.toNNReal (t * K₁) with hKG
    have hKG' : (KG : ℝ) = t * K₁ := Real.coe_toNNReal _ (mul_nonneg ht.1.le hK₁)
    have hGq : HolderOnWith KG α (Gt t) (halfBall ν q ρ) := by
      refine holderOnWith_iff_dist_le.2 fun y hy y' hy' ↦ ?_
      rw [hKG', dist_eq_norm]
      exact hGt t ht y (hBq hy) y' (hBq hy')
    obtain ⟨hfin, hest⟩ := hCest ν q ρ Ka KG (t * K₂) a (Gt t) u hν hρ hq.2 (hell.mono hBq)
      (hsym.mono hBq) (ha.mono hBq) hKaρ hGq (fun y hy ↦ hGb t ht y (hBq hy)) hlinq
    have hqB : q ∈ halfBall ν q ρ := ⟨mem_closedBall_self hρ.le, hq.2⟩
    have hosc : regionOsc u (halfBall ν q ρ) ≤ 2 * (M * t) :=
      regionOsc_le_two_mul_of_abs_le ⟨q, hqB⟩ fun y hy ↦
        abs_translate_sub_le (convex_halfBall ν z (4 * ρ)) hS4B hwB hM ht.1.le he
          (hB2S4 (hBq hy)) (htr t ht y (hBq hy))
    have hρα : 0 < ρ ^ (1 + (α : ℝ)) := by positivity
    have hsn : holderSeminormOn α (fderivWithin ℝ u (halfBall ν q ρ)) (halfBall ν q (ρ / 2)) ≤
        t * Q := by
      rw [hQ, mul_div_assoc', le_div_iff₀ hρα, mul_comm]
      refine hest.trans ?_
      rw [hKG']
      have : regionOsc u (halfBall ν q ρ) + ρ ^ (1 + (α : ℝ)) * (t * K₁) + ρ * (t * K₂) ≤
          t * (2 * M + ρ ^ (1 + (α : ℝ)) * K₁ + ρ * K₂) := by
        have e : t * (2 * M + ρ ^ (1 + (α : ℝ)) * K₁ + ρ * K₂) =
            2 * (M * t) + ρ ^ (1 + (α : ℝ)) * (t * K₁) + ρ * (t * K₂) := by ring
        rw [e]; linarith
      calc C * (regionOsc u (halfBall ν q ρ) + ρ ^ (1 + (α : ℝ)) * (t * K₁) + ρ * (t * K₂))
          ≤ C * (t * (2 * M + ρ ^ (1 + (α : ℝ)) * K₁ + ρ * K₂)) :=
            mul_le_mul_of_nonneg_left this hC0
        _ = t * (C * (2 * M + ρ ^ (1 + (α : ℝ)) * K₁ + ρ * K₂)) := by ring
    have hq'' : q' ∈ halfBall ν q (ρ / 2) :=
      ⟨by rw [mem_closedBall]; linarith [dist_triangle q' z q, dist_comm q z,
        mem_closedBall.1 hq'.1], hq'.2⟩
    have hqq : q ∈ halfBall ν q (ρ / 2) := ⟨mem_closedBall_self (by positivity), hq.2⟩
    have hd := dist_le_holderSeminormOn_mul hfin hqq hq''
    have hSq : S ⊆ halfBall ν q ρ := fun y hy ↦
      ⟨by rw [mem_closedBall]; linarith [dist_triangle y z q, dist_comm q z,
        mem_closedBall.1 hy.1], hy.2⟩
    have hud : DifferentiableOn ℝ u (halfBall ν q ρ) :=
      ((hlin t ht).1.differentiableOn one_ne_zero).mono hBq
    rw [fderivWithin_subset hSq (huS q hq) (hud q (hSq hq)),
      fderivWithin_subset hSq (huS q' hq') (hud q' (hSq hq')), ← dist_eq_norm]
    exact hd.trans (mul_le_mul_of_nonneg_right hsn (Real.rpow_nonneg dist_nonneg _))
  -- the sequence of difference quotients
  set tn : ℕ → ℝ := fun n ↦ ρ / (n + 1) with htn_def
  have htn : ∀ n, tn n ∈ Ioc (0 : ℝ) ρ := fun n ↦
    ⟨by positivity, div_le_self hρ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩
  set un : ℕ → E → ℝ := fun n y ↦ (tn n)⁻¹ * (w (tn n • e + y) - w y) with hun
  have hdiffu : ∀ n, DifferentiableOn ℝ (fun y ↦ w (tn n • e + y) - w y) S := fun n ↦
    ((hlin _ (htn n)).1.differentiableOn one_ne_zero).mono hS_B2
  have hdiff : ∀ n, DifferentiableOn ℝ (un n) S := fun n ↦ (hdiffu n).const_mul _
  have hHun : ∀ n, ∀ q ∈ S, ∀ q' ∈ S,
      ‖fderivWithin ℝ (un n) S q - fderivWithin ℝ (un n) S q'‖ ≤ Q * dist q q' ^ (α : ℝ) := by
    intro n q hq q' hq'
    have ht := htn n
    rw [fderivWithin_const_mul (huS q hq) ((hdiffu n) q hq),
      fderivWithin_const_mul (huS q' hq') ((hdiffu n) q' hq'), ← smul_sub, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 ht.1.le)]
    calc (tn n)⁻¹ * ‖fderivWithin ℝ (fun y ↦ w (tn n • e + y) - w y) S q -
          fderivWithin ℝ (fun y ↦ w (tn n • e + y) - w y) S q'‖
        ≤ (tn n)⁻¹ * ((tn n * Q) * dist q q' ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left (hpair _ ht q hq q' hq') (inv_nonneg.2 ht.1.le)
      _ = Q * dist q q' ^ (α : ℝ) := by
          have : tn n ≠ 0 := ht.1.ne'
          field_simp
  have hlim : TendstoUniformlyOn un (fun y ↦ fderivWithin ℝ w B y e) atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hT : Tendsto (fun n : ℕ ↦ (Hw : ℝ) * tn n ^ (α : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto tn atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
        rw [mul_zero] at this
        refine this.congr fun n ↦ ?_
        simp only [htn_def, mul_one_div]
      have h2 := (h1.rpow_const (Or.inr (le_of_lt (by exact_mod_cast hα)))).const_mul (Hw : ℝ)
      simpa [Real.zero_rpow (ne_of_gt (by exact_mod_cast hα : (0 : ℝ) < α))] using h2
    filter_upwards [hT.eventually (gt_mem_nhds hε)] with n hn y hy
    rw [dist_comm, Real.dist_eq]
    exact (abs_diffQuot_sub_le (convex_halfBall ν z (4 * ρ)) hS4B hwB hHw (htn n).1 he
      (hB2S4 (hS_B2 hy)) (htr _ (htn n) y (hS_B2 hy))).trans_lt hn
  -- an inner ball and a diameter bound for `S`
  set c : E := z + (ρ / 8) • ν with hc
  have hcz : dist c z = ρ / 8 := by
    rw [hc, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, Real.norm_of_nonneg (by positivity),
      mul_one]
  have hball : closedBall c (ρ / 16) ⊆ S := by
    intro y hy
    rw [mem_closedBall] at hy
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall]; linarith [dist_triangle y c z]
    · rw [mem_halfSpace]
      have h1 : ⟪y, ν⟫ = ⟪z, ν⟫ + ρ / 8 + ⟪y - c, ν⟫ := by
        simp only [hc, inner_sub_left, inner_add_left, real_inner_smul_left,
          real_inner_self_of_norm_eq_one hν]
        ring
      have h2 : |⟪y - c, ν⟫| ≤ ρ / 16 := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [hν, mul_one, ← dist_eq_norm]
        exact hy
      linarith [neg_abs_le ⟪y - c, ν⟫]
  have hD : ∀ p ∈ S, dist p c ≤ ρ / 2 := fun p hp ↦ by
    linarith [dist_triangle p z c, dist_comm z c, mem_closedBall.1 hp.1]
  obtain ⟨g, hg, hgH⟩ := exists_hasFDerivWithinAt_of_tendstoUniformlyOn
    (convex_halfBall ν z (ρ / 4)) (by positivity : (0 : ℝ) < ρ / 16) hball hD hdiff
    (by exact_mod_cast hα : (0 : ℝ) < α) hQ0 hHun hlim
  exact ⟨g, hg, Q, hQ0, hgH⟩

end BasicElliptic.Div
