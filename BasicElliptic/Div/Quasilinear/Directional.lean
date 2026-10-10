/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.DifferenceQuotient
public import BasicElliptic.Statements.Div
public import BasicElliptic.Common.WithinDeriv
import BasicElliptic.Common.UniformLimit
import BasicElliptic.Div.Boundary.Main
import BasicElliptic.Holder.Algebra

/-!
# Directional second derivatives by difference quotients

`Div.exists_hasFDerivWithinAt_fderivWithin_apply`: let `w` be a quasilinear conormal solution on
`B = halfBall ν x r` whose within-gradient is `α`-Hölder (constant `H_w`) on
`halfBall ν z (4ρ)` and takes values in a convex `K ⊆ U` on which `DΦ` is bounded by `Λ` and
`L`-Lipschitz. Let `e` be a direction (`‖e‖ ≤ 1`) whose translations `y ↦ h e + y`,
`0 < h ≤ ρ`, preserve the half space on `closedBall z (2ρ)`; this holds for every tangential `e`
(`⟪e, ν⟫ = 0`), and for every `e` when the ball lies in the open half space. Then the directional
derivative `∂_e w = D_B w (·) e` is differentiable within `S = halfBall ν z (ρ/4)`, with an
`α`-Hölder derivative.

## Proof

For `0 < h ≤ ρ`, `w(h e + ·)` and `w` are quasilinear conormal solutions on `halfBall ν z (2ρ)`
(`IsQuasilinearConormalSolOn.translate`, `.restrict`), so `u_h = w(h e + ·) - w` is a linear
conormal solution with the chord coefficient `a_h(y) = chordCoeff Φ (∇w(h e + y)) (∇w(y))`
(`IsQuasilinearConormalSolOn.sub`): symmetric, `(lam, Λ)`-elliptic, and `2 L H_w`-Hölder.
At every `p ∈ halfBall ν z ρ` the scaled conormal estimate (`Div.c1Holder_halfBall_estimate`, with
`K = 2 L H_w ρ^α` fixed before `C`) on `halfBall ν p ρ` gives
`ρ^{1+α} [D u_h]_{α, halfBall ν p (ρ/2)} ≤ C osc u_h ≤ 2 C M h` (mean value inequality), the
seminorm being finite by the qualitative conormal theorem. Any two points of `S` lie in such a
`halfBall ν p (ρ/2)` (take `p` one of them), so the derivatives of `u_h / h` are uniformly
`α`-Hölder on `S`. Finally `u_h / h → ∂_e w` uniformly on `S` (`|u_h/h - ∂_e w| ≤ H_w h^α`), and
`exists_hasFDerivWithinAt_of_tendstoUniformlyOn` (`Common/UniformLimit.lean`) concludes, along
`h_n = ρ / (n + 1)`.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology NNReal

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The oscillation is at most twice a bound on `|f|`. -/
theorem regionOsc_le_two_mul_of_abs_le {X : Type*} {f : X → ℝ} {s : Set X} (hs : s.Nonempty)
    {c : ℝ} (h : ∀ y ∈ s, |f y| ≤ c) : regionOsc f s ≤ 2 * c := by
  rw [regionOsc_def]
  have h1 : sSup (f '' s) ≤ c := csSup_le (hs.image f)
    (by rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (h y hy))
  have h2 : -c ≤ sInf (f '' s) := le_csInf (hs.image f)
    (by rintro _ ⟨y, hy, rfl⟩; exact neg_le_of_abs_le (h y hy))
  linarith

/-- The oscillation of a function bounded on a nonempty set is nonnegative. -/
theorem regionOsc_nonneg_of_abs_le {X : Type*} {f : X → ℝ} {s : Set X} (hs : s.Nonempty)
    {c : ℝ} (h : ∀ y ∈ s, |f y| ≤ c) : 0 ≤ regionOsc f s := by
  rw [regionOsc_def, sub_nonneg]
  refine csInf_le_csSup (hs.image f) ⟨-c, ?_⟩ ⟨c, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩; exact neg_le_of_abs_le (h y hy)
  · rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (h y hy)

/-- Conormal solutions only see the coefficient on the half ball. -/
theorem IsConormalSolOn.congr_coeff {ν : E} {a a' : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ}
    {x : E} {r : ℝ} {w : E → ℝ} (h : IsConormalSolOn ν a G f x r w)
    (ha : EqOn a a' (halfBall ν x r)) : IsConormalSolOn ν a' G f x r w := by
  refine ⟨h.1, fun φ hφ ↦ Eq.trans ?_ (h.2 φ hφ)⟩
  refine setIntegral_congr_fun (measurableSet_halfBall ν x r) fun y hy ↦ ?_
  simp only [ha hy]

variable (E) in
/-- The scaled conormal estimate (`Div/Boundary/Estimate.lean`) for problems without data, together
with the finiteness of the Hölder seminorm (from the qualitative conormal theorem), at centres in
the closed half space. -/
theorem exists_holderSeminormOn_le_of_isConormalSolOn {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {lam Λ Kc : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν p : E) (ρ : ℝ) (Ka : ℝ≥0) (a : E → E →L[ℝ] E) (u : E → ℝ),
      ‖ν‖ = 1 → 0 < ρ → 0 ≤ ⟪p, ν⟫ → IsUniformlyElliptic lam Λ a (halfBall ν p ρ) →
      IsSymmetricOn a (halfBall ν p ρ) → HolderOnWith Ka α a (halfBall ν p ρ) →
      (Ka : ℝ) * ρ ^ (α : ℝ) ≤ Kc → IsConormalSolOn ν a 0 0 p ρ u →
      eHolderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≠ ⊤ ∧
      ρ ^ (1 + (α : ℝ)) *
          holderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2)) ≤
        C * regionOsc u (halfBall ν p ρ) := by
  obtain ⟨C, hC⟩ := Div.c1Holder_halfBall_estimate E α hα hα1 lam Λ Kc hlam
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ν p ρ Ka a u hν hρ hp hell hsym ha hKa hu
  have hp' : -ρ < ⟪p, ν⟫ := by linarith
  have hG : HolderOnWith 0 α (0 : E → E) (halfBall ν p ρ) := holderOnWith_const 0 0 α _
  have hfm : AEStronglyMeasurable (0 : E → ℝ) (volume.restrict (halfBall ν p ρ)) :=
    aestronglyMeasurable_const
  constructor
  · obtain ⟨-, Cq, hq⟩ := Div.contDiffHolderOn_one_halfBall_of_isConormalSolution E α hα hα1 ν p
      ρ lam Λ Ka 0 0 a 0 0 u hν hρ hp' hlam hell hsym ha hG hfm (fun y _ ↦ by simp) hu
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
  · have h := hC ν p ρ Ka 0 0 0 a 0 0 u hν hρ hp' hell hsym ha hKa hG (fun y _ ↦ by simp) hfm
      (fun y _ ↦ by simp) hu
    simp only [NNReal.coe_zero, mul_zero, add_zero] at h
    have hpB : p ∈ halfBall ν p ρ := ⟨mem_closedBall_self hρ.le, hp⟩
    obtain ⟨c, hc⟩ := (isCompact_halfBall ν p ρ).exists_bound_of_continuousOn
      (hu.1.continuousOn)
    have hosc := regionOsc_nonneg_of_abs_le ⟨p, hpB⟩ (fun y hy ↦ (Real.norm_eq_abs _).symm.le.trans
      (hc y hy))
    have h0 : 0 ≤ ρ * ‖fderivWithin ℝ u (halfBall ν p ρ) p‖ := by positivity
    calc ρ ^ (1 + (α : ℝ)) *
          holderSeminormOn α (fderivWithin ℝ u (halfBall ν p ρ)) (halfBall ν p (ρ / 2))
        ≤ C * regionOsc u (halfBall ν p ρ) := by linarith
      _ ≤ max C 0 * regionOsc u (halfBall ν p ρ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hosc

/-- **Directional second derivatives by difference quotients** (see the module
docstring). -/
theorem exists_hasFDerivWithinAt_fderivWithin_apply {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {ν : E} (hν : ‖ν‖ = 1) {Φ : E → E} {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hΦ : ContDiffOn ℝ 1 Φ U) {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    {x : E} {r : ℝ} {w : E → ℝ} (h : IsQuasilinearConormalSolOn ν Φ x r w)
    {z : E} {ρ : ℝ} (hρ : 0 < ρ) (hz : 0 ≤ ⟪z, ν⟫) (hzr : dist z x + 4 * ρ ≤ r)
    {K : Set E} (hK : Convex ℝ K) (hKU : K ⊆ U) {Λ L : ℝ}
    (hΛ : ∀ p ∈ K, ‖fderiv ℝ Φ p‖ ≤ Λ) (hL0 : 0 ≤ L)
    (hL : ∀ a ∈ K, ∀ b ∈ K, ‖fderiv ℝ Φ a - fderiv ℝ Φ b‖ ≤ L * ‖a - b‖)
    (hgK : ∀ y ∈ halfBall ν z (4 * ρ), gradientWithin w (halfBall ν x r) y ∈ K)
    {Hw : ℝ≥0}
    (hHw : HolderOnWith Hw α (gradientWithin w (halfBall ν x r)) (halfBall ν z (4 * ρ)))
    {M : ℝ} (hM : ∀ y ∈ halfBall ν z (4 * ρ), ‖gradientWithin w (halfBall ν x r) y‖ ≤ M)
    {e : E} (he : ‖e‖ ≤ 1)
    (hcompat : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ y ∈ closedBall z (2 * ρ),
      (0 ≤ ⟪t • e + y, ν⟫ ↔ 0 ≤ ⟪y, ν⟫)) :
    ∃ g : E → E →L[ℝ] ℝ, (∀ y ∈ halfBall ν z (ρ / 4),
      HasFDerivWithinAt (fun y ↦ fderivWithin ℝ w (halfBall ν x r) y e) (g y)
        (halfBall ν z (ρ / 4)) y) ∧
      ∃ H : ℝ, 0 ≤ H ∧ ∀ y ∈ halfBall ν z (ρ / 4), ∀ y' ∈ halfBall ν z (ρ / 4),
        ‖g y - g y'‖ ≤ H * dist y y' ^ (α : ℝ) := by
  set B := halfBall ν x r with hB
  set S4 := halfBall ν z (4 * ρ) with hS4
  set B2 := halfBall ν z (2 * ρ) with hB2
  set S := halfBall ν z (ρ / 4) with hS
  set Kc : ℝ := 2 * L * Hw * ρ ^ (α : ℝ) with hKc
  set Ka : ℝ≥0 := Real.toNNReal (2 * L * Hw) with hKa
  have hKa' : (Ka : ℝ) = 2 * L * Hw := Real.coe_toNNReal _ (by positivity)
  obtain ⟨C, hC0, hCest⟩ := exists_holderSeminormOn_le_of_isConormalSolOn E hα hα1
    (Λ := Λ) (Kc := Kc) hlam
  have hzS4 : z ∈ S4 := ⟨mem_closedBall_self (by positivity), hz⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hzS4)
  have hr : 0 < r := by linarith [dist_nonneg (x := z) (y := x)]
  have hball4 : closedBall z (4 * ρ) ⊆ closedBall x r := closedBall_subset_closedBall' (by linarith)
  have hS4B : S4 ⊆ B := inter_subset_inter_left _ hball4
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hxν : -r < ⟪x, ν⟫ := by
    have h1 : |⟪z - x, ν⟫| ≤ dist z x := by
      rw [dist_eq_norm]; exact (abs_real_inner_le_norm _ _).trans (by rw [hν, mul_one])
    have h2 : ⟪z - x, ν⟫ = ⟪z, ν⟫ - ⟪x, ν⟫ := inner_sub_left _ _ _
    have := (abs_le.1 h1).2
    linarith
  have hBu := uniqueDiffOn_halfBall hν hr hxν
  have hgU : ∀ y ∈ S4, gradientWithin w B y ∈ U := fun y hy ↦ hKU (hgK y hy)
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
  -- the linear conormal problem for `u_t = w (t e + ·) - w` on `B2`
  have hlin : ∀ t ∈ Ioc (0 : ℝ) ρ, IsConormalSolOn ν
      (fun y ↦ chordCoeff Φ (gradientWithin w B (t • e + y)) (gradientWithin w B y)) 0 0 z
      (2 * ρ) (fun y ↦ w (t • e + y) - w y) := by
    intro t ht
    have h2ρ : (0 : ℝ) < 2 * ρ := by positivity
    have hz2 : -(2 * ρ) < ⟪z, ν⟫ := by linarith
    have hzv : -(2 * ρ) < ⟪t • e + z, ν⟫ := by
      have := (hcompat t ht z (mem_closedBall_self h2ρ.le)).2 hz; linarith
    have hdz : dist (t • e + z) z ≤ ρ := by
      rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht.1.le]
      nlinarith [ht.2, norm_nonneg e, ht.1]
    have hdx : dist (t • e + z) x + 2 * ρ ≤ r := by
      linarith [dist_triangle (t • e + z) z x]
    have hsub : closedBall (t • e + z) (2 * ρ) ⊆ closedBall x r :=
      closedBall_subset_closedBall' (by linarith)
    have hsub' : ball (t • e + z) (2 * ρ) ⊆ ball x r := ball_subset_ball' (by linarith)
    have h₁ := h.translate hν h2ρ hz2 hzv hsub hsub' (hcompat t ht)
    have h₂ := h.restrict hν h2ρ hz2 (closedBall_subset_closedBall' (by linarith))
      (ball_subset_ball' (by linarith))
    have hB2u := uniqueDiffOn_halfBall hν h2ρ hz2
    have hg₁ : ∀ y ∈ B2, gradientWithin (fun y ↦ w (t • e + y)) B2 y =
        gradientWithin w B (t • e + y) := fun y hy ↦
      gradientWithin_translate hν h2ρ hz2 (fun y hy ↦ hS4B (htr t ht y hy)) hwB
        (by rintro _ ⟨u, hu, rfl⟩; exact hS4B (htr t ht u hu)) hy
    have hg₂ : ∀ y ∈ B2, gradientWithin w B2 y = gradientWithin w B y := fun y hy ↦
      gradientWithin_eq_of_subset (hB2S4.trans hS4B) (hB2u y hy) (hwB y (hS4B (hB2S4 hy)))
    have hlin' := IsQuasilinearConormalSolOn.sub hν h2ρ hz2 hU hUc hΦ h₁ h₂
      (fun y hy ↦ by rw [hg₁ y hy]; exact hgU _ (htr t ht y hy))
      (fun y hy ↦ by rw [hg₂ y hy]; exact hgU _ (hB2S4 hy))
    refine hlin'.congr_coeff fun y hy ↦ ?_
    change chordCoeff Φ (gradientWithin (fun y ↦ w (t • e + y)) B2 y) (gradientWithin w B2 y) = _
    rw [hg₁ y hy, hg₂ y hy]
  -- properties of the coefficient
  set a : ℝ → E → E →L[ℝ] E := fun t y ↦
    chordCoeff Φ (gradientWithin w B (t • e + y)) (gradientWithin w B y) with ha
  have hell_a : ∀ t ∈ Ioc (0 : ℝ) ρ, IsUniformlyElliptic lam Λ (a t) B2 := fun t ht y hy ↦
    ⟨le_inner_chordCoeff hU hUc hΦ hell (hgU _ (htr t ht y hy)) (hgU _ (hB2S4 hy)),
      norm_chordCoeff_le hK hΛ (hgK _ (htr t ht y hy)) (hgK _ (hB2S4 hy))⟩
  have hsym_a : ∀ t ∈ Ioc (0 : ℝ) ρ, IsSymmetricOn (a t) B2 := fun t ht y hy ↦
    isSymmetric_chordCoeff hU hUc hΦ hsym (hgU _ (htr t ht y hy)) (hgU _ (hB2S4 hy))
  have hhol_a : ∀ t ∈ Ioc (0 : ℝ) ρ, HolderOnWith Ka α (a t) B2 := by
    intro t ht
    refine holderOnWith_of_dist_le (by positivity) fun y hy y' hy' ↦ ?_
    rw [dist_eq_norm]
    refine (norm_chordCoeff_sub_le hU hUc hΦ hK hKU hL0 hL (hgK _ (htr t ht y hy))
      (hgK _ (hB2S4 hy)) (hgK _ (htr t ht y' hy')) (hgK _ (hB2S4 hy'))).trans ?_
    have h1 : ‖gradientWithin w B (t • e + y) - gradientWithin w B (t • e + y')‖ ≤
        Hw * dist y y' ^ (α : ℝ) := by
      rw [← dist_eq_norm]
      have := hHw.dist_le (htr t ht y hy) (htr t ht y' hy')
      rwa [dist_add_left] at this
    have h2 : ‖gradientWithin w B y - gradientWithin w B y'‖ ≤ Hw * dist y y' ^ (α : ℝ) := by
      rw [← dist_eq_norm]; exact hHw.dist_le (hB2S4 hy) (hB2S4 hy')
    calc L * (‖gradientWithin w B (t • e + y) - gradientWithin w B (t • e + y')‖ +
          ‖gradientWithin w B y - gradientWithin w B y'‖)
        ≤ L * (Hw * dist y y' ^ (α : ℝ) + Hw * dist y y' ^ (α : ℝ)) := by gcongr
      _ = 2 * L * Hw * dist y y' ^ (α : ℝ) := by ring
  have hKaρ : (Ka : ℝ) * ρ ^ (α : ℝ) ≤ Kc := by rw [hKa']
  have hSz : S ⊆ halfBall ν z ρ := halfBall_mono ν z (by linarith)
  have hS_B2 : S ⊆ B2 := halfBall_mono ν z (by linarith)
  have huS : UniqueDiffOn ℝ S := uniqueDiffOn_halfBall hν (by positivity) (by linarith)
  -- the uniform Hölder bound for the derivatives of `u_t` on `S`
  have hpair : ∀ t ∈ Ioc (0 : ℝ) ρ, ∀ q ∈ S, ∀ q' ∈ S,
      ‖fderivWithin ℝ (fun y ↦ w (t • e + y) - w y) S q -
          fderivWithin ℝ (fun y ↦ w (t • e + y) - w y) S q'‖ ≤
        (C * (2 * (M * t)) / ρ ^ (1 + (α : ℝ))) * dist q q' ^ (α : ℝ) := by
    intro t ht q hq q' hq'
    set u : E → ℝ := fun y ↦ w (t • e + y) - w y with hu
    have hqz : dist q z ≤ ρ / 4 := hq.1
    have hq'z : dist q' z ≤ ρ / 4 := hq'.1
    have hBq : halfBall ν q ρ ⊆ B2 :=
      inter_subset_inter_left _ (closedBall_subset_closedBall' (by linarith))
    have hq0 : 0 ≤ ⟪q, ν⟫ := hq.2
    have hlinq := (hlin t ht).restrict_halfBall (y := q) hν hρ (by linarith)
      (closedBall_subset_closedBall' (by linarith)) (ball_subset_ball' (by linarith))
    obtain ⟨hfin, hest⟩ := hCest ν q ρ Ka (a t) u hν hρ hq.2 ((hell_a t ht).mono hBq)
      ((hsym_a t ht).mono hBq) ((hhol_a t ht).mono hBq) hKaρ hlinq
    have hqB : q ∈ halfBall ν q ρ := ⟨mem_closedBall_self hρ.le, hq.2⟩
    have hosc : regionOsc u (halfBall ν q ρ) ≤ 2 * (M * t) :=
      regionOsc_le_two_mul_of_abs_le ⟨q, hqB⟩ fun y hy ↦
        abs_translate_sub_le (convex_halfBall ν z (4 * ρ)) hS4B hwB hM ht.1.le he
          (hB2S4 (hBq hy)) (htr t ht y (hBq hy))
    have hρα : 0 < ρ ^ (1 + (α : ℝ)) := by positivity
    have hsn : holderSeminormOn α (fderivWithin ℝ u (halfBall ν q ρ)) (halfBall ν q (ρ / 2)) ≤
        C * (2 * (M * t)) / ρ ^ (1 + (α : ℝ)) := by
      rw [le_div_iff₀ hρα, mul_comm]
      exact hest.trans (mul_le_mul_of_nonneg_left hosc hC0)
    have hq'' : q' ∈ halfBall ν q (ρ / 2) :=
      ⟨by rw [mem_closedBall]; linarith [dist_triangle q' z q, dist_comm q z], hq'.2⟩
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
  set H : ℝ := C * (2 * M) / ρ ^ (1 + (α : ℝ)) with hH
  have hH0 : 0 ≤ H := by positivity
  have hHun : ∀ n, ∀ q ∈ S, ∀ q' ∈ S,
      ‖fderivWithin ℝ (un n) S q - fderivWithin ℝ (un n) S q'‖ ≤ H * dist q q' ^ (α : ℝ) := by
    intro n q hq q' hq'
    have ht := htn n
    rw [fderivWithin_const_mul (huS q hq) ((hdiffu n) q hq),
      fderivWithin_const_mul (huS q' hq') ((hdiffu n) q' hq'), ← smul_sub, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 ht.1.le)]
    calc (tn n)⁻¹ * ‖fderivWithin ℝ (fun y ↦ w (tn n • e + y) - w y) S q -
          fderivWithin ℝ (fun y ↦ w (tn n • e + y) - w y) S q'‖
        ≤ (tn n)⁻¹ * ((C * (2 * (M * tn n)) / ρ ^ (1 + (α : ℝ))) * dist q q' ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left (hpair _ ht q hq q' hq') (inv_nonneg.2 ht.1.le)
      _ = H * dist q q' ^ (α : ℝ) := by
          have : tn n ≠ 0 := ht.1.ne'
          rw [hH]; field_simp
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
    (by exact_mod_cast hα : (0 : ℝ) < α) hH0 hHun hlim
  exact ⟨g, hg, H, hH0, hgH⟩

end BasicElliptic.Div
