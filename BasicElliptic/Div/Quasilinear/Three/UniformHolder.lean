/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.GradientHolder
import BasicElliptic.Div.Quasilinear.FrozenDecay
import BasicElliptic.Holder.Algebra

/-!
# The a priori `C^{1,1/2}` bound with explicit constants

`Div.exists_holderOnWith_gradientWithin_unif` is `Div.exists_holderOnWith_gradientWithin_near`
at `q = 0` with the constants depending only on `E`, `ν`, `lam`, a bound `Λ` on `‖DΦ(0)‖`, a
Lipschitz constant `L` of `DΦ` at `0` and the radius `δ` of the ball on which `Φ` is given. The
proof is the same; the neighbourhood on which the normalized `DΦ` is close to the identity is
chosen from `L` instead of from the continuity of `DΦ`.
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace
open scoped NNReal Gradient

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open ContinuousLinearMap in
variable (E) in
/-- **Quantitative local `C^{1,1/2}` near the gradient value `0`, uniform in `Φ`.** There are
`η, c₁ > 0` and `C₁ ≥ 0`, depending only on `E`, `ν`, `lam`, `Λ`, `L` and `δ`, such that for every
`Φ ∈ C¹(ball 0 δ)` with `DΦ(0)` symmetric, `lam`-elliptic, `‖DΦ(0)‖ ≤ Λ` and
`‖DΦ(p) - DΦ(0)‖ ≤ L ‖p‖` on `ball 0 δ`: if `w` is a quasilinear conormal solution on
`halfBall ν x r`, `0 ≤ ⟪y, ν⟫`, `closedBall y ρ ⊆ ball x r` and `‖∇w‖ ≤ η` on `halfBall ν y ρ`,
then `∇w` is `1/2`-Hölder on `halfBall ν y (c₁ ρ)` with constant `C₁ / √ρ`. -/
theorem exists_holderOnWith_gradientWithin_unif {ν : E} (hν : ‖ν‖ = 1) {lam Λ L δ : ℝ}
    (hlam : 0 < lam) (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∃ η > 0, ∃ c₁ > 0, ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (Φ : E → E), ContDiffOn ℝ 1 Φ (ball 0 δ) →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ 0 ξ, ξ⟫) →
      (fderiv ℝ Φ 0 : E →ₗ[ℝ] E).IsSymmetric → ‖fderiv ℝ Φ 0‖ ≤ Λ →
      (∀ p ∈ ball (0 : E) δ, ‖fderiv ℝ Φ p - fderiv ℝ Φ 0‖ ≤ L * ‖p‖) →
      ∀ (x : E) (r : ℝ) (w : E → ℝ) (y : E) (ρ : ℝ),
      0 < r → -r < ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x r w → 0 < ρ → 0 ≤ ⟪y, ν⟫ →
      closedBall y ρ ⊆ ball x r →
      (∀ z ∈ halfBall ν y ρ, ‖gradientWithin w (halfBall ν x r) z‖ ≤ η) →
      HolderOnWith (Real.toNNReal (C₁ / √ρ)) (1 / 2) (gradientWithin w (halfBall ν x r))
        (halfBall ν y (c₁ * ρ)) := by
  obtain ⟨ε₀, hε₀, C₀, hC₀, hNE⟩ := holderOnWith_gradientWithin_of_smallOsc E hν
  set ε := min ε₀ 1 with hε
  have hε0 : 0 < ε := lt_min hε₀ one_pos
  set s := 1 / √lam with hs
  have hs0 : 0 < s := by positivity
  set lΛ := √Λ with hlΛ
  have hlΛ0 : 0 ≤ lΛ := Real.sqrt_nonneg _
  set δ' := δ / (s + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  set η' := min (δ' / 2) (ε / (s ^ 3 * L + 1)) with hη'
  have hη'0 : 0 < η' := lt_min (by positivity) (by positivity)
  refine ⟨η' / (lΛ + 1), by positivity, 1 / (16 * (lΛ + 1) * (s + 1)), by positivity,
    s * C₀ * η' * √(lΛ + 1) * s ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro Φ hΦ hell hsym hbd hLip x r w y ρ hr hx h hρ hyν hball hnear
  -- normalization `M⁻¹ DΦ(0) M⁻† = 1`, `M` preserving the half space
  obtain ⟨M, hMM, ⟨m, hm1, -, hMν⟩, hMn, hMsn⟩ := exists_halfSpace_sqrt hν hlam hsym hell hbd
  have hm : 0 < m := (Real.sqrt_pos.2 hlam).trans_le hm1
  set A : E →L[ℝ] E := ContinuousLinearMap.adjoint (M.symm : E →L[ℝ] E) with hA
  set Φ' : E → E := fun p ↦ M.symm (Φ (A p)) with hΦ'def
  set KA := ‖ContinuousLinearMap.adjoint (M : E →L[ℝ] E)‖ with hKA
  set KM := ‖(M : E →L[ℝ] E)‖ with hKM
  set KS := ‖(M.symm : E →L[ℝ] E)‖ with hKS
  have hKA0 : 0 ≤ KA := norm_nonneg _
  have hKM0 : 0 ≤ KM := norm_nonneg _
  have hKS0 : 0 ≤ KS := norm_nonneg _
  have hKAe : KA = KM := by rw [hKA, hKM, LinearIsometryEquiv.norm_map]
  have hAn : ‖A‖ = KS := by rw [hA, hKS, LinearIsometryEquiv.norm_map]
  have hKMb : KM ≤ lΛ := hMn
  have hKSb : KS ≤ s := by rw [hKS, hs]; exact hMsn
  have hKAb : KA ≤ lΛ := hKAe ▸ hKMb
  have hAb : ‖A‖ ≤ s := hAn ▸ hKSb
  -- `A` maps `ball 0 δ'` into `ball 0 δ`
  have hAball : ∀ p ∈ ball (0 : E) δ', A p ∈ ball (0 : E) δ := fun p hp ↦ by
    rw [mem_ball_zero_iff] at hp ⊢
    calc ‖A p‖ ≤ s * ‖p‖ := (A.le_opNorm p).trans (mul_le_mul_of_nonneg_right hAb (norm_nonneg _))
      _ ≤ s * δ' := mul_le_mul_of_nonneg_left hp.le hs0.le
      _ < δ := by
          rw [hδ', mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  set U' := ball (0 : E) δ' with hU'
  have hU'o : IsOpen U' := isOpen_ball
  have hΦ' : ContDiffOn ℝ 1 Φ' U' :=
    (M.symm : E →L[ℝ] E).contDiff.comp_contDiffOn (hΦ.comp A.contDiff.contDiffOn hAball)
  have hfd : ∀ p ∈ U', fderiv ℝ Φ' p = (M.symm : E →L[ℝ] E) ∘L fderiv ℝ Φ (A p) ∘L A :=
    fun p hp ↦ by
      have hd : HasFDerivAt Φ (fderiv ℝ Φ (A p)) (A p) :=
        (((hΦ.differentiableOn one_ne_zero) _ (hAball p hp)).differentiableAt
          (isOpen_ball.mem_nhds (hAball p hp))).hasFDerivAt
      exact ((M.symm : E →L[ℝ] E).hasFDerivAt.comp p (hd.comp p A.hasFDerivAt)).fderiv
  have hAq : ∀ v, A (ContinuousLinearMap.adjoint (M : E →L[ℝ] E) v) = v := fun v ↦ by
    rw [hA, ← ContinuousLinearMap.comp_apply, adjoint_symm_comp_adjoint,
      one_apply_eq_self]
  have h0U' : (0 : E) ∈ U' := mem_ball_self hδ'0
  have hfd1 : fderiv ℝ Φ' 0 = 1 := by
    rw [hfd 0 h0U', map_zero]; exact symm_comp_comp_adjoint_symm_eq_one hMM
  -- `DΦ'` is close to the identity on `closedBall 0 η'`
  have hη'δ' : η' < δ' := (min_le_left _ _).trans_lt (by linarith)
  have hcb : closedBall (0 : E) η' ⊆ U' := closedBall_subset_ball hη'δ'
  have hclose : ∀ p ∈ closedBall (0 : E) η', ‖fderiv ℝ Φ' p - 1‖ ≤ ε := fun p hp ↦ by
    have hpU := hcb hp
    have hp' : ‖p‖ ≤ η' := mem_closedBall_zero_iff.1 hp
    rw [← hfd1, hfd p hpU, hfd 0 h0U', map_zero, ← ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.sub_comp]
    have hAp : ‖A p‖ ≤ s * ‖p‖ :=
      (A.le_opNorm p).trans (mul_le_mul_of_nonneg_right hAb (norm_nonneg _))
    have hl := hLip (A p) (hAball p hpU)
    calc ‖(M.symm : E →L[ℝ] E) ∘L (fderiv ℝ Φ (A p) - fderiv ℝ Φ 0) ∘L A‖
        ≤ KS * (‖fderiv ℝ Φ (A p) - fderiv ℝ Φ 0‖ * ‖A‖) :=
          (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) hKS0)
      _ ≤ s * ((L * (s * ‖p‖)) * s) := by
          gcongr
          exact hl.trans (mul_le_mul_of_nonneg_left hAp hL)
      _ = s ^ 3 * L * ‖p‖ := by ring
      _ ≤ s ^ 3 * L * η' := by gcongr
      _ ≤ (s ^ 3 * L + 1) * (ε / (s ^ 3 * L + 1)) := by
          gcongr
          · linarith
          · exact min_le_right _ _
      _ = ε := by field_simp
  have hD : SmallOscData Φ' U' 0 η' ε :=
    { isOpen := hU'o
      convex := convex_ball _ _
      contDiffOn := hΦ'
      pos := hη'0
      subset := hcb
      norm_sub_one_le := hclose
      le_one := min_le_right _ _ }
  set B := halfBall ν x r with hBdef
  set g := gradientWithin w B with hg
  -- the affine map `T z = c + M z`, `c` the foot point of `y`
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  set c := y - ⟪y, ν⟫ • ν with hc
  have hcν : ⟪c, ν⟫ = 0 := by
    rw [hc, inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]
  have hinner : ∀ z, ⟪c + M z, ν⟫ = m * ⟪z, ν⟫ := inner_affine_eq hcν hMν
  set z₀ := M.symm (y - c) with hz₀
  have hTz₀ : c + M z₀ = y := by rw [hz₀, ContinuousLinearEquiv.apply_symm_apply]; abel
  have hz₀ν : 0 ≤ ⟪z₀, ν⟫ := by
    have h1 := hinner z₀
    rw [hTz₀] at h1
    exact (mul_nonneg_iff_of_pos_left hm).1 (h1 ▸ hyν)
  set R₀ := ρ / (KM + 1) with hR₀
  have hR₀0 : 0 < R₀ := by positivity
  have hKMR : KM * R₀ ≤ ρ := by
    rw [hR₀, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hdistM : ∀ z, dist (c + M z) y ≤ KM * dist z z₀ := fun z ↦ by
    rw [← hTz₀, dist_add_left, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (M : E →L[ℝ] E).le_opNorm _
  have hTρ : ∀ z ∈ closedBall z₀ R₀, c + M z ∈ closedBall y ρ := fun z hz ↦
    mem_closedBall.2 ((hdistM z).trans ((mul_le_mul_of_nonneg_left (mem_closedBall.1 hz)
      hKM0).trans hKMR))
  have hsub : closedBall z₀ R₀ ⊆ (fun z ↦ c + M z) ⁻¹' ball x r := fun z hz ↦
    hball (hTρ z hz)
  obtain ⟨hsol, hgr⟩ := h.comp_affine hν hr hx M hm hcν hMν hR₀0 hz₀ν hsub
  have hsol' : IsQuasilinearConormalSolOn ν Φ' z₀ R₀ (fun z ↦ w (c + M z)) := hsol
  have hrange' : ∀ z' ∈ halfBall ν z₀ R₀, gradientWithin (fun z ↦ w (c + M z))
      (halfBall ν z₀ R₀) z' ∈ closedBall (0 : E) η' := by
    intro z' hz'
    have hTy : c + M z' ∈ halfBall ν y ρ := ⟨hTρ z' hz'.1,
      by rw [mem_halfSpace, hinner]; exact mul_nonneg hm.le hz'.2⟩
    rw [hgr z' hz', mem_closedBall_zero_iff]
    refine ((ContinuousLinearMap.adjoint (M : E →L[ℝ] E)).le_opNorm _).trans ?_
    calc KA * ‖g (c + M z')‖ ≤ lΛ * (η' / (lΛ + 1)) :=
          mul_le_mul hKAb (hnear _ hTy) (norm_nonneg _) hlΛ0
      _ ≤ η' := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hH := hNE Φ' U' 0 η' ε z₀ R₀ _ hD (min_le_left _ _) hR₀0 hz₀ν hsol' hrange'
  set H := Real.toNNReal (C₀ * η' / √R₀) with hHdef
  -- back to the original variables
  set c₁ := 1 / (16 * (lΛ + 1) * (s + 1)) with hc₁
  have hpull : ∀ y' ∈ halfBall ν y (c₁ * ρ),
      M.symm (y' - c) ∈ halfBall ν z₀ (R₀ / 16) ∧ c + M (M.symm (y' - c)) = y' := by
    intro y' hy'
    have hT : c + M (M.symm (y' - c)) = y' := by
      rw [ContinuousLinearEquiv.apply_symm_apply]; abel
    refine ⟨⟨?_, ?_⟩, hT⟩
    · rw [mem_closedBall, hz₀, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right]
      refine ((M.symm : E →L[ℝ] E).le_opNorm _).trans ?_
      rw [← dist_eq_norm]
      have h1 : dist y' y ≤ c₁ * ρ := mem_closedBall.1 hy'.1
      calc KS * dist y' y ≤ (s + 1) * (c₁ * ρ) :=
            mul_le_mul (by linarith) h1 dist_nonneg (by positivity)
        _ = ρ / (16 * (lΛ + 1)) := by rw [hc₁]; field_simp
        _ ≤ R₀ / 16 := by
            rw [hR₀, div_div, div_le_div_iff_of_pos_left hρ (by positivity) (by positivity)]
            linarith
    · have h1 := hinner (M.symm (y' - c))
      rw [hT] at h1
      exact (mul_nonneg_iff_of_pos_left hm).1 (h1 ▸ hy'.2)
  have hgy : ∀ y' ∈ halfBall ν y (c₁ * ρ),
      g y' = A (gradientWithin (fun z ↦ w (c + M z)) (halfBall ν z₀ R₀) (M.symm (y' - c))) :=
    fun y' hy' ↦ by
      obtain ⟨hz', hT⟩ := hpull y' hy'
      rw [hgr _ (halfBall_mono ν z₀ (by linarith) hz'), hAq, hT]
  have hHr0 : 0 ≤ s * C₀ * η' * √(lΛ + 1) * s ^ (1 / 2 : ℝ) / √ρ := by positivity
  refine holderOnWith_iff_dist_le.2 fun y₁ hy₁ y₂ hy₂ ↦ ?_
  have hhalf : (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 := by norm_num
  have hH' := (holderOnWith_iff_dist_le.1 hH) _ (hpull y₁ hy₁).1 _ (hpull y₂ hy₂).1
  rw [hhalf] at hH' ⊢
  rw [hgy y₁ hy₁, hgy y₂ hy₂, dist_eq_norm, ← map_sub, Real.coe_toNNReal _ hHr0]
  refine (A.le_opNorm _).trans ?_
  rw [← dist_eq_norm]
  have hz : dist (M.symm (y₁ - c)) (M.symm (y₂ - c)) ≤ KS * dist y₁ y₂ := by
    rw [dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right, dist_eq_norm]
    exact (M.symm : E →L[ℝ] E).le_opNorm _
  have hHv : (H : ℝ) = C₀ * η' / √R₀ := Real.coe_toNNReal _ (by positivity)
  rw [hHv] at hH'
  have hR₀s : √R₀ = √ρ / √(KM + 1) := by rw [hR₀, Real.sqrt_div' _ (by positivity)]
  have hsρ : 0 < √ρ := Real.sqrt_pos.2 hρ
  calc ‖A‖ * dist _ _ ≤ ‖A‖ * (C₀ * η' / √R₀ *
        dist (M.symm (y₁ - c)) (M.symm (y₂ - c)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hH' (norm_nonneg _)
    _ ≤ ‖A‖ * (C₀ * η' / √R₀ * (KS * dist y₁ y₂) ^ (1 / 2 : ℝ)) := by gcongr
    _ = ‖A‖ * C₀ * η' * √(KM + 1) * KS ^ (1 / 2 : ℝ) / √ρ * dist y₁ y₂ ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow hKS0 dist_nonneg, hR₀s]
        have : 0 < √(KM + 1) := Real.sqrt_pos.2 (by positivity)
        field_simp
    _ ≤ s * C₀ * η' * √(lΛ + 1) * s ^ (1 / 2 : ℝ) / √ρ * dist y₁ y₂ ^ (1 / 2 : ℝ) := by
        gcongr

end BasicElliptic.Div
