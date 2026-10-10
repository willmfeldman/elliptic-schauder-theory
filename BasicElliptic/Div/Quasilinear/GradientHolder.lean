/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Div
public import BasicElliptic.Defs.Holder
public import BasicElliptic.Normalize.ChangeOfVariables
import BasicElliptic.Div.Quasilinear.FrozenDecay
import BasicElliptic.Holder.Algebra

/-!
# Hölder continuity of the gradient of a `C¹` quasilinear conormal solution

`Div.IsQuasilinearConormalSolOn.exists_holderOnWith_gradientWithin`: a `C¹` quasilinear conormal
weak solution (`∫_{B⁺} ⟪Φ(∇w), ∇φ⟫ = 0`, `Φ ∈ C¹(U)` with `DΦ` symmetric and uniformly elliptic
on the open convex `U ⊇ ∇w(B⁺)`) has a locally Hölder continuous gradient up to the flat part:
near every point of `ball x r ∩ halfSpace ν` the within-gradient is `α`-Hölder for some
`α ∈ (0, 1)`.

**Status: proved**, with `α = 1/2`.

The equation cannot simply be linearized with the coefficient
`a(y) = ∫₀¹ DΦ(p₀ + t (∇w(y) - p₀)) dt`, which is only continuous when `w` is only `C¹`, so the
`C^{1,α}` theory with Hölder coefficients (`Div/Boundary/Estimate.lean`) does not apply. The
classical proof (Giaquinta–Martinazzi, for the interior; the flat boundary via even reflection
after normalizing
`DΦ(∇w(x₀)) = 1`) is a Campanato iteration for `∇w` with a *small-oscillation* perturbation
term: with the frozen constant coefficient `a₀ = DΦ(∇w(x₀))`, `w` solves the linear conormal
problem `∫ ⟪a₀ ∇w, ∇φ⟫ = ∫ ⟪G, ∇φ⟫`, `G = a₀ ∇w - Φ(∇w)`, and
`|G(y) - G(y')| ≤ ε(ρ) |∇w(y) - ∇w(y')|` on `B_ρ(x₀)`, with `ε(ρ) → 0` by the uniform continuity
of `∇w` and of `DΦ`. The one-step harmonic-replacement comparison then gives
`ψ(σ) ≤ C ((σ/ρ)^{d+2} + ε(ρ)²) ψ(ρ) + (lower order)` for `ψ(σ) = ∫_{B_σ} |∇w - (∇w)_σ|²`, and
the iteration lemma with an `ε` term gives Campanato decay of every order `d + 2α < d + 2`.
The later steps (difference quotients, `C²` up to the flat part) use this lemma only through its
conclusion.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace
open scoped NNReal Gradient

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open ContinuousLinearMap in
/-- **Transport of a quasilinear conormal solution** under a half-space-preserving affine map
`T z = c + M z` (`c` on the flat part, `⟪M z, ν⟫ = m ⟪z, ν⟫`, `m > 0`), restricted to a half
ball `halfBall ν z R` whose closed ball is mapped into `ball x r`: `w ∘ T` solves the problem with
`Φ̃ = M⁻¹ ∘ Φ ∘ M⁻†`, and `∇(w ∘ T) = M† (∇w ∘ T)`. -/
theorem IsQuasilinearConormalSolOn.comp_affine {ν x c : E} {r : ℝ} {Φ : E → E} {w : E → ℝ}
    (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (h : IsQuasilinearConormalSolOn ν Φ x r w)
    (M : E ≃L[ℝ] E) {m : ℝ} (hm : 0 < m) (hc : ⟪c, ν⟫ = 0) (hMν : ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫)
    {z : E} {R : ℝ} (hR : 0 < R) (hz : 0 ≤ ⟪z, ν⟫)
    (hsub : closedBall z R ⊆ (fun z ↦ c + M z) ⁻¹' ball x r) :
    IsQuasilinearConormalSolOn ν (fun q ↦ M.symm (Φ (adjoint (M.symm : E →L[ℝ] E) q))) z R
        (fun z ↦ w (c + M z)) ∧
      ∀ z' ∈ halfBall ν z R, gradientWithin (fun z ↦ w (c + M z)) (halfBall ν z R) z' =
        adjoint (M : E →L[ℝ] E) (gradientWithin w (halfBall ν x r) (c + M z')) := by
  set T : E → E := fun z ↦ c + M z with hT
  set B := halfBall ν x r with hBdef
  have hB := uniqueDiffOn_halfBall hν hr hx
  have hBm := measurableSet_halfBall ν x r
  have hpre : T ⁻¹' B = T ⁻¹' closedBall x r ∩ halfSpace ν := by
    rw [hBdef, halfBall, preimage_inter, preimage_affine_halfSpace hm hc hMν]
  have hsB : halfBall ν z R ⊆ T ⁻¹' B := by
    rw [hpre]
    exact fun y hy ↦ ⟨ball_subset_closedBall (hsub hy.1), hy.2⟩
  have hzR : -R < ⟪z, ν⟫ := by linarith
  have hlin := IsWeakSolWithin.comp_affine (isQuasilinearConormalSolOn_iff.1 h) hB hBm M c
  have hgrad : ∀ z' ∈ halfBall ν z R, gradientWithin (fun z ↦ w (c + M z)) (halfBall ν z R) z' =
      adjoint (M : E →L[ℝ] E) (gradientWithin w B (c + M z')) := fun z' hz' ↦ by
    rw [gradientWithin_eq_of_subset hsB (uniqueDiffOn_halfBall hν hR hzR z' hz')
      ((hlin.1.differentiableOn one_ne_zero) z' (hsB hz'))]
    exact gradientWithin_comp_affine M c ((h.1.differentiableOn one_ne_zero) _ (hsB hz'))
      (uniqueDiffOn_preimage_affine hB M c z' (hsB hz'))
  refine ⟨⟨hlin.1.mono hsB, fun φ hφ ↦ ?_⟩, hgrad⟩
  have hres := hlin.restrict (ball_subset_closedBall.trans hsub) hsB
    (fun y hy ↦ ⟨ball_subset_closedBall hy.2, (hpre ▸ hy.1).2⟩)
    (measurableSet_preimage_affine hBm M c) (measurableSet_halfBall ν z R)
    (uniqueDiffOn_halfBall hν hR hzR)
  have key := hres.2 φ hφ
  simp only [Pi.zero_apply, zero_comp, comp_zero, zero_apply, inner_zero_left, integral_zero,
    zero_mul, add_zero] at key
  refine Eq.trans (setIntegral_congr_fun (measurableSet_halfBall ν z R) fun z' hz' ↦ ?_) key.symm
  simp only
  rw [hgrad z' hz', ← comp_apply, adjoint_symm_comp_adjoint, one_apply_eq_self]

variable (E) in
/-- **Quantitative local `C^{1,1/2}` near a gradient value** `q` at which `DΦ` is symmetric and
elliptic. There are `η, c₁ > 0` and `C₁ ≥ 0` (depending on `E`, `ν`, `Φ`, `q`, `lam`) such that:
if `w` is a quasilinear conormal solution on `halfBall ν x r`, `0 ≤ ⟪y, ν⟫`,
`closedBall y ρ ⊆ ball x r` and `‖∇w - q‖ ≤ η` on `halfBall ν y ρ`, then `∇w` is `1/2`-Hölder
on `halfBall ν y (c₁ ρ)` with constant `C₁ / √ρ`.

Proof: normalize `M⁻¹ DΦ(q) M⁻† = 1` with a half-space-preserving `M`
(`exists_halfSpace_sqrt`), transport (`IsQuasilinearConormalSolOn.comp_affine`), choose the
neighbourhood of `M† q` on which `DΦ̃` is `ε₀`-close to the identity, apply
`holderOnWith_gradientWithin_of_smallOsc`, and transport back. -/
theorem exists_holderOnWith_gradientWithin_near {ν q : E} (hν : ‖ν‖ = 1) {Φ : E → E}
    {U : Set E} (hU : IsOpen U) (hΦ : ContDiffOn ℝ 1 Φ U) (hqU : q ∈ U) {lam : ℝ}
    (hlam : 0 < lam) (hell : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ q ξ, ξ⟫)
    (hsym : (fderiv ℝ Φ q : E →ₗ[ℝ] E).IsSymmetric) :
    ∃ η > 0, ∃ c₁ > 0, ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (x : E) (r : ℝ) (w : E → ℝ) (y : E) (ρ : ℝ),
      0 < r → -r < ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x r w → 0 < ρ → 0 ≤ ⟪y, ν⟫ →
      closedBall y ρ ⊆ ball x r →
      (∀ z ∈ halfBall ν y ρ, ‖gradientWithin w (halfBall ν x r) z - q‖ ≤ η) →
      HolderOnWith (Real.toNNReal (C₁ / √ρ)) (1 / 2) (gradientWithin w (halfBall ν x r))
        (halfBall ν y (c₁ * ρ)) := by
  -- normalization `M⁻¹ DΦ(q) M⁻† = 1`, `M` preserving the half space
  obtain ⟨M, hMM, ⟨m, hm1, -, hMν⟩, -, -⟩ := exists_halfSpace_sqrt hν hlam hsym hell le_rfl
  have hm : 0 < m := (Real.sqrt_pos.2 hlam).trans_le hm1
  set A : E →L[ℝ] E := ContinuousLinearMap.adjoint (M.symm : E →L[ℝ] E) with hA
  set Φ' : E → E := fun p ↦ M.symm (Φ (A p)) with hΦ'def
  set U' := A ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage A.continuous
  have hΦ' : ContDiffOn ℝ 1 Φ' U' :=
    (M.symm : E →L[ℝ] E).contDiff.comp_contDiffOn (hΦ.comp A.contDiff.contDiffOn fun p hp ↦ hp)
  have hfd : ∀ p ∈ U', fderiv ℝ Φ' p = (M.symm : E →L[ℝ] E) ∘L fderiv ℝ Φ (A p) ∘L A :=
    fun p hp ↦ by
      have hd : HasFDerivAt Φ (fderiv ℝ Φ (A p)) (A p) :=
        (((hΦ.differentiableOn one_ne_zero) _ hp).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
      exact ((M.symm : E →L[ℝ] E).hasFDerivAt.comp p (hd.comp p A.hasFDerivAt)).fderiv
  set q' := ContinuousLinearMap.adjoint (M : E →L[ℝ] E) q with hq'
  have hAq : ∀ v, A (ContinuousLinearMap.adjoint (M : E →L[ℝ] E) v) = v := fun v ↦ by
    rw [hA, ← ContinuousLinearMap.comp_apply, adjoint_symm_comp_adjoint,
      one_apply_eq_self]
  have hq'U : q' ∈ U' := by
    change A q' ∈ U; rw [hq', hAq]; exact hqU
  have hfd1 : fderiv ℝ Φ' q' = 1 := by
    rw [hfd q' hq'U, hq', hAq]; exact symm_comp_comp_adjoint_symm_eq_one hMM
  -- the small-oscillation neighbourhood
  obtain ⟨ε₀, hε₀, C₀, hC₀, hNE⟩ := holderOnWith_gradientWithin_of_smallOsc E hν
  set ε := min ε₀ 1 with hε
  have hcont : ContinuousAt (fderiv ℝ Φ') q' :=
    (hΦ'.continuousOn_fderiv_of_isOpen hU'o le_rfl).continuousAt (hU'o.mem_nhds hq'U)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 hcont ε (lt_min hε₀ one_pos)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.isOpen_iff.1 hU'o q' hq'U
  set η' := min δ₁ δ₂ / 2 with hη'
  have hη0 : 0 < η' := by positivity
  have hηδ : ∀ p ∈ closedBall q' η', dist p q' < min δ₁ δ₂ := fun p hp ↦
    lt_of_le_of_lt (mem_closedBall.1 hp) (by rw [hη']; linarith [lt_min hδ₁ hδ₂])
  have hD : SmallOscData Φ' (ball q' δ₂) q' η' ε :=
    { isOpen := isOpen_ball
      convex := convex_ball q' δ₂
      contDiffOn := hΦ'.mono hδ₂'
      pos := hη0
      subset := fun p hp ↦ mem_ball.2 ((hηδ p hp).trans_le (min_le_right _ _))
      norm_sub_one_le := fun p hp ↦ by
        rw [← hfd1, ← dist_eq_norm]
        exact (hδ₁' ((hηδ p hp).trans_le (min_le_left _ _))).le
      le_one := min_le_right _ _ }
  set KA := ‖ContinuousLinearMap.adjoint (M : E →L[ℝ] E)‖ with hKA
  set KM := ‖(M : E →L[ℝ] E)‖ with hKM
  set KS := ‖(M.symm : E →L[ℝ] E)‖ with hKS
  have hKA0 : 0 ≤ KA := norm_nonneg _
  have hKM0 : 0 ≤ KM := norm_nonneg _
  have hKS0 : 0 ≤ KS := norm_nonneg _
  refine ⟨η' / (KA + 1), by positivity, 1 / (16 * (KM + 1) * (KS + 1)), by positivity,
    ‖A‖ * C₀ * η' * √(KM + 1) * KS ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro x r w y ρ hr hx h hρ hyν hball hnear
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
  have hrange' : ∀ z' ∈ halfBall ν z₀ R₀, gradientWithin (fun z ↦ w (c + M z))
      (halfBall ν z₀ R₀) z' ∈ closedBall q' η' := by
    intro z' hz'
    have hTy : c + M z' ∈ halfBall ν y ρ := ⟨hTρ z' hz'.1,
      by rw [mem_halfSpace, hinner]; exact mul_nonneg hm.le hz'.2⟩
    rw [hgr z' hz', mem_closedBall, dist_eq_norm, hq', ← map_sub]
    refine ((ContinuousLinearMap.adjoint (M : E →L[ℝ] E)).le_opNorm _).trans ?_
    calc KA * ‖g (c + M z') - q‖ ≤ KA * (η' / (KA + 1)) :=
          mul_le_mul_of_nonneg_left (hnear _ hTy) hKA0
      _ ≤ η' := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hH := hNE Φ' (ball q' δ₂) q' η' ε z₀ R₀ _ hD (min_le_left _ _) hR₀0 hz₀ν hsol hrange'
  set H := Real.toNNReal (C₀ * η' / √R₀) with hHdef
  -- back to the original variables
  have hpull : ∀ y' ∈ halfBall ν y (1 / (16 * (KM + 1) * (KS + 1)) * ρ),
      M.symm (y' - c) ∈ halfBall ν z₀ (R₀ / 16) ∧ c + M (M.symm (y' - c)) = y' := by
    intro y' hy'
    have hT : c + M (M.symm (y' - c)) = y' := by
      rw [ContinuousLinearEquiv.apply_symm_apply]; abel
    refine ⟨⟨?_, ?_⟩, hT⟩
    · rw [mem_closedBall, hz₀, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right]
      refine ((M.symm : E →L[ℝ] E).le_opNorm _).trans ?_
      rw [← dist_eq_norm]
      have h1 : dist y' y ≤ 1 / (16 * (KM + 1) * (KS + 1)) * ρ := mem_closedBall.1 hy'.1
      calc KS * dist y' y ≤ KS * (1 / (16 * (KM + 1) * (KS + 1)) * ρ) :=
            mul_le_mul_of_nonneg_left h1 hKS0
        _ ≤ R₀ / 16 := by
            rw [hR₀]
            have hk : KM + 1 ≠ 0 := by positivity
            have hk' : KS + 1 ≠ 0 := by positivity
            field_simp
            nlinarith
    · have h1 := hinner (M.symm (y' - c))
      rw [hT] at h1
      exact (mul_nonneg_iff_of_pos_left hm).1 (h1 ▸ hy'.2)
  have hgy : ∀ y' ∈ halfBall ν y (1 / (16 * (KM + 1) * (KS + 1)) * ρ),
      g y' = A (gradientWithin (fun z ↦ w (c + M z)) (halfBall ν z₀ R₀) (M.symm (y' - c))) :=
    fun y' hy' ↦ by
      obtain ⟨hz', hT⟩ := hpull y' hy'
      rw [hgr _ (halfBall_mono ν z₀ (by linarith) hz'), hAq, hT]
  have hHr0 : 0 ≤ ‖A‖ * C₀ * η' * √(KM + 1) * KS ^ (1 / 2 : ℝ) / √ρ := by positivity
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
  calc ‖A‖ * dist _ _ ≤ ‖A‖ * (C₀ * η' / √R₀ *
        dist (M.symm (y₁ - c)) (M.symm (y₂ - c)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hH' (norm_nonneg _)
    _ ≤ ‖A‖ * (C₀ * η' / √R₀ * (KS * dist y₁ y₂) ^ (1 / 2 : ℝ)) := by gcongr
    _ = ‖A‖ * C₀ * η' * √(KM + 1) * KS ^ (1 / 2 : ℝ) / √ρ * dist y₁ y₂ ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow hKS0 dist_nonneg, hR₀s]
        have : 0 < √ρ := Real.sqrt_pos.2 hρ
        have : 0 < √(KM + 1) := Real.sqrt_pos.2 (by positivity)
        field_simp

/-- **Local `C^{1,α}` of `C¹` quasilinear conormal solutions** (see the module docstring),
with `α = 1/2`. -/
theorem IsQuasilinearConormalSolOn.exists_holderOnWith_gradientWithin {ν x : E} {r : ℝ}
    {Φ : E → E} {U : Set E} {lam : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r)
    (hx : -r < ⟪x, ν⟫) (hU : IsOpen U) (_hUc : Convex ℝ U) (hlam : 0 < lam)
    (hΦ : ContDiffOn ℝ 1 Φ U) (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {y : E} (hy : y ∈ ball x r ∩ halfSpace ν) :
    ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧ ∃ δ > 0, ∃ H : ℝ≥0,
      HolderOnWith H α (gradientWithin w (halfBall ν x r)) (halfBall ν y δ) := by
  set B := halfBall ν x r with hBdef
  set g := gradientWithin w B with hg
  have hyB : y ∈ B := ⟨ball_subset_closedBall hy.1, hy.2⟩
  have hgc : ContinuousOn g B := continuousOn_gradientWithin_halfBall hν hr hx h.1
  obtain ⟨η, hη, c₁, hc₁, C₁, -, hGL⟩ := exists_holderOnWith_gradientWithin_near E hν hU hΦ
    (hrange y hyB) hlam (hell _ (hrange y hyB)) (hsym _ (hrange y hyB))
  obtain ⟨δ₃, hδ₃, hδ₃'⟩ := Metric.continuousWithinAt_iff.1 (hgc y hyB) η hη
  have hrx : 0 < r - dist y x := sub_pos.2 (mem_ball.1 hy.1)
  set ρ := min (δ₃ / 2) ((r - dist y x) / 2) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have hball : closedBall y ρ ⊆ ball x r := fun z hz ↦ by
    rw [mem_ball]; rw [mem_closedBall] at hz
    linarith [dist_triangle z y x, min_le_right (δ₃ / 2) ((r - dist y x) / 2)]
  refine ⟨1 / 2, by norm_num, by norm_num, c₁ * ρ, by positivity, _,
    hGL x r w y ρ hr hx h hρ0 hy.2 hball fun z hz ↦ ?_⟩
  rw [← dist_eq_norm]
  refine (hδ₃' ⟨hball hz.1 |> ball_subset_closedBall, hz.2⟩ ?_).le
  exact (mem_closedBall.1 hz.1).trans_lt (by linarith [min_le_left (δ₃ / 2) ((r - dist y x) / 2)])

end BasicElliptic.Div
