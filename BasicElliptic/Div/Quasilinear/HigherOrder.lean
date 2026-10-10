/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.SecondOrder
import BasicElliptic.Div.Higher.SecondOrder
import BasicElliptic.Holder.Closure
import BasicElliptic.Holder.Algebra
import BasicElliptic.Normalize.ChangeOfVariables
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `C³` up to the flat part for quasilinear conormal solutions (`k = 2`)

`Div.contDiffOn_three_halfBall_of_quasilinear_conormal`: a `C¹` quasilinear conormal solution with
`Φ ∈ C³(U)`, `DΦ` symmetric and uniformly elliptic on the open convex `U ⊇ ∇w(B⁺)`, is `C³` on
`halfBall ν x (r/2)` (in fact near every point of `ball x r ∩ halfSpace ν`). This is the `k = 2`
case of `Div.QuasilinearConormalStatement`.

## Proof

Fix `y₀ ∈ ball x r ∩ halfSpace ν`, an orthonormal basis `(b_i)` and the tangential projections
`e_i = b_i - ⟪b_i, ν⟫ ν`.

1. **`C^{2,α}` of `w`** (`Div.exists_hessian_holder_halfBall`, `k = 1`): on a small half ball
   around `y₀`, `D_B w` has an `α`-Hölder within-derivative.
2. **The coefficient** `a = DΦ(∇w)` is then `C¹` with an `α`-Hölder derivative
   `D²Φ(∇w) ∘ D²w` (`Φ ∈ C³`; `D²Φ` is Lipschitz on a compact convex neighbourhood of the
   values of `∇w`, and `∇w` is Lipschitz).
3. **The differentiated weak identity**
   (`IsQuasilinearConormalSolOn.isConormalSolOn_fderivWithin_apply`): for tangential `e`,
   `u = ∂_e w` is a linear conormal solution with coefficient `a`, no data. Proof: the
   translated identities give `∫ ⟪(V(t e + ·) - V)/t, ∇φ⟫ = 0` for `V = Φ ∘ ∇w`, and dominated
   convergence (`V` is Lipschitz) passes to `t → 0⁺`, the limit being `DV · e = a ∇u` by the
   symmetry of the within Hessian.
4. **Linear `C^{2,α}`** (`Div.exists_hessian_halfBall_of_linear`): each `∂_{e_i} w` is
   `C²` near `y₀`.
5. **Assembly** (`Div.contDiffOn_add_two_of_rows`, general order): if the tangential rows
   `∂_{e_i} w` are `C^{m+1}` and `a` is `C^m`, then the equation `Σ_j D²w(b_j, a b_j) = 0`
   (`Div.sum_hessianWithin_eq_zero`) expresses `∂_ν(∂_ν w)` as a `C^m` expression of the rows and
   `a` (`Div.hessian_apply_normal`), so `∂_ν w`, hence `D w`, is `C^{m+1}` and `w` is `C^{m+2}`.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology NNReal ContDiff

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Assembly: higher regularity from the tangential rows and the equation -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Higher regularity from the tangential rows.** On a set `S` with unique derivatives, let
`w ∈ C²(S)` have a symmetric within Hessian `H` satisfying `Σ_j H(b_j, A b_j) = 0` with `A`
symmetric, `⟪A ν, ν⟫ ≠ 0`. If the tangential rows `y ↦ D_S w(y) (b_i - ⟪b_i, ν⟫ ν)` are
`C^{m+1}` and `A` is `C^m` on `S`, then `w` is `C^{m+2}` on `S`. -/
theorem contDiffOn_add_two_of_rows {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {ν : E}
    {S : Set E} (hS : UniqueDiffOn ℝ S) {w : E → ℝ} (hw : ContDiffOn ℝ 2 w S)
    (hsymm : ∀ y ∈ S, ∀ u v, fderivWithin ℝ (fderivWithin ℝ w S) S y u v =
      fderivWithin ℝ (fderivWithin ℝ w S) S y v u)
    {A : E → E →L[ℝ] E} (hAs : ∀ y ∈ S, (A y : E →ₗ[ℝ] E).IsSymmetric)
    (hApos : ∀ y ∈ S, ⟪A y ν, ν⟫ ≠ 0)
    (heq : ∀ y ∈ S, ∑ j, fderivWithin ℝ (fderivWithin ℝ w S) S y (b j) (A y (b j)) = 0)
    {m : ℕ} (hA : ContDiffOn ℝ m A S)
    (hrows : ∀ i, ContDiffOn ℝ (m + 1 : ℕ)
      (fun y ↦ fderivWithin ℝ w S y (b i - ⟪b i, ν⟫ • ν)) S) :
    ContDiffOn ℝ (m + 2 : ℕ) w S := by
  set D := fderivWithin ℝ w S with hD
  set H := fderivWithin ℝ D S with hH
  have hD1 : ContDiffOn ℝ 1 D S := hw.fderivWithin hS (by norm_num)
  have hDd : ∀ y ∈ S, HasFDerivWithinAt D (H y) S y := fun y hy ↦
    ((hD1.differentiableOn one_ne_zero) y hy).hasFDerivWithinAt
  set e : ι → E := fun i ↦ b i - ⟪b i, ν⟫ • ν with he
  set g : ι → E → E →L[ℝ] ℝ := fun i ↦ fderivWithin ℝ (fun y ↦ D y (e i)) S with hg
  have hgm : ∀ i, ContDiffOn ℝ m (g i) S := fun i ↦
    (hrows i).fderivWithin hS (by push_cast; exact le_rfl)
  have hrowd : ∀ i, ∀ y ∈ S, HasFDerivWithinAt (fun y ↦ D y (e i))
      ((ContinuousLinearMap.apply ℝ ℝ (e i)) ∘L H y) S y := fun i y hy ↦
    (ContinuousLinearMap.apply ℝ ℝ (e i)).hasFDerivAt.comp_hasFDerivWithinAt y (hDd y hy)
  have hgi : ∀ y ∈ S, ∀ i ξ, g i y ξ = H y ξ (e i) := fun y hy i ξ ↦ by
    simp only [hg]
    rw [(hrowd i y hy).fderivWithin (hS y hy)]
    rfl
  set gν : E → E →L[ℝ] ℝ := fun y ↦ ∑ i, (g i y ν) • innerSL ℝ (b i) +
    normalHessian b ν (A y) (fun i ↦ g i y) • innerSL ℝ ν with hgν
  have hνd : ∀ y ∈ S, HasFDerivWithinAt (fun y ↦ D y ν) (gν y) S y := by
    intro y hy
    have h1 : HasFDerivWithinAt (fun y ↦ D y ν)
        ((ContinuousLinearMap.apply ℝ ℝ ν) ∘L H y) S y :=
      (ContinuousLinearMap.apply ℝ ℝ ν).hasFDerivAt.comp_hasFDerivWithinAt y (hDd y hy)
    convert h1 using 1
    ext ξ
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.apply_apply]
    rw [hessian_apply_normal b (H y) (hsymm y hy) (hAs y hy) (hApos y hy) (heq y hy)
      (hgi y hy) ξ]
    simp only [hgν, add_apply, FunLike.coe_sum,
      Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply,
      smul_eq_mul]
    have hc : ∑ i, g i y ν * ⟪b i, ξ⟫ = ∑ i, ⟪b i, ξ⟫ * g i y ν :=
      Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    rw [hc]; ring
  have hAapp : ∀ v, ContDiffOn ℝ m (fun y ↦ A y v) S := fun v ↦ hA.clm_apply contDiffOn_const
  have hgapp : ∀ i v, ContDiffOn ℝ m (fun y ↦ g i y v) S := fun i v ↦
    (hgm i).clm_apply contDiffOn_const
  have hnH : ContDiffOn ℝ m (fun y ↦ normalHessian b ν (A y) (fun i ↦ g i y)) S := by
    simp only [normalHessian, tangentialHessian]
    refine ContDiffOn.div (ContDiffOn.neg (ContDiffOn.sum fun j _ ↦ ?_))
      ((hAapp ν).inner ℝ contDiffOn_const) hApos
    refine (ContDiffOn.sum fun i _ ↦ ?_).add (((hAapp (b j)).inner ℝ contDiffOn_const).mul
      (ContDiffOn.sum fun i _ ↦ contDiffOn_const.mul (hgapp i ν)))
    exact (contDiffOn_const.inner ℝ (hAapp (b j))).mul (hgapp i (b j))
  have hgνm : ContDiffOn ℝ m gν S :=
    (ContDiffOn.sum fun i _ ↦ (hgapp i ν).smul contDiffOn_const).add
      (hnH.smul contDiffOn_const)
  have hDν : ContDiffOn ℝ (m + 1 : ℕ) (fun y ↦ D y ν) S := by
    rw [Nat.cast_succ]
    refine contDiffOn_succ_of_fderivWithin (fun y hy ↦ (hνd y hy).differentiableWithinAt)
      (by simp) ?_
    exact hgνm.congr fun y hy ↦ (hνd y hy).fderivWithin (hS y hy)
  have hDb : ∀ i, ContDiffOn ℝ (m + 1 : ℕ) (fun y ↦ D y (b i)) S := fun i ↦ by
    have : (fun y ↦ D y (b i)) = fun y ↦ D y (e i) + ⟪b i, ν⟫ * D y ν := by
      funext y
      have : b i = e i + ⟪b i, ν⟫ • ν := by simp [he]
      conv_lhs => rw [this]
      rw [map_add, map_smul, smul_eq_mul]
    rw [this]
    exact (hrows i).add (contDiffOn_const.mul hDν)
  have hDm : ContDiffOn ℝ (m + 1 : ℕ) D S := by
    have hDe : D = fun y ↦ ∑ i, D y (b i) • innerSL ℝ (b i) := by
      funext y
      ext ξ
      simp only [FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul]
      conv_lhs => rw [← b.sum_repr' ξ]
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    rw [hDe]
    exact ContDiffOn.sum fun i _ ↦ (hDb i).smul contDiffOn_const
  have e2 : ((m + 2 : ℕ) : WithTop ℕ∞) = ((m + 1 : ℕ) : WithTop ℕ∞) + 1 := by
    push_cast; ring
  rw [e2]
  exact contDiffOn_succ_of_fderivWithin (hw.differentiableOn (by norm_num)) (by simp) hDm

/-! ### The equation up to the flat part -/

/-- **The equation `tr (DΦ(∇w) D²w) = 0` at every point of a half ball** on which `w` is `C²`
(by continuity from the interior, `Div.trace_hessian_eq_zero`). -/
theorem sum_hessianWithin_eq_zero {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {z : E} (hz : 0 ≤ ⟪z, ν⟫) {ρ : ℝ}
    (hρ : 0 < ρ) (hball : closedBall z ρ ⊆ ball x r)
    (hC2 : ContDiffOn ℝ 2 w (halfBall ν z ρ)) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {y : E} (hy : y ∈ halfBall ν z ρ) :
    ∑ i, fderivWithin ℝ (fderivWithin ℝ w (halfBall ν z ρ)) (halfBall ν z ρ) y (b i)
      (fderiv ℝ Φ (gradientWithin w (halfBall ν x r) y) (b i)) = 0 := by
  set S := halfBall ν z ρ with hS
  set B := halfBall ν x r with hB
  have huS := uniqueDiffOn_halfBall hν hρ (by linarith : -ρ < ⟪z, ν⟫)
  have hSB : S ⊆ B := fun y hy ↦ ⟨ball_subset_closedBall (hball hy.1), hy.2⟩
  have hgc : ContinuousOn (gradientWithin w B) B :=
    continuousOn_gradientWithin_halfBall hν hr hx h.1
  have hHc : ContinuousOn (fderivWithin ℝ (fderivWithin ℝ w S) S) S :=
    (hC2.fderivWithin huS (by norm_num : ((1 : ℕ) : ℕ∞ω) + 1 ≤ 2)).continuousOn_fderivWithin huS
      le_rfl
  have hDΦ : ContinuousOn (fderiv ℝ Φ) U := hΦ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  set F : E → ℝ := fun y ↦ ∑ i, fderivWithin ℝ (fderivWithin ℝ w S) S y (b i)
    (fderiv ℝ Φ (gradientWithin w B y) (b i)) with hF
  have hFc : ContinuousOn F S := by
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    exact (hHc.clm_apply continuousOn_const).clm_apply
      (((hDΦ.comp (hgc.mono hSB) fun y hy ↦ hrange y (hSB hy))).clm_apply continuousOn_const)
  set Ω' := interior S with hΩ'
  have hΩ'o : IsOpen Ω' := isOpen_interior
  have hΩ'S : Ω' ⊆ S := interior_subset
  have hΩ'Ω : Ω' ⊆ ball x r ∩ openHalfSpace ν := fun y hy ↦
    ⟨hball (hΩ'S hy).1, subset_openHalfSpace_of_isOpen hν hΩ'o (hΩ'S.trans fun _ h ↦ h.2) hy⟩
  have hF0 : ∀ y ∈ Ω', F y = 0 := by
    intro y hy
    have hyx := hΩ'Ω hy
    have heq : fderivWithin ℝ w S =ᶠ[𝓝 y] fderiv ℝ w := by
      filter_upwards [hΩ'o.mem_nhds hy] with z hz
      exact fderivWithin_of_mem_nhds (mem_of_superset (hΩ'o.mem_nhds hz) hΩ'S)
    have h1 : fderivWithin ℝ (fderivWithin ℝ w S) S y = fderiv ℝ (fderiv ℝ w) y := by
      rw [fderivWithin_of_mem_nhds (mem_of_superset (hΩ'o.mem_nhds hy) hΩ'S), heq.fderiv_eq]
    have := trace_hessian_eq_zero hν hr hx hU hUc hlam hΦ hell hsym hrange h b hyx
    have h2 : gradientWithin w B y = ∇ w y := gradientWithin_halfBall_eq hyx
    simp only [hF, h1, h2]
    exact this
  have hcl : closure Ω' = S := by
    rw [hΩ', (convex_halfBall ν z ρ).closure_interior_eq_closure_of_nonempty_interior
      (interior_halfBall_nonempty hν hρ (by linarith)), (isClosed_halfBall ν z ρ).closure_eq]
  have hmem := ((hFc y hy).mono hΩ'S).mem_closure_image (by rw [hcl]; exact hy)
  have hsub : F '' Ω' ⊆ {0} := by rintro _ ⟨y, hy, rfl⟩; exact hF0 y hy
  have := closure_mono hsub hmem
  rwa [closure_singleton, mem_singleton_iff] at this

/-! ### The differentiated weak identity -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Small tangential shifts map `halfBall ν z s` into `halfBall ν z s'` (`s < s'`). -/
theorem exists_tangential_shift {ν z e : E} {s s' : ℝ} (hss' : s < s') (he : ⟪e, ν⟫ = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ, ‖t • e‖ < s' - s ∧
      ∀ y ∈ halfBall ν z s, t • e + y ∈ halfBall ν z s' := by
  refine ⟨(s' - s) / (‖e‖ + 1), div_pos (by linarith) (by positivity), fun t ht ↦ ?_⟩
  have hte : ‖t • e‖ < s' - s := by
    rw [norm_smul, Real.norm_of_nonneg ht.1.le]
    have h1 : t * (‖e‖ + 1) < s' - s := by
      have := ht.2
      rw [lt_div_iff₀ (by positivity)] at this
      exact this
    nlinarith [ht.1]
  refine ⟨hte, fun y hy ↦ ⟨?_, ?_⟩⟩
  · rw [mem_closedBall]
    have : dist (t • e + y) y = ‖t • e‖ := by rw [dist_eq_norm, add_sub_cancel_right]
    linarith [dist_triangle (t • e + y) y z, mem_closedBall.1 hy.1]
  · rw [mem_halfSpace, inner_add_left, real_inner_smul_left, he, mul_zero, zero_add]
    exact hy.2

/-- **Differentiating a weak identity along translations** (dominated convergence). Let `V` have
a within-derivative `DV` on the convex `T` bounded by `Lv`, let `t • e + S ⊆ T` for
`t ∈ (0, δ)`, and suppose `∫_S ⟪V(t e + ·) - V, Ψ⟫ = 0` for these `t`, with `Ψ` continuous on
the compact `S`. Then `∫_S ⟪DV · e, Ψ⟫ = 0`. -/
theorem setIntegral_inner_fderiv_apply_eq_zero {S T : Set E} (hST : S ⊆ T) (hSc : IsCompact S)
    (hSm : MeasurableSet S) (hTc : Convex ℝ T) {V : E → E} {DV : E → E →L[ℝ] E}
    (hVd : ∀ y ∈ T, HasFDerivWithinAt V (DV y) T y) {Lv : ℝ} (hLv : ∀ y ∈ T, ‖DV y‖ ≤ Lv)
    {e : E} {δ : ℝ} (hδ0 : 0 < δ) (htT : ∀ t ∈ Ioo 0 δ, ∀ y ∈ S, t • e + y ∈ T)
    {Ψ : E → E} (hΨ : ContinuousOn Ψ S)
    (htr : ∀ t ∈ Ioo 0 δ, ∫ y in S, ⟪V (t • e + y) - V y, Ψ y⟫ = 0) :
    ∫ y in S, ⟪DV y e, Ψ y⟫ = 0 := by
  have hVc : ContinuousOn V T := fun y hy ↦ (hVd y hy).continuousWithinAt
  have hLip : ∀ y ∈ T, ∀ y' ∈ T, ‖V y' - V y‖ ≤ Lv * ‖y' - y‖ := fun y hy y' hy' ↦
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hVd hLv hTc hy hy'
  have hVtc : ∀ t ∈ Ioo 0 δ, ContinuousOn (fun y ↦ V (t • e + y)) S := fun t ht ↦
    hVc.comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ htT t ht y hy
  set F : ℝ → E → ℝ := fun t y ↦ ⟪t⁻¹ • (V (t • e + y) - V y), Ψ y⟫ with hF
  have hF0 : ∀ t ∈ Ioo 0 δ, ∫ y in S, F t y = 0 := by
    intro t ht
    simp only [hF, real_inner_smul_left]
    rw [integral_const_mul, htr t ht, mul_zero]
  obtain ⟨Mφ, hMφ⟩ := hSc.exists_bound_of_continuousOn hΨ
  have hlim : Tendsto (fun t ↦ ∫ y in S, F t y) (𝓝[>] 0)
      (𝓝 (∫ y in S, ⟪DV y e, Ψ y⟫)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ Lv * ‖e‖ * Mφ) ?_ ?_
      (integrableOn_const hSc.measure_lt_top.ne) ?_
    · filter_upwards [Ioo_mem_nhdsGT hδ0] with t ht
      exact ContinuousOn.aestronglyMeasurable
        ((((hVtc t ht).sub (hVc.mono hST)).const_smul t⁻¹).inner hΨ) hSm
    · filter_upwards [Ioo_mem_nhdsGT hδ0] with t ht
      refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun y hy ↦ ?_)
      have h1 : ‖t⁻¹ • (V (t • e + y) - V y)‖ ≤ Lv * ‖e‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.1.le)]
        have h2 := hLip y (hST hy) (t • e + y) (htT t ht y hy)
        rw [add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht.1.le] at h2
        calc t⁻¹ * ‖V (t • e + y) - V y‖ ≤ t⁻¹ * (Lv * (t * ‖e‖)) :=
              mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 ht.1.le)
          _ = (t⁻¹ * t) * (Lv * ‖e‖) := by ring
          _ = Lv * ‖e‖ := by rw [inv_mul_cancel₀ ht.1.ne', one_mul]
      calc ‖F t y‖ ≤ ‖t⁻¹ • (V (t • e + y) - V y)‖ * ‖Ψ y‖ := norm_inner_le_norm _ _
        _ ≤ Lv * ‖e‖ * Mφ := by
          gcongr
          · exact (norm_nonneg _).trans h1
          · exact hMφ y hy
    · refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun y hy ↦ ?_)
      have hdlim : Tendsto (fun t : ℝ ↦ t • e) (𝓝[>] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds (by
          have hc : Continuous fun t : ℝ ↦ t • e := continuous_id.smul continuous_const
          simpa using hc.tendsto 0)
      have hdtop : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • e ∈ T := by
        filter_upwards [Ioo_mem_nhdsGT hδ0] with t ht
        rw [add_comm]; exact htT t ht y hy
      have hcd : Tendsto (fun t : ℝ ↦ t⁻¹ • t • e) (𝓝[>] 0) (𝓝 e) :=
        tendsto_const_nhds.congr' (by
          filter_upwards [self_mem_nhdsWithin] with t ht
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul])
      have := Filter.Tendsto.inner (𝕜 := ℝ) ((hVd y (hST hy)).lim hdlim hdtop hcd)
        (tendsto_const_nhds (x := Ψ y))
      refine this.congr' (Eventually.of_forall fun t ↦ ?_)
      simp only [hF, add_comm y]
  have hlim0 : Tendsto (fun t ↦ ∫ y in S, F t y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hδ0] with t ht
      exact (hF0 t ht).symm)
  exact tendsto_nhds_unique hlim hlim0

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The within Hessian on a half ball.** If `w` is differentiable on `B ⊇ T = halfBall ν z s'`
and `C²` on `T`, then `D = D_B w` is `C¹` on `T`, its within-derivative `H` on `T` is
symmetric, and for `S ⊆ T` with unique derivatives the within-gradient of `∂_e w = D(·) e` on `S`
is `(D(·) e)`-dual of `H(·) e`: `∇_S(∂_e w)(y) = (toDual)⁻¹ (H(y) e)`. -/
theorem hessianWithin_halfBall_data {ν z : E} {s' : ℝ} (hν : ‖ν‖ = 1) (hs' : 0 < s')
    (hz : 0 ≤ ⟪z, ν⟫) {B : Set E} {w : E → ℝ} (hTB : halfBall ν z s' ⊆ B)
    (hwB : DifferentiableOn ℝ w B) (hC2 : ContDiffOn ℝ 2 w (halfBall ν z s')) :
    ContDiffOn ℝ 1 (fderivWithin ℝ w B) (halfBall ν z s') ∧
      (∀ y ∈ halfBall ν z s', ∀ u v,
        fderivWithin ℝ (fderivWithin ℝ w B) (halfBall ν z s') y u v =
          fderivWithin ℝ (fderivWithin ℝ w B) (halfBall ν z s') y v u) ∧
      ∀ {S : Set E}, S ⊆ halfBall ν z s' → UniqueDiffOn ℝ S → ∀ e : E, ∀ y ∈ S,
        gradientWithin (fun y ↦ fderivWithin ℝ w B y e) S y =
          (InnerProductSpace.toDual ℝ E).symm
            (fderivWithin ℝ (fderivWithin ℝ w B) (halfBall ν z s') y e) := by
  set T := halfBall ν z s' with hT
  have huT := uniqueDiffOn_halfBall hν hs' (by linarith : -s' < ⟪z, ν⟫)
  set D := fderivWithin ℝ w B with hD
  have hDT : ∀ y ∈ T, fderivWithin ℝ w T y = D y := fun y hy ↦
    fderivWithin_subset hTB (huT y hy) (hwB y (hTB hy))
  have hD1 : ContDiffOn ℝ 1 D T :=
    (hC2.fderivWithin huT (by norm_num)).congr fun y hy ↦ (hDT y hy).symm
  have hHd : ∀ y ∈ T, HasFDerivWithinAt D (fderivWithin ℝ D T y) T y := fun y hy ↦
    ((hD1.differentiableOn one_ne_zero) y hy).hasFDerivWithinAt
  have hclT : closure (interior T) = T := by
    rw [(convex_halfBall ν z s').closure_interior_eq_closure_of_nonempty_interior
      (interior_halfBall_nonempty hν hs' (by linarith)), (isClosed_halfBall ν z s').closure_eq]
  have hsymm : ∀ y ∈ T, ∀ u v, fderivWithin ℝ D T y u v = fderivWithin ℝ D T y v u := by
    intro y hy u v
    have hs2 := (hC2 y hy).isSymmSndFDerivWithinAt (by simp) huT (by rw [hclT]; exact hy) hy u v
    have hc : fderivWithin ℝ (fderivWithin ℝ w T) T y = fderivWithin ℝ D T y :=
      fderivWithin_congr (fun z hz ↦ hDT z hz) (hDT y hy)
    rwa [hc] at hs2
  refine ⟨hD1, hsymm, fun {S} hST huS e y hy ↦ ?_⟩
  have hud : HasFDerivWithinAt (fun y ↦ D y e)
      ((ContinuousLinearMap.apply ℝ ℝ e) ∘L fderivWithin ℝ D T y) S y :=
    ((ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasFDerivWithinAt y
      (hHd y (hST hy))).mono hST
  rw [gradientWithin, hud.fderivWithin (huS y hy)]
  congr 1
  ext ξ
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  exact hsymm y (hST hy) ξ e

/-- **The differentiated weak identity** (step 3 of the proof). Let `w` be a quasilinear conormal
solution on `B = halfBall ν x r` (`Φ ∈ C¹(U)`, `∇w(B) ⊆ U`) which is `C²` on
`halfBall ν z s'`, `closedBall z s' ⊆ ball x r`, `⟪z, ν⟫ ≥ 0`. For a tangential direction `e`
(`⟪e, ν⟫ = 0`) and `s < s'`, the derivative `∂_e w = D_B w (·) e` is a linear conormal solution
on `halfBall ν z s` with coefficient `DΦ(∇w)` and no data:
`∫_{B_s⁺} ⟪DΦ(∇w) ∇(∂_e w), ∇φ⟫ = 0` for `φ ∈ C¹_c(ball z s)`.

Proof: with `V = Φ ∘ ∇w`, the translated identities give `∫ ⟪(V(t e + ·) - V)/t, ∇φ⟫ = 0` for
small `t > 0`; `V` is Lipschitz on the convex `halfBall ν z s'`, so dominated convergence gives
`∫ ⟪DV · e, ∇φ⟫ = 0` (`Div.setIntegral_inner_fderiv_apply_eq_zero`), and
`DV(y) e = DΦ(∇w(y)) D²w(y) e = DΦ(∇w(y)) ∇(∂_e w)(y)` by the symmetry of the within Hessian. -/
theorem IsQuasilinearConormalSolOn.isConormalSolOn_fderivWithin_apply {ν x : E} {r : ℝ}
    {Φ : E → E} {U : Set E} {w : E → ℝ} (hν : ‖ν‖ = 1) (hU : IsOpen U)
    (hΦ : ContDiffOn ℝ 1 Φ U)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {z : E} {s s' : ℝ} (hs : 0 < s)
    (hss' : s < s') (hz : 0 ≤ ⟪z, ν⟫) (hball : closedBall z s' ⊆ ball x r)
    (hC2 : ContDiffOn ℝ 2 w (halfBall ν z s')) {e : E} (he : ⟪e, ν⟫ = 0) :
    IsConormalSolOn ν (fun y ↦ fderiv ℝ Φ (gradientWithin w (halfBall ν x r) y)) 0 0 z s
      (fun y ↦ fderivWithin ℝ w (halfBall ν x r) y e) := by
  set B := halfBall ν x r with hB
  set T := halfBall ν z s' with hT
  set S := halfBall ν z s with hS
  have hs' : 0 < s' := hs.trans hss'
  have hTB : T ⊆ B := fun y hy ↦ ⟨ball_subset_closedBall (hball hy.1), hy.2⟩
  have hST : S ⊆ T := halfBall_mono ν z hss'.le
  have hSm : MeasurableSet S := measurableSet_halfBall ν z s
  have huS := uniqueDiffOn_halfBall hν hs (by linarith : -s < ⟪z, ν⟫)
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  obtain ⟨hD1, -, hgrad⟩ := hessianWithin_halfBall_data hν hs' hz hTB hwB hC2
  set D := fderivWithin ℝ w B with hD
  set H : E → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦ fderivWithin ℝ D T y with hH
  have huT := uniqueDiffOn_halfBall hν hs' (by linarith : -s' < ⟪z, ν⟫)
  have hHd : ∀ y ∈ T, HasFDerivWithinAt D (H y) T y := fun y hy ↦
    ((hD1.differentiableOn one_ne_zero) y hy).hasFDerivWithinAt
  have hHc : ContinuousOn H T := hD1.continuousOn_fderivWithin huT le_rfl
  -- the flux `V = Φ ∘ ∇w` and its derivative
  set Tc : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap with hTc
  have hTa : ∀ ℓ, Tc ℓ = (InnerProductSpace.toDual ℝ E).symm ℓ := fun _ ↦ rfl
  set gw := gradientWithin w B with hgw
  have hgwD : gw = fun y ↦ Tc (D y) := by
    funext y; rw [hgw, gradientWithin, hTa]
  have hgwd : ∀ y ∈ T, HasFDerivWithinAt gw (Tc ∘L H y) T y := fun y hy ↦ by
    rw [hgwD]; exact Tc.hasFDerivAt.comp_hasFDerivWithinAt y (hHd y hy)
  have hgU : ∀ y ∈ T, gw y ∈ U := fun y hy ↦ hrange y (hTB hy)
  have hgwc : ContinuousOn gw T := fun y hy ↦ (hgwd y hy).continuousWithinAt
  set V : E → E := fun y ↦ Φ (gw y) with hV
  set DV : E → E →L[ℝ] E := fun y ↦ fderiv ℝ Φ (gw y) ∘L (Tc ∘L H y) with hDV
  have hVd : ∀ y ∈ T, HasFDerivWithinAt V (DV y) T y := fun y hy ↦
    (((hΦ.differentiableOn one_ne_zero) _ (hgU y hy)).differentiableAt
      (hU.mem_nhds (hgU y hy))).hasFDerivAt.comp_hasFDerivWithinAt y (hgwd y hy)
  have hVc : ContinuousOn V T := hΦ.continuousOn.comp hgwc hgU
  have hDVc : ContinuousOn DV T :=
    ((hΦ.continuousOn_fderiv_of_isOpen hU le_rfl).comp hgwc hgU).clm_comp
      (continuousOn_const.clm_comp hHc)
  obtain ⟨Lv, hLv⟩ := (isCompact_halfBall ν z s').exists_bound_of_continuousOn hDVc
  -- `DV · e = DΦ(∇w) ∇(∂_e w)`
  have hkey : ∀ y ∈ S, fderiv ℝ Φ (gw y) (gradientWithin (fun y ↦ D y e) S y) = DV y e :=
    fun y hy ↦ by rw [hgrad hST huS e y hy]; rfl
  refine ⟨(hD1.clm_apply contDiffOn_const).mono hST, fun φ hφ ↦ ?_⟩
  simp only [Pi.zero_apply, inner_zero_left, integral_zero, zero_mul, add_zero]
  have hI : ∫ y in S, ⟪fderiv ℝ Φ (gw y) (gradientWithin (fun y ↦ D y e) S y), ∇ φ y⟫ =
      ∫ y in S, ⟪DV y e, ∇ φ y⟫ :=
    setIntegral_congr_fun hSm fun y hy ↦ by rw [hkey y hy]
  rw [hI]
  -- the translated identities
  have hφc : Continuous (∇ φ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ.1.continuous_fderiv one_ne_zero)
  have hz' : -s < ⟪z, ν⟫ := by linarith
  obtain ⟨δ, hδ0, hδ⟩ := exists_tangential_shift (z := z) hss' he
  have hint : ∀ {f : E → E}, ContinuousOn f S → IntegrableOn (fun y ↦ ⟪f y, ∇ φ y⟫) S :=
    fun hf ↦ (hf.inner hφc.continuousOn).integrableOn_compact (isCompact_halfBall ν z s)
  refine setIntegral_inner_fderiv_apply_eq_zero hST (isCompact_halfBall ν z s) hSm
    (convex_halfBall ν z s') hVd hLv hδ0 (fun t ht ↦ (hδ t ht).2) hφc.continuousOn
    fun t ht ↦ ?_
  have htT := (hδ t ht).2
  have hdz : dist (t • e + z) z < s' - s := by
    rw [dist_eq_norm, add_sub_cancel_right]; exact (hδ t ht).1
  have hsub : closedBall (t • e + z) s ⊆ closedBall x r :=
    (closedBall_subset_closedBall' (by linarith)).trans (hball.trans ball_subset_closedBall)
  have hsub' : ball (t • e + z) s ⊆ ball x r :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall' (by linarith))).trans hball
  have hzv : -s < ⟪t • e + z, ν⟫ := by
    rw [inner_add_left, real_inner_smul_left, he, mul_zero, zero_add]; exact hz'
  have hcompat : ∀ y ∈ closedBall z s, (0 ≤ ⟪t • e + y, ν⟫ ↔ 0 ≤ ⟪y, ν⟫) := fun y _ ↦ by
    rw [inner_add_left, real_inner_smul_left, he, mul_zero, zero_add]
  have h₁ := h.translate hν hs hz' hzv hsub hsub' hcompat
  have h₂ := h.restrict hν hs hz'
    ((closedBall_subset_closedBall hss'.le).trans (hball.trans ball_subset_closedBall))
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall hss'.le)).trans hball)
  have e₁ : ∀ y ∈ S, gradientWithin (fun y ↦ w (t • e + y)) S y = gw (t • e + y) :=
    fun y hy ↦ gradientWithin_translate hν hs hz' (S := B)
      (fun y hy ↦ hTB (htT y hy)) hwB
      (by rintro _ ⟨u, hu, rfl⟩; exact hTB (htT u hu)) hy
  have e₂ : ∀ y ∈ S, gradientWithin w S y = gw y := fun y hy ↦
    gradientWithin_eq_of_subset (hST.trans hTB) (huS y hy) (hwB y (hTB (hST hy)))
  have a₁ : ∫ y in S, ⟪V (t • e + y), ∇ φ y⟫ = 0 := by
    rw [← h₁.2 φ hφ]
    exact setIntegral_congr_fun hSm fun y hy ↦ by rw [← hS, e₁ y hy]
  have a₂ : ∫ y in S, ⟪V y, ∇ φ y⟫ = 0 := by
    rw [← h₂.2 φ hφ]
    exact setIntegral_congr_fun hSm fun y hy ↦ by rw [← hS, e₂ y hy]
  have hVtc : ContinuousOn (fun y ↦ V (t • e + y)) S :=
    hVc.comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ htT y hy
  rw [show (∫ y in S, ⟪V (t • e + y) - V y, ∇ φ y⟫) =
      (∫ y in S, ⟪V (t • e + y), ∇ φ y⟫) - ∫ y in S, ⟪V y, ∇ φ y⟫ by
    rw [← integral_sub (hint hVtc) (hint (hVc.mono hST))]
    congr 1
    funext y
    exact inner_sub_left _ _ _, a₁, a₂, sub_zero]

/-- **The differentiated weak identity, linear case.** Let `u` be a conormal solution on
`B = halfBall ν x r` of `∫ ⟪a ∇u, ∇φ⟫ = ∫ ⟪G, ∇φ⟫` with `u ∈ C²`, `a, G ∈ C¹` on
`T = halfBall ν z s'`, `closedBall z s' ⊆ ball x r`, `⟪z, ν⟫ ≥ 0`. For tangential `e` and `s < s'`,
`∂_e u = D_B u (·) e` solves on `halfBall ν z s` the conormal problem with coefficient `a` and flux
`D_T G(·) e - D_T a(·) e ∇u`. Same proof as
`IsQuasilinearConormalSolOn.isConormalSolOn_fderivWithin_apply`, with `V = a ∇u - G`. -/
theorem IsConormalSolOn.isConormalSolOn_fderivWithin_apply {ν x : E} {r : ℝ}
    {a : E → E →L[ℝ] E} {G : E → E} {u : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r)
    (hx : -r < ⟪x, ν⟫) (h : IsConormalSolOn ν a G 0 x r u) {z : E} {s s' : ℝ} (hs : 0 < s)
    (hss' : s < s') (hz : 0 ≤ ⟪z, ν⟫) (hball : closedBall z s' ⊆ ball x r)
    (hC2 : ContDiffOn ℝ 2 u (halfBall ν z s')) (ha : ContDiffOn ℝ 1 a (halfBall ν z s'))
    (hG : ContDiffOn ℝ 1 G (halfBall ν z s')) {e : E} (he : ⟪e, ν⟫ = 0) :
    IsConormalSolOn ν a (fun y ↦ fderivWithin ℝ G (halfBall ν z s') y e -
        fderivWithin ℝ a (halfBall ν z s') y e (gradientWithin u (halfBall ν x r) y)) 0 z s
      (fun y ↦ fderivWithin ℝ u (halfBall ν x r) y e) := by
  set B := halfBall ν x r with hB
  set T := halfBall ν z s' with hT
  set S := halfBall ν z s with hS
  have hs' : 0 < s' := hs.trans hss'
  have hTB : T ⊆ B := fun y hy ↦ ⟨ball_subset_closedBall (hball hy.1), hy.2⟩
  have hST : S ⊆ T := halfBall_mono ν z hss'.le
  have hSm : MeasurableSet S := measurableSet_halfBall ν z s
  have hSc : IsCompact S := isCompact_halfBall ν z s
  have huS := uniqueDiffOn_halfBall hν hs (by linarith : -s < ⟪z, ν⟫)
  have huT := uniqueDiffOn_halfBall hν hs' (by linarith : -s' < ⟪z, ν⟫)
  have huB : DifferentiableOn ℝ u B := h.1.differentiableOn one_ne_zero
  obtain ⟨hD1, -, hgrad⟩ := hessianWithin_halfBall_data hν hs' hz hTB huB hC2
  set D := fderivWithin ℝ u B with hD
  set H : E → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦ fderivWithin ℝ D T y with hH
  have hHd : ∀ y ∈ T, HasFDerivWithinAt D (H y) T y := fun y hy ↦
    ((hD1.differentiableOn one_ne_zero) y hy).hasFDerivWithinAt
  have hHc : ContinuousOn H T := hD1.continuousOn_fderivWithin huT le_rfl
  set Tc : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap with hTc
  have hTa : ∀ ℓ, Tc ℓ = (InnerProductSpace.toDual ℝ E).symm ℓ := fun _ ↦ rfl
  set gu := gradientWithin u B with hgu
  have hguD : gu = fun y ↦ Tc (D y) := by
    funext y; rw [hgu, gradientWithin, hTa]
  have hgud : ∀ y ∈ T, HasFDerivWithinAt gu (Tc ∘L H y) T y := fun y hy ↦ by
    rw [hguD]; exact Tc.hasFDerivAt.comp_hasFDerivWithinAt y (hHd y hy)
  have hguc : ContinuousOn gu T := fun y hy ↦ (hgud y hy).continuousWithinAt
  set Da := fderivWithin ℝ a T with hDa
  set DG := fderivWithin ℝ G T with hDG
  have hDad : ∀ y ∈ T, HasFDerivWithinAt a (Da y) T y := fun y hy ↦
    ((ha.differentiableOn one_ne_zero) y hy).hasFDerivWithinAt
  have hDGd : ∀ y ∈ T, HasFDerivWithinAt G (DG y) T y := fun y hy ↦
    ((hG.differentiableOn one_ne_zero) y hy).hasFDerivWithinAt
  have hDac : ContinuousOn Da T := ha.continuousOn_fderivWithin huT le_rfl
  have hDGc : ContinuousOn DG T := hG.continuousOn_fderivWithin huT le_rfl
  -- the flux `V = a ∇u - G` and its derivative
  set V : E → E := fun y ↦ a y (gu y) - G y with hV
  set DV : E → E →L[ℝ] E := fun y ↦ (a y).comp (Tc ∘L H y) +
    (ContinuousLinearMap.apply ℝ E (gu y)).comp (Da y) - DG y with hDV
  have hVd : ∀ y ∈ T, HasFDerivWithinAt V (DV y) T y := fun y hy ↦ by
    refine (((hDad y hy).clm_apply (hgud y hy)).sub (hDGd y hy)).congr_fderiv ?_
    ext ξ
    simp [hDV]
  have hVc : ContinuousOn V T := fun y hy ↦ (hVd y hy).continuousWithinAt
  have hDVc : ContinuousOn DV T :=
    ((ha.continuousOn.clm_comp (continuousOn_const.clm_comp hHc)).add
      (((ContinuousLinearMap.apply ℝ E).continuous.comp_continuousOn hguc).clm_comp
        hDac)).sub hDGc
  obtain ⟨Lv, hLv⟩ := (isCompact_halfBall ν z s').exists_bound_of_continuousOn hDVc
  set G' : E → E := fun y ↦ DG y e - Da y e (gu y) with hG'
  have hkey : ∀ y ∈ S, a y (gradientWithin (fun y ↦ D y e) S y) = DV y e + G' y := by
    intro y hy
    rw [hgrad hST huS e y hy]
    simp only [hDV, hG', sub_apply, add_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply]
    rw [hTa]
    abel
  refine ⟨(hD1.clm_apply contDiffOn_const).mono hST, fun φ hφ ↦ ?_⟩
  simp only [Pi.zero_apply, zero_mul, integral_zero, add_zero]
  have hφc : Continuous (∇ φ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ.1.continuous_fderiv one_ne_zero)
  have hint : ∀ {f : E → E}, ContinuousOn f S → IntegrableOn (fun y ↦ ⟪f y, ∇ φ y⟫) S :=
    fun hf ↦ (hf.inner hφc.continuousOn).integrableOn_compact hSc
  have hG'c : ContinuousOn G' S :=
    ((hDGc.clm_apply continuousOn_const).sub
      ((hDac.clm_apply continuousOn_const).clm_apply hguc)).mono hST
  have hDVec : ContinuousOn (fun y ↦ DV y e) S := (hDVc.clm_apply continuousOn_const).mono hST
  have hI : ∫ y in S, ⟪a y (gradientWithin (fun y ↦ D y e) S y), ∇ φ y⟫ =
      (∫ y in S, ⟪DV y e, ∇ φ y⟫) + ∫ y in S, ⟪G' y, ∇ φ y⟫ := by
    rw [← integral_add (hint hDVec) (hint hG'c)]
    refine setIntegral_congr_fun hSm fun y hy ↦ ?_
    rw [hkey y hy, inner_add_left]
  rw [hI]
  convert zero_add (∫ y in S, ⟪G' y, ∇ φ y⟫) using 2
  -- the translated identities
  have hz' : -s < ⟪z, ν⟫ := by linarith
  obtain ⟨δ, hδ0, hδ⟩ := exists_tangential_shift (z := z) hss' he
  refine setIntegral_inner_fderiv_apply_eq_zero hST hSc hSm
    (convex_halfBall ν z s') hVd hLv hδ0 (fun t ht ↦ (hδ t ht).2) hφc.continuousOn
    fun t ht ↦ ?_
  have htT := (hδ t ht).2
  have hdz : dist (t • e + z) z < s' - s := by
    rw [dist_eq_norm, add_sub_cancel_right]; exact (hδ t ht).1
  have hsub : closedBall (t • e + z) s ⊆ closedBall x r :=
    (closedBall_subset_closedBall' (by linarith)).trans (hball.trans ball_subset_closedBall)
  have hsub' : ball (t • e + z) s ⊆ ball x r :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall' (by linarith))).trans hball
  have hcompat : ∀ y ∈ closedBall z s, (0 ≤ ⟪t • e + y, ν⟫ ↔ 0 ≤ ⟪y, ν⟫) := fun y _ ↦ by
    rw [inner_add_left, real_inner_smul_left, he, mul_zero, zero_add]
  have h₁ := h.translate hν hr hx hs hz' hsub hsub' hcompat
  have h₂ := h.restrict_halfBall hν hs hz'
    ((closedBall_subset_closedBall hss'.le).trans (hball.trans ball_subset_closedBall))
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall hss'.le)).trans hball)
  have e₁ : ∀ y ∈ S, gradientWithin (fun y ↦ u (t • e + y)) S y = gu (t • e + y) :=
    fun y hy ↦ gradientWithin_translate hν hs hz' (S := B)
      (fun y hy ↦ hTB (htT y hy)) huB
      (by rintro _ ⟨v, hv, rfl⟩; exact hTB (htT v hv)) hy
  have e₂ : ∀ y ∈ S, gradientWithin u S y = gu y := fun y hy ↦
    gradientWithin_eq_of_subset (hST.trans hTB) (huS y hy) (huB y (hTB (hST hy)))
  have hshift : ∀ {f : E → E}, ContinuousOn f T → ContinuousOn (fun y ↦ f (t • e + y)) S :=
    fun hf ↦ hf.comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ htT y hy
  have hac : ContinuousOn (fun y ↦ a y (gu y)) T := ha.continuousOn.clm_apply hguc
  have i₁ := h₁.2 φ hφ
  have i₂ := h₂.2 φ hφ
  simp only [Pi.zero_apply, zero_mul, integral_zero, add_zero] at i₁ i₂
  have a₁ : ∫ y in S, ⟪a (t • e + y) (gu (t • e + y)), ∇ φ y⟫ =
      ∫ y in S, ⟪G (t • e + y), ∇ φ y⟫ := by
    rw [← i₁]
    exact setIntegral_congr_fun hSm fun y hy ↦ by rw [← hS, e₁ y hy]
  have a₂ : ∫ y in S, ⟪a y (gu y), ∇ φ y⟫ = ∫ y in S, ⟪G y, ∇ φ y⟫ := by
    rw [← i₂]
    exact setIntegral_congr_fun hSm fun y hy ↦ by rw [← hS, e₂ y hy]
  have hsplit : ∫ y in S, ⟪V (t • e + y) - V y, ∇ φ y⟫ =
      ((∫ y in S, ⟪a (t • e + y) (gu (t • e + y)), ∇ φ y⟫) -
        ∫ y in S, ⟪G (t • e + y), ∇ φ y⟫) -
      ((∫ y in S, ⟪a y (gu y), ∇ φ y⟫) - ∫ y in S, ⟪G y, ∇ φ y⟫) := by
    have hA : IntegrableOn (fun y ↦ ⟪a (t • e + y) (gu (t • e + y)), ∇ φ y⟫ -
        ⟪G (t • e + y), ∇ φ y⟫) S := (hint (hshift hac)).sub (hint (hshift hG.continuousOn))
    have hB : IntegrableOn (fun y ↦ ⟪a y (gu y), ∇ φ y⟫ - ⟪G y, ∇ φ y⟫) S :=
      (hint (hac.mono hST)).sub (hint (hG.continuousOn.mono hST))
    rw [← integral_sub (hint (hshift hac)) (hint (hshift hG.continuousOn)),
      ← integral_sub (hint (hac.mono hST)) (hint (hG.continuousOn.mono hST)),
      ← integral_sub hA hB]
    congr 1
    funext y
    simp only [hV, inner_sub_left]
  rw [hsplit, a₁, a₂, sub_self, sub_self, sub_zero]

/-! ### The coefficient `DΦ(∇w)` -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **`C^{1,α}` of a composition.** Let `S` be compact and convex with unique derivatives, and
`g` have an `α`-Hölder within-derivative `g'` on `S` (`0 < α ≤ 1`), with values in a compact
convex `K ⊆ U`, `U` open. If `Ψ ∈ C²(U)`, then `Ψ ∘ g` is `C¹` on `S` with an `α`-Hölder
within-derivative. -/
theorem contDiffOn_one_comp_and_holder {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS : UniqueDiffOn ℝ S) (hSc : IsCompact S) (hScv : Convex ℝ S) {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α ≤ 1) {g : E → E} {g' : E → E →L[ℝ] E}
    (hg : ∀ y ∈ S, HasFDerivWithinAt g (g' y) S y) (hg' : ∃ C, HolderOnWith C α g' S)
    {Ψ : E → F} {K U : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKU : K ⊆ U) (hΨ : ContDiffOn ℝ 2 Ψ U) (hgK : ∀ y ∈ S, g y ∈ K) :
    ContDiffOn ℝ 1 (fun y ↦ Ψ (g y)) S ∧
      ∃ C, HolderOnWith C α (fderivWithin ℝ (fun y ↦ Ψ (g y)) S) S := by
  have hgU : ∀ y ∈ S, g y ∈ U := fun y hy ↦ hKU (hgK y hy)
  have hΨd : ∀ p ∈ U, HasFDerivAt Ψ (fderiv ℝ Ψ p) p := fun p hp ↦
    ((hΨ.differentiableOn (by norm_num) p hp).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
  have hcd : ∀ y ∈ S, HasFDerivWithinAt (fun y ↦ Ψ (g y)) (fderiv ℝ Ψ (g y) ∘L g' y) S y :=
    fun y hy ↦ (hΨd _ (hgU y hy)).comp_hasFDerivWithinAt y (hg y hy)
  have hfd : ∀ y ∈ S, fderivWithin ℝ (fun y ↦ Ψ (g y)) S y = fderiv ℝ Ψ (g y) ∘L g' y :=
    fun y hy ↦ (hcd y hy).fderivWithin (hS y hy)
  obtain ⟨Cg, hCg⟩ := hg'
  have hg'c : ContinuousOn g' S := hCg.continuousOn hα
  have hgc : ContinuousOn g S := fun y hy ↦ (hg y hy).continuousWithinAt
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ Ψ) U := hΨ.fderiv_of_isOpen hU (by norm_num)
  have hDc : ContinuousOn (fderiv ℝ Ψ) U := hD1.continuousOn
  -- Hölder continuity of `y ↦ DΨ(g y)`
  obtain ⟨A, hA⟩ := exists_bound_of_holderOnWith hSc hα hCg
  have hglip : LipschitzOnWith A g S :=
    hScv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hg fun y hy ↦ by
      rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hA y hy
  obtain ⟨Dm, hDm⟩ := Metric.isBounded_iff.1 hSc.isBounded
  obtain ⟨L₀, hL₀⟩ := hK.exists_bound_of_continuousOn
    ((hD1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  have hDlip : LipschitzOnWith (Real.toNNReal L₀) (fderiv ℝ Ψ) K := by
    refine hKc.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun p ↦ fderiv ℝ (fderiv ℝ Ψ) p) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · exact ((hD1.differentiableOn one_ne_zero p (hKU hp)).differentiableAt
        (hU.mem_nhds (hKU hp))).hasFDerivAt.hasFDerivWithinAt
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hL₀ p hp).trans (Real.le_coe_toNNReal L₀)
  have hDm0 : 0 ≤ max Dm 0 := le_max_right _ _
  have hgH := holderOnWith_of_lipschitzOnWith hglip hα1 hDm0
    fun x hx y hy ↦ (hDm hx hy).trans (le_max_left _ _)
  have hDgH : ∃ C, HolderOnWith C α (fun y ↦ fderiv ℝ Ψ (g y)) S :=
    ⟨_, holderOnWith_comp_lipschitzOnWith hDlip hgH hgK⟩
  have hprod : ∃ C, HolderOnWith C α (fun y ↦ fderiv ℝ Ψ (g y) ∘L g' y) S := by
    simpa only [ContinuousLinearMap.compL_apply] using
      exists_holderOnWith_bilinear hSc hα (ContinuousLinearMap.compL ℝ E E F) hDgH ⟨Cg, hCg⟩
  refine ⟨?_, ?_⟩
  · have e1 : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
    rw [e1]
    refine contDiffOn_succ_of_fderivWithin (fun y hy ↦ (hcd y hy).differentiableWithinAt)
      (by simp) ?_
    refine (contDiffOn_zero.2 ?_).congr hfd
    exact ((hDc.comp hgc hgU).clm_comp hg'c)
  · obtain ⟨C, hC⟩ := hprod
    exact ⟨C, holderOnWith_iff_dist_le.2 fun p hp q hq ↦ by
      rw [hfd p hp, hfd q hq]; exact hC.dist_le hp hq⟩

/-! ### `k = 2`: `C³` up to the flat part -/

/-- **`C³` near every point of `ball x r ∩ halfSpace ν`** (`k = 2`; see the module docstring). -/
theorem exists_contDiffOn_three_halfBall {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 3 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) {y₀ : E} (hy₀ : y₀ ∈ ball x r ∩ halfSpace ν) :
    ∃ ρ > 0, ContDiffOn ℝ 3 w (halfBall ν y₀ ρ) := by
  have hΦ2 : ContDiffOn ℝ 2 Φ U := hΦ.of_le (by norm_num)
  have hΦ1 : ContDiffOn ℝ 1 Φ U := hΦ.of_le (by norm_num)
  set B := halfBall ν x r with hB
  have hy₀ν : 0 ≤ ⟪y₀, ν⟫ := hy₀.2
  have hy₀B : y₀ ∈ B := ⟨ball_subset_closedBall hy₀.1, hy₀.2⟩
  -- step 1: `C^{2,α}` of `w` near `y₀`
  obtain ⟨α, hα, hα1, ρ₀, hρ₀, hball₀, Hs, hHs, CH, hCH⟩ :=
    exists_hessian_holder_halfBall hν hr hx hU hUc hlam hΦ2 hell hsym hrange h hy₀
  set gw := gradientWithin w B with hgw
  set p₀ := gw y₀ with hp₀
  obtain ⟨κ₂, hκ₂, hκU⟩ := Metric.isOpen_iff.1 hU p₀ (hrange y₀ hy₀B)
  set κ := κ₂ / 2 with hκ
  have hKU : closedBall p₀ κ ⊆ U := (closedBall_subset_ball (by linarith)).trans hκU
  obtain ⟨η, hη, hηc⟩ := Metric.continuousWithinAt_iff.1
    ((continuousOn_gradientWithin_halfBall hν hr hx h.1) y₀ hy₀B) κ (by positivity)
  set s' := min ρ₀ (η / 2) with hs'
  have hs'0 : 0 < s' := lt_min hρ₀ (by positivity)
  set s := s' / 2 with hs
  have hs0 : 0 < s := by positivity
  set T := halfBall ν y₀ s' with hT
  set S := halfBall ν y₀ s with hS
  have hTρ : T ⊆ halfBall ν y₀ ρ₀ := halfBall_mono ν y₀ (min_le_left _ _)
  have hballT : closedBall y₀ s' ⊆ ball x r :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans hball₀
  have hTB : T ⊆ B := fun y hy ↦ ⟨ball_subset_closedBall (hballT hy.1), hy.2⟩
  have hST : S ⊆ T := halfBall_mono ν y₀ (by linarith)
  have huT := uniqueDiffOn_halfBall hν hs'0 (by linarith : -s' < ⟪y₀, ν⟫)
  have huS := uniqueDiffOn_halfBall hν hs0 (by linarith : -s < ⟪y₀, ν⟫)
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  set D := fderivWithin ℝ w B with hD
  have hC2T : ContDiffOn ℝ 2 w T :=
    contDiffOn_two_of_hasFDerivWithinAt huT (D := D)
      (fun y hy ↦ ((hwB y (hTB hy)).hasFDerivWithinAt).mono hTB)
      (fun y hy ↦ (hHs y (hTρ hy)).mono hTρ) ((hCH.continuousOn hα).mono hTρ)
  have hgK : ∀ y ∈ T, gw y ∈ closedBall p₀ κ := fun y hy ↦ by
    rw [mem_closedBall]
    have h1 : dist y y₀ ≤ s' := mem_closedBall.1 hy.1
    have h2 : s' ≤ η / 2 := min_le_right _ _
    exact (hηc (hTB hy) (by linarith)).le
  -- step 2: the coefficient `a = DΦ(∇w)` is `C^{1,α}` on `S`
  set Tc : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap with hTc
  have hgwD : gw = fun y ↦ Tc (D y) := by
    funext y; rw [hgw, gradientWithin]; rfl
  have hgwd : ∀ y ∈ S, HasFDerivWithinAt gw (Tc ∘L Hs y) S y := fun y hy ↦ by
    rw [hgwD]
    exact Tc.hasFDerivAt.comp_hasFDerivWithinAt y
      ((hHs y (hTρ (hST hy))).mono (hST.trans hTρ))
  have hg'H : ∃ C, HolderOnWith C α (fun y ↦ Tc ∘L Hs y) S := by
    simpa only [ContinuousLinearMap.compL_apply] using
      exists_holderOnWith_clm (ContinuousLinearMap.compL ℝ E (StrongDual ℝ E) E Tc)
        ⟨CH, hCH.mono (hST.trans hTρ)⟩
  have hΨ : ContDiffOn ℝ 2 (fderiv ℝ Φ) U := hΦ.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨ha1, Kda, hKda⟩ := contDiffOn_one_comp_and_holder huS (isCompact_halfBall ν y₀ s)
    (convex_halfBall ν y₀ s) hα hα1.le hgwd hg'H hU (isCompact_closedBall p₀ κ)
    (convex_closedBall p₀ κ) hKU hΨ (fun y hy ↦ hgK y (hST hy))
  set a : E → E →L[ℝ] E := fun y ↦ fderiv ℝ Φ (gw y) with ha
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall p₀ κ).exists_bound_of_continuousOn
    ((hΦ.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU)
  have hellA : IsUniformlyElliptic lam Λ a S := fun y hy ↦
    ⟨hell _ (hrange y (hTB (hST hy))), hΛ _ (hgK y (hST hy))⟩
  have hsymA : IsSymmetricOn a S := fun y hy ↦ hsym _ (hrange y (hTB (hST hy)))
  -- step 3: the tangential derivatives solve the linear problem
  set b := stdOrthonormalBasis ℝ E with hbdef
  set e : Fin (Module.finrank ℝ E) → E := fun i ↦ b i - ⟪b i, ν⟫ • ν with he
  have hetan : ∀ i, ⟪e i, ν⟫ = 0 := fun i ↦ by
    simp only [he, inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν]
    ring
  have hlin : ∀ i, IsConormalSolOn ν a 0 0 y₀ s (fun y ↦ D y (e i)) := fun i ↦
    h.isConormalSolOn_fderivWithin_apply hν hU hΦ1 hrange hs0 (by linarith) hy₀ν hballT hC2T
      (hetan i)
  -- step 4: linear `C^{2,α}`
  have hloc : ∀ i, ∃ ρ > 0, ∃ Hi : E → E →L[ℝ] E →L[ℝ] ℝ,
      (∀ y ∈ halfBall ν y₀ ρ, HasFDerivWithinAt (fderivWithin ℝ (fun y ↦ D y (e i)) S)
        (Hi y) (halfBall ν y₀ ρ) y) ∧ ∃ C : ℝ≥0, HolderOnWith C α Hi (halfBall ν y₀ ρ) :=
    fun i ↦ exists_hessian_halfBall_of_linear hα hα1 hν hs0 (by linarith) hlam hellA hsymA ha1
      hKda (G := 0) contDiff_zero_fun.contDiffOn (Kdg := 0)
      (by rw [fderivWithin_zero]; exact holderOnWith_const 0 0 α _) continuous_const
      (Kf := 0) (holderOnWith_const 0 0 α _) (hlin i) ⟨mem_ball_self hs0, hy₀ν⟩
  choose ρi hρi Hi hHi Ci hCi using hloc
  obtain ⟨ε, ⟨hεi, hεs⟩, hε⟩ := (((eventually_all.2 fun i ↦ mem_of_superset
    (Ioo_mem_nhdsGT (hρi i)) fun t ht ↦ ht.2).and (Ioo_mem_nhdsGT (half_pos hs0))).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have hε0 : 0 < ε := hε
  set S₃ := halfBall ν y₀ ε with hS₃
  have hS₃S : S₃ ⊆ S := halfBall_mono ν y₀ (by linarith [hεs.2])
  have hS₃i : ∀ i, S₃ ⊆ halfBall ν y₀ (ρi i) := fun i ↦ halfBall_mono ν y₀ (le_of_lt (hεi i))
  have hu₃ := uniqueDiffOn_halfBall hν hε0 (by linarith : -ε < ⟪y₀, ν⟫)
  have hrowC2 : ∀ i, ContDiffOn ℝ 2 (fun y ↦ D y (e i)) S₃ := fun i ↦
    contDiffOn_two_of_hasFDerivWithinAt hu₃ (D := fderivWithin ℝ (fun y ↦ D y (e i)) S)
      (fun y hy ↦ ((((hlin i).1.differentiableOn one_ne_zero) y
        (hS₃S hy)).hasFDerivWithinAt).mono hS₃S)
      (fun y hy ↦ (hHi i y (hS₃i i hy)).mono (hS₃i i))
      (((hCi i).continuousOn hα).mono (hS₃i i))
  -- step 5: assembly
  have hS₃B : S₃ ⊆ B := hS₃S.trans (hST.trans hTB)
  have hball₃ : closedBall y₀ ε ⊆ ball x r :=
    (closedBall_subset_closedBall (by linarith [hεs.2])).trans hballT
  have hC2₃ : ContDiffOn ℝ 2 w S₃ := hC2T.mono (hS₃S.trans hST)
  have hD₃ : ∀ y ∈ S₃, fderivWithin ℝ w S₃ y = D y := fun y hy ↦
    fderivWithin_subset hS₃B (hu₃ y hy) (hwB y (hS₃B hy))
  have hcl₃ : closure (interior S₃) = S₃ := by
    rw [(convex_halfBall ν y₀ ε).closure_interior_eq_closure_of_nonempty_interior
      (interior_halfBall_nonempty hν hε0 (by linarith)), (isClosed_halfBall ν y₀ ε).closure_eq]
  have hApos : ∀ y ∈ S₃, ⟪a y ν, ν⟫ ≠ 0 := fun y hy ↦ by
    have := (hellA y (hS₃S hy)).1 ν
    rw [hν] at this
    exact (by linarith : (0 : ℝ) < ⟪a y ν, ν⟫).ne'
  have hfin := contDiffOn_add_two_of_rows b hu₃ hC2₃ (A := a) (m := 1)
    (fun y hy u v ↦ (hC2₃ y hy).isSymmSndFDerivWithinAt (by simp) hu₃
      (by rw [hcl₃]; exact hy) hy u v)
    (fun y hy ↦ hsymA y (hS₃S hy)) hApos
    (fun y hy ↦ sum_hessianWithin_eq_zero hν hr hx hU hUc hlam hΦ2 hell hsym hrange h hy₀ν
      hε0 hball₃ hC2₃ b hy)
    (by exact_mod_cast ha1.mono hS₃S)
    (fun i ↦ by
      have := (hrowC2 i).congr fun y hy ↦ (show fderivWithin ℝ w S₃ y (e i) = D y (e i) by
        rw [hD₃ y hy])
      exact_mod_cast this)
  exact ⟨ε, hε0, by exact_mod_cast hfin⟩

/-- **`C³` up to the flat part for quasilinear conormal solutions** (`k = 2` of
`Div.QuasilinearConormalStatement`). -/
theorem contDiffOn_three_halfBall_of_quasilinear_conormal {ν x : E} {r : ℝ} {Φ : E → E}
    {U : Set E} {lam : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫)
    (hU : IsOpen U) (hUc : Convex ℝ U) (hlam : 0 < lam) (hΦ : ContDiffOn ℝ 3 Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) : ContDiffOn ℝ 3 w (halfBall ν x (r / 2)) := by
  intro y hy
  have hy' : y ∈ ball x r ∩ halfSpace ν :=
    ⟨mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (by linarith)), hy.2⟩
  obtain ⟨ρ, hρ, hc⟩ := exists_contDiffOn_three_halfBall hν hr hx hU hUc hlam hΦ hell hsym
    hrange h hy'
  refine (hc y ⟨mem_closedBall_self hρ.le, hy.2⟩).mono_of_mem_nhdsWithin ?_
  exact mem_of_superset (inter_mem_nhdsWithin _ (ball_mem_nhds y hρ))
    fun z hz ↦ ⟨ball_subset_closedBall hz.2, hz.1.2⟩

end BasicElliptic.Div
