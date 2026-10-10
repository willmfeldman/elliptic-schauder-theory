/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Directional
public import BasicElliptic.Holder.Closure
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Tangential difference quotients of linear conormal solutions

Let `w` be a conormal solution of `-div (a ∇w - G) = f` on `B = halfBall ν x r`, and let `e ⊥ ν`.
For `t` small, `u_t = w (t e + ·) - w` is a conormal solution, on a smaller half ball, of the
problem with the **same** coefficient `a`, no right-hand side, and the flux

`G̃_t = G (t e + ·) - G - (a (t e + ·) - a) ∇w (t e + ·) - P_t e`,
`P_t (y) = ∫₀ᵗ f (σ e + y) dσ`

(`Div.IsConormalSolOn.translate_sub`). The last term moves the difference quotient of `f`, which is
not bounded uniformly in `t` when `f` is only `C^α`, onto the test function: since `e` is
tangential, `∂_e P_t = f (t e + ·) - f` and the half space is invariant along `e`, so
`∫_{B⁺} (f (t e + ·) - f) φ = -∫_{B⁺} P_t ∂_e φ` (`Div.setIntegral_halfBall_translate_sub_mul`,
integration by parts along lines in direction `e`, against `1_H φ`). This is the usual way a
`C^α` right-hand side enters the difference-quotient argument (GT, GM).

The flux is `O(t)` in `C^α` (`Div.norm_translate_sub_sub_le`, `Div.abs_primitive_sub_le`), which
is what the uniform estimate needs.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001. (GT)
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012. (GM)
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology NNReal Interval

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Elementary operations on conormal solutions -/

/-- Conormal solutions only see their data on the half ball. -/
theorem IsConormalSolOn.congr_data {ν : E} {a a' : E → E →L[ℝ] E} {G G' : E → E}
    {f f' : E → ℝ} {x : E} {r : ℝ} {w : E → ℝ} (h : IsConormalSolOn ν a G f x r w)
    (ha : EqOn a a' (halfBall ν x r)) (hG : EqOn G G' (halfBall ν x r))
    (hf : EqOn f f' (halfBall ν x r)) : IsConormalSolOn ν a' G' f' x r w := by
  refine ⟨h.1, fun φ hφ ↦ ?_⟩
  have key := h.2 φ hφ
  have hm := measurableSet_halfBall ν x r
  set B := halfBall ν x r
  have e1 : ∫ y in B, ⟪a' y (gradientWithin w B y), ∇ φ y⟫ =
      ∫ y in B, ⟪a y (gradientWithin w B y), ∇ φ y⟫ :=
    setIntegral_congr_fun hm fun y hy ↦ by rw [ha hy]
  have e2 : ∫ y in B, ⟪G' y, ∇ φ y⟫ = ∫ y in B, ⟪G y, ∇ φ y⟫ :=
    setIntegral_congr_fun hm fun y hy ↦ by rw [hG hy]
  have e3 : ∫ y in B, f' y * φ y = ∫ y in B, f y * φ y :=
    setIntegral_congr_fun hm fun y hy ↦ by rw [hf hy]
  change ∫ y in B, ⟪a' y (gradientWithin w B y), ∇ φ y⟫ =
    (∫ y in B, ⟪G' y, ∇ φ y⟫) + ∫ y in B, f' y * φ y
  rw [e1, e2, e3]
  exact key

/-- **Translation of a linear conormal solution** by a vector `v` preserving the half space on
`closedBall z s`: `w (v + ·)` solves the translated problem on `halfBall ν z s`. -/
theorem IsConormalSolOn.translate {ν : E} {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ}
    {x : E} {r : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (h : IsConormalSolOn ν a G f x r w)
    (hr : 0 < r) (hx : -r < ⟪x, ν⟫) {z v : E} {s : ℝ} (hs : 0 < s) (hz : -s < ⟪z, ν⟫)
    (hsub : closedBall (v + z) s ⊆ closedBall x r) (hsub' : ball (v + z) s ⊆ ball x r)
    (hcompat : ∀ y ∈ closedBall z s, (0 ≤ ⟪v + y, ν⟫ ↔ 0 ≤ ⟪y, ν⟫)) :
    IsConormalSolOn ν (fun y ↦ a (v + y)) (fun y ↦ G (v + y)) (fun y ↦ f (v + y)) z s
      (fun y ↦ w (v + y)) := by
  have hdist : ∀ y, dist (v + y) (v + z) = dist y z := fun y ↦ by
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub]
  have h1 := IsWeakSolWithin.comp_affine h (uniqueDiffOn_halfBall hν hr hx)
    (measurableSet_halfBall ν x r) (ContinuousLinearEquiv.refl ℝ E) v
  have h2 := h1.restrict (U' := ball z s) (s' := halfBall ν z s)
    (fun y hy ↦ by
      simp only [mem_preimage, ContinuousLinearEquiv.coe_refl', id]
      exact hsub' (by rw [mem_ball, hdist]; exact hy))
    (fun y hy ↦ by
      simp only [mem_preimage, ContinuousLinearEquiv.coe_refl', id]
      refine ⟨hsub (by rw [mem_closedBall, hdist]; exact hy.1), ?_⟩
      exact (hcompat y hy.1).2 hy.2)
    (fun y hy ↦ by
      simp only [ContinuousLinearEquiv.coe_refl', id] at hy
      exact ⟨ball_subset_closedBall hy.2, (hcompat y (ball_subset_closedBall hy.2)).1 hy.1.2⟩)
    (measurableSet_preimage_affine (measurableSet_halfBall ν x r) _ v)
    (measurableSet_halfBall ν z s) (uniqueDiffOn_halfBall hν hs hz)
  unfold IsConormalSolOn
  simpa [ContinuousLinearMap.adjoint_id] using h2

omit [FiniteDimensional ℝ E] in
private theorem integrableOn_inner_of_continuousOn [FiniteDimensional ℝ E] {ν z : E} {s : ℝ}
    {V : E → E} (hV : ContinuousOn V (halfBall ν z s)) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) :
    IntegrableOn (fun y ↦ ⟪V y, ∇ φ y⟫) (halfBall ν z s) := by
  have hφc : Continuous (∇ φ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  exact ContinuousOn.integrableOn_compact (isCompact_halfBall ν z s) (hV.inner hφc.continuousOn)

/-- **Difference of two conormal solutions** on the same half ball, with the coefficient of the
second: `w₁ - w₂` solves the problem with coefficient `a₂`, flux
`G₁ - G₂ - (a₁ - a₂) ∇w₁` and right-hand side `f₁ - f₂`. -/
theorem IsConormalSolOn.sub_of_continuousOn {ν z : E} {s : ℝ} {a₁ a₂ : E → E →L[ℝ] E}
    {G₁ G₂ : E → E} {f₁ f₂ : E → ℝ} {w₁ w₂ : E → ℝ} (hν : ‖ν‖ = 1) (hs : 0 < s)
    (hz : -s < ⟪z, ν⟫) (h₁ : IsConormalSolOn ν a₁ G₁ f₁ z s w₁)
    (h₂ : IsConormalSolOn ν a₂ G₂ f₂ z s w₂) (ha₁ : ContinuousOn a₁ (halfBall ν z s))
    (ha₂ : ContinuousOn a₂ (halfBall ν z s)) (hG₁ : ContinuousOn G₁ (halfBall ν z s))
    (hG₂ : ContinuousOn G₂ (halfBall ν z s)) (hf₁ : IntegrableOn f₁ (halfBall ν z s))
    (hf₂ : IntegrableOn f₂ (halfBall ν z s)) :
    IsConormalSolOn ν a₂
      (fun y ↦ G₁ y - G₂ y - (a₁ y - a₂ y) (gradientWithin w₁ (halfBall ν z s) y))
      (fun y ↦ f₁ y - f₂ y) z s (fun y ↦ w₁ y - w₂ y) := by
  set B := halfBall ν z s with hB
  have hBu := uniqueDiffOn_halfBall hν hs hz
  have hBm : MeasurableSet B := measurableSet_halfBall ν z s
  refine ⟨h₁.1.sub h₂.1, fun φ hφ ↦ ?_⟩
  have hg₁ := continuousOn_gradientWithin_halfBall hν hs hz h₁.1
  have hg₂ := continuousOn_gradientWithin_halfBall hν hs hz h₂.1
  have hgr : ∀ y ∈ B, gradientWithin (fun y ↦ w₁ y - w₂ y) B y =
      gradientWithin w₁ B y - gradientWithin w₂ B y := fun y hy ↦ by
    rw [gradientWithin, gradientWithin, gradientWithin,
      fderivWithin_fun_sub (hBu y hy) ((h₁.1.differentiableOn one_ne_zero) y hy)
        ((h₂.1.differentiableOn one_ne_zero) y hy), map_sub]
  have i1 : IntegrableOn (fun y ↦ ⟪a₁ y (gradientWithin w₁ B y), ∇ φ y⟫) B :=
    integrableOn_inner_of_continuousOn (ha₁.clm_apply hg₁) hφ.1
  have i2 : IntegrableOn (fun y ↦ ⟪a₂ y (gradientWithin w₂ B y), ∇ φ y⟫) B :=
    integrableOn_inner_of_continuousOn (ha₂.clm_apply hg₂) hφ.1
  have i3 : IntegrableOn (fun y ↦ ⟪(a₁ y - a₂ y) (gradientWithin w₁ B y), ∇ φ y⟫) B :=
    integrableOn_inner_of_continuousOn ((ha₁.sub ha₂).clm_apply hg₁) hφ.1
  have i4 : IntegrableOn (fun y ↦ ⟪G₁ y, ∇ φ y⟫) B := integrableOn_inner_of_continuousOn hG₁ hφ.1
  have i5 : IntegrableOn (fun y ↦ ⟪G₂ y, ∇ φ y⟫) B := integrableOn_inner_of_continuousOn hG₂ hφ.1
  have i12 : IntegrableOn (fun y ↦ ⟪a₁ y (gradientWithin w₁ B y), ∇ φ y⟫ -
      ⟪a₂ y (gradientWithin w₂ B y), ∇ φ y⟫) B := i1.sub i2
  have i45 : IntegrableOn (fun y ↦ ⟪G₁ y, ∇ φ y⟫ - ⟪G₂ y, ∇ φ y⟫) B := i4.sub i5
  have hφb : ∀ {g : E → ℝ}, IntegrableOn g B → IntegrableOn (fun y ↦ g y * φ y) B :=
    fun hg ↦ hg.mul_continuousOn (hφ.1.continuous.continuousOn) (isCompact_halfBall ν z s)
  have k₁ := h₁.2 φ hφ
  have k₂ := h₂.2 φ hφ
  have eL : ∫ y in B, ⟪a₂ y (gradientWithin (fun y ↦ w₁ y - w₂ y) B y), ∇ φ y⟫ =
      (∫ y in B, ⟪a₁ y (gradientWithin w₁ B y), ∇ φ y⟫) -
        (∫ y in B, ⟪a₂ y (gradientWithin w₂ B y), ∇ φ y⟫) -
        ∫ y in B, ⟪(a₁ y - a₂ y) (gradientWithin w₁ B y), ∇ φ y⟫ := by
    rw [← integral_sub i1 i2, ← integral_sub i12 i3]
    refine setIntegral_congr_fun hBm fun y hy ↦ ?_
    simp only [hgr y hy, map_sub, sub_apply, inner_sub_left]
    ring
  have eR : ∫ y in B, ⟪G₁ y - G₂ y - (a₁ y - a₂ y) (gradientWithin w₁ B y), ∇ φ y⟫ =
      (∫ y in B, ⟪G₁ y, ∇ φ y⟫) - (∫ y in B, ⟪G₂ y, ∇ φ y⟫) -
        ∫ y in B, ⟪(a₁ y - a₂ y) (gradientWithin w₁ B y), ∇ φ y⟫ := by
    rw [← integral_sub i4 i5, ← integral_sub i45 i3]
    refine setIntegral_congr_fun hBm fun y hy ↦ ?_
    simp only [inner_sub_left]
  have eF : ∫ y in B, (f₁ y - f₂ y) * φ y = (∫ y in B, f₁ y * φ y) - ∫ y in B, f₂ y * φ y := by
    rw [← integral_sub (hφb hf₁) (hφb hf₂)]
    refine setIntegral_congr_fun hBm fun y _ ↦ ?_
    ring
  change ∫ y in B, ⟪a₂ y (gradientWithin (fun y ↦ w₁ y - w₂ y) B y), ∇ φ y⟫ =
    (∫ y in B, ⟪G₁ y - G₂ y - (a₁ y - a₂ y) (gradientWithin w₁ B y), ∇ φ y⟫) +
      ∫ y in B, (f₁ y - f₂ y) * φ y
  rw [eL, eR, eF, k₁, k₂]
  ring

/-! ### The right-hand side in divergence form -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The `e`-primitive `P_t (y) = ∫₀ᵗ f (σ e + y) dσ` has line derivative `f (t e + y) - f y` in
direction `e`. -/
theorem hasLineDerivAt_primitive {f : E → ℝ} (hf : Continuous f) (e : E) (t : ℝ) (y : E) :
    HasLineDerivAt ℝ (fun y ↦ ∫ σ in (0 : ℝ)..t, f (σ • e + y)) (f (t • e + y) - f y) y e := by
  set k : ℝ → ℝ := fun σ ↦ f (σ • e + y) with hk
  have hkc : Continuous k := hf.comp ((continuous_id.smul continuous_const).add continuous_const)
  set K : ℝ → ℝ := fun u ↦ ∫ σ in (0 : ℝ)..u, k σ with hK
  have hKd : ∀ u, HasDerivAt K (k u) u := fun u ↦ (hkc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have heq : (fun s : ℝ ↦ ∫ σ in (0 : ℝ)..t, f (σ • e + (y + s • e))) =
      fun s ↦ K (s + t) - K s := by
    funext s
    have e1 : (fun σ : ℝ ↦ f (σ • e + (y + s • e))) = fun σ ↦ k (σ + s) := by
      funext σ; simp only [hk, add_smul]; congr 1; abel
    rw [e1, intervalIntegral.integral_comp_add_right (fun σ ↦ k σ) s, zero_add, hK,
      intervalIntegral.integral_interval_sub_left (hkc.intervalIntegrable _ _)
        (hkc.intervalIntegrable _ _), add_comm]
  unfold HasLineDerivAt
  rw [heq]
  have h1 : HasDerivAt (fun s : ℝ ↦ K (s + t)) (k (0 + t)) 0 :=
    (hKd (0 + t)).comp_add_const 0 t
  have h2 := (h1.sub (hKd 0))
  simp only [zero_add, hk, zero_smul] at h2
  exact h2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_primitive {f : E → ℝ} (hf : Continuous f) (e : E) (t : ℝ) :
    Continuous fun y ↦ ∫ σ in (0 : ℝ)..t, f (σ • e + y) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y σ ↦ f (σ • e + y))
    (by exact hf.comp (by fun_prop : Continuous fun p : E × ℝ ↦ p.2 • e + p.1)) 0 t

/-- **The `C^α` right-hand side in divergence form**: for `e ⊥ ν` (or `closedBall z s` inside the
half space), `f` continuous and `φ ∈ C¹_c(ball z s)`,
`∫_{B⁺} (f (t e + ·) - f) φ = -∫_{B⁺} P_t ∂_e φ` with `P_t (y) = ∫₀ᵗ f (σ e + y) dσ`. -/
theorem setIntegral_halfBall_translate_sub_mul {ν e : E} {z : E} {s : ℝ}
    (he : ⟪e, ν⟫ = 0 ∨ closedBall z s ⊆ halfSpace ν) {f : E → ℝ}
    (hf : Continuous f) (t : ℝ) {φ : E → ℝ} (hφ : IsTestFn (ball z s) φ) :
    ∫ y in halfBall ν z s, (f (t • e + y) - f y) * φ y =
      -∫ y in halfBall ν z s, (∫ σ in (0 : ℝ)..t, f (σ • e + y)) * fderiv ℝ φ y e := by
  set H := halfSpace ν with hH
  set P : E → ℝ := fun y ↦ ∫ σ in (0 : ℝ)..t, f (σ • e + y) with hP
  set D : E → ℝ := fun y ↦ f (t • e + y) - f y with hD
  have hPc : Continuous P := continuous_primitive hf e t
  have hDc : Continuous D :=
    (hf.comp (continuous_const.add continuous_id)).sub hf
  have hφd : Differentiable ℝ φ := hφ.1.differentiable one_ne_zero
  have hφ'c : Continuous fun y ↦ fderiv ℝ φ y e :=
    (hφ.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hHm : MeasurableSet H := measurableSet_halfSpace ν
  have h0 := fun y (hy : y ∉ ball z s) ↦ hφ.eq_zero_and_gradient_eq_zero hy
  have hφ'0 : ∀ y ∉ ball z s, fderiv ℝ φ y e = 0 := fun y hy ↦ by
    have : y ∉ tsupport φ := fun h ↦ hy (hφ.2.2 h)
    rw [fderiv_of_notMem_tsupport ℝ this]; rfl
  -- from the half ball to the half space
  have hsub : halfBall ν z s ⊆ H := halfBall_subset_halfSpace ν z s
  have hout : ∀ y ∈ H \ halfBall ν z s, y ∉ ball z s := fun y hy hyb ↦
    hy.2 ⟨ball_subset_closedBall hyb, hy.1⟩
  have e1 : ∫ y in halfBall ν z s, D y * φ y = ∫ y in H, D y * φ y :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hHm hsub fun y hy ↦ by
      simp [(h0 y (hout y hy)).1]).symm
  have e2 : ∫ y in halfBall ν z s, P y * fderiv ℝ φ y e = ∫ y in H, P y * fderiv ℝ φ y e :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hHm hsub fun y hy ↦ by
      simp [hφ'0 y (hout y hy)]).symm
  change ∫ y in halfBall ν z s, D y * φ y = -∫ y in halfBall ν z s, P y * fderiv ℝ φ y e
  rw [e1, e2]
  -- integration by parts along `e` against `g = 1_H φ`
  set g : E → ℝ := H.indicator φ with hg
  set g' : E → ℝ := H.indicator fun y ↦ fderiv ℝ φ y e with hg'
  have hgl : ∀ y, HasLineDerivAt ℝ g (g' y) y e := by
    rcases he with he | hball
    · have hHe : ∀ y (u : ℝ), (y + u • e ∈ H ↔ y ∈ H) := fun y u ↦ by
        simp only [hH, mem_halfSpace, inner_add_left, real_inner_smul_left, he, mul_zero,
          add_zero]
      intro y
      by_cases hy : y ∈ H
      · have h1 : HasLineDerivAt ℝ φ (fderiv ℝ φ y e) y e :=
          (hφd y).hasFDerivAt.hasLineDerivAt e
        unfold HasLineDerivAt at h1 ⊢
        have heq : (fun u : ℝ ↦ g (y + u • e)) = fun u ↦ φ (y + u • e) := by
          funext u; simp only [hg, indicator_of_mem ((hHe y u).2 hy)]
        rw [heq, hg', indicator_of_mem hy]
        exact h1
      · unfold HasLineDerivAt
        have heq : (fun u : ℝ ↦ g (y + u • e)) = fun _ ↦ 0 := by
          funext u; simp only [hg, indicator_of_notMem (fun h ↦ hy ((hHe y u).1 h))]
        rw [heq, hg', indicator_of_notMem hy]
        exact hasDerivAt_const _ _
    · have hgφ : g = φ := by
        funext y
        by_cases hy : y ∈ H
        · simp only [hg, indicator_of_mem hy]
        · have : y ∉ ball z s := fun h ↦ hy (hball (ball_subset_closedBall h))
          simp only [hg, indicator_of_notMem hy, (h0 y this).1]
      have hgφ' : g' = fun y ↦ fderiv ℝ φ y e := by
        funext y
        by_cases hy : y ∈ H
        · simp only [hg', indicator_of_mem hy]
        · have : y ∉ ball z s := fun h ↦ hy (hball (ball_subset_closedBall h))
          simp only [hg', indicator_of_notMem hy, hφ'0 y this]
      intro y
      rw [hgφ, hgφ']
      exact (hφd y).hasFDerivAt.hasLineDerivAt e
  have hcs : ∀ {k : E → ℝ}, Continuous k → ∀ {m : E → ℝ}, Continuous m →
      (∀ y ∉ ball z s, m y = 0) → Integrable (fun y ↦ k y * H.indicator m y) := by
    intro k hk m hm hm0
    have hsupp : HasCompactSupport fun y ↦ k y * m y := by
      refine HasCompactSupport.intro (isCompact_closedBall z s) fun y hy ↦ ?_
      rw [hm0 y fun h ↦ hy (ball_subset_closedBall h), mul_zero]
    have hi := ((hk.mul hm).integrable_of_hasCompactSupport (μ := volume) hsupp).indicator hHm
    refine hi.congr (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ H
    · simp [indicator_of_mem hy]
    · simp [indicator_of_notMem hy]
  have i1 := hcs hDc hφd.continuous fun y hy ↦ (h0 y hy).1
  have i2 := hcs hPc hφ'c hφ'0
  have i3 := hcs hPc hφd.continuous fun y hy ↦ (h0 y hy).1
  have ibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ) (f := P) (f' := D) (g := g) (g' := g')
    (v := e) (by simpa using i1) (by simpa using i2) (by simpa using i3)
    (fun y _ ↦ hasLineDerivAt_primitive hf e t y) (fun y _ ↦ hgl y)
  simp only [ContinuousLinearMap.mul_apply'] at ibp
  have r1 : ∫ y, P y * g' y = ∫ y in H, P y * fderiv ℝ φ y e := by
    rw [← integral_indicator hHm]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ H
    · simp [hg', indicator_of_mem hy]
    · simp [hg', indicator_of_notMem hy]
  have r2 : ∫ y, D y * g y = ∫ y in H, D y * φ y := by
    rw [← integral_indicator hHm]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ H
    · simp [hg, indicator_of_mem hy]
    · simp [hg, indicator_of_notMem hy]
  rw [r1, r2] at ibp
  rw [ibp, neg_neg]

/-- Moving the difference quotient of a continuous `f` into the flux (`e ⊥ ν`, or
`closedBall z s` inside the half space). -/
theorem IsConormalSolOn.translate_sub_rhs {ν e : E} {z : E} {s : ℝ}
    (he : ⟪e, ν⟫ = 0 ∨ closedBall z s ⊆ halfSpace ν) {a : E → E →L[ℝ] E}
    {G : E → E} {f : E → ℝ} (hf : Continuous f) {t : ℝ} {u : E → ℝ}
    (hG : ContinuousOn G (halfBall ν z s))
    (h : IsConormalSolOn ν a G (fun y ↦ f (t • e + y) - f y) z s u) :
    IsConormalSolOn ν a (fun y ↦ G y - (∫ σ in (0 : ℝ)..t, f (σ • e + y)) • e) 0 z s u := by
  refine ⟨h.1, fun φ hφ ↦ ?_⟩
  have key := h.2 φ hφ
  rw [setIntegral_halfBall_translate_sub_mul he hf t hφ] at key
  have i1 := integrableOn_inner_of_continuousOn hG hφ.1
  have i2 : IntegrableOn (fun y ↦ (∫ σ in (0 : ℝ)..t, f (σ • e + y)) * fderiv ℝ φ y e)
      (halfBall ν z s) :=
    ContinuousOn.integrableOn_compact (isCompact_halfBall ν z s)
      ((continuous_primitive hf e t).mul
        ((hφ.1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).continuousOn
  have hge : ∀ y, ⟪e, ∇ φ y⟫ = fderiv ℝ φ y e := fun y ↦ by
    rw [real_inner_comm]; exact InnerProductSpace.toDual_symm_apply
  change _ = (∫ y in halfBall ν z s,
      ⟪G y - (∫ σ in (0 : ℝ)..t, f (σ • e + y)) • e, ∇ φ y⟫) +
    ∫ y in halfBall ν z s, (0 : E → ℝ) y * φ y
  simp only [Pi.zero_apply, zero_mul, integral_zero, add_zero, inner_sub_left,
    real_inner_smul_left, hge]
  rw [integral_sub i1 i2, key, sub_eq_add_neg]

/-! ### The difference-quotient problem -/

/-- **The tangential difference-quotient problem**. Let `w` be a conormal
solution on `B = halfBall ν x r` with `a`, `G` continuous on `B` and `f` agreeing on `B` with a
continuous `fh`. Let `e` be tangential (or `closedBall z (s + |t| ‖e‖)` inside the half space),
and let `closedBall z s` and its translate by `t e` lie inside `B`. Then
`u_t = w (t e + ·) - w` solves on `halfBall ν z s` the conormal problem with coefficient `a`, no
right-hand side, and flux `G (t e + ·) - G - (a (t e + ·) - a) ∇w (t e + ·) - P_t e`, where
`P_t = ∫₀ᵗ fh (σ e + ·) dσ`. -/
theorem IsConormalSolOn.translate_sub {ν : E} {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ}
    {x : E} {r : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (h : IsConormalSolOn ν a G f x r w)
    (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (ha : ContinuousOn a (halfBall ν x r))
    (hG : ContinuousOn G (halfBall ν x r)) {fh : E → ℝ} (hfh : Continuous fh)
    (hff : EqOn f fh (halfBall ν x r)) {e : E} {t : ℝ} {z : E} {s : ℝ}
    (he : ⟪e, ν⟫ = 0 ∨ closedBall z (s + |t| * ‖e‖) ⊆ halfSpace ν)
    (hs : 0 < s) (hz : 0 ≤ ⟪z, ν⟫) (hzr : dist z x + s + |t| * ‖e‖ ≤ r) :
    IsConormalSolOn ν a
      (fun y ↦ G (t • e + y) - G y -
        (a (t • e + y) - a y) (gradientWithin w (halfBall ν x r) (t • e + y)) -
        (∫ σ in (0 : ℝ)..t, fh (σ • e + y)) • e) 0 z s (fun y ↦ w (t • e + y) - w y) := by
  set B := halfBall ν x r with hB
  set Bz := halfBall ν z s with hBz
  have hz' : -s < ⟪z, ν⟫ := by linarith
  have hte : dist (t • e + z) z ≤ |t| * ‖e‖ := by
    rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs]
  have hts : 0 ≤ |t| * ‖e‖ := by positivity
  have hcompat : ∀ y ∈ closedBall z s, (0 ≤ ⟪t • e + y, ν⟫ ↔ 0 ≤ ⟪y, ν⟫) := fun y hy ↦ by
    rcases he with he | hball
    · rw [inner_add_left, real_inner_smul_left, he, mul_zero, zero_add]
    · have h1 : y ∈ halfSpace ν := hball (closedBall_subset_closedBall (by linarith) hy)
      have h2 : t • e + y ∈ halfSpace ν := hball (by
        rw [mem_closedBall]
        have : dist (t • e + y) y = |t| * ‖e‖ := by
          rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs]
        linarith [dist_triangle (t • e + y) y z, mem_closedBall.1 hy])
      exact ⟨fun _ ↦ h1, fun _ ↦ h2⟩
  have he' : ⟪e, ν⟫ = 0 ∨ closedBall z s ⊆ halfSpace ν := he.imp id fun h ↦
    (closedBall_subset_closedBall (by linarith)).trans h
  have hsub1 : closedBall (t • e + z) s ⊆ closedBall x r :=
    closedBall_subset_closedBall' (by linarith [dist_triangle (t • e + z) z x])
  have hsub1' : ball (t • e + z) s ⊆ ball x r :=
    ball_subset_ball' (by linarith [dist_triangle (t • e + z) z x])
  have hsub2 : closedBall z s ⊆ closedBall x r := closedBall_subset_closedBall' (by
    nlinarith [abs_nonneg t, norm_nonneg e])
  have hsub2' : ball z s ⊆ ball x r :=
    ball_subset_ball' (by nlinarith [abs_nonneg t, norm_nonneg e])
  have hmaps : ∀ y ∈ Bz, t • e + y ∈ B := fun y hy ↦ by
    refine ⟨hsub1 ?_, (hcompat y hy.1).2 hy.2⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_add_left_eq_sub, ← dist_eq_norm]; exact hy.1
  have hBzB : Bz ⊆ B := inter_subset_inter_left _ hsub2
  have h₁ := h.translate hν hr hx hs hz' hsub1 hsub1' hcompat
  have h₂ := h.restrict_halfBall hν hs hz' hsub2 hsub2'
  have htc : ContinuousOn (fun y : E ↦ t • e + y) Bz :=
    (continuous_const.add continuous_id).continuousOn
  have hfhi : ∀ {k : E → ℝ}, Continuous k → IntegrableOn k Bz := fun hk ↦
    hk.continuousOn.integrableOn_compact (isCompact_halfBall ν z s)
  have h₃ := IsConormalSolOn.sub_of_continuousOn hν hs hz' h₁ h₂ (ha.comp htc hmaps)
    (ha.mono hBzB) (hG.comp htc hmaps) (hG.mono hBzB)
    ((hfhi (hfh.comp (continuous_const.add continuous_id))).congr_fun
      (fun y hy ↦ (hff (hmaps y hy)).symm) (measurableSet_halfBall ν z s))
    ((hfhi hfh).congr_fun (fun y hy ↦ (hff (hBzB hy)).symm) (measurableSet_halfBall ν z s))
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hgr : ∀ y ∈ Bz, gradientWithin (fun y ↦ w (t • e + y)) Bz y =
      gradientWithin w B (t • e + y) := fun y hy ↦
    gradientWithin_translate hν hs hz' hmaps hwB (by rintro _ ⟨u, hu, rfl⟩; exact hmaps u hu) hy
  have h₄ := h₃.congr_data (a' := a) (G' := fun y ↦ G (t • e + y) - G y -
      (a (t • e + y) - a y) (gradientWithin w B (t • e + y)))
    (f' := fun y ↦ fh (t • e + y) - fh y) (fun _ _ ↦ rfl)
    (fun y hy ↦ by beta_reduce; rw [show halfBall ν z s = Bz from rfl, hgr y hy])
    (fun y hy ↦ by simp only [hff (hmaps y hy), hff (hBzB hy)])
  refine h₄.translate_sub_rhs he' hfh ?_
  refine ((hG.comp htc hmaps).sub (hG.mono hBzB)).sub ?_
  refine ((ha.comp htc hmaps).sub (ha.mono hBzB)).clm_apply ?_
  exact (continuousOn_gradientWithin_halfBall hν hr hx h.1).comp htc hmaps

/-! ### Bounds for the difference-quotient flux -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Second differences of a function with a Hölder derivative**:
`‖(g (v + y) - g y) - (g (v + y') - g y')‖ ≤ K ‖y - y'‖^α ‖v‖` when `Dg` is `K`-Hölder on a convex
set containing the four points. -/
theorem norm_translate_sub_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {S : Set E} (hS : Convex ℝ S) {Dg : E → E →L[ℝ] F}
    (hDg : ∀ p ∈ S, HasFDerivWithinAt g (Dg p) S p) {K α : ℝ≥0}
    (hK : HolderOnWith K α Dg S) {v y y' : E} (hy : y ∈ S) (hy' : y' ∈ S) (hvy : v + y ∈ S)
    (hvy' : v + y' ∈ S) :
    ‖(g (v + y) - g y) - (g (v + y') - g y')‖ ≤ K * dist y y' ^ (α : ℝ) * ‖v‖ := by
  set c := y' - y with hc
  set S' := {p | p ∈ S ∧ p + c ∈ S} with hS'
  have hS'c : Convex ℝ S' := hS.inter (hS.translate_preimage_left c)
  have hyS : y ∈ S' := ⟨hy, by simpa [hc] using hy'⟩
  have hvyS : v + y ∈ S' := ⟨hvy, by
    have : v + y + c = v + y' := by rw [hc]; abel
    rw [this]; exact hvy'⟩
  have hder : ∀ p ∈ S', HasFDerivWithinAt (fun p ↦ g p - g (p + c)) (Dg p - Dg (p + c)) S' p := by
    intro p hp
    have h1 := (hDg p hp.1).mono fun q (hq : q ∈ S') ↦ hq.1
    have h2 : HasFDerivWithinAt (fun p ↦ g (p + c)) (Dg (p + c)) S' p := by
      have := (hDg (p + c) hp.2).comp p ((hasFDerivAt_id p).add_const c).hasFDerivWithinAt
        (fun q (hq : q ∈ S') ↦ hq.2)
      simpa [Function.comp_def] using this
    exact h1.sub h2
  have hbd : ∀ p ∈ S', ‖Dg p - Dg (p + c)‖ ≤ K * dist y y' ^ (α : ℝ) := by
    intro p hp
    rw [← dist_eq_norm]
    refine (hK.dist_le hp.1 hp.2).trans (le_of_eq ?_)
    congr 2
    rw [dist_eq_norm, dist_eq_norm, hc]
    rw [show p - (p + (y' - y)) = -(y' - y) by abel, norm_neg, norm_sub_rev]
  have hmv := hS'c.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbd hyS hvyS
  have e1 : g (v + y) - g (v + y + c) - (g y - g (y + c)) =
      (g (v + y) - g y) - (g (v + y') - g y') := by
    have h1 : v + y + c = v + y' := by rw [hc]; abel
    have h2 : y + c = y' := by rw [hc]; abel
    rw [h1, h2]; abel
  rw [e1, add_sub_cancel_right] at hmv
  exact hmv

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- First differences: `‖g (v + y) - g y‖ ≤ M ‖v‖` when `‖Dg‖ ≤ M` on a convex set containing the
segment. -/
theorem norm_translate_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {S : Set E} (hS : Convex ℝ S) {Dg : E → E →L[ℝ] F}
    (hDg : ∀ p ∈ S, HasFDerivWithinAt g (Dg p) S p) {M : ℝ} (hM : ∀ p ∈ S, ‖Dg p‖ ≤ M)
    {v y : E} (hy : y ∈ S) (hvy : v + y ∈ S) : ‖g (v + y) - g y‖ ≤ M * ‖v‖ := by
  have := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le hDg hM hy hvy
  rwa [add_sub_cancel_right] at this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Hölder bound for the `e`-primitive: `|P_t y - P_t y'| ≤ |t| K ‖y - y'‖^α` when `f` is
`K`-Hölder on a set containing `σ e + y`, `σ e + y'` for `σ` between `0` and `t`. -/
theorem abs_primitive_sub_le {f : E → ℝ} (hf : Continuous f) {S : Set E} {K α : ℝ≥0}
    (hK : HolderOnWith K α f S) {e y y' : E} {t : ℝ}
    (hS : ∀ σ ∈ Ι (0 : ℝ) t, σ • e + y ∈ S ∧ σ • e + y' ∈ S) :
    |(∫ σ in (0 : ℝ)..t, f (σ • e + y)) - ∫ σ in (0 : ℝ)..t, f (σ • e + y')| ≤
      |t| * (K * dist y y' ^ (α : ℝ)) := by
  have hc : ∀ y, Continuous fun σ : ℝ ↦ f (σ • e + y) := fun y ↦
    hf.comp ((continuous_id.smul continuous_const).add continuous_const)
  rw [← intervalIntegral.integral_sub ((hc y).intervalIntegrable _ _)
    ((hc y').intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (f := fun σ ↦ f (σ • e + y) - f (σ • e + y')) (C := K * dist y y' ^ (α : ℝ))
    fun σ hσ ↦ by
      rw [Real.norm_eq_abs, ← Real.dist_eq]
      refine ((hK.dist_le (hS σ hσ).1 (hS σ hσ).2)).trans (le_of_eq ?_)
      rw [dist_add_left]
  rw [Real.norm_eq_abs, sub_zero] at this
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Sup bound for the `e`-primitive. -/
theorem abs_primitive_le {f : E → ℝ} {S : Set E} {Mf : ℝ} (hMf : ∀ p ∈ S, |f p| ≤ Mf)
    {e y : E} {t : ℝ} (hS : ∀ σ ∈ Ι (0 : ℝ) t, σ • e + y ∈ S) :
    |∫ σ in (0 : ℝ)..t, f (σ • e + y)| ≤ |t| * Mf := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (f := fun σ ↦ f (σ • e + y)) (C := Mf) fun σ hσ ↦ by
      rw [Real.norm_eq_abs]; exact hMf _ (hS σ hσ)
  rw [Real.norm_eq_abs, sub_zero] at this
  linarith

end BasicElliptic.Div
