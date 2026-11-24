/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Three.Canonical

/-!
# Third-order tensors from tangential entries

* `Div.norm_le_of_tangential_three`: a trilinear form `T` that is symmetric in its last two slots
  and under exchanging its first and last slots (hence fully symmetric), whose entries with two
  tangential arguments are bounded by `τ`, and which satisfies the differentiated equation
  `|Σ_j T(ξ, b_j, A b_j)| ≤ R ‖ξ‖`, is bounded in norm by an explicit multiple of `τ + R`.
* `Div.norm_apply_sub_apply_le`: the difference of `P a c` and `P' a' c'` for bilinear `P, P'`.
-/

public section

open Metric Set RealInnerProductSpace

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_apply_sub_apply_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (P P' : E →L[ℝ] F →L[ℝ] G) (a a' : E) (c c' : F) :
    ‖P a c - P' a' c'‖ ≤ ‖P - P'‖ * ‖a‖ * ‖c‖ + ‖P'‖ * ‖a - a'‖ * ‖c‖ +
      ‖P'‖ * ‖a'‖ * ‖c - c'‖ := by
  have e : P a c - P' a' c' = (P - P') a c + P' (a - a') c + P' a' (c - c') := by
    simp only [sub_apply, map_sub]; abel
  rw [e]
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact ((P - P') a).le_opNorm c |>.trans (by gcongr; exact (P - P').le_opNorm a)
  · exact (P' (a - a')).le_opNorm c |>.trans (by gcongr; exact P'.le_opNorm _)
  · exact (P' a').le_opNorm _ |>.trans (by gcongr; exact P'.le_opNorm _)

set_option maxSynthPendingDepth 6 in
/-- **A symmetric trilinear form from its tangential entries and the differentiated equation.** -/
theorem norm_le_of_tangential_three {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {ν : E} (hν : ‖ν‖ = 1) (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h23 : ∀ ξ u v, T ξ u v = T ξ v u) (h13 : ∀ ξ u v, T ξ u v = T v u ξ)
    {A : E →L[ℝ] E} (hA : (A : E →ₗ[ℝ] E).IsSymmetric) {lam Λ : ℝ} (hlam : 0 < lam)
    (hell : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫) (hAΛ : ‖A‖ ≤ Λ) {R τ : ℝ} (hR : 0 ≤ R)
    (hτ : 0 ≤ τ) (heq : ∀ ξ, |∑ j, T ξ (b j) (A (b j))| ≤ R * ‖ξ‖)
    (htan : ∀ β e e', ⟪e, ν⟫ = 0 → ⟪e', ν⟫ = 0 → |T β e e'| ≤ τ * ‖β‖ * ‖e‖ * ‖e'‖) :
    ‖T‖ ≤ (2 * τ * (1 + Fintype.card ι * Λ / lam) + R / lam) *
        (1 + 2 * (1 + Fintype.card ι * Λ / lam)) + R / lam := by
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hAΛ
  set lm := 1 + Fintype.card ι * Λ / lam with hlm
  have hlm0 : 0 ≤ lm := by positivity
  -- symmetry in the first two slots
  have h12 : ∀ ξ u v, T ξ u v = T u ξ v := fun ξ u v ↦ by
    rw [h23, h13, h23]
  set N₁ := 2 * τ * lm + R / lam with hN₁
  have hN₁0 : 0 ≤ N₁ := by positivity
  -- tangential first argument
  have hξt : ∀ ξ, ⟪ξ, ν⟫ = 0 → ‖T ξ‖ ≤ N₁ * ‖ξ‖ := by
    intro ξ hξ
    have hrow : ∀ e : E, ⟪e, ν⟫ = 0 → ‖T ξ e‖ ≤ (τ * ‖ξ‖) * ‖e‖ := fun e he ↦ by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun β ↦ ?_
      rw [Real.norm_eq_abs, show T ξ e β = T β e ξ by rw [h13, h23, h13, h23, h13]]
      calc |T β e ξ| ≤ τ * ‖β‖ * ‖e‖ * ‖ξ‖ := htan β e ξ he hξ
        _ = τ * ‖ξ‖ * ‖e‖ * ‖β‖ := by ring
    have := norm_le_of_tangential_approx b hν (T ξ) (h23 ξ) hA hlam hell hAΛ (heq ξ)
      (by positivity) hrow
    calc ‖T ξ‖ ≤ 2 * (τ * ‖ξ‖) * lm + R * ‖ξ‖ / lam := this
      _ = N₁ * ‖ξ‖ := by rw [hN₁]; ring
  -- the normal first argument
  set N₂ := 2 * N₁ * lm + R / lam with hN₂
  have hN₂0 : 0 ≤ N₂ := by positivity
  have hνb : ‖T ν‖ ≤ N₂ := by
    have hrow : ∀ e : E, ⟪e, ν⟫ = 0 → ‖T ν e‖ ≤ N₁ * ‖e‖ := fun e he ↦ by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun β ↦ ?_
      rw [h12]
      calc ‖T e ν β‖ ≤ ‖T e ν‖ * ‖β‖ := (T e ν).le_opNorm β
        _ ≤ (‖T e‖ * ‖ν‖) * ‖β‖ := by gcongr; exact (T e).le_opNorm ν
        _ ≤ (N₁ * ‖e‖ * 1) * ‖β‖ := by rw [hν]; gcongr; exact hξt e he
        _ = N₁ * ‖e‖ * ‖β‖ := by ring
    have := norm_le_of_tangential_approx b hν (T ν) (h23 ν) hA hlam hell hAΛ (heq ν)
      hN₁0 hrow
    calc ‖T ν‖ ≤ 2 * N₁ * lm + R * ‖ν‖ / lam := this
      _ = N₂ := by rw [hν, mul_one]
  -- all arguments
  have hK : 0 ≤ N₁ + N₂ := by positivity
  have hbound : ‖T‖ ≤ N₁ + N₂ := by
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun ξ ↦ ?_
    set P := ξ - ⟪ξ, ν⟫ • ν with hP
    have hPν : ⟪P, ν⟫ = 0 := by
      rw [hP, inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]
    have hPn : ‖P‖ ≤ ‖ξ‖ := by
      have h1 : ‖P‖ ^ 2 = ‖ξ‖ ^ 2 - ⟪ξ, ν⟫ ^ 2 := by
        rw [hP, @norm_sub_sq_real, norm_smul, hν, real_inner_smul_right, Real.norm_eq_abs,
          mul_one, sq_abs]
        ring
      have h2 : ‖P‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by rw [h1]; nlinarith [sq_nonneg ⟪ξ, ν⟫]
      nlinarith [norm_nonneg P, norm_nonneg ξ]
    have hξν : |⟪ξ, ν⟫| ≤ ‖ξ‖ := by simpa [hν] using abs_real_inner_le_norm ξ ν
    have hdec : T ξ = T P + ⟪ξ, ν⟫ • T ν := by
      rw [hP, map_sub, map_smul, sub_add_cancel]
    rw [hdec]
    calc ‖T P + ⟪ξ, ν⟫ • T ν‖ ≤ ‖T P‖ + ‖⟪ξ, ν⟫ • T ν‖ := norm_add_le _ _
      _ ≤ N₁ * ‖P‖ + |⟪ξ, ν⟫| * N₂ := by
          rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hξt P hPν
      _ ≤ N₁ * ‖ξ‖ + ‖ξ‖ * N₂ := by gcongr
      _ = (N₁ + N₂) * ‖ξ‖ := by ring
  refine hbound.trans (le_of_eq ?_)
  rw [hN₂, hN₁]; ring

end BasicElliptic.Div
