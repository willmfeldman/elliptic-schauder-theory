/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Boundary.Iterate

/-!
# Scaled boundary expansions for the Laplacian on half balls

`ν` is a unit vector, `γ = 2 + α`, `B_r⁺ = halfBall ν 0 r`.

* `Nondiv.expansion_halfBall_neumann`: there is `C = C(E, α)` such that if
  `u ∈ C(B̄_r⁺) ∩ C²(B_r⁺)`, `|u| ≤ M₀`, `|Δu(z) − σ| ≤ H |z|^α` in the open half ball and
  `|∂_ν u(z)| ≤ G |z|^{1+α}` at flat points, then with `N = M₀ + r² |σ| + r^γ (H + G)` there is
  a quadratic `P` with `tr P = σ`, `|P(0)| + r ‖DP(0)‖ + r² ‖quad P‖ ≤ C N` and
  `|u(z) − P(z)| ≤ C N (|z|/r)^γ` on `B_r⁺ ∩ {|z| < r}`.
* `Nondiv.expansion_halfBall_dirichlet`: the same with `u = 0` on the flat part and
  `N = M₀ + r² |σ| + r^γ H`.
* `QuadPoly.normalSq ν σ`: the quadratic `σ ⟪z, ν⟫² / 2`, with trace `σ`, vanishing on the flat
  part; the initial polynomial of the Dirichlet iteration.

## Provenance

The half-ball analogue of `Nondiv.expansion_of_laplacian`.
-/

public section

open Metric Set Filter Topology Module InnerProductSpace
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace BasicElliptic

namespace QuadPoly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic `z ↦ σ ⟪z, ν⟫² / 2`. -/
noncomputable def normalSq (ν : E) (σ : ℝ) : QuadPoly E :=
  ⟨0, 0, σ • (innerSL ℝ ν).smulRight (innerSL ℝ ν)⟩

theorem eval_normalSq (ν : E) (σ : ℝ) (z : E) :
    (normalSq ν σ).eval z = σ / 2 * ⟪z, ν⟫ ^ 2 := by
  have h : (innerSL ℝ ν) z = ⟪z, ν⟫ := by rw [innerSL_apply_apply, real_inner_comm]
  simp [normalSq, eval, h]
  ring

theorem trace_normalSq [FiniteDimensional ℝ E] {ν : E} (hν : ‖ν‖ = 1) (σ : ℝ) :
    (normalSq ν σ).trace = σ := by
  have h : ∀ v : E, (innerSL ℝ ν) v = ⟪ν, v⟫ := fun v ↦ by rw [innerSL_apply_apply]
  simp only [trace, normalSq, smul_apply, ContinuousLinearMap.smulRight_apply, h, smul_eq_mul]
  rw [← Finset.mul_sum]
  have := (stdOrthonormalBasis ℝ E).sum_inner_mul_inner ν ν
  simp only [real_inner_comm ν] at this
  rw [this, real_inner_self_of_norm_eq_one hν, mul_one]

theorem sumNorm_normalSq_le {ν : E} (hν : ‖ν‖ = 1) (σ : ℝ) : (normalSq ν σ).sumNorm ≤ |σ| := by
  simp only [sumNorm, normalSq, abs_zero, norm_zero, zero_add]
  calc ‖σ • (innerSL ℝ ν).smulRight (innerSL ℝ ν)‖
      ≤ ‖σ‖ * ‖(innerSL ℝ ν).smulRight (innerSL ℝ ν)‖ := norm_smul_le _ _
    _ ≤ |σ| * (1 * 1) := by
        rw [Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, hν]
    _ = |σ| := by ring

theorem abs_eval_normalSq_le {ν : E} (hν : ‖ν‖ = 1) (σ : ℝ) (z : E) :
    |(normalSq ν σ).eval z| ≤ |σ| * ‖z‖ ^ 2 := by
  rw [eval_normalSq, abs_mul, abs_div, abs_two, abs_pow]
  have h1 : |⟪z, ν⟫| ≤ ‖z‖ := by
    have := abs_real_inner_le_norm z ν; rwa [hν, mul_one] at this
  have h2 : |⟪z, ν⟫| ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : 0 ≤ |σ| := abs_nonneg σ
  nlinarith [sq_nonneg ‖z‖]

theorem vanishesOnFlat_normalSq (ν : E) (σ : ℝ) : Nondiv.VanishesOnFlat ν (normalSq ν σ) :=
  fun z hz ↦ by rw [eval_normalSq, mem_flatPart.1 hz]; ring

end QuadPoly

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- **Scaled Neumann expansion on a half ball** (pointwise Hölder data at the centre). There is
`C = C(E, α) ≥ 0` such that: if `‖ν‖ = 1`, `u` is continuous on `halfBall ν 0 r` and `C²` in
`ball 0 r ∩ openHalfSpace ν`, `|u| ≤ M₀`, `|Δu(z) − σ| ≤ H |z|^α` in the open half ball, and the
inward normal derivative satisfies `|∂_ν u(z)| ≤ G |z|^{1+α}` at flat points of `ball 0 r`, then
with `N = M₀ + r² |σ| + r^{2+α} (H + G)` there is a quadratic `P` with `tr P = σ`,
`|P(0)| + r ‖DP(0)‖ + r² ‖quad P‖ ≤ C N` and `|u(z) − P(z)| ≤ C N (|z|/r)^{2+α}` for
`z ∈ halfSpace ν`, `|z| < r`. -/
theorem expansion_halfBall_neumann {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ν : E}, ‖ν‖ = 1 → ∀ (u : E → ℝ) (r M₀ σ H G : ℝ), 0 < r → 0 ≤ H →
      0 ≤ G → ContinuousOn u (halfBall ν 0 r) → ContDiffOn ℝ 2 u (ball 0 r ∩ openHalfSpace ν) →
      (∀ z ∈ halfBall ν (0 : E) r, |u z| ≤ M₀) →
      (∀ z ∈ ball (0 : E) r ∩ openHalfSpace ν, |Δ u z - σ| ≤ H * ‖z‖ ^ α) →
      (∀ z ∈ ball (0 : E) r, z ∈ flatPart ν → ∃ d : ℝ,
        HasDerivWithinAt (fun t : ℝ ↦ u (z + t • ν)) d (Ici 0) 0 ∧ |d| ≤ G * ‖z‖ ^ (1 + α)) →
      ∃ P : QuadPoly E, P.trace = σ ∧
        |P.const| + r * ‖P.lin‖ + r ^ 2 * ‖P.quad‖ ≤
          C * (M₀ + r ^ 2 * |σ| + r ^ (2 + α) * (H + G)) ∧
        ∀ z ∈ halfSpace ν, ‖z‖ < r →
          |u z - P.eval z| ≤
            C * (M₀ + r ^ 2 * |σ| + r ^ (2 + α) * (H + G)) * (‖z‖ / r) ^ (2 + α) := by
  obtain ⟨δ₀, C₁, A, hδ₀, hC₁, hA, hexp⟩ := expansion_at_origin_neumann (E := E) hα
  set K : ℝ := max 1 (1 / δ₀) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKδ : 1 / δ₀ ≤ K := le_max_right _ _
  refine ⟨K * max (1 + C₁) A, by positivity,
    fun {ν} hν u r M₀ σ H G hr hH hG hu hu2 hM₀ hΔ hNeu ↦ ?_⟩
  have h0mem : (0 : E) ∈ halfBall ν 0 r := ⟨mem_closedBall_self hr.le, by simp⟩
  have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0 h0mem)
  have hrγ : 0 < r ^ (2 + α) := Real.rpow_pos_of_pos hr _
  set N₀ : ℝ := M₀ + r ^ 2 * |σ| + r ^ (2 + α) * (H + G) with hN₀
  set N : ℝ := M₀ + r ^ 2 * |σ| + r ^ (2 + α) * (H + G) / δ₀ with hN
  have hN0 : 0 ≤ N := by positivity
  have hNN₀ : N ≤ K * N₀ := by
    have h1 : r ^ (2 + α) * (H + G) / δ₀ ≤ K * (r ^ (2 + α) * (H + G)) := by
      rw [div_eq_mul_one_div, mul_comm K]
      exact mul_le_mul_of_nonneg_left hKδ (by positivity)
    have h2 : M₀ + r ^ 2 * |σ| ≤ K * (M₀ + r ^ 2 * |σ|) := le_mul_of_one_le_left (by positivity) hK1
    rw [hN, hN₀]; nlinarith
  have hCN : N * max (1 + C₁) A ≤ K * max (1 + C₁) A * N₀ := by
    have := mul_le_mul_of_nonneg_right hNN₀ (le_max_of_le_right hA : (0 : ℝ) ≤ max (1 + C₁) A)
    linarith
  have hN₀0 : 0 ≤ N₀ := by positivity
  rcases hN0.eq_or_lt with hN0' | hNpos
  · -- degenerate case: `u = 0`, `σ = 0`
    have hM : M₀ = 0 := by
      have : 0 ≤ r ^ 2 * |σ| := by positivity
      have : 0 ≤ r ^ (2 + α) * (H + G) / δ₀ := by positivity
      linarith
    have hσ : σ = 0 := by
      have h1 : r ^ 2 * |σ| = 0 := by
        have : 0 ≤ r ^ (2 + α) * (H + G) / δ₀ := by positivity
        have : 0 ≤ r ^ 2 * |σ| := by positivity
        linarith
      simpa [hr.ne'] using h1
    refine ⟨0, by simp [QuadPoly.trace, hσ], by
      simp only [QuadPoly.zero_const, abs_zero, QuadPoly.zero_lin, norm_zero, mul_zero,
        add_zero, QuadPoly.zero_quad]
      positivity, fun z hzh hz ↦ ?_⟩
    rw [QuadPoly.eval_zero_poly, sub_zero]
    exact (hM₀ z ⟨mem_closedBall_zero_iff.2 hz.le, hzh⟩).trans (by rw [hM]; positivity)
  -- the normalized function on `B₁⁺`
  have hnorm : ∀ y : E, ‖r • y‖ = r * ‖y‖ := fun y ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hmapsC : MapsTo (fun y : E ↦ r • y) (halfBall ν 0 1) (halfBall ν 0 r) := fun y hy ↦ by
    simpa using smul_mem_halfBall hr hy
  have hmapsB : MapsTo (fun y : E ↦ r • y) (ball 0 1 ∩ openHalfSpace ν)
      (ball 0 r ∩ openHalfSpace ν) := fun y hy ↦ by
    simpa using smul_mem_ball_inter_openHalfSpace hr hy
  set v : E → ℝ := fun y ↦ u (r • y) / N with hv
  have hsc : ContDiff ℝ 2 fun y : E ↦ r • y := contDiff_const_smul r
  have hvc : ContinuousOn v (halfBall ν 0 1) :=
    (hu.comp hsc.continuous.continuousOn hmapsC).div_const _
  have hv2 : ContDiffOn ℝ 2 v (ball 0 1 ∩ openHalfSpace ν) :=
    (hu2.comp hsc.contDiffOn hmapsB).div_const _
  set σ' : ℝ := r ^ 2 * σ / N with hσ'
  have hσ'abs : |σ'| = r ^ 2 * |σ| / N := by
    rw [hσ', abs_div, abs_mul, abs_of_pos hNpos, abs_of_nonneg (sq_nonneg r)]
  have hσ'1 : M₀ / N + |σ'| ≤ 1 := by
    rw [hσ'abs, ← add_div, div_le_one hNpos, hN]
    have : 0 ≤ r ^ (2 + α) * (H + G) / δ₀ := by positivity
    linarith
  have hv0 : ∀ y ∈ halfBall ν (0 : E) 1,
      |v y - (QuadPoly.isotropic σ' : QuadPoly E).eval y| ≤ 1 := by
    intro y hy
    have h1 : |v y| ≤ M₀ / N := by
      rw [hv, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right (hM₀ _ (hmapsC hy)) hNpos.le
    have h2 := QuadPoly.abs_eval_isotropic_le (E := E) σ' y
    have hy1 : ‖y‖ ^ 2 ≤ 1 := by
      have := mem_closedBall_zero_iff.1 hy.1
      nlinarith [norm_nonneg y]
    have h3 : |σ'| * ‖y‖ ^ 2 ≤ |σ'| := mul_le_of_le_one_right (abs_nonneg _) hy1
    calc _ ≤ |v y| + |(QuadPoly.isotropic σ' : QuadPoly E).eval y| := abs_sub _ _
      _ ≤ 1 := by linarith
  have hNH : r ^ (2 + α) * (H + G) ≤ δ₀ * N := by
    have : r ^ (2 + α) * (H + G) / δ₀ ≤ N := by
      rw [hN]; nlinarith [abs_nonneg σ, sq_nonneg r]
    rw [div_le_iff₀ hδ₀] at this
    linarith
  have hvΔ : ∀ y ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ v y - σ'| ≤ δ₀ * ‖y‖ ^ α := by
    intro y hy
    have hry := hmapsB hy
    have hU : IsOpen (ball (0 : E) r ∩ openHalfSpace ν) :=
      isOpen_ball.inter (isOpen_openHalfSpace ν)
    have hat : ContDiffAt ℝ 2 u (r • y) := hu2.contDiffAt (hU.mem_nhds hry)
    have e0 : v = fun y ↦ (u (r • y) - (0 : QuadPoly E).eval (r • y)) / N := by
      funext y; simp [hv]
    rw [e0, laplacian_rescale_sub 0 r N hat]
    have htr : (0 : QuadPoly E).trace = 0 := by simp [QuadPoly.trace]
    rw [htr, sub_zero, hσ', ← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hNpos,
      abs_of_nonneg (sq_nonneg r)]
    have hb := hΔ _ hry
    rw [hnorm, Real.mul_rpow hr.le (norm_nonneg _)] at hb
    have e : r ^ 2 * (H * (r ^ α * ‖y‖ ^ α)) = r ^ (2 + α) * H * ‖y‖ ^ α := by
      rw [Real.rpow_add hr, Real.rpow_two]; ring
    rw [div_le_iff₀ hNpos]
    have hHN : r ^ (2 + α) * H ≤ δ₀ * N := by nlinarith [Real.rpow_nonneg hr.le (2 + α)]
    calc r ^ 2 * |Δ u (r • y) - σ| ≤ r ^ 2 * (H * (r ^ α * ‖y‖ ^ α)) := by gcongr
      _ = r ^ (2 + α) * H * ‖y‖ ^ α := e
      _ ≤ δ₀ * N * ‖y‖ ^ α := by gcongr
      _ = δ₀ * ‖y‖ ^ α * N := by ring
  have hvN : ∀ y ∈ ball (0 : E) 1, y ∈ flatPart ν → ∃ d : ℝ,
      HasDerivWithinAt (fun t : ℝ ↦ v (y + t • ν)) d (Ici 0) 0 ∧
        |d| ≤ δ₀ * ‖y‖ ^ (1 + α) := by
    intro y hy hyf
    have hry : r • y ∈ ball (0 : E) r := by
      rw [mem_ball_zero_iff, hnorm]
      exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hy) hr).trans_eq (mul_one r)
    have hryf : r • y ∈ flatPart ν := by
      simp only [mem_flatPart, real_inner_smul_left, mem_flatPart.1 hyf, mul_zero]
    obtain ⟨d, hd, hdb⟩ := hNeu _ hry hryf
    have hlin : HasDerivWithinAt (fun t : ℝ ↦ r * t) r (Ici 0) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul r |>.hasDerivWithinAt
    have hmaps : MapsTo (fun t : ℝ ↦ r * t) (Ici 0) (Ici 0) := fun t ht ↦
      mul_nonneg hr.le ht
    have hd0 : HasDerivWithinAt (fun t : ℝ ↦ u (r • y + t • ν)) d (Ici 0) (r * 0) := by
      rw [mul_zero]; exact hd
    have hcomp := (hd0.comp (0 : ℝ) hlin hmaps).div_const N
    refine ⟨d * r / N, ?_, ?_⟩
    · convert hcomp using 2 with t
      simp only [hv, Function.comp_apply, smul_add, smul_smul]
    · rw [hnorm, Real.mul_rpow hr.le (norm_nonneg _)] at hdb
      have e : r * r ^ (1 + α) = r ^ (2 + α) := by
        rw [show (2 : ℝ) + α = 1 + (1 + α) by ring, Real.rpow_add hr 1 (1 + α), Real.rpow_one]
      have hGN : r ^ (2 + α) * G ≤ δ₀ * N := by nlinarith [Real.rpow_nonneg hr.le (2 + α)]
      rw [abs_div, abs_mul, abs_of_pos hr, abs_of_pos hNpos, div_le_iff₀ hNpos]
      have hyα : 0 ≤ ‖y‖ ^ (1 + α) := by positivity
      calc |d| * r ≤ G * (r ^ (1 + α) * ‖y‖ ^ (1 + α)) * r := by gcongr
        _ = r ^ (2 + α) * G * ‖y‖ ^ (1 + α) := by rw [← e]; ring
        _ ≤ δ₀ * N * ‖y‖ ^ (1 + α) := by gcongr
        _ = δ₀ * ‖y‖ ^ (1 + α) * N := by ring
  obtain ⟨P, hPtr, hPc, hPap⟩ := hexp hν hvc hv2 (QuadPoly.trace_isotropic σ')
    (isEvenPoly_isotropic ν σ') hv0 hvΔ hvN
  have hP0 : (QuadPoly.isotropic σ' : QuadPoly E).sumNorm ≤ 1 :=
    (QuadPoly.sumNorm_isotropic_le σ').trans (by
      have : 0 ≤ M₀ / N := div_nonneg hM₀0 hNpos.le
      linarith)
  refine ⟨N • P.rescale r⁻¹, ?_, ?_, fun z hzh hz ↦ ?_⟩
  · rw [QuadPoly.trace_smul, QuadPoly.trace_rescale, hPtr, hσ']
    field_simp
  · have e : |(N • P.rescale r⁻¹).const| + r * ‖(N • P.rescale r⁻¹).lin‖ +
        r ^ 2 * ‖(N • P.rescale r⁻¹).quad‖ = N * P.sumNorm := by
      simp only [QuadPoly.smul_const, QuadPoly.smul_lin, QuadPoly.smul_quad,
        QuadPoly.rescale_const, QuadPoly.rescale_lin, QuadPoly.rescale_quad, norm_smul,
        Real.norm_eq_abs, abs_mul, abs_of_pos hNpos, abs_inv, abs_of_pos hr, abs_pow,
        QuadPoly.sumNorm]
      field_simp
    rw [e]
    calc N * P.sumNorm ≤ N * max (1 + C₁) A :=
          mul_le_mul_of_nonneg_left ((hPc.trans (by linarith)).trans (le_max_left _ _)) hN0
      _ ≤ _ := hCN
  · set y : E := r⁻¹ • z with hy
    have hSy : r • y = z := by rw [hy, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hy1 : ‖y‖ < 1 := by
      rw [hy, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div,
        div_lt_one hr]
      exact hz
    have hyh : y ∈ halfSpace ν := by
      rw [hy, mem_halfSpace, real_inner_smul_left]
      exact mul_nonneg (inv_nonneg.2 hr.le) hzh
    have hyz : ‖y‖ = ‖z‖ / r := by
      rw [hy, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]
    have hap := hPap y hyh hy1
    simp only [hv, hSy] at hap
    have e : u z - (N • P.rescale r⁻¹).eval z = N * (u z / N - P.eval y) := by
      rw [QuadPoly.eval_smul, QuadPoly.eval_rescale, ← hy, mul_sub, mul_div_cancel₀ _ hNpos.ne']
    rw [e, abs_mul, abs_of_pos hNpos, ← hyz]
    have hyγ : 0 ≤ ‖y‖ ^ (2 + α) := Real.rpow_nonneg (norm_nonneg _) _
    calc N * |u z / N - P.eval y| ≤ N * (A * ‖y‖ ^ (2 + α)) := by gcongr
      _ ≤ N * max (1 + C₁) A * ‖y‖ ^ (2 + α) := by
          rw [← mul_assoc]; gcongr; exact le_max_right _ _
      _ ≤ K * max (1 + C₁) A * N₀ * ‖y‖ ^ (2 + α) := by gcongr

/-- **Scaled Dirichlet expansion on a half ball** (pointwise Hölder data at the centre). There is
`C = C(E, α) ≥ 0` such that: if `‖ν‖ = 1`, `u` is continuous on `halfBall ν 0 r`, `C²` in
`ball 0 r ∩ openHalfSpace ν`, `u = 0` on the flat part, `|u| ≤ M₀` and
`|Δu(z) − σ| ≤ H |z|^α` in the open half ball, then with `N = M₀ + r² |σ| + r^{2+α} H` there is a
quadratic `P` with `tr P = σ`, `|P(0)| + r ‖DP(0)‖ + r² ‖quad P‖ ≤ C N` and
`|u(z) − P(z)| ≤ C N (|z|/r)^{2+α}` for `z ∈ halfSpace ν`, `|z| < r`. -/
theorem expansion_halfBall_dirichlet {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ν : E}, ‖ν‖ = 1 → ∀ (u : E → ℝ) (r M₀ σ H : ℝ), 0 < r → 0 ≤ H →
      ContinuousOn u (halfBall ν 0 r) → ContDiffOn ℝ 2 u (ball 0 r ∩ openHalfSpace ν) →
      (∀ z ∈ halfBall ν (0 : E) r, |u z| ≤ M₀) →
      (∀ z ∈ ball (0 : E) r ∩ openHalfSpace ν, |Δ u z - σ| ≤ H * ‖z‖ ^ α) →
      (∀ z ∈ halfBall ν (0 : E) r, z ∈ flatPart ν → u z = 0) →
      ∃ P : QuadPoly E, P.trace = σ ∧
        |P.const| + r * ‖P.lin‖ + r ^ 2 * ‖P.quad‖ ≤
          C * (M₀ + r ^ 2 * |σ| + r ^ (2 + α) * H) ∧
        ∀ z ∈ halfSpace ν, ‖z‖ < r →
          |u z - P.eval z| ≤
            C * (M₀ + r ^ 2 * |σ| + r ^ (2 + α) * H) * (‖z‖ / r) ^ (2 + α) := by
  obtain ⟨δ₀, C₁, A, hδ₀, hC₁, hA, hexp⟩ := expansion_at_origin_dirichlet (E := E) hα
  set K : ℝ := max 1 (1 / δ₀) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKδ : 1 / δ₀ ≤ K := le_max_right _ _
  refine ⟨K * max (1 + C₁) A, by positivity,
    fun {ν} hν u r M₀ σ H hr hH hu hu2 hM₀ hΔ hD ↦ ?_⟩
  have h0mem : (0 : E) ∈ halfBall ν 0 r := ⟨mem_closedBall_self hr.le, by simp⟩
  have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0 h0mem)
  have hrγ : 0 < r ^ (2 + α) := Real.rpow_pos_of_pos hr _
  set N₀ : ℝ := M₀ + r ^ 2 * |σ| + r ^ (2 + α) * H with hN₀
  set N : ℝ := M₀ + r ^ 2 * |σ| + r ^ (2 + α) * H / δ₀ with hN
  have hN0 : 0 ≤ N := by positivity
  have hNN₀ : N ≤ K * N₀ := by
    have h1 : r ^ (2 + α) * H / δ₀ ≤ K * (r ^ (2 + α) * H) := by
      rw [div_eq_mul_one_div, mul_comm K]
      exact mul_le_mul_of_nonneg_left hKδ (by positivity)
    have h2 : M₀ + r ^ 2 * |σ| ≤ K * (M₀ + r ^ 2 * |σ|) := le_mul_of_one_le_left (by positivity) hK1
    rw [hN, hN₀]; nlinarith
  have hCN : N * max (1 + C₁) A ≤ K * max (1 + C₁) A * N₀ := by
    have := mul_le_mul_of_nonneg_right hNN₀ (le_max_of_le_right hA : (0 : ℝ) ≤ max (1 + C₁) A)
    linarith
  have hN₀0 : 0 ≤ N₀ := by positivity
  rcases hN0.eq_or_lt with hN0' | hNpos
  · have hM : M₀ = 0 := by
      have : 0 ≤ r ^ 2 * |σ| := by positivity
      have : 0 ≤ r ^ (2 + α) * H / δ₀ := by positivity
      linarith
    have hσ : σ = 0 := by
      have h1 : r ^ 2 * |σ| = 0 := by
        have : 0 ≤ r ^ (2 + α) * H / δ₀ := by positivity
        have : 0 ≤ r ^ 2 * |σ| := by positivity
        linarith
      simpa [hr.ne'] using h1
    refine ⟨0, by simp [QuadPoly.trace, hσ], by
      simp only [QuadPoly.zero_const, abs_zero, QuadPoly.zero_lin, norm_zero, mul_zero,
        add_zero, QuadPoly.zero_quad]
      positivity, fun z hzh hz ↦ ?_⟩
    rw [QuadPoly.eval_zero_poly, sub_zero]
    exact (hM₀ z ⟨mem_closedBall_zero_iff.2 hz.le, hzh⟩).trans (by rw [hM]; positivity)
  have hnorm : ∀ y : E, ‖r • y‖ = r * ‖y‖ := fun y ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hmapsC : MapsTo (fun y : E ↦ r • y) (halfBall ν 0 1) (halfBall ν 0 r) := fun y hy ↦ by
    simpa using smul_mem_halfBall hr hy
  have hmapsB : MapsTo (fun y : E ↦ r • y) (ball 0 1 ∩ openHalfSpace ν)
      (ball 0 r ∩ openHalfSpace ν) := fun y hy ↦ by
    simpa using smul_mem_ball_inter_openHalfSpace hr hy
  set v : E → ℝ := fun y ↦ u (r • y) / N with hv
  have hsc : ContDiff ℝ 2 fun y : E ↦ r • y := contDiff_const_smul r
  have hvc : ContinuousOn v (halfBall ν 0 1) :=
    (hu.comp hsc.continuous.continuousOn hmapsC).div_const _
  have hv2 : ContDiffOn ℝ 2 v (ball 0 1 ∩ openHalfSpace ν) :=
    (hu2.comp hsc.contDiffOn hmapsB).div_const _
  set σ' : ℝ := r ^ 2 * σ / N with hσ'
  have hσ'abs : |σ'| = r ^ 2 * |σ| / N := by
    rw [hσ', abs_div, abs_mul, abs_of_pos hNpos, abs_of_nonneg (sq_nonneg r)]
  have hσ'1 : M₀ / N + |σ'| ≤ 1 := by
    rw [hσ'abs, ← add_div, div_le_one hNpos, hN]
    have : 0 ≤ r ^ (2 + α) * H / δ₀ := by positivity
    linarith
  have hv0 : ∀ y ∈ halfBall ν (0 : E) 1,
      |v y - (QuadPoly.normalSq ν σ').eval y| ≤ 1 := by
    intro y hy
    have h1 : |v y| ≤ M₀ / N := by
      rw [hv, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right (hM₀ _ (hmapsC hy)) hNpos.le
    have h2 := QuadPoly.abs_eval_normalSq_le hν σ' y
    have hy1 : ‖y‖ ^ 2 ≤ 1 := by
      have := mem_closedBall_zero_iff.1 hy.1
      nlinarith [norm_nonneg y]
    have h3 : |σ'| * ‖y‖ ^ 2 ≤ |σ'| := mul_le_of_le_one_right (abs_nonneg _) hy1
    calc _ ≤ |v y| + |(QuadPoly.normalSq ν σ').eval y| := abs_sub _ _
      _ ≤ 1 := by linarith
  have hvΔ : ∀ y ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ v y - σ'| ≤ δ₀ * ‖y‖ ^ α := by
    intro y hy
    have hry := hmapsB hy
    have hU : IsOpen (ball (0 : E) r ∩ openHalfSpace ν) :=
      isOpen_ball.inter (isOpen_openHalfSpace ν)
    have hat : ContDiffAt ℝ 2 u (r • y) := hu2.contDiffAt (hU.mem_nhds hry)
    have e0 : v = fun y ↦ (u (r • y) - (0 : QuadPoly E).eval (r • y)) / N := by
      funext y; simp [hv]
    rw [e0, laplacian_rescale_sub 0 r N hat]
    have htr : (0 : QuadPoly E).trace = 0 := by simp [QuadPoly.trace]
    rw [htr, sub_zero, hσ', ← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hNpos,
      abs_of_nonneg (sq_nonneg r)]
    have hb := hΔ _ hry
    rw [hnorm, Real.mul_rpow hr.le (norm_nonneg _)] at hb
    have hNH : r ^ (2 + α) * H ≤ δ₀ * N := by
      have : r ^ (2 + α) * H / δ₀ ≤ N := by
        rw [hN]; nlinarith [abs_nonneg σ, sq_nonneg r]
      rw [div_le_iff₀ hδ₀] at this
      linarith
    have e : r ^ 2 * (H * (r ^ α * ‖y‖ ^ α)) = r ^ (2 + α) * H * ‖y‖ ^ α := by
      rw [Real.rpow_add hr, Real.rpow_two]; ring
    rw [div_le_iff₀ hNpos]
    calc r ^ 2 * |Δ u (r • y) - σ| ≤ r ^ 2 * (H * (r ^ α * ‖y‖ ^ α)) := by gcongr
      _ = r ^ (2 + α) * H * ‖y‖ ^ α := e
      _ ≤ δ₀ * N * ‖y‖ ^ α := by gcongr
      _ = δ₀ * ‖y‖ ^ α * N := by ring
  have hvD : ∀ y ∈ halfBall ν (0 : E) 1, y ∈ flatPart ν → v y = 0 := by
    intro y hy hyf
    have hryf : r • y ∈ flatPart ν := by
      simp only [mem_flatPart, real_inner_smul_left, mem_flatPart.1 hyf, mul_zero]
    simp [hv, hD _ (hmapsC hy) hryf]
  obtain ⟨P, hPtr, hPc, hPap⟩ := hexp hν hvc hv2 (QuadPoly.trace_normalSq hν σ')
    (QuadPoly.vanishesOnFlat_normalSq ν σ') hv0 hvΔ hvD
  have hP0 : (QuadPoly.normalSq ν σ').sumNorm ≤ 1 :=
    (QuadPoly.sumNorm_normalSq_le hν σ').trans (by
      have : 0 ≤ M₀ / N := div_nonneg hM₀0 hNpos.le
      linarith)
  refine ⟨N • P.rescale r⁻¹, ?_, ?_, fun z hzh hz ↦ ?_⟩
  · rw [QuadPoly.trace_smul, QuadPoly.trace_rescale, hPtr, hσ']
    field_simp
  · have e : |(N • P.rescale r⁻¹).const| + r * ‖(N • P.rescale r⁻¹).lin‖ +
        r ^ 2 * ‖(N • P.rescale r⁻¹).quad‖ = N * P.sumNorm := by
      simp only [QuadPoly.smul_const, QuadPoly.smul_lin, QuadPoly.smul_quad,
        QuadPoly.rescale_const, QuadPoly.rescale_lin, QuadPoly.rescale_quad, norm_smul,
        Real.norm_eq_abs, abs_mul, abs_of_pos hNpos, abs_inv, abs_of_pos hr, abs_pow,
        QuadPoly.sumNorm]
      field_simp
    rw [e]
    calc N * P.sumNorm ≤ N * max (1 + C₁) A :=
          mul_le_mul_of_nonneg_left ((hPc.trans (by linarith)).trans (le_max_left _ _)) hN0
      _ ≤ _ := hCN
  · set y : E := r⁻¹ • z with hy
    have hSy : r • y = z := by rw [hy, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hy1 : ‖y‖ < 1 := by
      rw [hy, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div,
        div_lt_one hr]
      exact hz
    have hyh : y ∈ halfSpace ν := by
      rw [hy, mem_halfSpace, real_inner_smul_left]
      exact mul_nonneg (inv_nonneg.2 hr.le) hzh
    have hyz : ‖y‖ = ‖z‖ / r := by
      rw [hy, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]
    have hap := hPap y hyh hy1
    simp only [hv, hSy] at hap
    have e : u z - (N • P.rescale r⁻¹).eval z = N * (u z / N - P.eval y) := by
      rw [QuadPoly.eval_smul, QuadPoly.eval_rescale, ← hy, mul_sub, mul_div_cancel₀ _ hNpos.ne']
    rw [e, abs_mul, abs_of_pos hNpos, ← hyz]
    have hyγ : 0 ≤ ‖y‖ ^ (2 + α) := Real.rpow_nonneg (norm_nonneg _) _
    calc N * |u z / N - P.eval y| ≤ N * (A * ‖y‖ ^ (2 + α)) := by gcongr
      _ ≤ N * max (1 + C₁) A * ‖y‖ ^ (2 + α) := by
          rw [← mul_assoc]; gcongr; exact le_max_right _ _
      _ ≤ K * max (1 + C₁) A * N₀ * ‖y‖ ^ (2 + α) := by gcongr

end Nondiv

end BasicElliptic
