/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Boundary.Scaled
public import BasicElliptic.Nondiv.Interior.Freeze

/-!
# Freezing the coefficients at a flat point

Let `ν` be a unit vector, `x₀ ∈ flatPart ν`, `B_R⁺(x₀) = halfBall ν x₀ R` and `U = ball x₀ R ∩
openHalfSpace ν`. Let `u` be continuous on `B_R⁺(x₀)`, `C²` in `U`, and solve `tr (a D²u) = F` in
`U` (first-order terms are absorbed into `F` by the caller). With `a₀ = a(x₀)`:
```
tr (a₀ D²u) = F − tr ((a − a₀) D²u),
```
whose right side is Hölder **at `x₀`** with constant `K_F + d K_a M₂` (`M₂ ≥ sup_U ‖D²u‖`).

The normalization `T z = x₀ + M z` with `M M† = sym a₀`, `⟪M z, ν⟫ = m ⟪z, ν⟫`
(`exists_halfSpace_sqrt`) maps `halfBall ν 0 (R/√Λ)` into `B_R⁺(x₀)`, preserves the
flat part, and turns `tr (a₀ D²)` into the Laplacian (the skew part of `a₀` drops out). Moreover
`M ν = (sym a₀) ν / m`, so the normal derivative of `u ∘ T` is `1/m` times the derivative of `u`
along the conormal `(sym a₀) ν`.

* `Nondiv.expansion_at_flat_point_dirichlet`: if `u = 0` on the flat part, there is a quadratic `P`
  with `tr (a₀ D²P) = F(x₀)`, `|P(0)| + R ‖DP(0)‖ + R² ‖quad P‖ ≤ C N` and
  `|u(y) − P(y − x₀)| ≤ C N (|y − x₀| / R)^{2+α}` for `y ∈ halfSpace ν`, `|y − x₀| < κ R`, where
  `N = M₀ + R² M_F + R^{2+α} (K_F + d K_a M₂)` and `C, κ` depend only on `E, α, lam, Λ`.
* `Nondiv.expansion_at_flat_point_conormal`: if `a₀` is symmetric and the derivative of `u` along
  the conormal `a₀ ν` at flat points `y` is bounded by `G |y − x₀|^{1+α}`, the same holds with
  `N = M₀ + R² M_F + R^{2+α} (K_F + d K_a M₂ + G)`.
-/

public section

open Metric Set Filter Topology Module InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Half-space-preserving normalization of a nonsymmetric coefficient.** If
`lam ‖ξ‖² ≤ ⟪a₀ ξ, ξ⟫` and `‖a₀‖ ≤ Λ`, there is `M` with `‖M‖ ≤ √Λ`, `‖M⁻¹‖ ≤ 1/√lam`,
`⟪M z, ν⟫ = m ⟪z, ν⟫` for some `m ∈ [√lam, √Λ]`, `m • M ν = (sym a₀) ν`, and
`M⁻¹ a₀ M⁻† = I + K` with `K` skew. -/
theorem exists_halfSpace_normalization {a₀ : E →L[ℝ] E} {ν : E} (hν : ‖ν‖ = 1) {lam Λ : ℝ}
    (hlam : 0 < lam) (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a₀ ξ, ξ⟫) (hbd : ‖a₀‖ ≤ Λ) :
    ∃ (M : E ≃L[ℝ] E) (m : ℝ) (K : E →L[ℝ] E), √lam ≤ m ∧ m ≤ √Λ ∧
      (∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫) ∧ m • M ν = symPart a₀ ν ∧
      ‖(M : E →L[ℝ] E)‖ ≤ √Λ ∧ ‖(M.symm : E →L[ℝ] E)‖ ≤ 1 / √lam ∧
      (M.symm : E →L[ℝ] E) ∘L a₀ ∘L adjoint (M.symm : E →L[ℝ] E) = 1 + K ∧
      adjoint K = -K := by
  obtain ⟨M, hM, ⟨m, hm1, hm2, hmν⟩, hMn, hMn'⟩ := exists_halfSpace_sqrt hν hlam
    (isSymmetric_symPart a₀) (fun ξ ↦ (inner_symPart_self a₀ ξ).symm ▸ hell ξ)
    ((norm_symPart_le a₀).trans hbd)
  set K := (M.symm : E →L[ℝ] E) ∘L skewPart a₀ ∘L adjoint (M.symm : E →L[ℝ] E)
  have hadjν : adjoint (M : E →L[ℝ] E) ν = m • ν := by
    refine ext_inner_left ℝ fun z ↦ ?_
    rw [adjoint_inner_right, real_inner_smul_right, real_inner_comm, ← hmν]
    exact real_inner_comm _ _
  refine ⟨M, m, K, hm1, hm2, hmν, ?_, hMn, hMn', ?_, ?_⟩
  · have := congrArg (fun A : E →L[ℝ] E ↦ A ν) hM
    simp only [coe_comp, Function.comp_apply, hadjν, map_smul] at this
    exact this
  · rw [← symm_comp_comp_adjoint_symm_eq_one hM]
    conv_lhs => rw [← symPart_add_skewPart a₀]
    rw [add_comp, comp_add]
  · simp only [K]
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint, adjoint_skewPart]
    ext; simp

/-- The trace of the Hessian of a polynomial against `a₀` after the normalization: if
`M⁻¹ a₀ M⁻† = I + K` with `K` skew, then `∑ᵢ D²(P ∘ M⁻¹)(a₀ eᵢ, eᵢ) = tr P`. -/
theorem sum_hess_compCLM_eq_trace (P : QuadPoly E) (a₀ : E →L[ℝ] E) (M : E ≃L[ℝ] E)
    (K : E →L[ℝ] E)
    (hconj : (M.symm : E →L[ℝ] E) ∘L a₀ ∘L adjoint (M.symm : E →L[ℝ] E) = 1 + K)
    (hK : adjoint K = -K) :
    ∑ i, (P.compCLM (M.symm : E →L[ℝ] E)).hess (a₀ (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i) = P.trace := by
  set Q := P.compCLM (M.symm : E →L[ℝ] E)
  have h := laplacian_comp_affine_eq_frozen isOpen_univ (Q.contDiff_eval.contDiffOn) a₀ M K
    hconj hK 0 (z := 0) (mem_univ _)
  simp only [zero_add, map_zero, QuadPoly.fderiv_fderiv_eval] at h
  rw [← h]
  have e : (fun z ↦ Q.eval (M z)) = P.eval := funext fun z ↦ by
    simp [Q, QuadPoly.eval_compCLM]
  rw [e, QuadPoly.laplacian_eval]

omit [FiniteDimensional ℝ E] in
private theorem norm_le_sqrt_mul {M : E ≃L[ℝ] E} {Λ : ℝ} (hMn : ‖(M : E →L[ℝ] E)‖ ≤ √Λ)
    (z : E) : ‖M z‖ ≤ √Λ * ‖z‖ :=
  ((M : E →L[ℝ] E).le_opNorm z).trans (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))

omit [FiniteDimensional ℝ E] in
private theorem norm_symm_le_div {M : E ≃L[ℝ] E} {lam : ℝ}
    (hMn' : ‖(M.symm : E →L[ℝ] E)‖ ≤ 1 / √lam) (y : E) : ‖M.symm y‖ ≤ ‖y‖ / √lam := by
  have := ((M.symm : E →L[ℝ] E).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right hMn' (norm_nonneg _))
  simpa [one_div, div_eq_inv_mul] using this

/-- The normalized function and its frozen equation (shared by the Dirichlet and conormal
cases). -/
private theorem normalized_laplacian_bound {α : ℝ} (hα : 0 < α ∧ α < 1) {Λ : ℝ} {ν : E}
    {a : E → E →L[ℝ] E} {F u : E → ℝ} {x₀ : E} {R Ka KF M₂ : ℝ}
    (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF) (hM₂ : 0 ≤ M₂)
    {M : E ≃L[ℝ] E} {K : E →L[ℝ] E}
    (hconj : (M.symm : E →L[ℝ] E) ∘L a x₀ ∘L adjoint (M.symm : E →L[ℝ] E) = 1 + K)
    (hK : adjoint K = -K)
    (hu2 : ContDiffOn ℝ 2 u (ball x₀ R ∩ openHalfSpace ν))
    (heq : ∀ y ∈ ball x₀ R ∩ openHalfSpace ν,
      ∑ i, fderiv ℝ (fderiv ℝ u) y (a y (stdOrthonormalBasis ℝ E i))
        (stdOrthonormalBasis ℝ E i) = F y)
    (ha : ∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖a y - a x₀‖ ≤ Ka * dist y x₀ ^ α)
    (hF : ∀ y ∈ ball x₀ R ∩ openHalfSpace ν, |F y - F x₀| ≤ KF * dist y x₀ ^ α)
    (hD2 : ∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M₂)
    (hMz : ∀ z, ‖M z‖ ≤ √Λ * ‖z‖) {z : E}
    (hz : x₀ + M z ∈ ball x₀ R ∩ openHalfSpace ν) :
    |Δ (fun z ↦ u (x₀ + M z)) z - F x₀| ≤
      (KF + finrank ℝ E * Ka * M₂) * √Λ ^ α * ‖z‖ ^ α := by
  set e := stdOrthonormalBasis ℝ E
  have hU : IsOpen (ball x₀ R ∩ openHalfSpace ν) := isOpen_ball.inter (isOpen_openHalfSpace ν)
  rw [laplacian_comp_affine_eq_frozen hU hu2 (a x₀) M K hconj hK x₀ hz]
  set y := x₀ + M z
  have hs : ∀ i, fderiv ℝ (fderiv ℝ u) y (a y (e i)) (e i) =
      fderiv ℝ (fderiv ℝ u) y (a x₀ (e i)) (e i) +
        fderiv ℝ (fderiv ℝ u) y ((a y - a x₀) (e i)) (e i) := fun i ↦ by
    rw [← add_apply, ← map_add, ← add_apply, add_sub_cancel]
  have h1 := heq y hz
  rw [Finset.sum_congr rfl fun i _ ↦ hs i, Finset.sum_add_distrib] at h1
  have h3 : |∑ i, fderiv ℝ (fderiv ℝ u) y ((a y - a x₀) (e i)) (e i)| ≤
      finrank ℝ E * Ka * M₂ * dist y x₀ ^ α := by
    refine (abs_sum_apply_le _ _).trans ?_
    have := mul_le_mul (hD2 y hz) (ha y hz) (norm_nonneg _) hM₂
    have hdim : (0 : ℝ) ≤ finrank ℝ E := by positivity
    calc (finrank ℝ E : ℝ) * (‖fderiv ℝ (fderiv ℝ u) y‖ * ‖a y - a x₀‖) ≤
          finrank ℝ E * (M₂ * (Ka * dist y x₀ ^ α)) := by gcongr
      _ = _ := by ring
  have h2 := hF y hz
  have hdist : dist y x₀ = ‖M z‖ := by simp [y, dist_eq_norm]
  have hle : dist y x₀ ^ α ≤ √Λ ^ α * ‖z‖ ^ α := by
    rw [hdist, ← Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hMz z) hα.1.le
  have hrw : ∑ i, fderiv ℝ (fderiv ℝ u) y (a x₀ (e i)) (e i) - F x₀ =
      (F y - F x₀) - ∑ i, fderiv ℝ (fderiv ℝ u) y ((a y - a x₀) (e i)) (e i) := by linarith
  rw [hrw]
  have hd0 : 0 ≤ dist y x₀ ^ α := Real.rpow_nonneg dist_nonneg _
  calc _ ≤ |F y - F x₀| + |∑ i, fderiv ℝ (fderiv ℝ u) y ((a y - a x₀) (e i)) (e i)| :=
        abs_sub _ _
    _ ≤ (KF + finrank ℝ E * Ka * M₂) * dist y x₀ ^ α := by nlinarith
    _ ≤ (KF + finrank ℝ E * Ka * M₂) * (√Λ ^ α * ‖z‖ ^ α) := by
        gcongr
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
/-- Pulling the normalized expansion back to the original coordinates. -/
private theorem pullback_expansion {α lam Λ : ℝ} (hα : 0 < α ∧ α < 1) (hlam : 0 < lam)
    (hlamΛ : lam ≤ Λ) {M : E ≃L[ℝ] E} (hMn' : ‖(M.symm : E →L[ℝ] E)‖ ≤ 1 / √lam)
    {ν x₀ : E} {u : E → ℝ} {m : ℝ}
    (hx₀ : ⟪x₀, ν⟫ = 0) (hm : 0 < m) (hmν : ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫)
    {R C₀ N' N K₁ : ℝ} (hR : 0 < R) (hC₀ : 0 ≤ C₀) (hN0 : 0 ≤ N)
    (hK₁ : 0 ≤ K₁) (hN'N : N' ≤ K₁ * N) {P' : QuadPoly E}
    (hc : |P'.const| + R / √Λ * ‖P'.lin‖ + (R / √Λ) ^ 2 * ‖P'.quad‖ ≤ C₀ * N')
    (hap : ∀ z ∈ halfSpace ν, ‖z‖ < R / √Λ →
      |u (x₀ + M z) - P'.eval z| ≤ C₀ * N' * (‖z‖ / (R / √Λ)) ^ (2 + α)) :
    |(P'.compCLM (M.symm : E →L[ℝ] E)).const| +
        R * ‖(P'.compCLM (M.symm : E →L[ℝ] E)).lin‖ +
        R ^ 2 * ‖(P'.compCLM (M.symm : E →L[ℝ] E)).quad‖ ≤
      C₀ * K₁ * (1 + √Λ / √lam + (√Λ / √lam) ^ 2 + (√Λ / √lam) ^ (2 + α)) * N ∧
    ∀ y ∈ halfSpace ν, dist y x₀ < √lam / √Λ * R →
      |u y - (P'.compCLM (M.symm : E →L[ℝ] E)).eval (y - x₀)| ≤
        C₀ * K₁ * (1 + √Λ / √lam + (√Λ / √lam) ^ 2 + (√Λ / √lam) ^ (2 + α)) * N *
          (dist y x₀ / R) ^ (2 + α) := by
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  set s := √Λ with hs_def
  set t := √lam with ht_def
  have hs : 0 < s := Real.sqrt_pos.2 hΛ
  have ht : 0 < t := Real.sqrt_pos.2 hlam
  have hts : t ≤ s := Real.sqrt_le_sqrt hlamΛ
  set Q := s / t with hQ_def
  have hQ1 : 1 ≤ Q := (one_le_div ht).2 hts
  set r := R / s with hr_def
  have hr : 0 < r := by positivity
  set P := P'.compCLM (M.symm : E →L[ℝ] E) with hP
  have hCQ : 0 ≤ C₀ * K₁ := by positivity
  refine ⟨?_, fun y hy hyd ↦ ?_⟩
  · have hl : ‖P.lin‖ ≤ ‖P'.lin‖ / t := by
      refine (P'.norm_lin_compCLM_le _).trans ?_
      calc ‖P'.lin‖ * ‖(M.symm : E →L[ℝ] E)‖ ≤ ‖P'.lin‖ * (1 / t) := by gcongr
        _ = ‖P'.lin‖ / t := by ring
    have hq : ‖P.quad‖ ≤ ‖P'.quad‖ / t ^ 2 := by
      refine (P'.norm_quad_compCLM_le _).trans ?_
      calc ‖P'.quad‖ * ‖(M.symm : E →L[ℝ] E)‖ * ‖(M.symm : E →L[ℝ] E)‖ ≤
            ‖P'.quad‖ * (1 / t) * (1 / t) := by gcongr
        _ = ‖P'.quad‖ / t ^ 2 := by ring
    have hc0 : P.const = P'.const := rfl
    have hRt : R / t = Q * r := by rw [hQ_def, hr_def]; field_simp
    have hRt2 : R ^ 2 / t ^ 2 = Q ^ 2 * r ^ 2 := by rw [← div_pow, hRt, mul_pow]
    have hQγ : 0 ≤ Q ^ (2 + α) := by positivity
    calc |P.const| + R * ‖P.lin‖ + R ^ 2 * ‖P.quad‖ ≤
          |P'.const| + R * (‖P'.lin‖ / t) + R ^ 2 * (‖P'.quad‖ / t ^ 2) := by
          rw [hc0]; gcongr
      _ = |P'.const| + Q * (r * ‖P'.lin‖) + Q ^ 2 * (r ^ 2 * ‖P'.quad‖) := by
          rw [show R * (‖P'.lin‖ / t) = R / t * ‖P'.lin‖ by ring,
            show R ^ 2 * (‖P'.quad‖ / t ^ 2) = R ^ 2 / t ^ 2 * ‖P'.quad‖ by ring, hRt, hRt2]
          ring
      _ ≤ (1 + Q + Q ^ 2 + Q ^ (2 + α)) * (|P'.const| + r * ‖P'.lin‖ + r ^ 2 * ‖P'.quad‖) := by
          have h1 : 0 ≤ r * ‖P'.lin‖ := by positivity
          have h2 : 0 ≤ r ^ 2 * ‖P'.quad‖ := by positivity
          have h0 : 0 ≤ |P'.const| := abs_nonneg _
          nlinarith [sq_nonneg Q]
      _ ≤ (1 + Q + Q ^ 2 + Q ^ (2 + α)) * (C₀ * N') := by gcongr
      _ ≤ (1 + Q + Q ^ 2 + Q ^ (2 + α)) * (C₀ * (K₁ * N)) := by gcongr
      _ = C₀ * K₁ * (1 + Q + Q ^ 2 + Q ^ (2 + α)) * N := by ring
  · set z := M.symm (y - x₀) with hz_def
    have hTz : x₀ + M z = y := by rw [hz_def, M.apply_symm_apply, add_sub_cancel]
    have hzn : ‖z‖ ≤ dist y x₀ / t := by
      rw [dist_eq_norm]; exact norm_symm_le_div hMn' _
    have hzr : ‖z‖ < r := by
      refine hzn.trans_lt ?_
      rw [div_lt_iff₀ ht]
      calc dist y x₀ < t / s * R := hyd
        _ = r * t := by rw [hr_def]; ring
    have hzh : z ∈ halfSpace ν := by
      have h1 : ⟪y, ν⟫ = m * ⟪z, ν⟫ := by rw [← hTz, inner_add_left, hx₀, hmν, zero_add]
      have h2 : 0 ≤ ⟪y, ν⟫ := hy
      rw [mem_halfSpace]
      by_contra h3
      have h4 := not_le.1 h3
      nlinarith
    have hPe : P.eval (y - x₀) = P'.eval z := by
      rw [hP, QuadPoly.eval_compCLM]; rfl
    have hb' := hap z hzh hzr
    rw [hTz] at hb'
    rw [hPe]
    have hzr' : ‖z‖ / r ≤ Q * (dist y x₀ / R) := by
      rw [div_le_iff₀ hr]
      calc ‖z‖ ≤ dist y x₀ / t := hzn
        _ = Q * (dist y x₀ / R) * r := by rw [hQ_def, hr_def]; field_simp
    have hdγ : 0 ≤ (dist y x₀ / R) ^ (2 + α) := by positivity
    calc |u y - P'.eval z| ≤ C₀ * N' * (‖z‖ / r) ^ (2 + α) := hb'
      _ ≤ C₀ * (K₁ * N) * (Q * (dist y x₀ / R)) ^ (2 + α) := by
          gcongr
          linarith [hα.1]
      _ = C₀ * K₁ * Q ^ (2 + α) * N * (dist y x₀ / R) ^ (2 + α) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
      _ ≤ C₀ * K₁ * (1 + Q + Q ^ 2 + Q ^ (2 + α)) * N * (dist y x₀ / R) ^ (2 + α) := by
          gcongr
          nlinarith [sq_nonneg Q]

variable [Nontrivial E]

/-- **Pointwise expansion at a flat point, Dirichlet case**. Let `0 < α < 1` and
`0 < lam ≤ Λ`. There are `C ≥ 0` and `κ > 0`, depending only on `E, α, lam, Λ`, such that the
following holds. Let `‖ν‖ = 1`, `x₀ ∈ flatPart ν`, and let `u` be continuous on `halfBall ν x₀ R`,
`C²` in `U = ball x₀ R ∩ openHalfSpace ν`, with `tr (a D²u) = F` in `U` and `u = 0` on the flat
part. Assume `a(x₀)` elliptic (`lam`, `Λ`), `‖a − a(x₀)‖ ≤ K_a |· − x₀|^α` and
`|F − F(x₀)| ≤ K_F |· − x₀|^α` in `U`, `|F(x₀)| ≤ M_F`, `|u| ≤ M₀` and `‖D²u‖ ≤ M₂`. Put
`N = M₀ + R² M_F + R^{2+α} (K_F + d K_a M₂)`. Then there is a quadratic `P` with
`tr (a(x₀) D²P) = F(x₀)`, `|P(0)| + R ‖DP(0)‖ + R² ‖quad P‖ ≤ C N` and
`|u(y) − P(y − x₀)| ≤ C N (|y − x₀| / R)^{2+α}` for `y ∈ halfSpace ν`, `|y − x₀| < κ R`. -/
theorem expansion_at_flat_point_dirichlet {α : ℝ} (hα : 0 < α ∧ α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ {ν : E}, ‖ν‖ = 1 → ∀ (a : E → E →L[ℝ] E) (F u : E → ℝ)
      (x₀ : E) (R M₀ M₂ MF Ka KF : ℝ), x₀ ∈ flatPart ν → 0 < R → 0 ≤ Ka → 0 ≤ KF → 0 ≤ M₂ →
      ContinuousOn u (halfBall ν x₀ R) → ContDiffOn ℝ 2 u (ball x₀ R ∩ openHalfSpace ν) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ∑ i, fderiv ℝ (fderiv ℝ u) y
        (a y (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F y) →
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x₀ ξ, ξ⟫) → ‖a x₀‖ ≤ Λ →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖a y - a x₀‖ ≤ Ka * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, |F y - F x₀| ≤ KF * dist y x₀ ^ α) →
      |F x₀| ≤ MF → (∀ y ∈ halfBall ν x₀ R, |u y| ≤ M₀) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M₂) →
      (∀ y ∈ halfBall ν x₀ R, y ∈ flatPart ν → u y = 0) →
      ∃ P : QuadPoly E,
        ∑ i, P.hess (a x₀ (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F x₀ ∧
        |P.const| + R * ‖P.lin‖ + R ^ 2 * ‖P.quad‖ ≤
          C * (M₀ + R ^ 2 * MF + R ^ (2 + α) * (KF + finrank ℝ E * Ka * M₂)) ∧
        ∀ y ∈ halfSpace ν, dist y x₀ < κ * R →
          |u y - P.eval (y - x₀)| ≤
            C * (M₀ + R ^ 2 * MF + R ^ (2 + α) * (KF + finrank ℝ E * Ka * M₂)) *
              (dist y x₀ / R) ^ (2 + α) := by
  obtain ⟨C₀, hC₀, hexp⟩ := expansion_halfBall_dirichlet (E := E) hα
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  set K₁ := max 1 (1 / lam) with hK₁
  have hK₁1 : 1 ≤ K₁ := le_max_left _ _
  set Q := √Λ / √lam with hQ
  refine ⟨C₀ * K₁ * (1 + Q + Q ^ 2 + Q ^ (2 + α)), √lam / √Λ, by positivity, by positivity,
    ?_⟩
  intro ν hν a F u x₀ R M₀ M₂ MF Ka KF hx₀ hR hKa hKF hM₂ huc hu2 heq hell hbd ha hF hFx hM₀
    hD2 hD
  have hx₀' : ⟪x₀, ν⟫ = 0 := hx₀
  obtain ⟨M, m, K, hm1, hm2, hmν, -, hMn, hMn', hconj, hK⟩ :=
    exists_halfSpace_normalization hν hlam hell hbd
  have hm : 0 < m := (Real.sqrt_pos.2 hlam).trans_le hm1
  have hs : 0 < √Λ := Real.sqrt_pos.2 hΛ
  set r := R / √Λ with hr_def
  have hr : 0 < r := by positivity
  have hsr : √Λ * r = R := by rw [hr_def]; field_simp
  have hMz := norm_le_sqrt_mul hMn
  have hdist : ∀ z, dist (x₀ + M z) x₀ = ‖M z‖ := fun z ↦ by
    rw [dist_eq_norm, add_sub_cancel_left]
  have hinner : ∀ z, ⟪x₀ + M z, ν⟫ = m * ⟪z, ν⟫ := fun z ↦ by
    rw [inner_add_left, hx₀', hmν, zero_add]
  have hmapsC : MapsTo (fun z ↦ x₀ + M z) (halfBall ν 0 r) (halfBall ν x₀ R) := fun z hz ↦ by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, hdist, ← hsr]
      exact (hMz z).trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hz.1) hs.le)
    · rw [mem_halfSpace, hinner]; exact mul_nonneg hm.le hz.2
  have hmapsB : MapsTo (fun z ↦ x₀ + M z) (ball 0 r ∩ openHalfSpace ν)
      (ball x₀ R ∩ openHalfSpace ν) := fun z hz ↦ by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, hdist, ← hsr]
      exact (hMz z).trans_lt (mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hz.1) hs)
    · rw [mem_openHalfSpace, hinner]; exact mul_pos hm hz.2
  have hT : ContDiff ℝ 2 fun z ↦ x₀ + M z := contDiff_const.add M.contDiff
  set ũ : E → ℝ := fun z ↦ u (x₀ + M z) with hũ
  have hũc : ContinuousOn ũ (halfBall ν 0 r) := huc.comp hT.continuous.continuousOn hmapsC
  have hũ2 : ContDiffOn ℝ 2 ũ (ball 0 r ∩ openHalfSpace ν) :=
    hu2.comp hT.contDiffOn hmapsB
  set H₀ := KF + finrank ℝ E * Ka * M₂ with hH₀
  have hH₀0 : 0 ≤ H₀ := by positivity
  have hΔ : ∀ z ∈ ball (0 : E) r ∩ openHalfSpace ν, |Δ ũ z - F x₀| ≤ H₀ * √Λ ^ α * ‖z‖ ^ α :=
    fun z hz ↦ normalized_laplacian_bound hα hKa hKF hM₂ hconj hK hu2 heq ha hF hD2 hMz
      (hmapsB hz)
  have hũD : ∀ z ∈ halfBall ν (0 : E) r, z ∈ flatPart ν → ũ z = 0 := fun z hz hzf ↦ by
    refine hD _ (hmapsC hz) ?_
    rw [mem_flatPart, hinner, mem_flatPart.1 hzf, mul_zero]
  obtain ⟨P', hP'tr, hP'c, hP'e⟩ := hexp hν ũ r M₀ (F x₀) (H₀ * √Λ ^ α) hr (by positivity)
    hũc hũ2 (fun z hz ↦ hM₀ _ (hmapsC hz)) hΔ hũD
  set N' := M₀ + r ^ 2 * |F x₀| + r ^ (2 + α) * (H₀ * √Λ ^ α) with hN'
  set N := M₀ + R ^ 2 * MF + R ^ (2 + α) * H₀ with hN
  have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ x₀ ⟨mem_closedBall_self hR.le, hx₀'.ge⟩)
  have hMF : 0 ≤ MF := (abs_nonneg _).trans hFx
  have hN'N : N' ≤ K₁ * N := by
    have hs2 : √Λ ^ 2 = Λ := Real.sq_sqrt hΛ.le
    have hr2 : r ^ 2 = R ^ 2 / Λ := by rw [hr_def, div_pow, hs2]
    have hrγ : r ^ (2 + α) * √Λ ^ α = R ^ (2 + α) / Λ := by
      rw [hr_def, Real.div_rpow hR.le hs.le, Real.rpow_add hs, Real.rpow_two, hs2]
      field_simp
    have hΛK : 1 / Λ ≤ K₁ := (one_div_le_one_div_of_le hlam hlamΛ).trans (le_max_right _ _)
    have h1 : r ^ 2 * |F x₀| ≤ K₁ * (R ^ 2 * MF) := by
      rw [hr2]
      calc R ^ 2 / Λ * |F x₀| ≤ R ^ 2 / Λ * MF := by gcongr
        _ = 1 / Λ * (R ^ 2 * MF) := by ring
        _ ≤ K₁ * (R ^ 2 * MF) := by gcongr
    have h2 : r ^ (2 + α) * (H₀ * √Λ ^ α) ≤ K₁ * (R ^ (2 + α) * H₀) := by
      calc r ^ (2 + α) * (H₀ * √Λ ^ α) = 1 / Λ * (R ^ (2 + α) * H₀) := by
            rw [mul_comm H₀, ← mul_assoc, hrγ]; ring
        _ ≤ K₁ * (R ^ (2 + α) * H₀) := by gcongr
    have h3 : M₀ ≤ K₁ * M₀ := le_mul_of_one_le_left hM₀0 hK₁1
    rw [hN', hN, mul_add, mul_add]; linarith
  obtain ⟨hPc, hPe⟩ := pullback_expansion hα hlam hlamΛ hMn' hx₀' hm hmν hR hC₀
    (by positivity) (by positivity) hN'N hP'c hP'e
  refine ⟨P'.compCLM (M.symm : E →L[ℝ] E), ?_, hPc, hPe⟩
  rw [sum_hess_compCLM_eq_trace P' (a x₀) M K hconj hK, hP'tr]

/-- **Pointwise expansion at a flat point, conormal case**. As
`Nondiv.expansion_at_flat_point_dirichlet`, with the Dirichlet condition replaced by: `a(x₀)` is
symmetric and at each flat point `y` of `ball x₀ R` the derivative of `u` along the conormal
`a(x₀) ν` (right-derivative of `t ↦ u (y + t • a(x₀) ν)` at `0`) is at most
`G |y − x₀|^{1+α}`; then `N = M₀ + R² M_F + R^{2+α} (K_F + d K_a M₂ + G)`. -/
theorem expansion_at_flat_point_conormal {α : ℝ} (hα : 0 < α ∧ α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ {ν : E}, ‖ν‖ = 1 → ∀ (a : E → E →L[ℝ] E) (F u : E → ℝ)
      (x₀ : E) (R M₀ M₂ MF Ka KF G : ℝ), x₀ ∈ flatPart ν → 0 < R → 0 ≤ Ka → 0 ≤ KF →
      0 ≤ M₂ → 0 ≤ G →
      ContinuousOn u (halfBall ν x₀ R) → ContDiffOn ℝ 2 u (ball x₀ R ∩ openHalfSpace ν) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ∑ i, fderiv ℝ (fderiv ℝ u) y
        (a y (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F y) →
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x₀ ξ, ξ⟫) → ‖a x₀‖ ≤ Λ → (a x₀ : E →ₗ[ℝ] E).IsSymmetric →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖a y - a x₀‖ ≤ Ka * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, |F y - F x₀| ≤ KF * dist y x₀ ^ α) →
      |F x₀| ≤ MF → (∀ y ∈ halfBall ν x₀ R, |u y| ≤ M₀) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M₂) →
      (∀ y ∈ ball x₀ R, y ∈ flatPart ν → ∃ d : ℝ,
        HasDerivWithinAt (fun t : ℝ ↦ u (y + t • a x₀ ν)) d (Ici 0) 0 ∧
          |d| ≤ G * dist y x₀ ^ (1 + α)) →
      ∃ P : QuadPoly E,
        ∑ i, P.hess (a x₀ (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F x₀ ∧
        |P.const| + R * ‖P.lin‖ + R ^ 2 * ‖P.quad‖ ≤
          C * (M₀ + R ^ 2 * MF + R ^ (2 + α) * (KF + finrank ℝ E * Ka * M₂ + G)) ∧
        ∀ y ∈ halfSpace ν, dist y x₀ < κ * R →
          |u y - P.eval (y - x₀)| ≤
            C * (M₀ + R ^ 2 * MF + R ^ (2 + α) * (KF + finrank ℝ E * Ka * M₂ + G)) *
              (dist y x₀ / R) ^ (2 + α) := by
  obtain ⟨C₀, hC₀, hexp⟩ := expansion_halfBall_neumann (E := E) hα
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  set K₁ := max 1 (1 / lam) with hK₁
  have hK₁1 : 1 ≤ K₁ := le_max_left _ _
  set Q := √Λ / √lam with hQ
  refine ⟨C₀ * K₁ * (1 + Q + Q ^ 2 + Q ^ (2 + α)), √lam / √Λ, by positivity, by positivity,
    ?_⟩
  intro ν hν a F u x₀ R M₀ M₂ MF Ka KF G hx₀ hR hKa hKF hM₂ hG huc hu2 heq hell hbd hsymm ha hF
    hFx hM₀ hD2 hcon
  have hx₀' : ⟪x₀, ν⟫ = 0 := hx₀
  obtain ⟨M, m, K, hm1, hm2, hmν, hMν, hMn, hMn', hconj, hK⟩ :=
    exists_halfSpace_normalization hν hlam hell hbd
  have hm : 0 < m := (Real.sqrt_pos.2 hlam).trans_le hm1
  have hs : 0 < √Λ := Real.sqrt_pos.2 hΛ
  have ht : 0 < √lam := Real.sqrt_pos.2 hlam
  -- the conormal direction
  have hsym : symPart (a x₀) = a x₀ := by
    have hadj : adjoint (a x₀) = a x₀ := isSelfAdjoint_iff_isSymmetric.2 hsymm
    ext ξ
    rw [symPart_apply, hadj, ← two_smul ℝ (a x₀ ξ), smul_smul]
    norm_num
  rw [hsym] at hMν
  have hMν' : M ν = m⁻¹ • a x₀ ν := by
    rw [← hMν, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  set r := R / √Λ with hr_def
  have hr : 0 < r := by positivity
  have hsr : √Λ * r = R := by rw [hr_def]; field_simp
  have hMz := norm_le_sqrt_mul hMn
  have hdist : ∀ z, dist (x₀ + M z) x₀ = ‖M z‖ := fun z ↦ by
    rw [dist_eq_norm, add_sub_cancel_left]
  have hinner : ∀ z, ⟪x₀ + M z, ν⟫ = m * ⟪z, ν⟫ := fun z ↦ by
    rw [inner_add_left, hx₀', hmν, zero_add]
  have hmapsC : MapsTo (fun z ↦ x₀ + M z) (halfBall ν 0 r) (halfBall ν x₀ R) := fun z hz ↦ by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, hdist, ← hsr]
      exact (hMz z).trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hz.1) hs.le)
    · rw [mem_halfSpace, hinner]; exact mul_nonneg hm.le hz.2
  have hmapsB : MapsTo (fun z ↦ x₀ + M z) (ball 0 r ∩ openHalfSpace ν)
      (ball x₀ R ∩ openHalfSpace ν) := fun z hz ↦ by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, hdist, ← hsr]
      exact (hMz z).trans_lt (mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hz.1) hs)
    · rw [mem_openHalfSpace, hinner]; exact mul_pos hm hz.2
  have hT : ContDiff ℝ 2 fun z ↦ x₀ + M z := contDiff_const.add M.contDiff
  set ũ : E → ℝ := fun z ↦ u (x₀ + M z) with hũ
  have hũc : ContinuousOn ũ (halfBall ν 0 r) := huc.comp hT.continuous.continuousOn hmapsC
  have hũ2 : ContDiffOn ℝ 2 ũ (ball 0 r ∩ openHalfSpace ν) :=
    hu2.comp hT.contDiffOn hmapsB
  set H₀ := KF + finrank ℝ E * Ka * M₂ with hH₀
  have hH₀0 : 0 ≤ H₀ := by positivity
  have hΔ : ∀ z ∈ ball (0 : E) r ∩ openHalfSpace ν, |Δ ũ z - F x₀| ≤ H₀ * √Λ ^ α * ‖z‖ ^ α :=
    fun z hz ↦ normalized_laplacian_bound hα hKa hKF hM₂ hconj hK hu2 heq ha hF hD2 hMz
      (hmapsB hz)
  -- the normal derivative of `ũ`
  set G' := G * √Λ ^ (1 + α) / m with hG'
  have hũN : ∀ z ∈ ball (0 : E) r, z ∈ flatPart ν → ∃ d : ℝ,
      HasDerivWithinAt (fun t : ℝ ↦ ũ (z + t • ν)) d (Ici 0) 0 ∧ |d| ≤ G' * ‖z‖ ^ (1 + α) := by
    intro z hz hzf
    have hyB : x₀ + M z ∈ ball x₀ R := by
      rw [mem_ball, hdist, ← hsr]
      exact (hMz z).trans_lt (mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hz) hs)
    have hyf : x₀ + M z ∈ flatPart ν := by
      rw [mem_flatPart, hinner, mem_flatPart.1 hzf, mul_zero]
    obtain ⟨d, hd, hdb⟩ := hcon _ hyB hyf
    have hlin : HasDerivWithinAt (fun t : ℝ ↦ m⁻¹ * t) m⁻¹ (Ici 0) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul m⁻¹ |>.hasDerivWithinAt
    have hmaps : MapsTo (fun t : ℝ ↦ m⁻¹ * t) (Ici 0) (Ici 0) := fun t ht ↦
      mul_nonneg (inv_nonneg.2 hm.le) ht
    have hd0 : HasDerivWithinAt (fun t : ℝ ↦ u (x₀ + M z + t • a x₀ ν)) d (Ici 0)
        (m⁻¹ * 0) := by rw [mul_zero]; exact hd
    have hcomp := hd0.comp (0 : ℝ) hlin hmaps
    refine ⟨d * m⁻¹, ?_, ?_⟩
    · convert hcomp using 2 with t
      simp only [hũ, Function.comp_apply, map_add, map_smul, hMν', smul_smul, add_assoc]
      rw [mul_comm]
    · rw [hdist] at hdb
      have hMzα : ‖M z‖ ^ (1 + α) ≤ √Λ ^ (1 + α) * ‖z‖ ^ (1 + α) := by
        rw [← Real.mul_rpow hs.le (norm_nonneg _)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hMz z) (by linarith)
      rw [abs_mul, abs_inv, abs_of_pos hm, hG']
      have hdb' : |d| ≤ G * (√Λ ^ (1 + α) * ‖z‖ ^ (1 + α)) :=
        hdb.trans (mul_le_mul_of_nonneg_left hMzα hG)
      calc |d| * m⁻¹ ≤ G * (√Λ ^ (1 + α) * ‖z‖ ^ (1 + α)) * m⁻¹ := by gcongr
        _ = G * √Λ ^ (1 + α) / m * ‖z‖ ^ (1 + α) := by field_simp
  obtain ⟨P', hP'tr, hP'c, hP'e⟩ := hexp hν ũ r M₀ (F x₀) (H₀ * √Λ ^ α) G' hr (by positivity)
    (by positivity) hũc hũ2 (fun z hz ↦ hM₀ _ (hmapsC hz)) hΔ hũN
  set N' := M₀ + r ^ 2 * |F x₀| + r ^ (2 + α) * (H₀ * √Λ ^ α + G') with hN'
  set N := M₀ + R ^ 2 * MF + R ^ (2 + α) * (H₀ + G) with hN
  have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ x₀ ⟨mem_closedBall_self hR.le, hx₀'.ge⟩)
  have hMF : 0 ≤ MF := (abs_nonneg _).trans hFx
  have hN'N : N' ≤ K₁ * N := by
    have hs2 : √Λ ^ 2 = Λ := Real.sq_sqrt hΛ.le
    have hr2 : r ^ 2 = R ^ 2 / Λ := by rw [hr_def, div_pow, hs2]
    have hrγ : r ^ (2 + α) * √Λ ^ α = R ^ (2 + α) / Λ := by
      rw [hr_def, Real.div_rpow hR.le hs.le, Real.rpow_add hs, Real.rpow_two, hs2]
      field_simp
    have hrγ' : r ^ (2 + α) * √Λ ^ (1 + α) = R ^ (2 + α) / √Λ := by
      rw [hr_def, Real.div_rpow hR.le hs.le, show (2 : ℝ) + α = 1 + (1 + α) by ring,
        Real.rpow_add hs, Real.rpow_one]
      field_simp
    have hΛK : 1 / Λ ≤ K₁ := (one_div_le_one_div_of_le hlam hlamΛ).trans (le_max_right _ _)
    have hsm : 1 / (√Λ * m) ≤ K₁ := by
      have : lam ≤ √Λ * m := by
        calc lam = √lam * √lam := (Real.mul_self_sqrt hlam.le).symm
          _ ≤ √Λ * m := mul_le_mul (Real.sqrt_le_sqrt hlamΛ) hm1 ht.le hs.le
      exact (one_div_le_one_div_of_le hlam this).trans (le_max_right _ _)
    have h1 : r ^ 2 * |F x₀| ≤ K₁ * (R ^ 2 * MF) := by
      rw [hr2]
      calc R ^ 2 / Λ * |F x₀| ≤ R ^ 2 / Λ * MF := by gcongr
        _ = 1 / Λ * (R ^ 2 * MF) := by ring
        _ ≤ K₁ * (R ^ 2 * MF) := by gcongr
    have h2 : r ^ (2 + α) * (H₀ * √Λ ^ α) ≤ K₁ * (R ^ (2 + α) * H₀) := by
      calc r ^ (2 + α) * (H₀ * √Λ ^ α) = 1 / Λ * (R ^ (2 + α) * H₀) := by
            rw [mul_comm H₀, ← mul_assoc, hrγ]; ring
        _ ≤ K₁ * (R ^ (2 + α) * H₀) := by gcongr
    have h2' : r ^ (2 + α) * G' ≤ K₁ * (R ^ (2 + α) * G) := by
      calc r ^ (2 + α) * G' = 1 / (√Λ * m) * (R ^ (2 + α) * G) := by
            rw [hG', show r ^ (2 + α) * (G * √Λ ^ (1 + α) / m) =
              r ^ (2 + α) * √Λ ^ (1 + α) * G / m by ring, hrγ']
            field_simp
        _ ≤ K₁ * (R ^ (2 + α) * G) := by gcongr
    have h3 : M₀ ≤ K₁ * M₀ := le_mul_of_one_le_left hM₀0 hK₁1
    have e1 : N' = M₀ + r ^ 2 * |F x₀| + r ^ (2 + α) * (H₀ * √Λ ^ α) + r ^ (2 + α) * G' := by
      rw [hN']; ring
    have e2 : K₁ * N = K₁ * M₀ + K₁ * (R ^ 2 * MF) + K₁ * (R ^ (2 + α) * H₀) +
        K₁ * (R ^ (2 + α) * G) := by rw [hN]; ring
    rw [e1, e2]; linarith
  obtain ⟨hPc, hPe⟩ := pullback_expansion hα hlam hlamΛ hMn' hx₀' hm hmν hR hC₀
    (by positivity) (by positivity) hN'N hP'c hP'e
  refine ⟨P'.compCLM (M.symm : E →L[ℝ] E), ?_, ?_, ?_⟩
  · rw [sum_hess_compCLM_eq_trace P' (a x₀) M K hconj hK, hP'tr]
  · convert hPc using 3
  · intro y hy hyd
    convert hPe y hy hyd using 3

end Nondiv

end BasicElliptic
