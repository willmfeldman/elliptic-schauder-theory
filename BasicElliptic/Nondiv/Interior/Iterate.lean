/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Interior.Step

/-!
# The nondivergence iteration and the limit polynomial

`E` is a nontrivial finite-dimensional real inner product space,
`γ = 2 + α` with `0 < α < 1`, and `B_r = ball 0 r`.

* `Nondiv.laplacian_rescale_sub`: `Δ ((u − P)(r ·) / c) = r² (Δu(r ·) − tr P) / c`, the only
  normalization the iteration uses.
* `Nondiv.iterate_step`: one step at scale `ρⁿ`, via `improvement_of_flatness`. The source
  hypothesis is the **pointwise** Hölder bound `|Δu(z) − σ| ≤ δ₀ |z|^α` at the base point `0`
  only.
* `Nondiv.exists_limit_poly`: the increments `Rₙ = (ρⁿ)^γ Qₙ(ρ^{-n} ·)` are geometrically small,
  so the coefficients converge (in the complete space of coefficient triples); the limit `P'`
  satisfies `|Pₙ − P'| ≤ C₀/(1 − ρ^α) (ρⁿ)^γ` on `B_{ρⁿ}`.
* `Nondiv.abs_le_of_forall_scale`: bounds at the scales `ρⁿ` give a bound at every scale.
* `Nondiv.expansion_at_origin`: the assembled iteration on `B₁`.
* `Nondiv.expansion_of_laplacian`: the scaled form on `B_r`: if `|u| ≤ M₀` and
  `|Δu(z) − σ| ≤ H |z|^α` in `B_r`, there is a quadratic `P` with `tr P = σ`,
  `|P(0)| + r ‖DP(0)‖ + r² ‖quad P‖ ≤ C N` and `|u(z) − P(z)| ≤ C N (|z|/r)^{2+α}` for `|z| < r`,
  where `N = M₀ + r² |σ| + r^{2+α} H` and `C = C(E, α)`.

## Provenance

Elliptic port of parabolic-basic-theory (own repository, commit
`2507d9a800377e91c591862286b2ba2d6464d918`), `ParabolicBasic/Schauder/Iteration/Iterate.lean`
(`iterate_step`, `exists_limit_poly`, `exists_pow_succ_le_lt`, `abs_le_of_forall_scale`,
`expansion_at_origin`) and the rescaling lemma `isHeatSolOn_rescale` of
`ParabolicBasic/Schauder/Iteration/Basic.lean`. Changes: parabolic cylinders and `pdist` become
Euclidean balls and the norm; the degree is fixed to `2` (`θ = α`); the viscosity equation becomes
the classical Laplacian of a `C²` function; the coefficient convergence is run once in the product
space of coefficient triples instead of entrywise.
-/

public section

open Metric Set Filter Topology Module InnerProductSpace
open scoped InnerProductSpace Laplacian

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Normalization -/

/-- **Rescaling.** `Δ ((u − P)(r ·) / c) (y) = r² (Δu(r y) − tr P) / c` when `u` is `C²` at
`r y`. -/
theorem laplacian_rescale_sub {u : E → ℝ} (P : QuadPoly E) (r c : ℝ) {y : E}
    (hu : ContDiffAt ℝ 2 u (r • y)) :
    Δ (fun y ↦ (u (r • y) - P.eval (r • y)) / c) y = r ^ 2 * (Δ u (r • y) - P.trace) / c := by
  set F : E → ℝ := c⁻¹ • (u - P.eval) with hF
  have e : (fun y ↦ (u (r • y) - P.eval (r • y)) / c) = fun y ↦ F (r • y) := by
    funext y; simp [hF, div_eq_inv_mul]
  have hP : ContDiffAt ℝ 2 P.eval (r • y) := P.contDiff_eval.contDiffAt
  rw [e, laplacian_comp_smul, hF, laplacian_smul (f := u - P.eval) _ (hu.sub hP),
    ContDiffAt.laplacian_sub (f₁ := u) (f₂ := P.eval) hu hP,
    QuadPoly.laplacian_eval, smul_eq_mul]
  ring

/-! ### One step of the iteration -/

omit [FiniteDimensional ℝ E] in
/-- The increment `t^γ Q(t⁻¹ ·)` (`γ = 2 + α`, `0 < t ≤ s`) is bounded by `‖Q‖ t^α s²` on
`closedBall 0 s`. -/
theorem abs_eval_smul_rescale_le (Q : QuadPoly E) {α t s : ℝ} (ht : 0 < t) (hts : t ≤ s)
    {z : E} (hz : ‖z‖ ≤ s) :
    |((t ^ (2 + α)) • Q.rescale t⁻¹).eval z| ≤ Q.sumNorm * t ^ α * s ^ 2 := by
  rw [QuadPoly.eval_smul, QuadPoly.eval_rescale, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  have hτ : 1 ≤ s / t := (one_le_div ht).2 hts
  have hy : ‖t⁻¹ • z‖ ≤ s / t := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hz ht.le
  have hb := Q.abs_eval_le_sumNorm_mul hτ hy
  have ht2 : t ^ (2 + α) = t ^ 2 * t ^ α := by
    rw [Real.rpow_add ht, Real.rpow_two]
  rw [ht2]
  calc t ^ 2 * t ^ α * |Q.eval (t⁻¹ • z)| ≤ t ^ 2 * t ^ α * (Q.sumNorm * (s / t) ^ 2) := by
        gcongr
    _ = Q.sumNorm * t ^ α * s ^ 2 := by field_simp

omit [FiniteDimensional ℝ E] in
/-- The coefficient size of the increment `t^γ Q(t⁻¹ ·)` (`0 < t ≤ 1`) is at most `‖Q‖ t^α`. -/
theorem sumNorm_smul_rescale_le (Q : QuadPoly E) {α t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ((t ^ (2 + α)) • Q.rescale t⁻¹).sumNorm ≤ Q.sumNorm * t ^ α := by
  rw [QuadPoly.sumNorm_smul_rescale Q (Real.rpow_pos_of_pos ht _).le (inv_nonneg.2 ht.le)]
  have ht2 : t ^ (2 + α) = t ^ 2 * t ^ α := by
    rw [Real.rpow_add ht, Real.rpow_two]
  have hta : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  have e : t ^ (2 + α) * (|Q.const| + t⁻¹ * ‖Q.lin‖ + t⁻¹ ^ 2 * ‖Q.quad‖) =
      t ^ α * (t ^ 2 * |Q.const| + t * ‖Q.lin‖ + ‖Q.quad‖) := by
    rw [ht2]; field_simp
  rw [e, mul_comm Q.sumNorm]
  refine mul_le_mul_of_nonneg_left ?_ hta.le
  have h2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1
  unfold QuadPoly.sumNorm
  nlinarith [abs_nonneg Q.const, norm_nonneg Q.lin]

/-- **Iteration, step.** Suppose improvement of flatness holds at radius `ρ` with source bound
`ρ^γ/4` (`hflat`), `u ∈ C²(B₁) ∩ C(B̄₁)` with `|Δu(z) − σ| ≤ ρ^γ/4 |z|^α`, and `P` (with
`tr P = σ`) approximates `u` to order `(ρⁿ)^γ` on `B_{ρⁿ}`. Then there is `Q` as in `hflat` such
that `P + (ρⁿ)^γ Q(ρ^{-n} ·)` approximates `u` to order `(ρ^{n+1})^γ` on `B_{ρ^{n+1}}`. -/
theorem iterate_step {α ρ C₀ σ : ℝ} (hα : 0 ≤ α) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hflat : ∀ {u : E → ℝ}, ContinuousOn u (closedBall 0 1) → ContDiffOn ℝ 2 u (ball 0 1) →
      (∀ z ∈ ball (0 : E) 1, |u z| ≤ 1) → (∀ z ∈ ball (0 : E) 1, |Δ u z| ≤ ρ ^ (2 + α) / 4) →
      ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧
        ∀ z ∈ ball (0 : E) ρ, |u z - Q.eval z| ≤ ρ ^ (2 + α))
    {u : E → ℝ} (hu : ContinuousOn u (closedBall 0 1)) (hu2 : ContDiffOn ℝ 2 u (ball 0 1))
    (hH : ∀ z ∈ ball (0 : E) 1, |Δ u z - σ| ≤ ρ ^ (2 + α) / 4 * ‖z‖ ^ α)
    (n : ℕ) {P : QuadPoly E} (hPtr : P.trace = σ)
    (hP : ∀ z ∈ ball (0 : E) (ρ ^ n), |u z - P.eval z| ≤ (ρ ^ n) ^ (2 + α)) :
    ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧
      ∀ z ∈ ball (0 : E) (ρ ^ (n + 1)),
        |u z - (P + ((ρ ^ n) ^ (2 + α)) • Q.rescale (ρ ^ n)⁻¹).eval z| ≤
          (ρ ^ (n + 1)) ^ (2 + α) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ρ ^ n := ⟨_, rfl⟩
  rw [← hr] at hP ⊢
  have hr0 : 0 < r := hr ▸ pow_pos hρ0 n
  have hr1 : r ≤ 1 := hr ▸ pow_le_one₀ hρ0.le hρ1
  have hrγ : 0 < r ^ (2 + α) := Real.rpow_pos_of_pos hr0 _
  have hnorm : ∀ y : E, ‖r • y‖ = r * ‖y‖ := fun y ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  have hmapsC : MapsTo (fun y : E ↦ r • y) (closedBall 0 1) (closedBall 0 1) := fun y hy ↦ by
    rw [mem_closedBall_zero_iff] at hy ⊢
    rw [hnorm]; nlinarith [norm_nonneg y]
  have hmapsB : ∀ y ∈ ball (0 : E) 1, r • y ∈ ball (0 : E) r := fun y hy ↦ by
    rw [mem_ball_zero_iff] at hy ⊢
    rw [hnorm]; nlinarith [norm_nonneg y]
  have hBr1 : ball (0 : E) r ⊆ ball 0 1 := ball_subset_ball hr1
  set w : E → ℝ := fun y ↦ (u (r • y) - P.eval (r • y)) / r ^ (2 + α) with hw
  have hsc : ContDiff ℝ 2 fun y : E ↦ r • y := contDiff_const_smul r
  have hwc : ContinuousOn w (closedBall 0 1) :=
    ((hu.comp hsc.continuous.continuousOn hmapsC).sub
      (P.continuous_eval.comp hsc.continuous).continuousOn).div_const _
  have hw2 : ContDiffOn ℝ 2 w (ball 0 1) :=
    ((hu2.comp hsc.contDiffOn fun y hy ↦ hBr1 (hmapsB y hy)).sub
      (P.contDiff_eval.comp hsc).contDiffOn).div_const _
  have hw1 : ∀ y ∈ ball (0 : E) 1, |w y| ≤ 1 := fun y hy ↦ by
    rw [hw, abs_div, abs_of_pos hrγ, div_le_one hrγ]
    exact hP _ (hmapsB y hy)
  have hwΔ : ∀ y ∈ ball (0 : E) 1, |Δ w y| ≤ ρ ^ (2 + α) / 4 := fun y hy ↦ by
    have hry := hmapsB y hy
    have hat : ContDiffAt ℝ 2 u (r • y) := hu2.contDiffAt (isOpen_ball.mem_nhds (hBr1 hry))
    rw [hw, laplacian_rescale_sub P r _ hat, hPtr]
    have hb := hH _ (hBr1 hry)
    have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.1 hy
    have e1 : ‖r • y‖ ^ α ≤ r ^ α := by
      rw [hnorm, Real.mul_rpow hr0.le (norm_nonneg _)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hr0.le _)
        (Real.rpow_le_one (norm_nonneg _) hy1.le hα)
    have e2 : r ^ 2 * r ^ α / r ^ (2 + α) = 1 := by
      rw [Real.rpow_add hr0, Real.rpow_two, div_self (by positivity)]
    rw [abs_div, abs_mul, abs_of_pos hrγ, abs_of_nonneg (sq_nonneg r)]
    have hδ : 0 ≤ ρ ^ (2 + α) / 4 := by positivity
    calc r ^ 2 * |Δ u (r • y) - σ| / r ^ (2 + α)
        ≤ r ^ 2 * (ρ ^ (2 + α) / 4 * r ^ α) / r ^ (2 + α) := by
          gcongr; exact hb.trans (mul_le_mul_of_nonneg_left e1 hδ)
      _ = ρ ^ (2 + α) / 4 * (r ^ 2 * r ^ α / r ^ (2 + α)) := by ring
      _ = ρ ^ (2 + α) / 4 := by rw [e2, mul_one]
  obtain ⟨Q, hQtr, hQc, hQap⟩ := hflat hwc hw2 hw1 hwΔ
  refine ⟨Q, hQtr, hQc, fun z hz ↦ ?_⟩
  set y : E := r⁻¹ • z with hy
  have hSy : r • y = z := by rw [hy, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  have hyρ : y ∈ ball (0 : E) ρ := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [pow_succ, ← hr, ← hSy, hnorm] at hz
    exact lt_of_mul_lt_mul_left hz hr0.le
  have hQy := hQap y hyρ
  simp only [hw, hSy] at hQy
  have hne : r ^ (2 + α) ≠ 0 := hrγ.ne'
  have e : u z - (P + (r ^ (2 + α)) • Q.rescale r⁻¹).eval z =
      r ^ (2 + α) * ((u z - P.eval z) / r ^ (2 + α) - Q.eval y) := by
    rw [QuadPoly.eval_add, QuadPoly.eval_smul, QuadPoly.eval_rescale, ← hy, mul_sub,
      mul_div_cancel₀ _ hne]
    ring
  rw [e, abs_mul, abs_of_pos hrγ]
  calc r ^ (2 + α) * |(u z - P.eval z) / r ^ (2 + α) - Q.eval y| ≤ r ^ (2 + α) * ρ ^ (2 + α) := by
        gcongr
    _ = (ρ ^ (n + 1)) ^ (2 + α) := by
      rw [pow_succ, Real.mul_rpow (pow_nonneg hρ0.le n) hρ0.le, hr]

/-- **Iteration, limit.** If `P (n+1) = P n + (ρⁿ)^γ (Q n)(ρ^{-n} ·)` with `‖Q n‖ ≤ C₀` and every
`P n` has trace `σ`, then the coefficients of `P n` converge to those of a quadratic `P'` with
trace `σ`, `‖P'‖ ≤ ‖P 0‖ + C₀/(1 − ρ^α)`, and `|P n − P'| ≤ C₀/(1 − ρ^α) (ρⁿ)^γ` on `B_{ρⁿ}`. -/
theorem exists_limit_poly {α ρ C₀ σ : ℝ} (hα : 0 < α) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (P Q : ℕ → QuadPoly E)
    (hPQ : ∀ n, P (n + 1) = P n + ((ρ ^ n) ^ (2 + α)) • (Q n).rescale (ρ ^ n)⁻¹)
    (hQc : ∀ n, (Q n).sumNorm ≤ C₀) (hPtr : ∀ n, (P n).trace = σ) :
    ∃ P' : QuadPoly E, P'.trace = σ ∧ P'.sumNorm ≤ (P 0).sumNorm + C₀ / (1 - ρ ^ α) ∧
      ∀ n : ℕ, ∀ z ∈ ball (0 : E) (ρ ^ n),
        |(P n).eval z - P'.eval z| ≤ C₀ / (1 - ρ ^ α) * (ρ ^ n) ^ (2 + α) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ρ ^ α := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := hr ▸ Real.rpow_pos_of_pos hρ0 α
  have hr1 : r < 1 := hr ▸ Real.rpow_lt_one hρ0.le hρ1 hα
  have h1r : 0 < 1 - r := by linarith
  have hC₀ : 0 ≤ C₀ := (QuadPoly.sumNorm_nonneg _).trans (hQc 0)
  have hC₁ : 0 ≤ C₀ / (1 - r) := div_nonneg hC₀ h1r.le
  have hpow : ∀ n : ℕ, (ρ ^ n) ^ α = r ^ n := fun n ↦ by
    rw [hr, ← Real.rpow_natCast_mul hρ0.le, mul_comm (n : ℝ) α, Real.rpow_mul_natCast hρ0.le]
  set R : ℕ → QuadPoly E := fun n ↦ ((ρ ^ n) ^ (2 + α)) • (Q n).rescale (ρ ^ n)⁻¹ with hR
  have hPR : ∀ n, P (n + 1) = P n + R n := hPQ
  have hRc : ∀ n, (R n).sumNorm ≤ C₀ * r ^ n := fun n ↦ by
    calc (R n).sumNorm ≤ (Q n).sumNorm * (ρ ^ n) ^ α :=
          sumNorm_smul_rescale_le (Q n) (pow_pos hρ0 n) (pow_le_one₀ hρ0.le hρ1.le)
      _ ≤ C₀ * r ^ n := by
          rw [hpow]; exact mul_le_mul_of_nonneg_right (hQc n) (pow_nonneg hr0.le n)
  -- the coefficient triples form a Cauchy sequence
  have hcs : CauchySeq fun n ↦ (P n).toTriple := cauchySeq_of_le_geometric r C₀ hr1 fun n ↦ by
    rw [hPR n]; exact (QuadPoly.dist_toTriple_add_le _ _).trans (hRc n)
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hcs
  set P' : QuadPoly E := QuadPoly.ofTriple T with hP'
  have hcomp : ∀ {β : Type} (g : QuadPoly E → β), (fun n ↦ g (P n)) =
      (fun p ↦ g (QuadPoly.ofTriple p)) ∘ fun n ↦ (P n).toTriple := fun g ↦ by
    funext n; simp
  have hev : ∀ z, Tendsto (fun n ↦ (P n).eval z) atTop (𝓝 (P'.eval z)) := fun z ↦ by
    rw [hcomp fun P ↦ P.eval z]
    exact ((QuadPoly.continuous_eval_ofTriple z).tendsto T).comp hT
  refine ⟨P', ?_, ?_, ?_⟩
  · -- trace
    have h1 : Tendsto (fun n ↦ (P n).trace) atTop (𝓝 P'.trace) := by
      rw [hcomp QuadPoly.trace]
      exact (QuadPoly.continuous_trace_ofTriple.tendsto T).comp hT
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun n ↦ (hPtr n).symm)
  · -- coefficient size
    have hcn : ∀ n, (P n).sumNorm ≤ (P 0).sumNorm + C₀ / (1 - r) * (1 - r ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hPR n]
        have e : C₀ / (1 - r) * (1 - r ^ n) + C₀ * r ^ n =
            C₀ / (1 - r) * (1 - r ^ (n + 1)) := by
          field_simp
          ring
        calc _ ≤ (P n).sumNorm + (R n).sumNorm := QuadPoly.sumNorm_add_le _ _
          _ ≤ (P 0).sumNorm + C₀ / (1 - r) * (1 - r ^ n) + C₀ * r ^ n :=
            add_le_add ih (hRc n)
          _ = _ := by rw [add_assoc, e]
    have hcn' : ∀ n, (P n).sumNorm ≤ (P 0).sumNorm + C₀ / (1 - r) := fun n ↦ by
      have : C₀ / (1 - r) * (1 - r ^ n) ≤ C₀ / (1 - r) :=
        mul_le_of_le_one_right hC₁ (by linarith [pow_nonneg hr0.le n])
      linarith [hcn n]
    have hlim : Tendsto (fun n ↦ (P n).sumNorm) atTop (𝓝 P'.sumNorm) := by
      rw [hcomp QuadPoly.sumNorm]
      exact (QuadPoly.continuous_sumNorm_ofTriple.tendsto T).comp hT
    exact le_of_tendsto' hlim hcn'
  · -- tail bound
    intro n z hz
    have hz1 : ‖z‖ ≤ ρ ^ n := (mem_ball_zero_iff.1 hz).le
    have hγn : (ρ ^ n) ^ (2 + α) = (ρ ^ n) ^ 2 * r ^ n := by
      rw [Real.rpow_add (pow_pos hρ0 n), Real.rpow_two, hpow]
    have hdistR : ∀ (x y : ℝ), dist x (x + y) = |y| := fun x y ↦ by
      rw [Real.dist_eq, abs_sub_comm, add_sub_cancel_left]
    have hv : ∀ j : ℕ, dist ((P (j + n)).eval z) ((P (j + 1 + n)).eval z) ≤
        C₀ * (ρ ^ n) ^ (2 + α) * r ^ j := by
      intro j
      rw [show j + 1 + n = (j + n) + 1 by omega, hPR (j + n), QuadPoly.eval_add, hdistR]
      have hle : ρ ^ (j + n) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
      calc _ ≤ (Q (j + n)).sumNorm * (ρ ^ (j + n)) ^ α * (ρ ^ n) ^ 2 :=
            abs_eval_smul_rescale_le (Q (j + n)) (pow_pos hρ0 _) hle hz1
        _ ≤ C₀ * r ^ (j + n) * (ρ ^ n) ^ 2 := by
            rw [hpow]
            gcongr
            exact hQc _
        _ = C₀ * (ρ ^ n) ^ (2 + α) * r ^ j := by rw [hγn, pow_add]; ring
    have hvlim : Tendsto (fun j ↦ (P (j + n)).eval z) atTop (𝓝 (P'.eval z)) :=
      (tendsto_add_atTop_iff_nat n).2 (hev z)
    have key := dist_le_of_le_geometric_of_tendsto₀ r _ hr1 hv hvlim
    rw [zero_add, Real.dist_eq] at key
    calc _ ≤ C₀ * (ρ ^ n) ^ (2 + α) / (1 - r) := key
      _ = _ := by ring

/-! ### All scales -/

omit [FiniteDimensional ℝ E] in
/-- Between two consecutive powers: for `0 < x < 1` and `ρ < 1` there is `m` with
`ρ^{m+1} ≤ x < ρ^m`. -/
theorem exists_pow_succ_le_lt {ρ x : ℝ} (hρ1 : ρ < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ m : ℕ, ρ ^ (m + 1) ≤ x ∧ x < ρ ^ m := by
  classical
  have hex : ∃ n : ℕ, ρ ^ n ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 hρ1
    exact ⟨n, hn.le⟩
  have hn := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := fun h ↦ by
    rw [h, pow_zero] at hn
    linarith
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0)]
    exact hn
  · by_contra h
    have := Nat.find_min' hex (not_lt.1 h)
    omega

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Iteration, all scales.** Bounds `|f| ≤ B (ρⁿ)^γ` on `B_{ρⁿ}` for every `n` give
`|f z| ≤ B ρ^{-γ} |z|^γ` for `|z| < 1`. -/
theorem abs_le_of_forall_scale {f : E → ℝ} {ρ B γ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : 0 < γ) (hB : 0 ≤ B)
    (h : ∀ n : ℕ, ∀ z ∈ ball (0 : E) (ρ ^ n), |f z| ≤ B * (ρ ^ n) ^ γ) :
    ∀ z : E, ‖z‖ < 1 → |f z| ≤ B / ρ ^ γ * ‖z‖ ^ γ := by
  intro q hq
  have hργ : 0 < ρ ^ γ := Real.rpow_pos_of_pos hρ0 γ
  have hmem : ∀ n : ℕ, ‖q‖ < ρ ^ n → q ∈ ball (0 : E) (ρ ^ n) := fun n hn ↦
    mem_ball_zero_iff.2 hn
  rcases (norm_nonneg q).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow hγ.ne', mul_zero]
    have hlim : Tendsto (fun n : ℕ ↦ B * (ρ ^ γ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hργ.le
        (Real.rpow_lt_one hρ0.le hρ1 hγ)).const_mul B
    refine ge_of_tendsto' hlim fun n ↦ ?_
    have := h n q (hmem n (by rw [← h0]; positivity))
    rwa [← Real.rpow_natCast_mul hρ0.le, mul_comm (n : ℝ) γ, Real.rpow_mul_natCast hρ0.le]
      at this
  · obtain ⟨m, hm1, hm2⟩ := exists_pow_succ_le_lt hρ1 hpos hq
    calc |f q| ≤ B * (ρ ^ m) ^ γ := h m q (hmem m hm2)
      _ = B / ρ ^ γ * (ρ ^ (m + 1)) ^ γ := by
        rw [pow_succ, Real.mul_rpow (pow_nonneg hρ0.le m) hρ0.le, div_mul_eq_mul_div,
          mul_div_assoc, mul_div_cancel_right₀ _ hργ.ne']
      _ ≤ B / ρ ^ γ * ‖q‖ ^ γ := by
        gcongr

/-! ### The assembled iteration -/

variable [Nontrivial E]

/-- **Iteration: expansion at the origin.** For `α ∈ (0, 1)` there are `δ₀ > 0`, `C₁ ≥ 0`,
`A ≥ 0` (depending only on `E` and `α`) such that: if `u ∈ C²(B₁) ∩ C(B̄₁)`, `P₀` has trace `σ`,
`|u − P₀| ≤ 1` in `B₁`, and `|Δu(z) − σ| ≤ δ₀ |z|^α` in `B₁` (Hölder **at the origin only**), then
there is a quadratic `P` with `tr P = σ`, `‖P‖ ≤ ‖P₀‖ + C₁` and `|u(z) − P(z)| ≤ A |z|^{2+α}` for
`|z| < 1`. -/
theorem expansion_at_origin {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ δ₀ C₁ A : ℝ, 0 < δ₀ ∧ 0 ≤ C₁ ∧ 0 ≤ A ∧ ∀ {u : E → ℝ} {σ : ℝ} {P₀ : QuadPoly E},
      ContinuousOn u (closedBall 0 1) → ContDiffOn ℝ 2 u (ball 0 1) → P₀.trace = σ →
      (∀ z ∈ ball (0 : E) 1, |u z - P₀.eval z| ≤ 1) →
      (∀ z ∈ ball (0 : E) 1, |Δ u z - σ| ≤ δ₀ * ‖z‖ ^ α) →
      ∃ P : QuadPoly E, P.trace = σ ∧ P.sumNorm ≤ P₀.sumNorm + C₁ ∧
        ∀ z : E, ‖z‖ < 1 → |u z - P.eval z| ≤ A * ‖z‖ ^ (2 + α) := by
  obtain ⟨ρ, C₀, hρ0, hρq, hC₀, hflat⟩ := improvement_of_flatness (E := E) hα
  have hρ1 : ρ < 1 := by linarith
  have hρα1 : ρ ^ α < 1 := Real.rpow_lt_one hρ0.le hρ1 hα.1
  have h1r : 0 < 1 - ρ ^ α := by linarith
  have hγ0 : (0 : ℝ) < 2 + α := by linarith
  have hργ : 0 < ρ ^ (2 + α) := Real.rpow_pos_of_pos hρ0 _
  have hC₁ : 0 ≤ C₀ / (1 - ρ ^ α) := div_nonneg hC₀ h1r.le
  refine ⟨ρ ^ (2 + α) / 4, C₀ / (1 - ρ ^ α), (1 + C₀ / (1 - ρ ^ α)) / ρ ^ (2 + α),
    by positivity, hC₁, div_nonneg (by linarith) hργ.le, ?_⟩
  intro u σ P₀ hu hu2 hP₀ hu₀ hH
  have hstep : ∀ (n : ℕ) (P : QuadPoly E), (P.trace = σ ∧
      ∀ z ∈ ball (0 : E) (ρ ^ n), |u z - P.eval z| ≤ (ρ ^ n) ^ (2 + α)) →
      ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧
        ∀ z ∈ ball (0 : E) (ρ ^ (n + 1)),
          |u z - (P + ((ρ ^ n) ^ (2 + α)) • Q.rescale (ρ ^ n)⁻¹).eval z| ≤
            (ρ ^ (n + 1)) ^ (2 + α) :=
    fun n P hP ↦ iterate_step hα.1.le hρ0 hρ1.le hflat hu hu2 hH n hP.1 hP.2
  choose! Qf hQf using hstep
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → QuadPoly E, seq 0 = P₀ ∧ ∀ n,
      seq (n + 1) = seq n + ((ρ ^ n) ^ (2 + α)) • (Qf n (seq n)).rescale (ρ ^ n)⁻¹ :=
    ⟨fun n ↦ Nat.rec P₀
      (fun n P ↦ P + ((ρ ^ n) ^ (2 + α)) • (Qf n P).rescale (ρ ^ n)⁻¹) n,
      rfl, fun _ ↦ rfl⟩
  have hI : ∀ n, (seq n).trace = σ ∧
      ∀ z ∈ ball (0 : E) (ρ ^ n), |u z - (seq n).eval z| ≤ (ρ ^ n) ^ (2 + α) := by
    intro n
    induction n with
    | zero =>
      rw [hseq0]
      refine ⟨hP₀, fun z hz ↦ ?_⟩
      rw [pow_zero, Real.one_rpow]
      exact hu₀ z (by simpa using hz)
    | succ n ih =>
      obtain ⟨hQs, -, hQb⟩ := hQf n (seq n) ih
      refine ⟨?_, ?_⟩
      · rw [hseqs, QuadPoly.trace_add, QuadPoly.trace_smul, QuadPoly.trace_rescale, hQs, ih.1]
        ring
      · rw [hseqs]; exact hQb
  obtain ⟨P', hP'tr, hP'c, hP'tail⟩ := exists_limit_poly hα.1 hρ0 hρ1 seq
    (fun n ↦ Qf n (seq n)) hseqs (fun n ↦ (hQf n _ (hI n)).2.1) (fun n ↦ (hI n).1)
  refine ⟨P', hP'tr, by rwa [hseq0] at hP'c, ?_⟩
  have hall : ∀ n : ℕ, ∀ z ∈ ball (0 : E) (ρ ^ n),
      |u z - P'.eval z| ≤ (1 + C₀ / (1 - ρ ^ α)) * (ρ ^ n) ^ (2 + α) := by
    intro n z hz
    have a := (hI n).2 z hz
    have b := hP'tail n z hz
    calc |u z - P'.eval z| ≤ |u z - (seq n).eval z| + |(seq n).eval z - P'.eval z| :=
          abs_sub_le _ _ _
      _ ≤ _ := by rw [add_mul, one_mul]; exact add_le_add a b
  exact abs_le_of_forall_scale hρ0 hρ1 hγ0 (by linarith) hall

/-- **Scaled expansion for the Laplacian** (pointwise Hölder source at the centre). There is
`C = C(E, α) ≥ 0` such that: if `u ∈ C²(B_r) ∩ C(B̄_r)`, `|u| ≤ M₀` in `B_r` and
`|Δu(z) − σ| ≤ H |z|^α` in `B_r`, then with `N = M₀ + r² |σ| + r^{2+α} H` there is a quadratic
`P` with `tr P = σ`, `|P(0)| + r ‖DP(0)‖ + r² ‖quad P‖ ≤ C N` and
`|u(z) − P(z)| ≤ C N (|z|/r)^{2+α}` for `|z| < r`. -/
theorem expansion_of_laplacian {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E → ℝ) (r M₀ σ H : ℝ), 0 < r → 0 ≤ H →
      ContinuousOn u (closedBall 0 r) → ContDiffOn ℝ 2 u (ball 0 r) →
      (∀ z ∈ ball (0 : E) r, |u z| ≤ M₀) →
      (∀ z ∈ ball (0 : E) r, |Δ u z - σ| ≤ H * ‖z‖ ^ α) →
      ∃ P : QuadPoly E, P.trace = σ ∧
        |P.const| + r * ‖P.lin‖ + r ^ 2 * ‖P.quad‖ ≤
          C * (M₀ + r ^ 2 * |σ| + r ^ (2 + α) * H) ∧
        ∀ z : E, ‖z‖ < r →
          |u z - P.eval z| ≤ C * (M₀ + r ^ 2 * |σ| + r ^ (2 + α) * H) * (‖z‖ / r) ^ (2 + α) := by
  obtain ⟨δ₀, C₁, A, hδ₀, hC₁, hA, hexp⟩ := expansion_at_origin (E := E) hα
  set K : ℝ := max 1 (1 / δ₀) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKδ : 1 / δ₀ ≤ K := le_max_right _ _
  refine ⟨K * max (1 + C₁) A, by positivity, fun u r M₀ σ H hr hH hu hu2 hM₀ hΔ ↦ ?_⟩
  have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0 (mem_ball_self hr))
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
  · -- degenerate case: `u = 0`, `σ = 0`
    have hM : M₀ = 0 := by
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
      positivity, fun z hz ↦ ?_⟩
    rw [QuadPoly.eval_zero_poly, sub_zero]
    exact (hM₀ z (mem_ball_zero_iff.2 hz)).trans (by rw [hM]; positivity)
  -- the normalized function on `B₁`
  have hnorm : ∀ y : E, ‖r • y‖ = r * ‖y‖ := fun y ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hmapsC : MapsTo (fun y : E ↦ r • y) (closedBall 0 1) (closedBall 0 r) := fun y hy ↦ by
    rw [mem_closedBall_zero_iff] at hy ⊢
    rw [hnorm]; nlinarith [norm_nonneg y]
  have hmapsB : ∀ y ∈ ball (0 : E) 1, r • y ∈ ball (0 : E) r := fun y hy ↦ by
    rw [mem_ball_zero_iff] at hy ⊢
    rw [hnorm]; nlinarith [norm_nonneg y]
  set v : E → ℝ := fun y ↦ (u (r • y) - (0 : QuadPoly E).eval (r • y)) / N with hv
  have hv' : ∀ y, v y = u (r • y) / N := fun y ↦ by simp [hv]
  have hsc : ContDiff ℝ 2 fun y : E ↦ r • y := contDiff_const_smul r
  have hvc : ContinuousOn v (closedBall 0 1) :=
    ((hu.comp hsc.continuous.continuousOn hmapsC).sub
      ((0 : QuadPoly E).continuous_eval.comp hsc.continuous).continuousOn).div_const _
  have hv2 : ContDiffOn ℝ 2 v (ball 0 1) :=
    ((hu2.comp hsc.contDiffOn hmapsB).sub
      ((0 : QuadPoly E).contDiff_eval.comp hsc).contDiffOn).div_const _
  set σ' : ℝ := r ^ 2 * σ / N with hσ'
  have hσ'abs : |σ'| = r ^ 2 * |σ| / N := by
    rw [hσ', abs_div, abs_mul, abs_of_pos hNpos, abs_of_nonneg (sq_nonneg r)]
  have hσ'1 : M₀ / N + |σ'| ≤ 1 := by
    rw [hσ'abs, ← add_div, div_le_one hNpos, hN]
    have : 0 ≤ r ^ (2 + α) * H / δ₀ := by positivity
    linarith
  have hv0 : ∀ y ∈ ball (0 : E) 1, |v y - (QuadPoly.isotropic σ' : QuadPoly E).eval y| ≤ 1 := by
    intro y hy
    have h1 : |v y| ≤ M₀ / N := by
      rw [hv', abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right (hM₀ _ (hmapsB y hy)) hNpos.le
    have h2 := QuadPoly.abs_eval_isotropic_le (E := E) σ' y
    have hy1 : ‖y‖ ^ 2 ≤ 1 := by
      have := (mem_ball_zero_iff.1 hy).le
      nlinarith [norm_nonneg y]
    have h3 : |σ'| * ‖y‖ ^ 2 ≤ |σ'| := mul_le_of_le_one_right (abs_nonneg _) hy1
    calc _ ≤ |v y| + |(QuadPoly.isotropic σ' : QuadPoly E).eval y| := abs_sub _ _
      _ ≤ 1 := by linarith
  have hvΔ : ∀ y ∈ ball (0 : E) 1, |Δ v y - σ'| ≤ δ₀ * ‖y‖ ^ α := by
    intro y hy
    have hry := hmapsB y hy
    have hat : ContDiffAt ℝ 2 u (r • y) := hu2.contDiffAt (isOpen_ball.mem_nhds hry)
    rw [hv, laplacian_rescale_sub 0 r N hat]
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
  obtain ⟨P, hPtr, hPc, hPap⟩ := hexp hvc hv2 (QuadPoly.trace_isotropic σ') hv0 hvΔ
  have hP0 : (QuadPoly.isotropic σ' : QuadPoly E).sumNorm ≤ 1 :=
    (QuadPoly.sumNorm_isotropic_le σ').trans (by
      have : 0 ≤ M₀ / N := div_nonneg hM₀0 hNpos.le
      linarith)
  refine ⟨N • P.rescale r⁻¹, ?_, ?_, fun z hz ↦ ?_⟩
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
    have hyz : ‖y‖ = ‖z‖ / r := by
      rw [hy, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]
    have hap := hPap y hy1
    rw [hv', hSy] at hap
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
