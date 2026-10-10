/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Boundary.Freeze
public import BasicElliptic.Nondiv.Interior.Estimate
public import BasicElliptic.Poly.Bridge

/-!
# Gluing interior and boundary expansions on the closed half ball

Let `ν` be a unit vector, `x ∈ flatPart ν`, `s = halfBall ν x r`, `S = halfBall ν x (r/2)` and `U =
ball x r ∩ openHalfSpace ν`. Let `u` be continuous on `s`, `C²` in `U` with `‖D²u‖ ≤ M₂`, and solve
`tr (a D²u) = F` in `U`, with `a` elliptic and `a, F` Hölder on `s`.

* `Nondiv.isSolOn_sub_poly`: subtracting a quadratic polynomial `P` changes the right side to
  `F − tr (a D²P)`.
* `Nondiv.polyApproxOn_halfBall_of_boundary` (**two-regime gluing**): if at every flat point
  `p ∈ S` there is a quadratic `P̄` with `tr (a(p) D²P̄) = F(p)`, `‖quad P̄‖ ≤ B_q` and
  `|u(y) − P̄(y − p)| ≤ A_b |y − p|^{2+α}` for `y ∈ s`, `|y − p| < ρ_b`, then `u` has uniform
  polynomial expansions of order `2 + α` at every point of `S` (`PolyApproxOn 2 α`). For
  `p ∈ S` at height `d = ⟪p, ν⟫`:
  - `d = 0`: the boundary expansion;
  - `0 < d < d₁`: the interior expansion (`Nondiv.expansion_at_point`) of `u − P̄(· − p̄)` at `p`
    on `B_{d/2}(p)`, `p̄ = p − d ν`; its size is `O(d^{2+α})` because `P̄` approximates `u`, and the
    frozen right side `F − tr (a D²P̄)` is `O(d^α)` at `p` by the trace identity at `p̄`. Far from
    `p` (`|q − p| ≳ d`) the boundary expansion at `p̄` is used directly;
  - `d ≥ d₁`: the interior expansion of `u` at the fixed scale `d₁/2`, and boundedness beyond.

## References

* L. A. Caffarelli, *Interior a priori estimates for solutions of fully non-linear equations*,
  Ann. of Math. (2) 130 (1989), no. 1, 189–213. (the two-regime argument)
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001.
-/

public section

open Metric Set Filter Topology Module InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace Laplacian RealInnerProductSpace NNReal

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- `D²(u − P) = D²u − D²P` at a point where `u` is `C²`. -/
theorem fderiv_fderiv_sub_eval {u : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {y : E} (hy : y ∈ U) (P : QuadPoly E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ u z - P.eval z)) y = fderiv ℝ (fderiv ℝ u) y - P.hess := by
  have hP : ∀ z, DifferentiableAt ℝ P.eval z := fun z ↦
    (P.contDiff_eval (n := 1)).differentiable one_ne_zero z
  have h1 : fderiv ℝ (fun z ↦ u z - P.eval z) =ᶠ[𝓝 y]
      fun z ↦ fderiv ℝ u z - fderiv ℝ P.eval z := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact _root_.fderiv_sub ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)) (hP z)
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) y :=
    ((hu.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hdP : DifferentiableAt ℝ (fderiv ℝ P.eval) y := by
    have : fderiv ℝ P.eval = fun z ↦ P.lin + P.hess z := funext P.fderiv_eval
    rw [this]; fun_prop
  rw [h1.fderiv_eq, ← QuadPoly.fderiv_fderiv_eval P y]
  exact (hdu.hasFDerivAt.sub hdP.hasFDerivAt).fderiv

/-- Subtracting a quadratic polynomial from a solution of `tr (a D²u) = F` on an open set gives a
solution (in the sense of `Nondiv.IsSolOn`, with `b = 0`) with right side `F − tr (a D²P)`. -/
theorem isSolOn_sub_poly {U : Set E} (hU : IsOpen U) {a : E → E →L[ℝ] E} {F u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U)
    (heq : ∀ y ∈ U, ∑ i, fderiv ℝ (fderiv ℝ u) y (a y (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i) = F y) (P : QuadPoly E) :
    IsSolOn a (fun _ ↦ 0)
      (fun y ↦ F y - ∑ i, P.hess (a y (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i))
      U (fun z ↦ u z - P.eval z) := by
  refine ⟨hu.sub P.contDiff_eval.contDiffOn, fun y hy ↦ ?_⟩
  simp only [op, iteratedFDerivWithin_two_apply_of_isOpen hU hy, inner_zero_left, add_zero,
    fderiv_fderiv_sub_eval hU hu hy P, sub_apply, Finset.sum_sub_distrib, heq y hy]

/-- Interior solutions of `tr (a D²u) = F` on an open set, in the sense of `Nondiv.IsSolOn`. -/
theorem isSolOn_of_fderiv {U : Set E} (hU : IsOpen U) {a : E → E →L[ℝ] E} {F u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U)
    (heq : ∀ y ∈ U, ∑ i, fderiv ℝ (fderiv ℝ u) y (a y (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i) = F y) :
    IsSolOn a (fun _ ↦ 0) F U u := by
  refine ⟨hu, fun y hy ↦ ?_⟩
  simp only [op, iteratedFDerivWithin_two_apply_of_isOpen hU hy, inner_zero_left, add_zero,
    heq y hy]

/-- The conclusion of `Nondiv.expansion_at_point` for given constants `C, κ`. -/
def InteriorExpansion (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (α lam Λ C κ : ℝ) : Prop :=
  ∀ (U : Set E) (a : E → E →L[ℝ] E) (b : E → E) (f w : E → ℝ)
    (x₀ : E) (R M₀ M₁ M₂ Mb Mf Ka Kb Kf : ℝ),
    IsOpen U → 0 < R → closedBall x₀ R ⊆ U → IsSolOn a b f U w →
    (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x₀ ξ, ξ⟫) → ‖a x₀‖ ≤ Λ →
    (∀ y ∈ ball x₀ R, ‖a y - a x₀‖ ≤ Ka * dist y x₀ ^ α) →
    (∀ y ∈ ball x₀ R, ‖b y - b x₀‖ ≤ Kb * dist y x₀ ^ α) →
    (∀ y ∈ ball x₀ R, |f y - f x₀| ≤ Kf * dist y x₀ ^ α) →
    0 ≤ Ka → 0 ≤ Kb → 0 ≤ Kf →
    ‖b x₀‖ ≤ Mb → |f x₀| ≤ Mf → ‖fderiv ℝ w x₀‖ ≤ M₁ →
    (∀ y ∈ ball x₀ R, |w y - w x₀| ≤ M₀) →
    (∀ y ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 w y‖ ≤ M₂) →
    ∃ P : QuadPoly E,
      R * ‖P.lin‖ + R ^ 2 * ‖P.quad‖ ≤
        C * (M₀ + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) *
          (Kf + Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - α) + finrank ℝ E * Ka * M₂)) ∧
      ∀ y, dist y x₀ < κ * R →
        |w y - P.eval (y - x₀)| ≤
          C * (M₀ + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) *
            (Kf + Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - α) + finrank ℝ E * Ka * M₂)) *
            (dist y x₀ / R) ^ (2 + α)

/-- `Nondiv.InteriorExpansion` with `b = 0`, in simplified form, recording `P(0) = w(x₀)`. -/
theorem InteriorExpansion.apply_zero {α lam Λ C κ : ℝ} (hα : 0 < α ∧ α < 1) (hκ : 0 < κ)
    (hexp : InteriorExpansion E α lam Λ C κ) {U : Set E} (hU : IsOpen U)
    {a : E → E →L[ℝ] E} {F w : E → ℝ} {x₀ : E} {R M₀ M₂ Mf Ka Kf : ℝ} (hR : 0 < R)
    (hBU : closedBall x₀ R ⊆ U) (hsol : IsSolOn a (fun _ ↦ 0) F U w)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x₀ ξ, ξ⟫) (hbd : ‖a x₀‖ ≤ Λ)
    (ha : ∀ y ∈ ball x₀ R, ‖a y - a x₀‖ ≤ Ka * dist y x₀ ^ α)
    (hf : ∀ y ∈ ball x₀ R, |F y - F x₀| ≤ Kf * dist y x₀ ^ α) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hFx : |F x₀| ≤ Mf) (hM₀ : ∀ y ∈ ball x₀ R, |w y - w x₀| ≤ M₀)
    (hM₂ : ∀ y ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 w y‖ ≤ M₂) :
    ∃ P : QuadPoly E,
      R * ‖P.lin‖ + R ^ 2 * ‖P.quad‖ ≤
        C * (M₀ + R ^ 2 * Mf + R ^ (2 + α) * (Kf + finrank ℝ E * Ka * M₂)) ∧
      (∀ y, dist y x₀ < κ * R →
        |w y - P.eval (y - x₀)| ≤
          C * (M₀ + R ^ 2 * Mf + R ^ (2 + α) * (Kf + finrank ℝ E * Ka * M₂)) *
            (dist y x₀ / R) ^ (2 + α)) ∧ P.const = w x₀ := by
  obtain ⟨P, hPc, hPe⟩ := hexp U a (fun _ ↦ 0) F w x₀ R M₀ ‖fderiv ℝ w x₀‖ M₂ 0 Mf Ka 0 Kf hU hR
    hBU hsol hell hbd ha (fun y _ ↦ by simp) hf hKa le_rfl hKf (by simp) hFx le_rfl hM₀ hM₂
  have e : M₀ + R ^ 2 * (Mf + 0 * ‖fderiv ℝ w x₀‖) + R ^ (2 + α) *
      (Kf + 0 * (‖fderiv ℝ w x₀‖ + M₂ * R) + 0 * M₂ * R ^ (1 - α) + finrank ℝ E * Ka * M₂) =
      M₀ + R ^ 2 * Mf + R ^ (2 + α) * (Kf + finrank ℝ E * Ka * M₂) := by ring
  rw [e] at hPc hPe
  refine ⟨P, hPc, hPe, ?_⟩
  have h0 := hPe x₀ (by rw [dist_self]; positivity)
  rw [dist_self, zero_div, Real.zero_rpow (by linarith), mul_zero, sub_self,
    QuadPoly.eval_zero] at h0
  linarith [abs_nonneg (w x₀ - P.const), abs_nonpos_iff.1 h0]

omit [FiniteDimensional ℝ E] in
/-- Coefficient bounds give an evaluation bound `|P(z)| ≤ |P(0)| + C N ρ / R + C N ρ² / R²` for
`|z| ≤ ρ`. -/
theorem abs_eval_le_of_coeff {P : QuadPoly E} {R CN ρ : ℝ} (hR : 0 < R)
    (hc : R * ‖P.lin‖ + R ^ 2 * ‖P.quad‖ ≤ CN) {z : E} (hz : ‖z‖ ≤ ρ) :
    |P.eval z| ≤ |P.const| + CN * ρ / R + CN * ρ ^ 2 / R ^ 2 := by
  have hl : ‖P.lin‖ ≤ CN / R := by
    rw [le_div_iff₀ hR]; nlinarith [norm_nonneg P.quad, sq_nonneg R]
  have hq : ‖P.quad‖ ≤ CN / R ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [norm_nonneg P.lin]
  have h := P.abs_eval_le z
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have h1 : ‖P.lin‖ * ‖z‖ ≤ CN / R * ρ := mul_le_mul hl hz (norm_nonneg _)
    ((norm_nonneg _).trans hl)
  have h2 : ‖P.quad‖ * ‖z‖ ^ 2 ≤ CN / R ^ 2 * ρ ^ 2 :=
    mul_le_mul hq (pow_le_pow_left₀ hz0 hz 2) (by positivity) ((norm_nonneg _).trans hq)
  calc |P.eval z| ≤ |P.const| + ‖P.lin‖ * ‖z‖ + ‖P.quad‖ * ‖z‖ ^ 2 := h
    _ ≤ |P.const| + CN / R * ρ + CN / R ^ 2 * ρ ^ 2 := by linarith
    _ = _ := by ring

/-- **Interior regime at a fixed scale.** If `u` solves `tr (a D²u) = F` (with `b = 0`) on an open
`U ⊇ B̄_R(p)`, `|u| ≤ M₀` on `T ⊇ B_R(p)`, then with
`N = 2 M₀ + R² M_F + R^{2+α} (K_F + d K_a M₂)` the interior expansion at `p` gives
`|u(q) − P(q − p)| ≤ A |q − p|^{2+α}` for `q ∈ T`, `|q − p| < ρ₀`, with
`A = C N / R^{2+α} + (2 M₀ + C N ρ₀ / R + C N ρ₀² / R²) / (κ R)^{2+α}`. -/
theorem approx_regime_interior {α lam Λ C κ : ℝ} (hα : 0 < α ∧ α < 1) (hC : 0 ≤ C) (hκ : 0 < κ)
    (hexp : InteriorExpansion E α lam Λ C κ) {U T : Set E} (hU : IsOpen U)
    {a : E → E →L[ℝ] E} {F u : E → ℝ} {p : E} {R M₀ M₂ MF Ka KF ρ₀ N : ℝ}
    (hR : 0 < R) (hBU : closedBall p R ⊆ U) (hsol : IsSolOn a (fun _ ↦ 0) F U u)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a p ξ, ξ⟫) (hbd : ‖a p‖ ≤ Λ)
    (ha : ∀ y ∈ ball p R, ‖a y - a p‖ ≤ Ka * dist y p ^ α)
    (hF : ∀ y ∈ ball p R, |F y - F p| ≤ KF * dist y p ^ α) (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    (hFx : |F p| ≤ MF) (hpT : p ∈ T) (hBT : ball p R ⊆ T) (hu0 : ∀ y ∈ T, |u y| ≤ M₀)
    (hM₂ : ∀ y ∈ ball p R, ‖iteratedFDeriv ℝ 2 u y‖ ≤ M₂)
    (hN : N = 2 * M₀ + R ^ 2 * MF + R ^ (2 + α) * (KF + finrank ℝ E * Ka * M₂)) :
    ∃ P : QuadPoly E, ∀ q ∈ T, dist q p < ρ₀ →
      |u q - P.eval (q - p)| ≤
        (C * N / R ^ (2 + α) +
          (2 * M₀ + C * N * ρ₀ / R + C * N * ρ₀ ^ 2 / R ^ 2) / (κ * R) ^ (2 + α)) *
          dist q p ^ (2 + α) := by
  have hγ : (0 : ℝ) < 2 + α := by linarith [hα.1]
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (hu0 p hpT)
  have hMF : 0 ≤ MF := (abs_nonneg _).trans hFx
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ p (mem_ball_self hR))
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  obtain ⟨P, hPc, hPe, hP0⟩ := hexp.apply_zero hα hκ hU hR hBU hsol hell hbd ha hF hKa hKF hFx
    (M₀ := 2 * M₀) (fun y hy ↦ by
      have h1 := hu0 y (hBT hy)
      have h2 := hu0 p hpT
      calc |u y - u p| ≤ |u y| + |u p| := abs_sub _ _
        _ ≤ 2 * M₀ := by linarith) hM₂
  rw [← hN] at hPc hPe
  refine ⟨P, fun q hq hqd ↦ ?_⟩
  have hRγ : 0 < R ^ (2 + α) := Real.rpow_pos_of_pos hR _
  have hd0 : 0 ≤ dist q p := dist_nonneg
  have hdγ : 0 ≤ dist q p ^ (2 + α) := Real.rpow_nonneg hd0 _
  have hB0 : 0 ≤ (2 * M₀ + C * N * ρ₀ / R + C * N * ρ₀ ^ 2 / R ^ 2) / (κ * R) ^ (2 + α) := by
    have : 0 ≤ ρ₀ := hd0.trans hqd.le
    positivity
  by_cases hnear : dist q p < κ * R
  · calc |u q - P.eval (q - p)| ≤ C * N * (dist q p / R) ^ (2 + α) := hPe q hnear
      _ = C * N / R ^ (2 + α) * dist q p ^ (2 + α) := by
          rw [Real.div_rpow hd0 hR.le]; ring
      _ ≤ _ := by gcongr; linarith
  · have hfar : κ * R ≤ dist q p := not_lt.1 hnear
    have hρ₀ : 0 ≤ ρ₀ := hd0.trans hqd.le
    have hev := abs_eval_le_of_coeff hR hPc (z := q - p) (ρ := ρ₀)
      (by rw [← dist_eq_norm]; exact hqd.le)
    rw [hP0] at hev
    have hB : |u q - P.eval (q - p)| ≤ 2 * M₀ + C * N * ρ₀ / R + C * N * ρ₀ ^ 2 / R ^ 2 := by
      have h1 := hu0 q hq
      have h2 := hu0 p hpT
      calc |u q - P.eval (q - p)| ≤ |u q| + |P.eval (q - p)| := abs_sub _ _
        _ ≤ _ := by linarith
    have hκR : 0 < κ * R := mul_pos hκ hR
    have h1 : 1 ≤ (dist q p / (κ * R)) ^ (2 + α) :=
      Real.one_le_rpow ((one_le_div hκR).2 hfar) hγ.le
    have hX : 0 ≤ 2 * M₀ + C * N * ρ₀ / R + C * N * ρ₀ ^ 2 / R ^ 2 := by positivity
    calc |u q - P.eval (q - p)| ≤ 2 * M₀ + C * N * ρ₀ / R + C * N * ρ₀ ^ 2 / R ^ 2 := hB
      _ ≤ (2 * M₀ + C * N * ρ₀ / R + C * N * ρ₀ ^ 2 / R ^ 2) *
            (dist q p / (κ * R)) ^ (2 + α) := le_mul_of_one_le_right hX h1
      _ = (2 * M₀ + C * N * ρ₀ / R + C * N * ρ₀ ^ 2 / R ^ 2) / (κ * R) ^ (2 + α) *
            dist q p ^ (2 + α) := by
          rw [Real.div_rpow hd0 hκR.le]; ring
      _ ≤ _ := by
          have : 0 ≤ C * N / R ^ (2 + α) := by positivity
          gcongr; linarith

/-- `∑ᵢ B(A eᵢ, eᵢ) − ∑ᵢ B(A' eᵢ, eᵢ) = ∑ᵢ B((A − A') eᵢ, eᵢ)`. -/
theorem sum_apply_sub (B : E →L[ℝ] E →L[ℝ] ℝ) (A A' : E →L[ℝ] E) :
    ∑ i, B (A (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) -
        ∑ i, B (A' (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) =
      ∑ i, B ((A - A') (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [sub_apply, map_sub]

private theorem rpow_split {d α : ℝ} (hd : 0 < d) :
    d ^ (2 + α) = d ^ (1 + α) * d ∧ d ^ (2 + α) = d ^ α * d ^ 2 := by
  constructor
  · rw [show (2 : ℝ) + α = (1 + α) + 1 by ring, Real.rpow_add hd, Real.rpow_one]
  · rw [show (2 : ℝ) + α = α + 2 by ring, Real.rpow_add hd, Real.rpow_two]

private theorem rpow_split' {d α : ℝ} (hd : 0 ≤ d) (hα : 0 < α) :
    d ^ (2 + α) = d ^ (1 + α) * d ∧ d ^ (2 + α) = d ^ α * d ^ 2 := by
  rcases hd.eq_or_lt with h | h
  · subst h
    simp [Real.zero_rpow (by linarith : (2 : ℝ) + α ≠ 0),
      Real.zero_rpow (by linarith : (1 : ℝ) + α ≠ 0), Real.zero_rpow hα.ne']
  · exact rpow_split h

/-- **Near-boundary regime, expansion.** Let `p` be at distance `d > 0` from a point `p̄` at which
the boundary expansion `|u − P̄(· − p̄)| ≤ A_b |· − p̄|^{2+α}` holds (on `T`, up to distance `ρ_b`),
with the trace identity `tr (a(p̄) D²P̄) = F(p̄)` and `‖quad P̄‖ ≤ B_q`. If `B̄_{d/2}(p) ⊆ U ∩ T`,
`u` solves `tr (a D²u) = F` on `U` with `‖D²u‖ ≤ M₂`, `a, F` are Hölder on `T` and
`3d/2 < ρ_b`, then `v = u − P̄(· − p̄)` has an interior expansion at `p` on `B_{d/2}(p)` of size
`C c₁ d^{2+α}`. -/
theorem near_expansion {α lam Λ C κ : ℝ} (hα : 0 < α ∧ α < 1) (hC : 0 ≤ C) (hκ : 0 < κ)
    (hexp : InteriorExpansion E α lam Λ C κ) {U T : Set E} (hU : IsOpen U)
    {a : E → E →L[ℝ] E} {F u : E → ℝ} (hu2 : ContDiffOn ℝ 2 u U)
    (heq : ∀ y ∈ U, ∑ i, fderiv ℝ (fderiv ℝ u) y (a y (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i) = F y)
    {p pb : E} {d M₂ Ka KF Bq Ab ρb : ℝ} (hd : 0 < d) (hppb : dist p pb = d)
    (hρ : 3 * d / 2 < ρb)
    (hBU : closedBall p (d / 2) ⊆ U) (hBT : closedBall p (d / 2) ⊆ T) (hpbT : pb ∈ T)
    (ha : ∀ y ∈ T, ∀ y' ∈ T, ‖a y - a y'‖ ≤ Ka * dist y y' ^ α)
    (hF : ∀ y ∈ T, ∀ y' ∈ T, |F y - F y'| ≤ KF * dist y y' ^ α)
    (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF) (hBq : 0 ≤ Bq) (hAb : 0 ≤ Ab)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a p ξ, ξ⟫) (hbd : ‖a p‖ ≤ Λ)
    (hD2 : ∀ y ∈ U, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M₂)
    {Pb : QuadPoly E}
    (hcons : ∑ i, Pb.hess (a pb (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F pb)
    (hq : ‖Pb.quad‖ ≤ Bq)
    (happ : ∀ y ∈ T, dist y pb < ρb → |u y - Pb.eval (y - pb)| ≤ Ab * dist y pb ^ (2 + α))
    {KF' c₁ : ℝ} (hKF' : KF' = KF + finrank ℝ E * Bq * Ka)
    (hc₁ : c₁ = 2 * Ab * 2 ^ (2 + α) + 2 * KF' + finrank ℝ E * Ka * (M₂ + Bq)) :
    ∃ P : QuadPoly E,
      d / 2 * ‖P.lin‖ + (d / 2) ^ 2 * ‖P.quad‖ ≤ C * (c₁ * d ^ (2 + α)) ∧
      (∀ y, dist y p < κ * (d / 2) →
        |(u y - Pb.eval (y - pb)) - P.eval (y - p)| ≤
          C * (c₁ * d ^ (2 + α)) * (dist y p / (d / 2)) ^ (2 + α)) ∧
      P.const = u p - Pb.eval (p - pb) := by
  set e := stdOrthonormalBasis ℝ E
  have hγ : (0 : ℝ) < 2 + α := by linarith [hα.1]
  have hR : 0 < d / 2 := by positivity
  have hpT : p ∈ T := hBT (mem_closedBall_self hR.le)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (hD2 p (hBU (mem_closedBall_self hR.le)))
  have hKF'0 : 0 ≤ KF' := by rw [hKF']; positivity
  set Pt := Pb.shift (-pb) with hPt
  have hPte : ∀ z, Pt.eval z = Pb.eval (z - pb) := fun z ↦ by
    rw [hPt, QuadPoly.eval_shift, sub_eq_add_neg]
  have hPth : Pt.hess = Pb.hess := rfl
  have hhess : ‖Pt.hess‖ ≤ Bq := (norm_hess_le_norm_quad Pt).trans hq
  set v : E → ℝ := fun z ↦ u z - Pt.eval z with hv
  set F' : E → ℝ := fun y ↦ F y - ∑ i, Pt.hess (a y (e i)) (e i) with hF'
  have hsol := isSolOn_sub_poly hU hu2 heq Pt
  have hF'H : ∀ y ∈ T, ∀ y' ∈ T, |F' y - F' y'| ≤ KF' * dist y y' ^ α := by
    intro y hy y' hy'
    have e1 : F' y - F' y' = (F y - F y') - ∑ i, Pt.hess ((a y - a y') (e i)) (e i) := by
      simp only [hF']; rw [← sum_apply_sub]; ring
    rw [e1, hKF']
    have h1 := hF y hy y' hy'
    have h2 := abs_sum_apply_le Pt.hess (a y - a y')
    have h3 : ‖Pt.hess‖ * ‖a y - a y'‖ ≤ Bq * (Ka * dist y y' ^ α) :=
      mul_le_mul hhess (ha y hy y' hy') (norm_nonneg _) hBq
    have hda : 0 ≤ dist y y' ^ α := Real.rpow_nonneg dist_nonneg _
    calc _ ≤ |F y - F y'| + |∑ i, Pt.hess ((a y - a y') (e i)) (e i)| := abs_sub _ _
      _ ≤ KF * dist y y' ^ α + finrank ℝ E * (Bq * (Ka * dist y y' ^ α)) := by
          gcongr; exact h2.trans (by gcongr)
      _ = _ := by ring
  have hF'pb : F' pb = 0 := by simp only [hF', hPth, hcons, sub_self]
  have hF'p : |F' p| ≤ KF' * d ^ α := by
    have := hF'H p hpT pb hpbT
    rwa [hF'pb, sub_zero, hppb] at this
  have hvb : ∀ y ∈ T, dist y pb < ρb → |v y| ≤ Ab * dist y pb ^ (2 + α) := fun y hy hyd ↦ by
    simp only [hv, hPte]; exact happ y hy hyd
  have hvp : |v p| ≤ Ab * d ^ (2 + α) := by
    have := hvb p hpT (by rw [hppb]; linarith)
    rwa [hppb] at this
  have hball : ∀ y ∈ ball p (d / 2), y ∈ T ∧ dist y pb < ρb ∧ dist y pb ≤ 2 * d := by
    intro y hy
    have h1 : dist y pb ≤ dist y p + dist p pb := dist_triangle _ _ _
    have h2 : dist y p < d / 2 := hy
    refine ⟨hBT (ball_subset_closedBall hy), by rw [hppb] at h1; linarith, ?_⟩
    rw [hppb] at h1; linarith
  have hM₀ : ∀ y ∈ ball p (d / 2), |v y - v p| ≤ 2 * Ab * (2 * d) ^ (2 + α) := by
    intro y hy
    obtain ⟨hyT, hyρ, hy2⟩ := hball y hy
    have h1 := hvb y hyT hyρ
    have h2 : dist y pb ^ (2 + α) ≤ (2 * d) ^ (2 + α) :=
      Real.rpow_le_rpow dist_nonneg hy2 hγ.le
    have h3 : d ^ (2 + α) ≤ (2 * d) ^ (2 + α) :=
      Real.rpow_le_rpow hd.le (by linarith) hγ.le
    calc |v y - v p| ≤ |v y| + |v p| := abs_sub _ _
      _ ≤ Ab * (2 * d) ^ (2 + α) + Ab * (2 * d) ^ (2 + α) := by
          gcongr
          · exact h1.trans (by gcongr)
          · exact hvp.trans (by gcongr)
      _ = 2 * Ab * (2 * d) ^ (2 + α) := by ring
  have hM₂v : ∀ y ∈ ball p (d / 2), ‖iteratedFDeriv ℝ 2 v y‖ ≤ M₂ + Bq := by
    intro y hy
    have hyU := hBU (ball_subset_closedBall hy)
    rw [← norm_fderiv_fderiv_eq, fderiv_fderiv_sub_eval hU hu2 hyU Pt]
    exact (norm_sub_le _ _).trans (add_le_add (hD2 y hyU) hhess)
  obtain ⟨P, hPc, hPe, hP0⟩ := hexp.apply_zero hα hκ hU hR hBU hsol hell hbd
    (fun y hy ↦ ha y (hball y hy).1 p hpT) (fun y hy ↦ hF'H y (hball y hy).1 p hpT) hKa hKF'0
    hF'p hM₀ hM₂v
  set N := 2 * Ab * (2 * d) ^ (2 + α) + (d / 2) ^ 2 * (KF' * d ^ α) +
    (d / 2) ^ (2 + α) * (KF' + finrank ℝ E * Ka * (M₂ + Bq)) with hN
  have hNle : N ≤ c₁ * d ^ (2 + α) := by
    obtain ⟨-, hs2⟩ := rpow_split (α := α) hd
    have h1 : (2 * d) ^ (2 + α) = 2 ^ (2 + α) * d ^ (2 + α) := Real.mul_rpow (by norm_num) hd.le
    have hdα : 0 ≤ d ^ α := Real.rpow_nonneg hd.le _
    have h2 : (d / 2) ^ 2 * (KF' * d ^ α) ≤ KF' * d ^ (2 + α) := by
      rw [hs2]
      have : (d / 2) ^ 2 ≤ d ^ 2 := by nlinarith
      calc (d / 2) ^ 2 * (KF' * d ^ α) ≤ d ^ 2 * (KF' * d ^ α) := by gcongr
        _ = KF' * (d ^ α * d ^ 2) := by ring
    have h3 : (d / 2) ^ (2 + α) ≤ d ^ (2 + α) :=
      Real.rpow_le_rpow hR.le (by linarith) hγ.le
    have h4 : 0 ≤ KF' + finrank ℝ E * Ka * (M₂ + Bq) := by positivity
    have h5 := mul_le_mul_of_nonneg_right h3 h4
    calc N ≤ 2 * Ab * (2 ^ (2 + α) * d ^ (2 + α)) + KF' * d ^ (2 + α) +
          d ^ (2 + α) * (KF' + finrank ℝ E * Ka * (M₂ + Bq)) := by
          rw [hN, h1]; linarith
      _ = c₁ * d ^ (2 + α) := by rw [hc₁]; ring
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  refine ⟨P, hPc.trans (by gcongr), fun y hy ↦ ?_, by rw [hP0]; simp only [hPte]⟩
  have := hPe y hy
  simp only [hPte] at this
  exact this.trans (by gcongr)

/-- **Near-boundary regime, bound.** The arithmetic of the two sub-regimes `|q − p| < κ d/2`
(interior expansion of `v = u − P̄(· − p̄)`) and `|q − p| ≥ κ d/2` (boundary expansion at `p̄` and
the coefficient bounds of the interior expansion). -/
theorem near_bound {α C κ c₁ Ab d t : ℝ} (hα : 0 < α ∧ α < 1) (hC : 0 ≤ C) (hκ : 0 < κ)
    (hc₁ : 0 ≤ c₁) (hAb : 0 ≤ Ab) (hd : 0 < d) (ht : 0 ≤ t) {V Vp Pq : ℝ}
    (hnear : t < κ * (d / 2) → |V - Pq| ≤ C * (c₁ * d ^ (2 + α)) * (t / (d / 2)) ^ (2 + α))
    (hV : κ * (d / 2) ≤ t → |V| ≤ Ab * ((1 + 2 / κ) * t) ^ (2 + α))
    (hVp : |Vp| ≤ Ab * d ^ (2 + α))
    (hPq : |Pq| ≤ |Vp| + C * (c₁ * d ^ (2 + α)) * t / (d / 2) +
      C * (c₁ * d ^ (2 + α)) * t ^ 2 / (d / 2) ^ 2) :
    |V - Pq| ≤
      (C * c₁ * 2 ^ (2 + α) + Ab * (1 + 2 / κ) ^ (2 + α) + Ab * (2 / κ) ^ (2 + α) +
        2 * C * c₁ * (2 / κ) ^ (1 + α) + 4 * C * c₁ * (2 / κ) ^ α) * t ^ (2 + α) := by
  have hγ : (0 : ℝ) < 2 + α := by linarith [hα.1]
  have hK : 0 < 2 / κ := by positivity
  have htγ : 0 ≤ t ^ (2 + α) := Real.rpow_nonneg ht _
  have hT1 : 0 ≤ C * c₁ * 2 ^ (2 + α) := by positivity
  have hT2 : 0 ≤ Ab * (1 + 2 / κ) ^ (2 + α) := by positivity
  have hT3 : 0 ≤ Ab * (2 / κ) ^ (2 + α) := by positivity
  have hT4 : 0 ≤ 2 * C * c₁ * (2 / κ) ^ (1 + α) := by positivity
  have hT5 : 0 ≤ 4 * C * c₁ * (2 / κ) ^ α := by positivity
  obtain ⟨hs1, hs2⟩ := rpow_split (α := α) hd
  obtain ⟨ht1, ht2⟩ := rpow_split' ht hα.1
  by_cases hn : t < κ * (d / 2)
  · have h2 : C * (c₁ * d ^ (2 + α)) * (t / (d / 2)) ^ (2 + α) =
        C * c₁ * 2 ^ (2 + α) * t ^ (2 + α) := by
      have e1 : t / (d / 2) = 2 * t / d := by field_simp
      rw [e1, Real.div_rpow (by positivity) hd.le, Real.mul_rpow (by norm_num) ht]
      have hdγ' : 0 < d ^ (2 + α) := Real.rpow_pos_of_pos hd _
      field_simp
    calc |V - Pq| ≤ C * c₁ * 2 ^ (2 + α) * t ^ (2 + α) := (hnear hn).trans h2.le
      _ ≤ _ := by gcongr; linarith
  · have hfar : κ * (d / 2) ≤ t := not_lt.1 hn
    have hdK : d ≤ 2 / κ * t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hκ]; linarith
    have hvq : |V| ≤ Ab * (1 + 2 / κ) ^ (2 + α) * t ^ (2 + α) := by
      refine (hV hfar).trans_eq ?_
      rw [Real.mul_rpow (by positivity) ht]; ring
    have hb1 : |Vp| ≤ Ab * (2 / κ) ^ (2 + α) * t ^ (2 + α) := by
      refine hVp.trans ?_
      rw [mul_assoc, ← Real.mul_rpow hK.le ht]
      gcongr
    have hb2 : C * (c₁ * d ^ (2 + α)) * t / (d / 2) ≤
        2 * C * c₁ * (2 / κ) ^ (1 + α) * t ^ (2 + α) := by
      have e1 : C * (c₁ * d ^ (2 + α)) * t / (d / 2) = 2 * C * c₁ * d ^ (1 + α) * t := by
        rw [hs1]; field_simp
      have h1 : d ^ (1 + α) ≤ (2 / κ) ^ (1 + α) * t ^ (1 + α) := by
        rw [← Real.mul_rpow hK.le ht]
        exact Real.rpow_le_rpow hd.le hdK (by linarith [hα.1])
      calc C * (c₁ * d ^ (2 + α)) * t / (d / 2) = 2 * C * c₁ * d ^ (1 + α) * t := e1
        _ ≤ 2 * C * c₁ * ((2 / κ) ^ (1 + α) * t ^ (1 + α)) * t := by gcongr
        _ = _ := by rw [ht1]; ring
    have hb3 : C * (c₁ * d ^ (2 + α)) * t ^ 2 / (d / 2) ^ 2 ≤
        4 * C * c₁ * (2 / κ) ^ α * t ^ (2 + α) := by
      have e1 : C * (c₁ * d ^ (2 + α)) * t ^ 2 / (d / 2) ^ 2 = 4 * C * c₁ * d ^ α * t ^ 2 := by
        rw [hs2]; field_simp; ring
      have h1 : d ^ α ≤ (2 / κ) ^ α * t ^ α := by
        rw [← Real.mul_rpow hK.le ht]
        exact Real.rpow_le_rpow hd.le hdK hα.1.le
      calc C * (c₁ * d ^ (2 + α)) * t ^ 2 / (d / 2) ^ 2 = 4 * C * c₁ * d ^ α * t ^ 2 := e1
        _ ≤ 4 * C * c₁ * ((2 / κ) ^ α * t ^ α) * t ^ 2 := by gcongr
        _ = _ := by rw [ht2]; ring
    have e : (C * c₁ * 2 ^ (2 + α) + Ab * (1 + 2 / κ) ^ (2 + α) + Ab * (2 / κ) ^ (2 + α) +
        2 * C * c₁ * (2 / κ) ^ (1 + α) + 4 * C * c₁ * (2 / κ) ^ α) * t ^ (2 + α) =
        C * c₁ * 2 ^ (2 + α) * t ^ (2 + α) + Ab * (1 + 2 / κ) ^ (2 + α) * t ^ (2 + α) +
        Ab * (2 / κ) ^ (2 + α) * t ^ (2 + α) + 2 * C * c₁ * (2 / κ) ^ (1 + α) * t ^ (2 + α) +
        4 * C * c₁ * (2 / κ) ^ α * t ^ (2 + α) := by ring
    rw [e]
    have h0 : 0 ≤ C * c₁ * 2 ^ (2 + α) * t ^ (2 + α) := mul_nonneg hT1 htγ
    calc |V - Pq| ≤ |V| + |Pq| := abs_sub _ _
      _ ≤ _ := by linarith

omit [FiniteDimensional ℝ E] in
/-- The projection `p − ⟪p, ν⟫ ν` of a point of `halfBall ν x ρ` (centre on the flat part) to the
flat part lies in `halfBall ν x ρ`, at distance `⟪p, ν⟫` from `p`. -/
theorem proj_mem_halfBall {ν x p : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) {ρ : ℝ}
    (hp : p ∈ halfBall ν x ρ) :
    p - ⟪p, ν⟫ • ν ∈ halfBall ν x ρ ∧ p - ⟪p, ν⟫ • ν ∈ flatPart ν ∧
      dist p (p - ⟪p, ν⟫ • ν) = ⟪p, ν⟫ := by
  have hνν : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  have hflat : ⟪p - ⟪p, ν⟫ • ν, ν⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, hνν, mul_one, sub_self]
  have hd : 0 ≤ ⟪p, ν⟫ := hp.2
  refine ⟨⟨?_, hflat.ge⟩, hflat, ?_⟩
  · rw [mem_closedBall, dist_eq_norm]
    have horth : ⟪p - ⟪p, ν⟫ • ν - x, ⟪p, ν⟫ • ν⟫ = 0 := by
      rw [real_inner_smul_right, inner_sub_left, hflat, hx, sub_zero, mul_zero]
    have h1 : ‖p - x‖ ^ 2 = ‖p - ⟪p, ν⟫ • ν - x‖ ^ 2 + ‖⟪p, ν⟫ • ν‖ ^ 2 := by
      have : p - x = (p - ⟪p, ν⟫ • ν - x) + ⟪p, ν⟫ • ν := by abel
      rw [this, norm_add_sq_real, horth]; ring
    have h2 : ‖p - x‖ ≤ ρ := by rw [← dist_eq_norm]; exact hp.1
    have h3 : ‖p - ⟪p, ν⟫ • ν - x‖ ^ 2 ≤ ‖p - x‖ ^ 2 := by
      rw [h1]; nlinarith [sq_nonneg ‖⟪p, ν⟫ • ν‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3 |>.trans h2
  · rw [dist_eq_norm, sub_sub_cancel, norm_smul, hν, mul_one, Real.norm_of_nonneg hd]

omit [FiniteDimensional ℝ E] in
/-- A closed ball around a point at height `d` of `halfBall ν x (r/2)`, of radius `ρ < d` with
`ρ < r/2`, lies in `ball x r ∩ openHalfSpace ν`. -/
theorem closedBall_subset_interior {ν x p : E} (hν : ‖ν‖ = 1) {r ρ : ℝ}
    (hp : p ∈ halfBall ν x (r / 2)) (hρd : ρ < ⟪p, ν⟫) (hρr : ρ < r / 2) :
    closedBall p ρ ⊆ ball x r ∩ openHalfSpace ν := by
  intro y hy
  refine ⟨?_, ?_⟩
  · rw [mem_ball]
    have h1 : dist y p ≤ ρ := hy
    have h2 : dist p x ≤ r / 2 := hp.1
    calc dist y x ≤ dist y p + dist p x := dist_triangle _ _ _
      _ < r := by linarith
  · rw [mem_openHalfSpace]
    have h1 : |⟪y - p, ν⟫| ≤ ‖y - p‖ := by
      have := abs_real_inner_le_norm (y - p) ν; rwa [hν, mul_one] at this
    have h2 : ‖y - p‖ ≤ ρ := by rw [← dist_eq_norm]; exact hy
    have h3 : ⟪y, ν⟫ = ⟪p, ν⟫ + ⟪y - p, ν⟫ := by rw [inner_sub_left]; ring
    rw [h3]
    linarith [neg_abs_le ⟪y - p, ν⟫]

variable [Nontrivial E]

/-- **Two-regime gluing on the half ball.** Let `‖ν‖ = 1`, `x ∈ flatPart ν`, `s = halfBall ν x r`,
`U = ball x r ∩ openHalfSpace ν`, and let `u` be `C²` in `U` with `|u| ≤ M₀` on `s` and
`‖D²u‖ ≤ M₂` in `U`, solving `tr (a D²u) = F` in `U`, where `a` is elliptic on `s` and `a, F` are
`α`-Hölder on `s` with `|F| ≤ M_F`. Suppose that at every flat point `p ∈ halfBall ν x (r/2)` there
is a quadratic `P̄` with `tr (a(p) D²P̄) = F(p)`, `‖quad P̄‖ ≤ B_q` and
`|u(y) − P̄(y − p)| ≤ A_b |y − p|^{2+α}` for `y ∈ s`, `|y − p| < ρ_b`. Then `u` has uniform
expansions of order `2 + α` at every point of `halfBall ν x (r/2)`. -/
theorem polyApproxOn_halfBall_of_boundary {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) {ν x : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) {r : ℝ} (hr : 0 < r)
    {a : E → E →L[ℝ] E} {F u : E → ℝ} {M₀ M₂ MF Ka KF Bq Ab ρb : ℝ}
    (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF) (hBq : 0 ≤ Bq) (hAb : 0 ≤ Ab) (hM₂ : 0 ≤ M₂) (hρb : 0 < ρb)
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r))
    (ha : ∀ y ∈ halfBall ν x r, ∀ y' ∈ halfBall ν x r, ‖a y - a y'‖ ≤ Ka * dist y y' ^ (α : ℝ))
    (hF : ∀ y ∈ halfBall ν x r, ∀ y' ∈ halfBall ν x r, |F y - F y'| ≤ KF * dist y y' ^ (α : ℝ))
    (hFb : ∀ y ∈ halfBall ν x r, |F y| ≤ MF)
    (hu2 : ContDiffOn ℝ 2 u (ball x r ∩ openHalfSpace ν))
    (hu0 : ∀ y ∈ halfBall ν x r, |u y| ≤ M₀)
    (hD2 : ∀ y ∈ ball x r ∩ openHalfSpace ν, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M₂)
    (heq : ∀ y ∈ ball x r ∩ openHalfSpace ν, ∑ i, fderiv ℝ (fderiv ℝ u) y
      (a y (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F y)
    (hbdry : ∀ p ∈ halfBall ν x (r / 2), p ∈ flatPart ν → ∃ P : QuadPoly E,
      ∑ i, P.hess (a p (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F p ∧
      ‖P.quad‖ ≤ Bq ∧ ∀ y ∈ halfBall ν x r, dist y p < ρb →
        |u y - P.eval (y - p)| ≤ Ab * dist y p ^ (2 + (α : ℝ))) :
    ∃ A ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ P : E → QuadPoly E,
      PolyApproxOn 2 α A ρ₀ u (halfBall ν x (r / 2)) P := by
  set αr : ℝ := (α : ℝ) with hαr
  have hα : 0 < αr ∧ αr < 1 := ⟨by exact_mod_cast hα0, by exact_mod_cast hα1⟩
  have hγ : (0 : ℝ) < 2 + αr := by linarith
  set s := halfBall ν x r with hs
  set S := halfBall ν x (r / 2) with hS
  have hSs : S ⊆ s := halfBall_mono ν x (by linarith)
  have hxs : x ∈ s := ⟨mem_closedBall_self hr.le, hx.ge⟩
  have hlamΛ : lam ≤ Λ := lam_le_of_isUniformlyElliptic hell hxs
  obtain ⟨CI, κ, hCI, hκ, hexp0⟩ := expansion_at_point (E := E) hα hlam hlamΛ
  have hexp : InteriorExpansion E αr lam Λ CI κ := hexp0
  set U := ball x r ∩ openHalfSpace ν with hUdef
  have hU : IsOpen U := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hUs : U ⊆ s := inter_subset_inter ball_subset_closedBall (openHalfSpace_subset_halfSpace ν)
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (hu0 x hxs)
  have hMF : 0 ≤ MF := (abs_nonneg _).trans (hFb x hxs)
  set d₁ := min (ρb / 4) (r / 8) with hd₁
  have hd₁0 : 0 < d₁ := lt_min (by positivity) (by positivity)
  have hd₁ρ : d₁ ≤ ρb / 4 := min_le_left _ _
  have hd₁r : d₁ ≤ r / 8 := min_le_right _ _
  set KF' := KF + finrank ℝ E * Bq * Ka with hKF'
  set c₁ := 2 * Ab * 2 ^ (2 + αr) + 2 * KF' + finrank ℝ E * Ka * (M₂ + Bq) with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  set A₁ := CI * c₁ * 2 ^ (2 + αr) + Ab * (1 + 2 / κ) ^ (2 + αr) + Ab * (2 / κ) ^ (2 + αr) +
    2 * CI * c₁ * (2 / κ) ^ (1 + αr) + 4 * CI * c₁ * (2 / κ) ^ αr with hA₁
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  set R₂ := d₁ / 2 with hR₂
  have hR₂0 : 0 < R₂ := by positivity
  set N₂ := 2 * M₀ + R₂ ^ 2 * MF + R₂ ^ (2 + αr) * (KF + finrank ℝ E * Ka * M₂) with hN₂
  set A₂ := CI * N₂ / R₂ ^ (2 + αr) +
    (2 * M₀ + CI * N₂ * d₁ / R₂ + CI * N₂ * d₁ ^ 2 / R₂ ^ 2) / (κ * R₂) ^ (2 + αr) with hA₂
  have hA₂0 : 0 ≤ A₂ := by rw [hA₂, hN₂]; positivity
  have key : ∀ p ∈ S, ∃ Pp : QuadPoly E, ∀ q ∈ S, dist q p < d₁ →
      |u q - Pp.eval (q - p)| ≤ (Ab + A₁ + A₂) * dist q p ^ (2 + αr) := by
    intro p hp
    have hps : p ∈ s := hSs hp
    rcases (show 0 ≤ ⟪p, ν⟫ from hp.2).eq_or_lt with h0 | hpos
    · -- flat points
      obtain ⟨P, -, -, happ⟩ := hbdry p hp h0.symm
      refine ⟨P, fun q hq hqd ↦ (happ q (hSs hq) (by linarith)).trans ?_⟩
      have : 0 ≤ dist q p ^ (2 + αr) := Real.rpow_nonneg dist_nonneg _
      gcongr; linarith
    by_cases hsmall : ⟪p, ν⟫ < d₁
    · -- near the flat part
      set d := ⟪p, ν⟫ with hd
      set pb := p - d • ν with hpb
      obtain ⟨hpbS, hpbf, hppb0⟩ := proj_mem_halfBall hν hx hp
      have hppb : dist p pb = d := hppb0
      obtain ⟨Pb, hcons, hq, happ⟩ := hbdry pb hpbS hpbf
      have hBU : closedBall p (d / 2) ⊆ U :=
        closedBall_subset_interior hν hp (by linarith) (by linarith)
      obtain ⟨P, hPc, hPe, hP0⟩ := near_expansion hα hCI hκ hexp hU hu2 heq hpos hppb
        (by linarith) hBU (hBU.trans hUs) (hSs hpbS) ha hF hKa hKF hBq hAb
        (hell p hps).1 (hell p hps).2 hD2 hcons hq happ hKF' hc₁
      refine ⟨(Pb.shift (-pb)).shift p + P, fun q hq hqd ↦ ?_⟩
      have hcalc : u q - ((Pb.shift (-pb)).shift p + P).eval (q - p) =
          (u q - Pb.eval (q - pb)) - P.eval (q - p) := by
        rw [QuadPoly.eval_add, QuadPoly.eval_shift, QuadPoly.eval_shift, sub_add_cancel,
          ← sub_eq_add_neg]; ring
      rw [hcalc]
      have ht0 : 0 ≤ dist q p := dist_nonneg
      have hqpb : dist q pb ≤ dist q p + d := by
        rw [← hppb]; exact dist_triangle _ _ _
      refine near_bound hα hCI hκ hc₁0 hAb hpos ht0 (Vp := u p - Pb.eval (p - pb))
        (fun h ↦ hPe q h) (fun hfar ↦ ?_) ?_ ?_ |>.trans ?_
      · refine (happ q (hSs hq) (by linarith)).trans ?_
        gcongr
        have : d ≤ 2 / κ * dist q p := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hκ]; linarith
        linarith
      · have := happ p hps (by rw [hppb]; linarith)
        rwa [hppb] at this
      · have := abs_eval_le_of_coeff (by positivity) hPc (z := q - p) (ρ := dist q p)
          (by rw [← dist_eq_norm])
        rwa [hP0] at this
      · have : 0 ≤ dist q p ^ (2 + αr) := Real.rpow_nonneg dist_nonneg _
        refine mul_le_mul_of_nonneg_right ?_ this
        rw [← hA₁]; linarith
    · -- far from the flat part
      have hd₁p : d₁ ≤ ⟪p, ν⟫ := not_lt.1 hsmall
      have hBU : closedBall p R₂ ⊆ U :=
        closedBall_subset_interior hν hp (by linarith) (by linarith)
      obtain ⟨P, hP⟩ := approx_regime_interior hα hCI hκ hexp hU (T := s) hR₂0 hBU
        (isSolOn_of_fderiv hU (hu2) heq) (hell p hps).1 (hell p hps).2
        (fun y hy ↦ ha y (hUs (hBU (ball_subset_closedBall hy))) p hps)
        (fun y hy ↦ hF y (hUs (hBU (ball_subset_closedBall hy))) p hps) hKa hKF (hFb p hps)
        hps (fun y hy ↦ hUs (hBU (ball_subset_closedBall hy))) hu0
        (fun y hy ↦ by
          rw [← norm_fderiv_fderiv_eq]; exact hD2 y (hBU (ball_subset_closedBall hy))) hN₂
        (ρ₀ := d₁)
      refine ⟨P, fun q hq hqd ↦ (hP q (hSs hq) hqd).trans ?_⟩
      have : 0 ≤ dist q p ^ (2 + αr) := Real.rpow_nonneg dist_nonneg _
      refine mul_le_mul_of_nonneg_right ?_ this
      rw [← hA₂]; linarith
  choose! P hP using key
  refine ⟨Ab + A₁ + A₂, d₁, hd₁0, P, ⟨fun _ _ ↦ trivial, fun p hp q hq hqd ↦ ?_⟩⟩
  have := hP p hp q hq hqd
  simpa using this

end Nondiv

end BasicElliptic
