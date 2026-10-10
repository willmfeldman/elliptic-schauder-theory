/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Nondiv
import BasicElliptic.Nondiv.Interior.Estimate
import BasicElliptic.Poly.Bridge

/-!
# Interior Schauder theory in nondivergence form

`Nondiv.contDiffHolderOn_two_of_isSolution` and `Nondiv.schauder_ball_estimate` prove
`Nondiv.SchauderInteriorStatement` and `Nondiv.SchauderBallEstimateStatement`.

## The qualitative theorem

Let `closedBall z ρ ⊆ U`. By compactness there is `δ > 0` with `closedBall z (δ + ρ) ⊆ U`. On
this compact ball the `C²` solution `w` has **finite** bounds `sup |w|`, `sup ‖Dw‖`,
`sup ‖D²w‖` (continuity of the derivatives on the open set `U`), and `b, f` are bounded (Hölder,
hence continuous). These finite bounds are proved here, not assumed. For every
`x₀ ∈ closedBall z ρ`, `Nondiv.expansion_at_point` (freezing the coefficients at `x₀`, harmonic
approximation and the sup-norm Campanato iteration) gives a quadratic `P x₀` with
`|w(y) − P x₀ (y − x₀)| ≤ A |y − x₀|^{2+α}` for `|y − x₀| < κ δ`, where `A` and `κ` do not depend
on `x₀`. The bridge `contDiffOn_two_of_polyApprox` turns these uniform expansions into
`ContDiffHolderOn 2 α w (closedBall z ρ)`.

## The scaled estimate

`Nondiv.schauder_ball_estimate` follows from `Nondiv.ball_estimate_of_nontrivial`
(`Nondiv/Interior/Estimate.lean`): a weighted sup of `(ρ − |y − x|)² ‖D²w(y)‖` over `ball x ρ`,
`ρ < r`, is finite (continuity of `D²w` on the compact `closedBall x ρ`) and is absorbed using
the frozen expansions; the Hölder seminorm on `closedBall x (r/2)` then comes from two
expansions at nearby points.

## References

* L. A. Caffarelli, *Interior a priori estimates for solutions of fully non-linear equations*,
  Ann. of Math. (2) 130 (1989), no. 1, 189–213.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001. (GT)
-/

public section

open Metric Set Module
open scoped NNReal RealInnerProductSpace

namespace BasicElliptic

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem contDiffHolderOn_of_subsingleton {w : E → ℝ} {S U : Set E} {α : ℝ≥0}
    (hS : S.Subsingleton) (hSU : S ⊆ U) (hw : ContDiffOn ℝ 2 w U) :
    ContDiffHolderOn 2 α w S := by
  refine ⟨by exact_mod_cast hw.mono hSU, 0, fun x hx y hy ↦ ?_⟩
  rw [hS hx hy, edist_self]
  exact bot_le

/-- **Interior Schauder regularity, nondivergence form** (GT, via Caffarelli's
polynomial approximation). A `C²` solution of `tr (a D²w) + ⟪b, ∇w⟫ = f` on an open
`U`, with `a` uniformly elliptic and `a, b, f ∈ C^α(U)`, is `C^{2,α}` on every closed ball in `U`.
-/
theorem Nondiv.contDiffHolderOn_two_of_isSolution : Nondiv.SchauderInteriorStatement E := by
  intro α hα0 hα1 U lam Λ Ka Kb Kf a b f w hU hlam hell ha hb hf hsol z ρ hzU
  by_cases hsub : (closedBall z ρ).Subsingleton
  · exact contDiffHolderOn_of_subsingleton E hsub hzU hsol.1
  -- `ρ > 0` and `E` is nontrivial
  have hρ : 0 < ρ := by
    by_contra hρ
    refine hsub fun x hx y hy ↦ ?_
    have h1 : dist x z ≤ 0 := (mem_closedBall.1 hx).trans (not_lt.1 hρ)
    have h2 : dist y z ≤ 0 := (mem_closedBall.1 hy).trans (not_lt.1 hρ)
    rw [dist_le_zero.1 h1, dist_le_zero.1 h2]
  obtain ⟨x₁, -, x₂, -, hx₁₂⟩ := Set.not_subsingleton_iff.1 hsub
  have : Nontrivial E := ⟨⟨x₁, x₂, hx₁₂⟩⟩
  have hα : 0 < (α : ℝ) ∧ (α : ℝ) < 1 := ⟨hα0, hα1⟩
  have hzU' : z ∈ U := hzU (mem_closedBall_self hρ.le)
  have hlamΛ : lam ≤ Λ := Nondiv.lam_le_of_isUniformlyElliptic hell hzU'
  -- a compact margin inside `U`
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall z ρ).exists_cthickening_subset_open hU hzU
  rw [cthickening_closedBall hδ.le hρ.le] at hδU
  set K := closedBall z (δ + ρ) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hball : ∀ x₀ ∈ closedBall z ρ, closedBall x₀ δ ⊆ K := fun x₀ hx₀ y hy ↦ by
    rw [mem_closedBall] at hx₀ hy ⊢
    linarith [dist_triangle y x₀ z]
  -- finite bounds on the compact set `K` (proved, not assumed)
  have hU2 : ContDiffOn ℝ 2 w U := hsol.1
  have hcD2 : ContinuousOn (iteratedFDeriv ℝ 2 w) U :=
    (hU2.continuousOn_iteratedFDerivWithin le_rfl hU.uniqueDiffOn).congr
      fun y hy ↦ (iteratedFDerivWithin_of_isOpen 2 hU hy).symm
  obtain ⟨Mw, hMw⟩ := hKc.exists_bound_of_continuousOn (hU2.continuousOn.mono hδU)
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn
    ((hU2.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hδU)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (hcD2.mono hδU)
  obtain ⟨Mb, hMb⟩ := hKc.exists_bound_of_continuousOn ((hb.continuousOn hα0).mono hδU)
  obtain ⟨Mf, hMf⟩ := hKc.exists_bound_of_continuousOn ((hf.continuousOn hα0).mono hδU)
  -- the uniform pointwise expansions
  obtain ⟨C, κ, hC, hκ, hexp⟩ := Nondiv.expansion_at_point (E := E) hα hlam hlamΛ
  set N : ℝ := 2 * Mw + δ ^ 2 * (Mf + Mb * M₁) + δ ^ (2 + (α : ℝ)) *
    (Kf + Kb * (M₁ + M₂ * δ) + Mb * M₂ * δ ^ (1 - (α : ℝ)) + finrank ℝ E * Ka * M₂) with hN
  have hpt : ∀ x₀ ∈ closedBall z ρ, ∃ P : QuadPoly E, ∀ y, dist y x₀ < κ * δ →
      |w y - P.eval (y - x₀)| ≤ C * N * (dist y x₀ / δ) ^ (2 + (α : ℝ)) := by
    intro x₀ hx₀
    have hBK := hball x₀ hx₀
    have hBU : closedBall x₀ δ ⊆ U := hBK.trans hδU
    have hbU : ball x₀ δ ⊆ U := ball_subset_closedBall.trans hBU
    have hx₀K : x₀ ∈ K := hBK (mem_closedBall_self hδ.le)
    have hx₀U : x₀ ∈ U := hδU hx₀K
    obtain ⟨P, -, hP⟩ := hexp U a b f w x₀ δ (2 * Mw) M₁ M₂ Mb Mf Ka Kb Kf hU hδ hBU hsol
      (hell x₀ hx₀U).1 (hell x₀ hx₀U).2
      (fun y hy ↦ by rw [← dist_eq_norm]; exact ha.dist_le (hbU hy) hx₀U)
      (fun y hy ↦ by rw [← dist_eq_norm]; exact hb.dist_le (hbU hy) hx₀U)
      (fun y hy ↦ by rw [← Real.dist_eq]; exact hf.dist_le (hbU hy) hx₀U)
      Ka.2 Kb.2 Kf.2 (hMb x₀ hx₀K) (by simpa using hMf x₀ hx₀K) (hM₁ x₀ hx₀K)
      (fun y hy ↦ by
        have h1 := hMw y (hBK (ball_subset_closedBall hy))
        have h2 := hMw x₀ hx₀K
        rw [Real.norm_eq_abs] at h1 h2
        calc |w y - w x₀| ≤ |w y| + |w x₀| := abs_sub _ _
          _ ≤ 2 * Mw := by linarith)
      (fun y hy ↦ hM₂ y (hBK (ball_subset_closedBall hy)))
    exact ⟨P, hP⟩
  choose! P hP using hpt
  have happrox : PolyApproxOn 2 α (C * N / δ ^ (2 + (α : ℝ))) (κ * δ) w (closedBall z ρ) P := by
    refine ⟨fun _ _ ↦ trivial, fun p hp q _ hd ↦ ?_⟩
    have := hP p hp q hd
    rw [Real.div_rpow dist_nonneg hδ.le] at this
    push_cast
    calc |w q - (P p).eval (q - p)| ≤ C * N * (dist q p ^ (2 + (α : ℝ)) / δ ^ (2 + (α : ℝ))) :=
          this
      _ = C * N / δ ^ (2 + (α : ℝ)) * dist q p ^ (2 + (α : ℝ)) := by ring
  have hint : (interior (closedBall z ρ)).Nonempty :=
    ⟨z, interior_maximal ball_subset_closedBall isOpen_ball (mem_ball_self hρ)⟩
  exact (contDiffOn_two_of_polyApprox hα0 hα1.le (mul_pos hκ hδ) (convex_closedBall z ρ)
    isBounded_closedBall hint happrox).1

/-- **Scaled interior Schauder estimate, nondivergence form** (GT, scaled):
`r² ‖D²w(x)‖ + r^{2+α} [D²w]_{α, B̄_{r/2}} ≤ C (osc_{B̄_r} w + r² M_f + r^{2+α} K_f)` with
`C = C(E, α, lam, Λ, K)`. In a nontrivial space this is `Nondiv.ball_estimate_of_nontrivial`
(absorption with finiteness proved from `C²` on compact balls); if `lam > Λ` the hypotheses are
void, and in the zero space `D²w = 0`. -/
theorem Nondiv.schauder_ball_estimate : Nondiv.SchauderBallEstimateStatement E := by
  intro α hα0 hα1 lam Λ K hlam
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨0, fun x r Ka Kb Kf Mb Mf a b f w _ _ _ _ _ _ _ _ _ _ _ ↦ ?_⟩
    have hz : ∀ y, iteratedFDeriv ℝ 2 w y = 0 := fun y ↦ by
      ext m
      rw [Subsingleton.elim m 0, ContinuousMultilinearMap.map_zero]
      rfl
    have hs : holderSeminormOn α (iteratedFDeriv ℝ 2 w) (closedBall x (r / 2)) ≤ 0 :=
      holderSeminormOn_le_of_dist_le le_rfl fun p _ q _ ↦ by simp [hz]
    simp only [hz, norm_zero, mul_zero, zero_add, zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hs
  by_cases hΛ : lam ≤ Λ
  · obtain ⟨C, -, h⟩ := Nondiv.ball_estimate_of_nontrivial (E := E) hα0 hα1 hlam hΛ K
    exact ⟨C, h⟩
  · exact ⟨0, fun x r _ _ _ _ _ _ _ _ _ hr hell _ _ _ _ _ _ _ _ _ ↦
      absurd (Nondiv.lam_le_of_isUniformlyElliptic hell (mem_ball_self hr)) hΛ⟩

end BasicElliptic
