/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Interior.PolyOps
public import BasicElliptic.Harmonic.DirichletBall
public import BasicElliptic.Harmonic.MaxPrinciple
public import BasicElliptic.Harmonic.Taylor
public import BasicElliptic.Harmonic.Estimates

/-!
# One step of the nondivergence iteration: improvement of flatness

Throughout `B₁ = ball 0 1` in a nontrivial finite-dimensional real inner product space `E`, `d = dim
E`.

* `Nondiv.abs_sub_le_of_harmonic_eqOn_sphere` (**comparison**): if `u ∈ C²(B₁) ∩ C(B̄₁)` has
  `|Δu| ≤ δ` in `B₁` and `h` is harmonic in `B₁`, continuous on `B̄₁`, with `h = u` on the
  sphere, then `|u − h| ≤ δ` on `B̄₁`. The barrier `δ (1 − |z|²) / (2d)` and the classical
  maximum principle for functions `C²` inside and continuous up to the boundary
  (`le_of_frontier_le_of_contDiffOn_two`) give `|u − h| ≤ δ / (2d)`; no `C²` regularity up to the
  sphere is needed.
* `Nondiv.taylorPoly h`: the second-order Taylor polynomial of `h` at the origin.
* `Nondiv.improvement_of_flatness`: there are `ρ ∈ (0, 1/4]` and `C₀ ≥ 0`, depending only on
  `E` and `α`, such that if `u ∈ C²(B₁) ∩ C(B̄₁)`, `|u| ≤ 1` and `|Δu| ≤ ρ^{2+α}/4` in `B₁`,
  then a quadratic polynomial `Q` with `tr Q = 0` and `sumNorm Q ≤ C₀` satisfies
  `|u − Q| ≤ ρ^{2+α}` on `ball 0 ρ`. The model is the harmonic replacement `h` of `u`
  (`exists_harmonic_ball_boundary`), and `Q` is its Taylor polynomial (`harmonic_taylor_le`,
  `norm_iteratedFDeriv_le_of_harmonic`).

## Provenance

Elliptic port of parabolic-basic-theory (own repository, commit
`2507d9a800377e91c591862286b2ba2d6464d918`), `ParabolicBasic/Schauder/Iteration/Approx.lean`
(`exists_caloric_approx`, `taylor_approx`) and `ParabolicBasic/Schauder/Iteration/Step.lean`
(`improvement_of_flatness`). Changes: caloric → harmonic; the viscosity comparison is replaced by
the classical `C²` maximum principle with an explicit barrier; the degree is fixed to `2` and the
source normalization is `|Δu| ≤ δ` (the constraint `src = 0` becomes `tr Q = 0`).
-/

public section

open Metric Set Filter Topology Module InnerProductSpace
open scoped InnerProductSpace Laplacian

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A bound on the open ball passes to the closed ball for a function continuous there. -/
theorem abs_le_on_closedBall_of_ball {u : E → ℝ} {x : E} {r M : ℝ} (hr : r ≠ 0)
    (hu : ContinuousOn u (closedBall x r)) (h : ∀ z ∈ ball x r, |u z| ≤ M) :
    ∀ z ∈ closedBall x r, |u z| ≤ M := by
  rw [← closure_ball x hr] at hu ⊢
  intro z hz
  have h1 := (continuous_abs.comp_continuousOn hu).image_closure (mem_image_of_mem _ hz)
  have h2 : closure ((fun q ↦ |u q|) '' ball x r) ⊆ Iic M :=
    closure_minimal (by rintro _ ⟨q, hq, rfl⟩; exact h q hq) isClosed_Iic
  exact h2 h1

variable [Nontrivial E]

omit [Nontrivial E] in
/-- The barrier `c (1 − ‖z‖²)` has Laplacian `−2 d c`. -/
private theorem laplacian_barrier (c : ℝ) (x : E) :
    Δ (fun y : E ↦ c - c * ‖y - 0‖ ^ 2) x = -(c * (2 * finrank ℝ E)) := by
  have hq : ContDiffAt ℝ 2 (fun y : E ↦ ‖y - 0‖ ^ 2) x :=
    (contDiff_norm_sub_sq (0 : E)).contDiffAt.of_le (by norm_cast)
  have e : (fun y : E ↦ c - c * ‖y - 0‖ ^ 2) = (fun _ ↦ c) - c • fun y : E ↦ ‖y - 0‖ ^ 2 := by
    funext y; simp [smul_eq_mul]
  rw [e, ContDiffAt.laplacian_sub (f₁ := fun _ ↦ c) (f₂ := c • fun y : E ↦ ‖y - 0‖ ^ 2)
    contDiffAt_const (hq.const_smul c), laplacian_smul c hq,
    laplacian_norm_sub_sq, laplacian_const]
  simp

/-- **Comparison with the harmonic replacement.** If `u ∈ C²(B₁) ∩ C(B̄₁)` has `|Δu| ≤ δ` in
`B₁`, and `h` is harmonic in `B₁`, continuous on `B̄₁` and equal to `u` on the unit sphere, then
`|u − h| ≤ δ` on `B̄₁`. (The barrier `δ (1 − ‖z‖²) / (2d)` gives the sharper `δ / (2d)`.) -/
theorem abs_sub_le_of_harmonic_eqOn_sphere {u h : E → ℝ} {δ : ℝ}
    (hu : ContinuousOn u (closedBall 0 1)) (hu2 : ContDiffOn ℝ 2 u (ball 0 1))
    (hΔ : ∀ z ∈ ball (0 : E) 1, |Δ u z| ≤ δ) (hh : ContinuousOn h (closedBall 0 1))
    (hharm : HarmonicOnNhd h (ball 0 1)) (hbd : EqOn h u (sphere 0 1)) :
    ∀ z ∈ closedBall (0 : E) 1, |u z - h z| ≤ δ := by
  have hd : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
  have hd1 : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast finrank_pos
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hΔ 0 (mem_ball_self one_pos))
  set c : ℝ := δ / (2 * finrank ℝ E) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcδ : c * (2 * finrank ℝ E) = δ := by rw [hc]; field_simp
  have hcle : c ≤ δ := by
    rw [hc, div_le_iff₀ (by positivity)]; nlinarith
  set B : E → ℝ := fun y ↦ c - c * ‖y - 0‖ ^ 2 with hB
  have hΔB : ∀ x, Δ B x = -δ := fun x ↦ by rw [hB, laplacian_barrier, hcδ]
  have hBc : ContinuousOn B (closure (ball (0 : E) 1)) :=
    (continuous_const.sub (continuous_const.mul
      ((continuous_id.sub continuous_const).norm.pow 2))).continuousOn
  have hB2 : ContDiffOn ℝ 2 B (ball 0 1) :=
    (contDiff_const.sub (contDiff_const.mul
      ((contDiff_norm_sub_sq (0 : E)).of_le (by norm_cast)))).contDiffOn
  have hcl : closure (ball (0 : E) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hfr : frontier (ball (0 : E) 1) = sphere 0 1 := frontier_ball 0 one_ne_zero
  have hh2 : ContDiffOn ℝ 2 h (ball 0 1) := hharm.contDiffOn
  have hΔh : ∀ x ∈ ball (0 : E) 1, Δ h x = 0 := fun x hx ↦ (hharm x hx).2.eq_of_nhds
  have hat : ∀ x ∈ ball (0 : E) 1, ContDiffAt ℝ 2 u x ∧ ContDiffAt ℝ 2 h x := fun x hx ↦
    ⟨hu2.contDiffAt (isOpen_ball.mem_nhds hx), hh2.contDiffAt (isOpen_ball.mem_nhds hx)⟩
  have hBfr : ∀ x ∈ frontier (ball (0 : E) 1), B x = 0 := by
    intro x hx
    rw [hfr, mem_sphere, dist_zero_right] at hx
    simp [hB, hx]
  have hBle : ∀ z ∈ closedBall (0 : E) 1, B z ≤ δ := by
    intro z _
    have : 0 ≤ c * ‖z - 0‖ ^ 2 := by positivity
    simp only [hB]; linarith
  rw [← hcl] at hu hh
  -- upper bound `u − h ≤ B`
  have hup := le_of_frontier_le_of_contDiffOn_two isOpen_ball isBounded_ball (u := u - h)
    (v := B) (hu2.sub hh2) hB2 (fun x hx ↦ by
      rw [hΔB, (hat x hx).1.laplacian_sub (hat x hx).2, hΔh x hx, sub_zero]
      exact (neg_le_of_abs_le (hΔ x hx)))
    (hu.sub hh) hBc (fun x hx ↦ by
      rw [hBfr x hx, Pi.sub_apply, hfr ▸ hx |> fun h' ↦ hbd h', sub_self])
  -- lower bound `h − u ≤ B`
  have hlo := le_of_frontier_le_of_contDiffOn_two isOpen_ball isBounded_ball (u := h - u)
    (v := B) (hh2.sub hu2) hB2 (fun x hx ↦ by
      rw [hΔB, (hat x hx).2.laplacian_sub (hat x hx).1, hΔh x hx, zero_sub, neg_le_neg_iff]
      exact le_of_abs_le (hΔ x hx))
    (hh.sub hu) hBc (fun x hx ↦ by
      rw [hBfr x hx, Pi.sub_apply, hfr ▸ hx |> fun h' ↦ hbd h', sub_self])
  intro z hz
  rw [← hcl] at hz
  have a := hup z hz
  have b := hlo z hz
  simp only [Pi.sub_apply] at a b
  rw [hcl] at hz
  have := hBle z hz
  rw [abs_le]; constructor <;> linarith

omit [Nontrivial E] in
/-- The second-order Taylor polynomial of `h` at the origin. Exposed so that its coefficients can be
read off. -/
@[expose] noncomputable def taylorPoly (h : E → ℝ) : QuadPoly E :=
  ⟨h 0, fderiv ℝ h 0, fderiv ℝ (fderiv ℝ h) 0⟩

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem taylorPoly_eval (h : E → ℝ) (z : E) :
    (taylorPoly h).eval z = h 0 + fderiv ℝ h 0 z + 1 / 2 * fderiv ℝ (fderiv ℝ h) 0 z z := by
  simp [taylorPoly, QuadPoly.eval]

omit [Nontrivial E] in
/-- The Taylor polynomial of a function harmonic at the origin is traceless. -/
theorem trace_taylorPoly {h : E → ℝ} (hh : HarmonicAt h 0) : (taylorPoly h).trace = 0 := by
  have h0 : Δ h 0 = 0 := hh.2.eq_of_nhds
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis] at h0
  simp only [iteratedFDeriv_two_apply] at h0
  rw [← h0]
  rfl

/-- **Improvement of flatness** (elliptic, degree two). There are `ρ ∈ (0, 1/4]` and `C₀ ≥ 0`
depending only on `E` and `α` such that: if `u ∈ C²(B₁) ∩ C(B̄₁)`, `|u| ≤ 1` and
`|Δu| ≤ ρ^{2+α}/4` in `B₁`, then there is a quadratic polynomial `Q` with `tr Q = 0`,
`sumNorm Q ≤ C₀` and `|u − Q| ≤ ρ^{2+α}` on `ball 0 ρ`. -/
theorem improvement_of_flatness {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ ρ C₀ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ 0 ≤ C₀ ∧ ∀ {u : E → ℝ},
      ContinuousOn u (closedBall 0 1) → ContDiffOn ℝ 2 u (ball 0 1) →
      (∀ z ∈ ball (0 : E) 1, |u z| ≤ 1) →
      (∀ z ∈ ball (0 : E) 1, |Δ u z| ≤ ρ ^ (2 + α) / 4) →
      ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧
        ∀ z ∈ ball (0 : E) ρ, |u z - Q.eval z| ≤ ρ ^ (2 + α) := by
  obtain ⟨CT₀, hCT₀, hT⟩ := harmonic_taylor_le E
  obtain ⟨CD, hCD, hD⟩ := norm_iteratedFDeriv_le_of_harmonic E
  set CT := max (8 * CT₀) 2 with hCTdef
  have hCT2 : 2 ≤ CT := le_max_right _ _
  have hb : 0 < 2 * CT := by positivity
  have h1α : 0 < 1 - α := by linarith
  set ρ := (2 * CT) ^ (-(1 / (1 - α))) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hb _
  have hρα : ρ ^ (1 - α) = (2 * CT)⁻¹ := by
    rw [hρdef, ← Real.rpow_mul hb.le,
      show -(1 / (1 - α)) * (1 - α) = -1 by field_simp, Real.rpow_neg_one]
  have hρ1 : ρ ≤ 1 := by
    refine (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) ?_).le
    have : 0 < 1 / (1 - α) := by positivity
    linarith
  have hρq : ρ ≤ 1 / 4 := by
    calc ρ = ρ ^ (1 : ℝ) := (Real.rpow_one ρ).symm
      _ ≤ ρ ^ (1 - α) := Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by linarith)
      _ = (2 * CT)⁻¹ := hρα
      _ ≤ 4⁻¹ := inv_anti₀ (by norm_num) (by linarith)
      _ = 1 / 4 := by norm_num
  have hγ : 0 ≤ ρ ^ (2 + α) := Real.rpow_nonneg hρ0.le _
  have hkey : CT₀ * 1 * (ρ / (1 / 2)) ^ 3 ≤ ρ ^ (2 + α) / 2 := by
    have e : ρ ^ 3 = ρ ^ (2 + α) * ρ ^ (1 - α) := by
      rw [← Real.rpow_add hρ0, ← Real.rpow_natCast]
      congr 1; push_cast; ring
    have e2 : CT₀ * 1 * (ρ / (1 / 2)) ^ 3 = 8 * CT₀ * ρ ^ 3 := by ring
    rw [e2, e, hρα]
    have hCTne : CT ≠ 0 := by positivity
    calc 8 * CT₀ * (ρ ^ (2 + α) * (2 * CT)⁻¹) ≤ CT * (ρ ^ (2 + α) * (2 * CT)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = ρ ^ (2 + α) / 2 := by field_simp
  refine ⟨ρ, 1 + 2 * CD + 4 * CD, hρ0, hρq, by positivity, fun {u} hu hu2 hu1 hΔ ↦ ?_⟩
  have hu1' := abs_le_on_closedBall_of_ball one_ne_zero hu hu1
  obtain ⟨h, hhc, hharm, hbd⟩ := exists_harmonic_ball_boundary (0 : E) one_pos
    (hu.mono sphere_subset_closedBall)
  have hh1 : ∀ y ∈ closedBall (0 : E) 1, |h y| ≤ 1 :=
    abs_le_of_harmonic_ball one_pos hharm hhc fun y hy ↦ by
      rw [hbd hy]; exact hu1' y (sphere_subset_closedBall hy)
  have huh := abs_sub_le_of_harmonic_eqOn_sphere hu hu2 hΔ hhc hharm hbd
  have hhalf : closedBall (0 : E) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have hharm' : HarmonicOnNhd h (closedBall 0 (1 / 2)) := fun y hy ↦ hharm y (hhalf hy)
  have hh1' : ∀ y ∈ closedBall (0 : E) (1 / 2), |h y| ≤ 1 := fun y hy ↦
    hh1 y (ball_subset_closedBall (hhalf hy))
  refine ⟨taylorPoly h, trace_taylorPoly (hharm 0 (mem_ball_self one_pos)), ?_, ?_⟩
  · have h0 : |h 0| ≤ 1 := hh1 0 (mem_closedBall_self zero_le_one)
    have h1 := hD 1 (by norm_num) h 0 (1 / 2) 1 (by norm_num) hharm' hh1'
    have h2 := hD 2 (by norm_num) h 0 (1 / 2) 1 (by norm_num) hharm' hh1'
    rw [norm_iteratedFDeriv_one] at h1
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h2
    simp only [QuadPoly.sumNorm, taylorPoly]
    have e1 : CD * 1 / (1 / 2) ^ 1 = 2 * CD := by ring
    have e2 : CD * 1 / (1 / 2) ^ 2 = 4 * CD := by ring
    rw [e1] at h1; rw [e2] at h2
    linarith
  · intro z hz
    have hzρ : z ∈ closedBall (0 : E) ρ := ball_subset_closedBall hz
    have hz1 : z ∈ closedBall (0 : E) 1 :=
      closedBall_subset_closedBall hρ1 hzρ
    have a := huh z hz1
    have b := (hT h 0 (1 / 2) ρ 1 (by norm_num) (by linarith) hharm' hh1' z hzρ).2.2
    simp only [sub_zero] at b
    rw [taylorPoly_eval]
    calc |u z - (h 0 + fderiv ℝ h 0 z + 1 / 2 * fderiv ℝ (fderiv ℝ h) 0 z z)|
        = |(u z - h z) + (h z - h 0 - fderiv ℝ h 0 z - 1 / 2 * fderiv ℝ (fderiv ℝ h) 0 z z)| := by
          ring_nf
      _ ≤ |u z - h z| + |h z - h 0 - fderiv ℝ h 0 z - 1 / 2 * fderiv ℝ (fderiv ℝ h) 0 z z| :=
          abs_add_le _ _
      _ ≤ ρ ^ (2 + α) := by linarith

end Nondiv

end BasicElliptic
