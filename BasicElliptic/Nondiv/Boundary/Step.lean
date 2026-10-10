/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Boundary.Comparison
public import BasicElliptic.Nondiv.Boundary.Model
public import BasicElliptic.Nondiv.Interior.Step

/-!
# One step of the boundary iteration: improvement of flatness on the half ball

`ν` is a unit vector, `B₁⁺ = halfBall ν 0 1` (closed) and `ball 0 1 ∩ openHalfSpace ν` its interior.
Normal derivatives at flat points are right-derivatives of `t ↦ u (z + t • ν)` at `0`.

* `Nondiv.exists_harmonic_taylor_step`: the harmonic part of the interior step
  (`Nondiv.improvement_of_flatness`): there are `ρ ∈ (0, 1/4]` and `C₀` (depending only on `E`
  and `α`) such that a harmonic `h` on `B₁` with `|h| ≤ 1` is approximated by its Taylor
  polynomial to `ρ^{2+α}/2` on `closedBall 0 ρ`.
* `Nondiv.improvement_of_flatness_neumann`: if `u ∈ C(B̄₁⁺) ∩ C²(B₁⁺)`, `|u| ≤ 1`,
  `|Δu| ≤ ρ^{2+α}/4` and `|∂_ν u| ≤ ρ^{2+α}/4` on the flat part, then an **even** traceless
  quadratic `Q` with `sumNorm Q ≤ C₀` satisfies `|u − Q| ≤ ρ^{2+α}` on `halfBall ν 0 ρ`. The model
  is the even harmonic replacement (`exists_harmonic_even_halfBall`), the error is controlled by
  the Neumann barrier (`abs_le_of_halfBall_neumann`), and `Q` is the even part of the Taylor
  polynomial of the model.
* `Nondiv.improvement_of_flatness_dirichlet`: the same with `u = 0` on the flat part, an odd
  model (`exists_harmonic_odd_halfBall`), the Dirichlet barrier, and `Q` vanishing on the flat
  part (the odd part of the Taylor polynomial).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001. (GT)
* G. M. Lieberman, *Oblique Derivative Problems for Elliptic Equations*, World Scientific, 2013.
* E. Milakis, L. E. Silvestre, *Regularity for fully nonlinear elliptic equations with Neumann
  boundary data*, Comm. Partial Differential Equations 31 (2006), no. 8, 1227–1252.

## Provenance

The structure is that of `Nondiv.improvement_of_flatness`, itself a port of
parabolic-basic-theory `ParabolicBasic/Schauder/Iteration/Step.lean` (own repository); the
reflection models replace the full-ball harmonic replacement (GT, Lieberman Ch. 4;
Milakis–Silvestre 2006 for the sup-norm boundary iteration).
-/

public section

open Metric Set Filter Topology Module InnerProductSpace
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]

omit [Nontrivial E] in
/-- **Harmonic Taylor step.** There are `ρ ∈ (0, 1/4]` and `C₀ ≥ 0`, depending only on `E` and
`α`, such that for `h` harmonic in `B₁`, continuous on `B̄₁`, with `|h| ≤ 1`, the Taylor
polynomial `T` of `h` at `0` is traceless, `sumNorm T ≤ C₀` and `|h − T| ≤ ρ^{2+α}/2` on
`closedBall 0 ρ`. -/
theorem exists_harmonic_taylor_step {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ ρ C₀ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ 0 ≤ C₀ ∧ ∀ {h : E → ℝ},
      ContinuousOn h (closedBall 0 1) → HarmonicOnNhd h (ball 0 1) →
      (∀ z ∈ closedBall (0 : E) 1, |h z| ≤ 1) →
      ∃ T : QuadPoly E, T.trace = 0 ∧ T.sumNorm ≤ C₀ ∧
        ∀ z ∈ closedBall (0 : E) ρ, |h z - T.eval z| ≤ ρ ^ (2 + α) / 2 := by
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
  refine ⟨ρ, 1 + 2 * CD + 4 * CD, hρ0, hρq, by positivity, fun {h} hhc hharm hh1 ↦ ?_⟩
  have hhalf : closedBall (0 : E) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have hharm' : HarmonicOnNhd h (closedBall 0 (1 / 2)) := fun y hy ↦ hharm y (hhalf hy)
  have hh1' : ∀ y ∈ closedBall (0 : E) (1 / 2), |h y| ≤ 1 := fun y hy ↦
    hh1 y (ball_subset_closedBall (hhalf hy))
  refine ⟨taylorPoly h, trace_taylorPoly (hharm 0 (mem_ball_self one_pos)), ?_, fun z hz ↦ ?_⟩
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
  · have b := (hT h 0 (1 / 2) ρ 1 (by norm_num) (by linarith) hharm' hh1' z hz).2.2
    simp only [sub_zero] at b
    rw [taylorPoly_eval]
    calc |h z - (h 0 + fderiv ℝ h 0 z + 1 / 2 * fderiv ℝ (fderiv ℝ h) 0 z z)|
        = |h z - h 0 - fderiv ℝ h 0 z - 1 / 2 * fderiv ℝ (fderiv ℝ h) 0 z z| := by ring_nf
      _ ≤ ρ ^ (2 + α) / 2 := b.trans hkey

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem reflect_mem_closedBall {ν : E} {ρ : ℝ} {z : E}
    (hz : z ∈ closedBall (0 : E) ρ) : reflect ν z ∈ closedBall (0 : E) ρ := by
  rw [mem_closedBall_zero_iff, (reflect ν).norm_map]; exact mem_closedBall_zero_iff.1 hz

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem abs_le_one_of_sphere {ν : E} {h u : E → ℝ}
    (hR : ∀ z ∈ closedBall (0 : E) 1, h (reflect ν z) = h z ∨ h (reflect ν z) = -h z)
    (hbd : ∀ z ∈ sphere (0 : E) 1, z ∈ halfSpace ν → h z = u z)
    (hu1 : ∀ z ∈ halfBall ν (0 : E) 1, |u z| ≤ 1) (hν : ‖ν‖ = 1) :
    ∀ z ∈ sphere (0 : E) 1, |h z| ≤ 1 := by
  intro z hz
  by_cases hzh : z ∈ halfSpace ν
  · rw [hbd z hz hzh]; exact hu1 z ⟨sphere_subset_closedBall hz, hzh⟩
  · have hRz : reflect ν z ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, (reflect ν).norm_map]; exact mem_sphere_zero_iff_norm.1 hz
    have hRh : reflect ν z ∈ halfSpace ν := by
      rw [mem_halfSpace, inner_reflect hν]
      have : ⟪z, ν⟫ < 0 := not_le.1 hzh
      linarith
    have := hu1 _ ⟨sphere_subset_closedBall hRz, hRh⟩
    rw [← hbd _ hRz hRh] at this
    rcases hR z (sphere_subset_closedBall hz) with h1 | h1 <;> rw [h1] at this
    · exact this
    · rwa [abs_neg] at this

/-- **Improvement of flatness, Neumann case.** There are `ρ ∈ (0, 1/4]` and `C₀ ≥ 0`, depending
only on `E` and `α`, such that: if `u` is continuous on `halfBall ν 0 1`, `C²` in
`ball 0 1 ∩ openHalfSpace ν`, `|u| ≤ 1`, `|Δu| ≤ ρ^{2+α}/4` in the open half ball and the inward
normal derivative of `u` at each flat point of `ball 0 1` is at most `ρ^{2+α}/4` in absolute
value, then there is an even (`IsEvenPoly ν`) traceless quadratic `Q` with `sumNorm Q ≤ C₀` and
`|u − Q| ≤ ρ^{2+α}` on `halfBall ν 0 ρ`. -/
theorem improvement_of_flatness_neumann {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ ρ C₀ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ 0 ≤ C₀ ∧ ∀ {ν : E}, ‖ν‖ = 1 → ∀ {u : E → ℝ},
      ContinuousOn u (halfBall ν 0 1) → ContDiffOn ℝ 2 u (ball 0 1 ∩ openHalfSpace ν) →
      (∀ z ∈ halfBall ν (0 : E) 1, |u z| ≤ 1) →
      (∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ u z| ≤ ρ ^ (2 + α) / 4) →
      (∀ z ∈ ball (0 : E) 1, z ∈ flatPart ν → ∃ d : ℝ,
        HasDerivWithinAt (fun t : ℝ ↦ u (z + t • ν)) d (Ici 0) 0 ∧ |d| ≤ ρ ^ (2 + α) / 4) →
      ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧ IsEvenPoly ν Q ∧
        ∀ z ∈ halfBall ν (0 : E) ρ, |u z - Q.eval z| ≤ ρ ^ (2 + α) := by
  obtain ⟨ρ, C₀, hρ0, hρq, hC₀, hstep⟩ := exists_harmonic_taylor_step (E := E) hα
  refine ⟨ρ, C₀, hρ0, hρq, hC₀, fun {ν} hν {u} hu hu2 hu1 hΔ hN ↦ ?_⟩
  have hδ : 0 ≤ ρ ^ (2 + α) / 4 := by positivity
  obtain ⟨h, hhc, hharm, hR, hbd⟩ := exists_harmonic_even_halfBall hν hu
  have hh1 : ∀ z ∈ closedBall (0 : E) 1, |h z| ≤ 1 :=
    abs_le_of_harmonic_ball one_pos hharm hhc
      (abs_le_one_of_sphere (fun z hz ↦ Or.inl (hR z hz)) hbd hu1 hν)
  obtain ⟨T, hTtr, hTc, hTap⟩ := hstep hhc hharm hh1
  have hU : IsOpen (ball (0 : E) 1 ∩ openHalfSpace ν) :=
    isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hh2 : ContDiffOn ℝ 2 h (ball 0 1) := hharm.contDiffOn
  -- the error `v = u − h`
  have hv := abs_le_of_halfBall_neumann hν hδ hδ (v := u - h)
    (hu.sub (hhc.mono (halfBall_subset_closedBall ν 0 1)))
    (hu2.sub (hh2.mono inter_subset_left))
    (fun z hz ↦ by
      have h1 := hu2.contDiffAt (hU.mem_nhds hz)
      have h2 := hh2.contDiffAt (isOpen_ball.mem_nhds hz.1)
      rw [h1.laplacian_sub h2, (hharm z hz.1).2.eq_of_nhds, Pi.zero_apply, sub_zero]
      exact hΔ z hz)
    (fun z hz hzh ↦ by simp [hbd z hz hzh])
    (fun z hz hzf ↦ by
      obtain ⟨d, hd, hdδ⟩ := hN z hz hzf
      have hR' : ∀ᶠ y in 𝓝 z, h (reflect ν y) = h y := by
        filter_upwards [isOpen_ball.mem_nhds hz] with y hy using hR y (ball_subset_closedBall hy)
      have h0 := hasDerivAt_line_eq_zero_of_reflect hν hzf
        ((hh2.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num)) hR'
      exact ⟨d - 0, hd.sub h0.hasDerivWithinAt, by rwa [sub_zero]⟩)
  set Q := T.evenPart ν
  have hQap := QuadPoly.abs_sub_evenPart_le (ν := ν) (S := closedBall (0 : E) ρ)
    (fun z hz ↦ reflect_mem_closedBall hz)
    (fun z hz ↦ hR z (closedBall_subset_closedBall (by linarith) hz)) hTap
  refine ⟨Q, by rw [QuadPoly.trace_evenPart, hTtr], (QuadPoly.sumNorm_evenPart_le _ _).trans hTc,
    QuadPoly.isEvenPoly_evenPart _, fun z hz ↦ ?_⟩
  have hz1 : z ∈ halfBall ν (0 : E) 1 := halfBall_mono ν 0 (by linarith) hz
  have a := hv z hz1
  have b := hQap z hz.1
  simp only [Pi.sub_apply] at a
  calc |u z - Q.eval z| = |(u z - h z) + (h z - Q.eval z)| := by ring_nf
    _ ≤ |u z - h z| + |h z - Q.eval z| := abs_add_le _ _
    _ ≤ ρ ^ (2 + α) := by linarith

/-- **Improvement of flatness, Dirichlet case.** There are `ρ ∈ (0, 1/4]` and `C₀ ≥ 0`, depending
only on `E` and `α`, such that: if `u` is continuous on `halfBall ν 0 1`, `C²` in
`ball 0 1 ∩ openHalfSpace ν`, `|u| ≤ 1`, `|Δu| ≤ ρ^{2+α}/4` in the open half ball and `u = 0` on
the flat part, then there is a traceless quadratic `Q` vanishing on `flatPart ν` with
`sumNorm Q ≤ C₀` and `|u − Q| ≤ ρ^{2+α}` on `halfBall ν 0 ρ`. -/
theorem improvement_of_flatness_dirichlet {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ ρ C₀ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ 0 ≤ C₀ ∧ ∀ {ν : E}, ‖ν‖ = 1 → ∀ {u : E → ℝ},
      ContinuousOn u (halfBall ν 0 1) → ContDiffOn ℝ 2 u (ball 0 1 ∩ openHalfSpace ν) →
      (∀ z ∈ halfBall ν (0 : E) 1, |u z| ≤ 1) →
      (∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ u z| ≤ ρ ^ (2 + α) / 4) →
      (∀ z ∈ halfBall ν (0 : E) 1, z ∈ flatPart ν → u z = 0) →
      ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧ VanishesOnFlat ν Q ∧
        ∀ z ∈ halfBall ν (0 : E) ρ, |u z - Q.eval z| ≤ ρ ^ (2 + α) := by
  obtain ⟨ρ, C₀, hρ0, hρq, hC₀, hstep⟩ := exists_harmonic_taylor_step (E := E) hα
  refine ⟨ρ, C₀, hρ0, hρq, hC₀, fun {ν} hν {u} hu hu2 hu1 hΔ hD ↦ ?_⟩
  have hδ : 0 ≤ ρ ^ (2 + α) / 4 := by positivity
  obtain ⟨h, hhc, hharm, hR, hbd⟩ := exists_harmonic_odd_halfBall hν hu hD
  have hh1 : ∀ z ∈ closedBall (0 : E) 1, |h z| ≤ 1 :=
    abs_le_of_harmonic_ball one_pos hharm hhc
      (abs_le_one_of_sphere (fun z hz ↦ Or.inr (hR z hz)) hbd hu1 hν)
  obtain ⟨T, hTtr, hTc, hTap⟩ := hstep hhc hharm hh1
  have hU : IsOpen (ball (0 : E) 1 ∩ openHalfSpace ν) :=
    isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hh2 : ContDiffOn ℝ 2 h (ball 0 1) := hharm.contDiffOn
  have hh0 : ∀ z ∈ closedBall (0 : E) 1, z ∈ flatPart ν → h z = 0 := fun z hz hzf ↦ by
    have := hR z hz
    rw [reflect_eq_self_of_mem_flatPart hν hzf] at this
    linarith
  have hv := abs_le_of_halfBall_dirichlet hν hδ (v := u - h)
    (hu.sub (hhc.mono (halfBall_subset_closedBall ν 0 1)))
    (hu2.sub (hh2.mono inter_subset_left))
    (fun z hz ↦ by
      have h1 := hu2.contDiffAt (hU.mem_nhds hz)
      have h2 := hh2.contDiffAt (isOpen_ball.mem_nhds hz.1)
      rw [h1.laplacian_sub h2, (hharm z hz.1).2.eq_of_nhds, Pi.zero_apply, sub_zero]
      exact hΔ z hz)
    (fun z hz hzh ↦ by simp [hbd z hz hzh])
    (fun z hz hzf ↦ by
      have hz' : z ∈ halfBall ν (0 : E) 1 :=
        ⟨ball_subset_closedBall hz, flatPart_subset_halfSpace ν hzf⟩
      simp [hD z hz' hzf, hh0 z (ball_subset_closedBall hz) hzf])
  set Q := T.oddPart ν
  have hQap := QuadPoly.abs_sub_oddPart_le (ν := ν) (S := closedBall (0 : E) ρ)
    (fun z hz ↦ reflect_mem_closedBall hz)
    (fun z hz ↦ hR z (closedBall_subset_closedBall (by linarith) hz)) hTap
  refine ⟨Q, QuadPoly.trace_oddPart _ _, (QuadPoly.sumNorm_oddPart_le _ _).trans hTc,
    QuadPoly.vanishesOnFlat_oddPart hν _, fun z hz ↦ ?_⟩
  have hz1 : z ∈ halfBall ν (0 : E) 1 := halfBall_mono ν 0 (by linarith) hz
  have a := hv z hz1
  have b := hQap z hz.1
  simp only [Pi.sub_apply] at a
  calc |u z - Q.eval z| = |(u z - h z) + (h z - Q.eval z)| := by ring_nf
    _ ≤ |u z - h z| + |h z - Q.eval z| := abs_add_le _ _
    _ ≤ ρ ^ (2 + α) := by linarith

end Nondiv

end BasicElliptic
