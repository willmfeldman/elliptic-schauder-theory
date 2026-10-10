/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Nondiv
import BasicElliptic.Nondiv.Boundary.Conormal

/-!
# Tier-1 flat-boundary Schauder theory in nondivergence form

`Nondiv.schauder_halfBall_conormal` and `Nondiv.schauder_halfBall_dirichlet` prove
`Nondiv.SchauderHalfBallConormalStatement` and `Nondiv.SchauderHalfBallDirichletStatement`.

## The Dirichlet theorem

Let `s = halfBall ν x r`, `U = ball x r ∩ openHalfSpace ν` and `u = w − g`. Then `u ∈ C²(s)`,
`u = 0` on the flat part, and `u` solves `tr (a D²u) = F` in `U` with the frozen right-hand side
`F = f − ⟪b, ∇w⟫ − tr (a D²g)` (`Nondiv.frozenRHS`), which is `α`-Hölder on `s`
(`Nondiv.exists_holder_frozenRHS`). All bounds (`sup |u|`, `sup ‖D²u‖`, `sup |F|`, `[F]_α`) are
finite by compactness of `s`. At every flat point `p` of `halfBall ν x (r/2)` the
boundary iteration (`Nondiv.expansion_at_flat_point_dirichlet`: normalization by a
half-space-preserving `M`, odd reflection model, Dirichlet barrier, sup-norm Campanato iteration)
gives a uniform boundary expansion; the two-regime gluing
(`Nondiv.polyApproxOn_halfBall_of_boundary`) extends it to every point of `halfBall ν x (r/2)`,
and the closed-region bridge (`contDiffOn_two_of_polyApprox`) gives
`u ∈ C^{2,α}(halfBall ν x (r/2))`; finally `w = u + g`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001. (GT)
-/

public section

open Metric Set Module
open scoped NNReal RealInnerProductSpace

namespace BasicElliptic

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Tier-1 boundary Schauder regularity, conormal-compatible condition** (GT). See the module
docstring for the proof. -/
theorem Nondiv.schauder_halfBall_conormal : Nondiv.SchauderHalfBallConormalStatement E := by
  intro α hα0 hα1 ν x r lam Λ Ka Kb Kf a b f β γ w hν hr hx hlam hell hsym haH hbH hfH hβ hβa hγ
    hsol hbc
  have : Nontrivial E := ⟨⟨ν, 0, fun h ↦ by simp [h] at hν⟩⟩
  have hαr : 0 < (α : ℝ) ∧ (α : ℝ) < 1 := ⟨hα0, hα1⟩
  obtain ⟨hcv, hcp, hsU, hdiam, hUs⟩ := Nondiv.halfBall_facts hν hx hr
  set s := halfBall ν x r with hs
  set U := ball x r ∩ openHalfSpace ν with hUdef
  have hU : IsOpen U := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hxs : x ∈ s := ⟨mem_closedBall_self hr.le, hx.ge⟩
  have hlamΛ : lam ≤ Λ := Nondiv.lam_le_of_isUniformlyElliptic hell hxs
  have hw : ContDiffOn ℝ 2 w s := hsol.1
  -- the frozen right-hand side (with `g = 0`)
  have h0 : ContDiffHolderOn 2 α (fun _ : E ↦ (0 : ℝ)) s := by
    refine ⟨contDiffOn_const, 0, fun y _ y' _ ↦ ?_⟩
    rw [iteratedFDerivWithin_const_of_ne (by norm_num)]
    simp
  set F := Nondiv.frozenRHS a b f w (fun _ ↦ 0) s with hF_def
  obtain ⟨KF, hKF, hFH⟩ := Nondiv.exists_holder_frozenRHS hα0 hα1 hν hx hr hell haH hbH hfH h0
    hw
  -- finite bounds (compactness)
  obtain ⟨Mw, hMw0, hMw⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp hw.continuousOn
  obtain ⟨M₂, hM₂0, hM₂⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp
    (hw.continuousOn_iteratedFDerivWithin le_rfl hsU)
  obtain ⟨M₁, hM₁0, hM₁⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp
    (hw.continuousOn_fderivWithin hsU (by norm_num))
  obtain ⟨M₂w, hM₂w0, hM₂w⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp
    (Nondiv.continuousOn_fderivWithin_fderivWithin hsU hw)
  have hβ1 : ContDiffOn ℝ 1 β s := by exact_mod_cast hβ.1
  have hγ1 : ContDiffOn ℝ 1 γ s := by exact_mod_cast hγ.1
  obtain ⟨MDβ, hMDβ0, hMDβ⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp
    (hβ1.continuousOn_fderivWithin hsU le_rfl)
  obtain ⟨MDγ, hMDγ0, hMDγ⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp
    (hγ1.continuousOn_fderivWithin hsU le_rfl)
  obtain ⟨Mγ, hMγ0, hMγ⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp hγ1.continuousOn
  obtain ⟨Cβ, hCβ⟩ := hβ.2
  obtain ⟨Cγ, hCγ⟩ := hγ.2
  have hu0 : ∀ y ∈ s, |w y| ≤ Mw := fun y hy ↦ by
    rw [← Real.norm_eq_abs]; exact hMw y hy
  have hD2 : ∀ y ∈ U, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M₂ := fun y hy ↦ by
    rw [Nondiv.norm_fderiv_fderiv_eq,
      ← Nondiv.iteratedFDerivWithin_eq_of_isOpen_subset hU hUs hy 2]
    exact hM₂ y (hUs hy)
  set MF := |F x| + KF * (2 * r) ^ (α : ℝ) with hMF
  have hFb : ∀ y ∈ s, |F y| ≤ MF := fun y hy ↦ by
    have h1 := hFH y hy x hxs
    have h2 : dist y x ^ (α : ℝ) ≤ (2 * r) ^ (α : ℝ) :=
      Real.rpow_le_rpow dist_nonneg (hdiam y hy x hxs) hα0.le
    have h3 : |F y| ≤ |F x| + |F y - F x| := by
      have := abs_add_le (F x) (F y - F x); rwa [add_sub_cancel] at this
    calc |F y| ≤ |F x| + |F y - F x| := h3
      _ ≤ |F x| + KF * (2 * r) ^ (α : ℝ) := by gcongr; exact h1.trans (by gcongr)
  have heq : ∀ y ∈ U, ∑ i, fderiv ℝ (fderiv ℝ w) y (a y (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i) = F y := fun y hy ↦ by
    have := Nondiv.fderiv_equation_sub hsU hU hUs hsol h0.1 hy
    simpa only [sub_zero] using this
  have ha' : ∀ y ∈ s, ∀ y' ∈ s, ‖a y - a y'‖ ≤ Ka * dist y y' ^ (α : ℝ) := fun y hy y' hy' ↦ by
    rw [← dist_eq_norm]; exact haH.dist_le hy hy'
  have hKa : (0 : ℝ) ≤ Ka := Ka.2
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hell x hxs).2
  have hMF0 : 0 ≤ MF := (abs_nonneg _).trans (hFb x hxs)
  -- boundary expansions at the flat points of `halfBall ν x (r/2)`
  obtain ⟨Cb, κb, hCb, hκb, hexpb⟩ := Nondiv.boundary_expansions_conormal (E := E) hα0 hα1
    hlam hlamΛ
  have hbdry := hexpb (G := (Cγ : ℝ) + Cβ * M₁ + MDβ * M₂w * (2 * r) ^ (1 - (α : ℝ)))
    (Bℓ := MDγ + M₁ * MDβ) (Mγ := Mγ) (Mw := Mw) (MF := MF) hν hx hr hKa hKF hM₂0
    (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hM₁0 hM₂w0 hMDβ0 hMw0 hell hsym ha' hFH hFb hw
    hu0 hD2 hM₁ hM₂w heq (hβ1.differentiableOn one_ne_zero) (hγ1.differentiableOn one_ne_zero)
    (fun y hy y' hy' ↦ Nondiv.norm_fderivWithin_sub_le_of_holder hsU hCγ hy hy')
    (fun y hy y' hy' ↦ Nondiv.norm_fderivWithin_sub_le_of_holder hsU hCβ hy hy')
    hMDβ hMDγ (fun y hy ↦ by rw [← Real.norm_eq_abs]; exact hMγ y hy) hβa hbc rfl rfl rfl
  obtain ⟨A, ρ₀, hρ₀, P, hPA⟩ := Nondiv.polyApproxOn_halfBall_of_boundary hα0 hα1 hlam hν hx hr
    hKa hKF (by positivity) (by positivity) hM₂0 (by positivity) hell ha' hFH hFb (hw.mono hUs)
    hu0 hD2 heq hbdry
  have hrh : 0 < r / 2 := by positivity
  exact (contDiffOn_two_of_polyApprox hα0 hα1.le hρ₀ (convex_halfBall ν x (r / 2))
    (isBounded_halfBall ν x (r / 2))
    (interior_halfBall_nonempty hν hrh (by rw [hx]; linarith)) hPA).1

/-- **Tier-1 boundary Schauder regularity, Dirichlet condition** (GT, in
the flat case). See the module docstring for the proof. -/
theorem Nondiv.schauder_halfBall_dirichlet : Nondiv.SchauderHalfBallDirichletStatement E := by
  intro α hα0 hα1 ν x r lam Λ Ka Kb Kf a b f g w hν hr hx hlam hell haH hbH hfH hg hsol hbc
  have : Nontrivial E := ⟨⟨ν, 0, fun h ↦ by simp [h] at hν⟩⟩
  have hαr : 0 < (α : ℝ) ∧ (α : ℝ) < 1 := ⟨hα0, hα1⟩
  obtain ⟨hcv, hcp, hsU, hdiam, hUs⟩ := Nondiv.halfBall_facts hν hx hr
  set s := halfBall ν x r with hs
  set U := ball x r ∩ openHalfSpace ν with hUdef
  have hU : IsOpen U := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hxs : x ∈ s := ⟨mem_closedBall_self hr.le, hx.ge⟩
  have hlamΛ : lam ≤ Λ := Nondiv.lam_le_of_isUniformlyElliptic hell hxs
  set u : E → ℝ := fun z ↦ w z - g z with hu_def
  have hg2 : ContDiffOn ℝ 2 g s := by exact_mod_cast hg.1
  have hu : ContDiffOn ℝ 2 u s := hsol.1.sub hg2
  set F := Nondiv.frozenRHS a b f w g s with hF_def
  obtain ⟨KF, hKF, hFH⟩ := Nondiv.exists_holder_frozenRHS hα0 hα1 hν hx hr hell haH hbH hfH hg
    hsol.1
  -- finite bounds (compactness)
  obtain ⟨M₀, hM₀0, hM₀⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp hu.continuousOn
  obtain ⟨M₂, hM₂0, hM₂⟩ := Nondiv.exists_bound_of_continuousOn_compact hcp
    (hu.continuousOn_iteratedFDerivWithin le_rfl hsU)
  have hu0 : ∀ y ∈ s, |u y| ≤ M₀ := fun y hy ↦ by
    rw [← Real.norm_eq_abs]; exact hM₀ y hy
  have hD2 : ∀ y ∈ U, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M₂ := fun y hy ↦ by
    rw [Nondiv.norm_fderiv_fderiv_eq,
      ← Nondiv.iteratedFDerivWithin_eq_of_isOpen_subset hU hUs hy 2]
    exact hM₂ y (hUs hy)
  set MF := |F x| + KF * (2 * r) ^ (α : ℝ) with hMF
  have hFb : ∀ y ∈ s, |F y| ≤ MF := fun y hy ↦ by
    have h1 := hFH y hy x hxs
    have h2 : dist y x ^ (α : ℝ) ≤ (2 * r) ^ (α : ℝ) :=
      Real.rpow_le_rpow dist_nonneg (hdiam y hy x hxs) hα0.le
    have h3 : |F y| ≤ |F x| + |F y - F x| := by
      have := abs_add_le (F x) (F y - F x); rwa [add_sub_cancel] at this
    calc |F y| ≤ |F x| + |F y - F x| := h3
      _ ≤ |F x| + KF * (2 * r) ^ (α : ℝ) := by gcongr; exact h1.trans (by gcongr)
  have heq : ∀ y ∈ U, ∑ i, fderiv ℝ (fderiv ℝ u) y (a y (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i) = F y := fun y hy ↦
    Nondiv.fderiv_equation_sub hsU hU hUs hsol hg2 hy
  have ha' : ∀ y ∈ s, ∀ y' ∈ s, ‖a y - a y'‖ ≤ Ka * dist y y' ^ (α : ℝ) := fun y hy y' hy' ↦ by
    rw [← dist_eq_norm]; exact haH.dist_le hy hy'
  have hKa : (0 : ℝ) ≤ Ka := Ka.2
  -- boundary expansions at the flat points of `halfBall ν x (r/2)`
  obtain ⟨Cb, κb, hCb, hκb, hexpb⟩ := Nondiv.expansion_at_flat_point_dirichlet (E := E) hαr hlam
    hlamΛ
  set R := r / 2 with hR_def
  have hR : 0 < R := by positivity
  set Nb := M₀ + R ^ 2 * MF + R ^ (2 + (α : ℝ)) * (KF + finrank ℝ E * Ka * M₂) with hNb
  have hNb0 : 0 ≤ Nb := by
    have : 0 ≤ MF := (abs_nonneg _).trans (hFb x hxs)
    positivity
  have hbdry : ∀ p ∈ halfBall ν x (r / 2), p ∈ flatPart ν → ∃ P : QuadPoly E,
      ∑ i, P.hess (a p (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F p ∧
      ‖P.quad‖ ≤ Cb * Nb / R ^ 2 ∧ ∀ y ∈ s, dist y p < κb * R →
        |u y - P.eval (y - p)| ≤ Cb * Nb / R ^ (2 + (α : ℝ)) * dist y p ^ (2 + (α : ℝ)) := by
    intro p hp hpf
    have hps : p ∈ s := halfBall_mono ν x (by linarith) hp
    have hpR : halfBall ν p R ⊆ s := fun y hy ↦ ⟨by
      have h1 : dist y p ≤ R := hy.1
      have h2 : dist p x ≤ r / 2 := hp.1
      rw [mem_closedBall]
      linarith [dist_triangle y p x], hy.2⟩
    have hpU : ball p R ∩ openHalfSpace ν ⊆ U := fun y hy ↦ ⟨by
      have h1 : dist y p < R := hy.1
      have h2 : dist p x ≤ r / 2 := hp.1
      rw [mem_ball]
      linarith [dist_triangle y p x], hy.2⟩
    obtain ⟨P, hcons, hPc, hPe⟩ := hexpb hν a F u p R M₀ M₂ MF Ka KF hpf hR hKa hKF hM₂0
      (hu.continuousOn.mono hpR) ((hu.mono hUs).mono hpU) (fun y hy ↦ heq y (hpU hy))
      (hell p hps).1 (hell p hps).2 (fun y hy ↦ ha' y (hUs (hpU hy)) p hps)
      (fun y hy ↦ hFH y (hUs (hpU hy)) p hps) (hFb p hps) (fun y hy ↦ hu0 y (hpR hy))
      (fun y hy ↦ hD2 y (hpU hy)) (fun y hy hyf ↦ by
        simp only [hu_def]; rw [hbc y ⟨hpR hy, hyf⟩, sub_self])
    refine ⟨P, hcons, ?_, fun y hy hyd ↦ ?_⟩
    · rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ R * ‖P.lin‖ := by positivity
      have : 0 ≤ |P.const| := abs_nonneg _
      linarith
    · refine (hPe y hy.2 hyd).trans_eq ?_
      rw [Real.div_rpow dist_nonneg hR.le]; ring
  obtain ⟨A, ρ₀, hρ₀, P, hPA⟩ := Nondiv.polyApproxOn_halfBall_of_boundary hα0 hα1 hlam hν hx hr
    hKa hKF (by positivity) (by positivity) hM₂0 (by positivity) hell ha' hFH hFb (hu.mono hUs)
    hu0 hD2 heq hbdry
  have hrh : 0 < r / 2 := by positivity
  have huS := (contDiffOn_two_of_polyApprox hα0 hα1.le hρ₀ (convex_halfBall ν x (r / 2))
    (isBounded_halfBall ν x (r / 2))
    (interior_halfBall_nonempty hν hrh (by rw [hx]; linarith)) hPA).1
  have hw_eq : w = fun y ↦ u y + g y := funext fun y ↦ by simp [hu_def]
  rw [hw_eq]
  exact Nondiv.contDiffHolderOn_add_restrict (halfBall_mono ν x (by linarith))
    (uniqueDiffOn_halfBall hν hrh (by rw [hx]; linarith)) hsU huS hg

end BasicElliptic
