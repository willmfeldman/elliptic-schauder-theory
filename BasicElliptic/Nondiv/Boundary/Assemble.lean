/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Boundary.Data
public import BasicElliptic.Statements.Nondiv

/-!
# The frozen right-hand side on the closed half ball

Let `s = halfBall ν x r`, `U = ball x r ∩ openHalfSpace ν`, and let `w ∈ C²(s)` solve `tr (a D²w) +
⟪b, ∇w⟫ = f` on `s` (derivatives within `s`). For `g ∈ C^{2,α}(s)` put
```
F = f − ⟪b, ∇w⟫ − tr (a D²g)        (within derivatives on s).
```
* `Nondiv.fderiv_equation_sub`: `u = w − g` solves `tr (a D²u) = F` in `U` (classical
  derivatives).
* `Nondiv.exists_holder_frozenRHS`: `F` is `α`-Hölder on `s`; the constant is finite by
  compactness (it involves `sup ‖Dw‖`, `sup ‖D²w‖`, `sup ‖D²g‖`, `[a]_α`, `[b]_α`, `[f]_α`).
* `Nondiv.contDiffHolderOn_add_restrict`: `C^{2,α}(S)` plus the restriction of `C^{2,α}(s)`.
-/

public section

open Metric Set Filter Topology Module InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem inner_gradientWithin_eq (w : E → ℝ) (s : Set E) (y v : E) :
    ⟪v, gradientWithin w s y⟫ = fderivWithin ℝ w s y v := by
  rw [gradientWithin, real_inner_comm, toDual_symm_apply]

omit [FiniteDimensional ℝ E] in
theorem iteratedFDerivWithin_eq_of_isOpen_subset {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {s U : Set E} (hU : IsOpen U) (hUs : U ⊆ s) {y : E}
    (hy : y ∈ U) (n : ℕ) : iteratedFDerivWithin ℝ n f s y = iteratedFDeriv ℝ n f y := by
  rw [← iteratedFDerivWithin_inter_open hU hy, inter_eq_right.2 hUs,
    iteratedFDerivWithin_of_isOpen n hU hy]

theorem halfBall_facts {ν x : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) {r : ℝ} (hr : 0 < r) :
    Convex ℝ (halfBall ν x r) ∧ IsCompact (halfBall ν x r) ∧ UniqueDiffOn ℝ (halfBall ν x r) ∧
      (∀ y ∈ halfBall ν x r, ∀ y' ∈ halfBall ν x r, dist y y' ≤ 2 * r) ∧
      ball x r ∩ openHalfSpace ν ⊆ halfBall ν x r := by
  refine ⟨convex_halfBall ν x r, (isCompact_closedBall x r).inter_right (isClosed_halfSpace ν),
    uniqueDiffOn_halfBall hν hr (by rw [hx]; linarith), fun y hy y' hy' ↦ ?_,
    inter_subset_inter ball_subset_closedBall (openHalfSpace_subset_halfSpace ν)⟩
  have h1 : dist y x ≤ r := hy.1
  have h2 : dist y' x ≤ r := hy'.1
  calc dist y y' ≤ dist y x + dist y' x := dist_triangle_right _ _ _
    _ ≤ 2 * r := by linarith

/-- The frozen right-hand side `F = f − ⟪b, ∇w⟫ − tr (a D²g)` (within derivatives on `s`). -/
noncomputable def frozenRHS (a : E → E →L[ℝ] E) (b : E → E) (f w g : E → ℝ) (s : Set E)
    (y : E) : ℝ :=
  f y - ⟪b y, gradientWithin w s y⟫ -
    ∑ i, iteratedFDerivWithin ℝ 2 g s y
      ![a y (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i]

/-- In the interior, `u = w − g` solves `tr (a D²u) = F` with the frozen right-hand side. -/
theorem fderiv_equation_sub {s U : Set E} (hs : UniqueDiffOn ℝ s) (hU : IsOpen U) (hUs : U ⊆ s)
    {a : E → E →L[ℝ] E} {b : E → E} {f w g : E → ℝ} (hsol : IsSolOn a b f s w)
    (hg : ContDiffOn ℝ 2 g s) {y : E} (hy : y ∈ U) :
    ∑ i, fderiv ℝ (fderiv ℝ (fun z ↦ w z - g z)) y (a y (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i) = frozenRHS a b f w g s y := by
  set e := stdOrthonormalBasis ℝ E
  have hys : y ∈ s := hUs hy
  have hop := hsol.2 y hys
  simp only [op] at hop
  have hsub : iteratedFDerivWithin ℝ 2 (fun z ↦ w z - g z) s y =
      iteratedFDerivWithin ℝ 2 w s y - iteratedFDerivWithin ℝ 2 g s y :=
    iteratedFDerivWithin_sub_apply (hsol.1 y hys) (hg y hys) hs hys
  have hterm : ∀ i, fderiv ℝ (fderiv ℝ (fun z ↦ w z - g z)) y (a y (e i)) (e i) =
      iteratedFDerivWithin ℝ 2 w s y ![a y (e i), e i] -
        iteratedFDerivWithin ℝ 2 g s y ![a y (e i), e i] := fun i ↦ by
    rw [← sub_apply, ← hsub,
      iteratedFDerivWithin_eq_of_isOpen_subset hU hUs hy, iteratedFDeriv_two_apply]
    simp
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_sub_distrib, frozenRHS]
  linarith

/-- **The frozen right-hand side is Hölder** on `halfBall ν x r`, with a finite constant
(compactness). -/
theorem exists_holder_frozenRHS {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) {ν x : E} (hν : ‖ν‖ = 1)
    (hx : ⟪x, ν⟫ = 0) {r lam Λ : ℝ} (hr : 0 < r) {Ka Kb Kf : ℝ≥0} {a : E → E →L[ℝ] E}
    {b : E → E} {f w g : E → ℝ}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r))
    (haH : HolderOnWith Ka α a (halfBall ν x r)) (hbH : HolderOnWith Kb α b (halfBall ν x r))
    (hfH : HolderOnWith Kf α f (halfBall ν x r)) (hg : ContDiffHolderOn 2 α g (halfBall ν x r))
    (hw : ContDiffOn ℝ 2 w (halfBall ν x r)) :
    ∃ KF : ℝ, 0 ≤ KF ∧ ∀ y ∈ halfBall ν x r, ∀ y' ∈ halfBall ν x r,
      |frozenRHS a b f w g (halfBall ν x r) y - frozenRHS a b f w g (halfBall ν x r) y'| ≤
        KF * dist y y' ^ (α : ℝ) := by
  set s := halfBall ν x r
  obtain ⟨hcv, hcp, hU, hdiam, -⟩ := halfBall_facts hν hx hr
  have hxs : x ∈ s := ⟨mem_closedBall_self hr.le, hx.ge⟩
  have hαr : 0 < (α : ℝ) ∧ (α : ℝ) < 1 := ⟨hα0, hα1⟩
  -- bounds
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound_of_continuousOn_compact hcp
    (hw.continuousOn_fderivWithin hU (by norm_num))
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_of_continuousOn_compact hcp
    (continuousOn_fderivWithin_fderivWithin hU hw)
  have hg2 : ContDiffOn ℝ 2 g s := by exact_mod_cast hg.1
  obtain ⟨MT, hMT0, hMT⟩ := exists_bound_of_continuousOn_compact hcp
    (hg2.continuousOn_iteratedFDerivWithin le_rfl hU)
  obtain ⟨Cg, hCg⟩ := hg.2
  set Mb := ‖b x‖ + Kb * (2 * r) ^ (α : ℝ) with hMb
  have hbb : ∀ y ∈ s, ‖b y‖ ≤ Mb := fun y hy ↦ by
    have h1 := hbH.dist_le hy hxs
    rw [dist_eq_norm] at h1
    have h2 : dist y x ^ (α : ℝ) ≤ (2 * r) ^ (α : ℝ) :=
      Real.rpow_le_rpow dist_nonneg (hdiam y hy x hxs) hα0.le
    calc ‖b y‖ ≤ ‖b x‖ + ‖b y - b x‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖b x‖ + Kb * (2 * r) ^ (α : ℝ) := by
          gcongr; exact h1.trans (by gcongr)
  have hΛ : ∀ y ∈ s, ‖a y‖ ≤ Λ := fun y hy ↦ (hell y hy).2
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ x hxs)
  refine ⟨Kf + (M₂ * (2 * r) ^ (1 - (α : ℝ)) * Mb + M₁ * Kb) +
      finrank ℝ E * (Cg * Λ + MT * Ka), by positivity, fun y hy y' hy' ↦ ?_⟩
  have hdα : 0 ≤ dist y y' ^ (α : ℝ) := Real.rpow_nonneg dist_nonneg _
  -- the three pieces
  have t1 : |f y - f y'| ≤ Kf * dist y y' ^ (α : ℝ) := by
    rw [← Real.dist_eq]; exact hfH.dist_le hy hy'
  have t2 : |⟪b y, gradientWithin w s y⟫ - ⟪b y', gradientWithin w s y'⟫| ≤
      (M₂ * (2 * r) ^ (1 - (α : ℝ)) * Mb + M₁ * Kb) * dist y y' ^ (α : ℝ) := by
    rw [inner_gradientWithin_eq, inner_gradientWithin_eq]
    refine (abs_apply_sub_apply_le _ _ _ _).trans ?_
    have hL := dist_le_rpow_of_lipschitz hM₂0 hαr (hdiam y hy y' hy')
      (norm_fderivWithin_sub_le hcv hU hw hM₂ hy hy')
    have hbd := hbH.dist_le hy hy'
    rw [dist_eq_norm] at hbd
    calc ‖fderivWithin ℝ w s y - fderivWithin ℝ w s y'‖ * ‖b y‖ +
          ‖fderivWithin ℝ w s y'‖ * ‖b y - b y'‖ ≤
        M₂ * (2 * r) ^ (1 - (α : ℝ)) * dist y y' ^ (α : ℝ) * Mb +
          M₁ * (Kb * dist y y' ^ (α : ℝ)) := by
          gcongr
          · exact hbb y hy
          · exact hM₁ y' hy'
      _ = _ := by ring
  have t3 : |∑ i, iteratedFDerivWithin ℝ 2 g s y
        ![a y (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i] -
      ∑ i, iteratedFDerivWithin ℝ 2 g s y'
        ![a y' (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i]| ≤
      finrank ℝ E * (Cg * Λ + MT * Ka) * dist y y' ^ (α : ℝ) := by
    refine (abs_trace_sub_le _ _ _ _).trans ?_
    have h1 := hCg.dist_le hy hy'
    have h2 := haH.dist_le hy hy'
    rw [dist_eq_norm] at h1 h2
    have hdim : (0 : ℝ) ≤ finrank ℝ E := by positivity
    calc (finrank ℝ E : ℝ) * (‖iteratedFDerivWithin ℝ 2 g s y - iteratedFDerivWithin ℝ 2 g s y'‖ *
          ‖a y‖ + ‖iteratedFDerivWithin ℝ 2 g s y'‖ * ‖a y - a y'‖) ≤
        finrank ℝ E * (Cg * dist y y' ^ (α : ℝ) * Λ + MT * (Ka * dist y y' ^ (α : ℝ))) := by
          gcongr
          · exact hΛ y hy
          · exact hMT y' hy'
      _ = _ := by ring
  simp only [frozenRHS]
  have e : f y - ⟪b y, gradientWithin w s y⟫ -
        ∑ i, iteratedFDerivWithin ℝ 2 g s y
          ![a y (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i] -
      (f y' - ⟪b y', gradientWithin w s y'⟫ -
        ∑ i, iteratedFDerivWithin ℝ 2 g s y'
          ![a y' (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i]) =
      (f y - f y') - (⟪b y, gradientWithin w s y⟫ - ⟪b y', gradientWithin w s y'⟫) -
      (∑ i, iteratedFDerivWithin ℝ 2 g s y
          ![a y (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i] -
        ∑ i, iteratedFDerivWithin ℝ 2 g s y'
          ![a y' (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i]) := by ring
  rw [e]
  calc _ ≤ |(f y - f y') - (⟪b y, gradientWithin w s y⟫ - ⟪b y', gradientWithin w s y'⟫)| +
        |∑ i, iteratedFDerivWithin ℝ 2 g s y
            ![a y (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i] -
          ∑ i, iteratedFDerivWithin ℝ 2 g s y'
            ![a y' (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i]| := abs_sub _ _
    _ ≤ |f y - f y'| + |⟪b y, gradientWithin w s y⟫ - ⟪b y', gradientWithin w s y'⟫| +
        |∑ i, iteratedFDerivWithin ℝ 2 g s y
            ![a y (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i] -
          ∑ i, iteratedFDerivWithin ℝ 2 g s y'
            ![a y' (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i]| := by
        gcongr; exact abs_sub _ _
    _ ≤ _ := by
        have := add_le_add (add_le_add t1 t2) t3
        linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `C^{2,α}(S)` plus the restriction of `C^{2,α}(s)` to `S ⊆ s` (both sets with unique
differentiability). -/
theorem contDiffHolderOn_add_restrict [NormedSpace ℝ E] {α : ℝ≥0} {S s : Set E} (hSs : S ⊆ s)
    (hS : UniqueDiffOn ℝ S) (hs : UniqueDiffOn ℝ s) {u g : E → ℝ}
    (hu : ContDiffHolderOn 2 α u S) (hg : ContDiffHolderOn 2 α g s) :
    ContDiffHolderOn 2 α (fun y ↦ u y + g y) S := by
  have hu2 : ContDiffOn ℝ 2 u S := by exact_mod_cast hu.1
  have hg2 : ContDiffOn ℝ 2 g s := by exact_mod_cast hg.1
  refine ⟨by exact_mod_cast hu2.add (hg2.mono hSs), ?_⟩
  obtain ⟨Cu, hCu⟩ := hu.2
  obtain ⟨Cg, hCg⟩ := hg.2
  refine ⟨Cu + Cg, holderOnWith_iff_dist_le.2 fun y hy y' hy' ↦ ?_⟩
  have hsplit : ∀ z ∈ S, iteratedFDerivWithin ℝ 2 (fun y ↦ u y + g y) S z =
      iteratedFDerivWithin ℝ 2 u S z + iteratedFDerivWithin ℝ 2 g s z := fun z hz ↦ by
    change iteratedFDerivWithin ℝ 2 (u + g) S z = _
    rw [iteratedFDerivWithin_add_apply (hu2 z hz) ((hg2.mono hSs) z hz) hS hz,
      iteratedFDerivWithin_subset hSs hS hs hg2 hz]
  rw [hsplit y hy, hsplit y' hy', dist_eq_norm]
  have h1 := hCu.dist_le hy hy'
  have h2 := hCg.dist_le (hSs hy) (hSs hy')
  rw [dist_eq_norm] at h1 h2
  calc ‖iteratedFDerivWithin ℝ 2 u S y + iteratedFDerivWithin ℝ 2 g s y -
        (iteratedFDerivWithin ℝ 2 u S y' + iteratedFDerivWithin ℝ 2 g s y')‖ =
      ‖(iteratedFDerivWithin ℝ 2 u S y - iteratedFDerivWithin ℝ 2 u S y') +
        (iteratedFDerivWithin ℝ 2 g s y - iteratedFDerivWithin ℝ 2 g s y')‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ Cu * dist y y' ^ (α : ℝ) + Cg * dist y y' ^ (α : ℝ) := add_le_add h1 h2
    _ = _ := by push_cast; ring

end Nondiv

end BasicElliptic
