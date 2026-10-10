/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Div
import BasicElliptic.Div.Higher.SecondOrder
import BasicElliptic.Div.Boundary.Main
import BasicElliptic.Holder.Closure
import BasicElliptic.Holder.Algebra
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Linear conormal `C^{2,α}` regularity

`Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff` proves `Div.C2HolderHalfBallStatement`: with
`a` symmetric, uniformly elliptic and `C^{1,α}`, `G ∈ C^{1,α}` and `f ∈ C^α` on the closed half
ball `B = halfBall ν x r`, a conormal weak solution `w ∈ C¹(B)` is `C^{2,α}` on
`halfBall ν x (r/2)`.

## Proof

* Replace `f` by a continuous extension `f̂` of `f|_B` (Tietze); the problem only sees `f` on `B`.
* Near every point `y₀` of `T = halfBall ν x (r/2)` (indeed of `ball x r ∩ halfSpace ν`),
  `Div.exists_hessian_halfBall_of_linear` gives a within-derivative of `D_B w` on a small half
  ball with an `α`-Hölder bound: tangential difference quotients and the uniform conormal
  boundary estimate (`Div/Higher/Directional.lean`), and the normal–normal derivative from the
  equation (`Div/Higher/SecondOrder.lean`).
* These local derivatives agree on overlaps (uniqueness of within-derivatives on the convex `T`),
  so they define one field `H₂` on `T`, the within-derivative of `D_B w` on `T`; `H₂` is Hölder
  near every point, hence on the compact `T` (`Div.exists_holderOnWith_of_locally`, Lebesgue
  number lemma).
* `ContDiffOn ℝ 2 w T` follows (`Div.contDiffOn_two_of_hasFDerivWithinAt`), and the second
  iterated within-derivative of `w` on `T` is `H₂` (as a bilinear map), hence Hölder.

If `⟪x, ν⟫ ≤ -r/2`, `T` has at most one point and the statement is trivial.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped NNReal Topology Gradient

namespace BasicElliptic

namespace Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Hölder continuity of the within-derivative from `C^{1,α}`. -/
private theorem holderOnWith_fderivWithin_of_contDiffHolderOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {α : ℝ≥0} {g : E → F} {s : Set E} (hs : UniqueDiffOn ℝ s)
    (hg : ContDiffHolderOn 1 α g s) : ∃ C : ℝ≥0, HolderOnWith C α (fderivWithin ℝ g s) s := by
  obtain ⟨-, C, hC⟩ := hg
  refine ⟨C, holderOnWith_iff_dist_le.2 fun p hp q hq ↦ ?_⟩
  rw [← dist_iteratedFDerivWithin_one g g (hs p hp) (hs q hq)]
  exact hC.dist_le hp hq

variable [MeasurableSpace E] [BorelSpace E]

/-- The main case `-r/2 < ⟪x, ν⟫` of the linear `C^{2,α}` theorem, with `f` continuous on `E`. -/
private theorem contDiffHolderOn_two_main {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν x : E}
    {r : ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hx2 : -(r / 2) < ⟪x, ν⟫)
    {lam Λ : ℝ} (hlam : 0 < lam) {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r)) (hsym : IsSymmetricOn a (halfBall ν x r))
    (ha : ContDiffOn ℝ 1 a (halfBall ν x r)) {Kda : ℝ≥0}
    (hDa : HolderOnWith Kda α (fderivWithin ℝ a (halfBall ν x r)) (halfBall ν x r))
    (hG : ContDiffOn ℝ 1 G (halfBall ν x r)) {Kdg : ℝ≥0}
    (hDG : HolderOnWith Kdg α (fderivWithin ℝ G (halfBall ν x r)) (halfBall ν x r))
    (hf : Continuous f) {Kf : ℝ≥0} (hfH : HolderOnWith Kf α f (halfBall ν x r))
    (h : IsConormalSolOn ν a G f x r w) : ContDiffHolderOn 2 α w (halfBall ν x (r / 2)) := by
  set B := halfBall ν x r with hB
  set T := halfBall ν x (r / 2) with hT
  have hTB : T ⊆ B := halfBall_mono ν x (by linarith)
  have huT : UniqueDiffOn ℝ T := uniqueDiffOn_halfBall hν (by positivity) hx2
  have hTc : IsCompact T := isCompact_halfBall ν x (r / 2)
  have hTin : ∀ y ∈ T, y ∈ ball x r ∩ halfSpace ν := fun y hy ↦
    ⟨mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (by linarith)), hy.2⟩
  set D := fderivWithin ℝ w B with hD
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  -- local second derivatives
  have hloc := fun y (hy : y ∈ T) ↦ exists_hessian_halfBall_of_linear hα hα1 hν hr hx hlam hell
    hsym ha hDa hG hDG hf hfH h (hTin y hy)
  choose! ρ hρ Hs hHs C hC using hloc
  -- transfer of a local derivative to `T`
  have htrans : ∀ y₀ ∈ T, ∀ y ∈ T ∩ ball y₀ (ρ y₀), HasFDerivWithinAt D (Hs y₀ y) T y := by
    intro y₀ hy₀ y hy
    have hyS : y ∈ halfBall ν y₀ (ρ y₀) := ⟨ball_subset_closedBall hy.2, hy.1.2⟩
    have h1 := (hHs y₀ hy₀ y hyS).mono (s := T ∩ ball y₀ (ρ y₀))
      fun z (hz : z ∈ T ∩ ball y₀ (ρ y₀)) ↦ ⟨ball_subset_closedBall hz.2, hz.1.2⟩
    exact (hasFDerivWithinAt_inter' (mem_nhdsWithin_of_mem_nhds
      (isOpen_ball.mem_nhds hy.2))).1 h1
  set H₂ : E → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦ Hs y y with hH₂
  have hH₂d : ∀ y ∈ T, HasFDerivWithinAt D (H₂ y) T y := fun y hy ↦
    htrans y hy y ⟨hy, mem_ball_self (hρ y hy)⟩
  have hagree : ∀ y₀ ∈ T, ∀ y ∈ T ∩ ball y₀ (ρ y₀), H₂ y = Hs y₀ y := fun y₀ hy₀ y hy ↦
    (huT y hy.1).eq (hH₂d y hy.1) (htrans y₀ hy₀ y hy)
  have hH₂loc : ∀ y₀ ∈ T, ∃ ε > 0, ∃ C : ℝ≥0, HolderOnWith C α H₂ (T ∩ ball y₀ ε) :=
    fun y₀ hy₀ ↦ ⟨ρ y₀, hρ y₀ hy₀, C y₀, holderOnWith_iff_dist_le.2 fun p hp q hq ↦ by
      rw [hagree y₀ hy₀ p hp, hagree y₀ hy₀ q hq]
      exact (hC y₀ hy₀).dist_le ⟨ball_subset_closedBall hp.2, hp.1.2⟩
        ⟨ball_subset_closedBall hq.2, hq.1.2⟩⟩
  obtain ⟨CH, hCH⟩ := exists_holderOnWith_of_locally hTc hα hH₂loc
  have hH₂c : ContinuousOn H₂ T := hCH.continuousOn hα
  have hwd : ∀ y ∈ T, HasFDerivWithinAt w (D y) T y := fun y hy ↦
    ((hwB y (hTB hy)).hasFDerivWithinAt).mono hTB
  have hC2 : ContDiffOn ℝ 2 w T := contDiffOn_two_of_hasFDerivWithinAt huT hwd hH₂d hH₂c
  refine ⟨by exact_mod_cast hC2, CH, holderOnWith_iff_dist_le.2 fun p hp q hq ↦ ?_⟩
  have hfdT : ∀ y ∈ T, fderivWithin ℝ w T y = D y := fun y hy ↦
    (hwd y hy).fderivWithin (huT y hy)
  have hfd2 : ∀ y ∈ T, fderivWithin ℝ (fderivWithin ℝ w T) T y = H₂ y := fun y hy ↦ by
    rw [fderivWithin_congr (fun z hz ↦ hfdT z hz) (hfdT y hy)]
    exact (hH₂d y hy).fderivWithin (huT y hy)
  calc dist (iteratedFDerivWithin ℝ 2 w T p) (iteratedFDerivWithin ℝ 2 w T q)
      ≤ dist (H₂ p) (H₂ q) := by
        rw [dist_eq_norm, dist_eq_norm]
        refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m ↦ ?_
        rw [sub_apply, iteratedFDerivWithin_two_apply w huT hp,
          iteratedFDerivWithin_two_apply w huT hq, hfd2 p hp, hfd2 q hq, Fin.prod_univ_two,
          ← sub_apply, ← sub_apply, ← mul_assoc]
        exact ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ CH * dist p q ^ (α : ℝ) := hCH.dist_le hp hq

end Div

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Linear conormal `C^{2,α}`** (see the module docstring). -/
theorem Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff : Div.C2HolderHalfBallStatement E := by
  intro α hα hα1 ν x r lam Λ Kf a G f w hν hr hx hlam hell hsym hA hGc hfH h
  set B := halfBall ν x r with hB
  set T := halfBall ν x (r / 2) with hT
  rcases le_or_gt ⟪x, ν⟫ (-(r / 2)) with hxs | hxs
  · have hsub := Div.halfBall_subsingleton hν (by linarith) hxs
    refine ⟨fun p hp ↦ ?_, 0, holderOnWith_iff_dist_le.2 fun p hp q hq ↦ ?_⟩
    · exact contDiffWithinAt_singleton.mono fun q hq ↦ hsub hq hp
    · rw [hsub hp hq, dist_self]; positivity
  have hBu := uniqueDiffOn_halfBall hν hr hx
  have ha : ContDiffOn ℝ 1 a B := by exact_mod_cast hA.1
  have hG : ContDiffOn ℝ 1 G B := by exact_mod_cast hGc.1
  obtain ⟨Kda, hDa⟩ := Div.holderOnWith_fderivWithin_of_contDiffHolderOn hBu hA
  obtain ⟨Kdg, hDG⟩ := Div.holderOnWith_fderivWithin_of_contDiffHolderOn hBu hGc
  -- a continuous extension of `f|_B` (Tietze)
  have hfc : ContinuousOn f B := hfH.continuousOn hα
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (isClosed_halfBall ν x r)
    ⟨B.domRestrict f, hfc.domRestrict⟩
  have hff : EqOn f g B := fun y hy ↦ (congrArg (fun F : C(B, ℝ) ↦ F ⟨y, hy⟩) hg).symm
  have hgH : HolderOnWith Kf α g B := holderOnWith_iff_dist_le.2 fun p hp q hq ↦ by
    rw [← hff hp, ← hff hq]; exact hfH.dist_le hp hq
  have h' := h.congr_data (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hff
  exact Div.contDiffHolderOn_two_main hα hα1 hν hr hx hxs hlam hell hsym ha hDa hG hDG
    g.continuous hgH h'

end BasicElliptic
