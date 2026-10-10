/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Boundary.Glue
public import BasicElliptic.Holder.Algebra

/-!
# Qualitative bounds for the data on a compact convex region

The tier-1 statements are qualitative: every bound used by the boundary iteration is a finite
constant obtained by compactness of the closed half ball, never assumed. This file collects the
elementary facts.

* `Nondiv.exists_bound_of_continuousOn_compact`: continuous functions are bounded on compact sets.
* `Nondiv.norm_fderivWithin_sub_le`: on a convex set with unique differentiability, a `C²` function
  has Lipschitz within-gradient, with constant `sup ‖D²w‖`.
* `Nondiv.dist_le_rpow_of_lipschitz`: on a set of diameter `≤ D`, a Lipschitz bound gives an
  `α`-Hölder bound with constant `L D^{1−α}`.
* `Nondiv.abs_apply_sub_apply_le`, `Nondiv.abs_trace_sub_le`: Hölder bounds for the pairings
  `⟪b, ∇w⟫` and `tr (a D²g)` of bounded Hölder factors.
-/

public section

open Metric Set Filter Topology Module InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Continuous functions are bounded on compact sets. -/
theorem exists_bound_of_continuousOn_compact {F : Type*} [NormedAddCommGroup F] {s : Set E}
    (hs : IsCompact s) {f : E → F} (hf : ContinuousOn f s) : ∃ C, 0 ≤ C ∧ ∀ y ∈ s, ‖f y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf
  exact ⟨max C 0, le_max_right _ _, fun y hy ↦ (hC y hy).trans (le_max_left _ _)⟩

omit [FiniteDimensional ℝ E] in
/-- On a convex set with unique differentiability, the within-gradient of a `C²` function is
Lipschitz with constant `M ≥ sup ‖D(Dw)‖`. -/
theorem norm_fderivWithin_sub_le {s : Set E} (hs : Convex ℝ s) (hU : UniqueDiffOn ℝ s)
    {w : E → ℝ} (hw : ContDiffOn ℝ 2 w s) {M : ℝ}
    (hM : ∀ y ∈ s, ‖fderivWithin ℝ (fderivWithin ℝ w s) s y‖ ≤ M) {y y' : E} (hy : y ∈ s)
    (hy' : y' ∈ s) :
    ‖fderivWithin ℝ w s y - fderivWithin ℝ w s y'‖ ≤ M * ‖y - y'‖ := by
  have hd : DifferentiableOn ℝ (fderivWithin ℝ w s) s :=
    (hw.fderivWithin hU (m := 1) (by norm_num)).differentiableOn (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_fderivWithin_le hd hM hs hy' hy

omit [FiniteDimensional ℝ E] in
/-- The second within-derivative of a `C²` function is continuous on a set with unique
differentiability. -/
theorem continuousOn_fderivWithin_fderivWithin {s : Set E} (hU : UniqueDiffOn ℝ s)
    {w : E → ℝ} (hw : ContDiffOn ℝ 2 w s) :
    ContinuousOn (fderivWithin ℝ (fderivWithin ℝ w s) s) s :=
  (hw.fderivWithin hU (m := 1) (by norm_num)).continuousOn_fderivWithin hU le_rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On a set of diameter `≤ D`, a Lipschitz bound `‖f y − f y'‖ ≤ L ‖y − y'‖` gives
`‖f y − f y'‖ ≤ L D^{1−α} ‖y − y'‖^α`. -/
theorem dist_le_rpow_of_lipschitz {F : Type*} [NormedAddCommGroup F] {f : E → F} {L D α : ℝ}
    (hL : 0 ≤ L) (hα : 0 < α ∧ α < 1) {y y' : E} (hyy : dist y y' ≤ D)
    (h : ‖f y - f y'‖ ≤ L * ‖y - y'‖) :
    ‖f y - f y'‖ ≤ L * D ^ (1 - α) * dist y y' ^ α := by
  rw [← dist_eq_norm y y'] at h
  have hd0 : 0 ≤ dist y y' := dist_nonneg
  rcases hd0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero] at h
    have : ‖f y - f y'‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this, ← h0, Real.zero_rpow hα.1.ne', mul_zero]
  have hD : 0 < D := hpos.trans_le hyy
  calc ‖f y - f y'‖ ≤ L * dist y y' := h
    _ = L * (dist y y' ^ (1 - α) * dist y y' ^ α) := by
        rw [← Real.rpow_add hpos]; simp
    _ ≤ L * (D ^ (1 - α) * dist y y' ^ α) := by
        gcongr; linarith [hα.2]
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
/-- **Hölder pairing.** `|L y (v y) − L y' (v y')| ≤ ‖L y − L y'‖ ‖v y‖ + ‖L y'‖ ‖v y − v y'‖`. -/
theorem abs_apply_sub_apply_le (L L' : E →L[ℝ] ℝ) (v v' : E) :
    |L v - L' v'| ≤ ‖L - L'‖ * ‖v‖ + ‖L'‖ * ‖v - v'‖ := by
  have e : L v - L' v' = (L - L') v + L' (v - v') := by simp [map_sub]
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← Real.norm_eq_abs]; exact (L - L').le_opNorm v
  · rw [← Real.norm_eq_abs]; exact L'.le_opNorm _

/-- **Hölder bound for traces.** For bilinear `T, T'` (as multilinear maps of two arguments) and
`A, A'`: `|∑ᵢ T(A eᵢ, eᵢ) − ∑ᵢ T'(A' eᵢ, eᵢ)| ≤ d (‖T − T'‖ ‖A‖ + ‖T'‖ ‖A − A'‖)`. -/
theorem abs_trace_sub_le
    (T T' : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ) (A A' : E →L[ℝ] E) :
    |∑ i, T ![A (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i] -
        ∑ i, T' ![A' (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i]| ≤
      finrank ℝ E * (‖T - T'‖ * ‖A‖ + ‖T'‖ * ‖A - A'‖) := by
  set e := stdOrthonormalBasis ℝ E
  have hbd : ∀ (S : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ) (v w : E),
      |S ![v, w]| ≤ ‖S‖ * ‖v‖ * ‖w‖ := fun S v w ↦ by
    rw [← Real.norm_eq_abs]
    refine (S.le_opNorm _).trans_eq ?_
    rw [Fin.prod_univ_two]; simp [mul_assoc]
  have hterm : ∀ i, |T ![A (e i), e i] - T' ![A' (e i), e i]| ≤
      ‖T - T'‖ * ‖A‖ + ‖T'‖ * ‖A - A'‖ := fun i ↦ by
    have hn : ‖e i‖ = 1 := e.orthonormal.1 i
    have hupd : T' ![A (e i), e i] - T' ![A' (e i), e i] = T' ![(A - A') (e i), e i] := by
      have h := T'.map_update_sub ![A (e i), e i] 0 (A (e i)) (A' (e i))
      have e1 : Function.update ![A (e i), e i] 0 (A (e i) - A' (e i)) =
          ![(A - A') (e i), e i] := by
        ext j; fin_cases j <;> rfl
      have e2 : Function.update ![A (e i), e i] 0 (A (e i)) = ![A (e i), e i] := by
        ext j; fin_cases j <;> rfl
      have e3 : Function.update ![A (e i), e i] 0 (A' (e i)) = ![A' (e i), e i] := by
        ext j; fin_cases j <;> rfl
      rw [e1, e2, e3] at h
      exact h.symm
    have e4 : T ![A (e i), e i] - T' ![A' (e i), e i] =
        (T - T') ![A (e i), e i] + T' ![(A - A') (e i), e i] := by
      rw [← hupd, sub_apply]; ring
    rw [e4]
    have h1 := hbd (T - T') (A (e i)) (e i)
    have h2 := hbd T' ((A - A') (e i)) (e i)
    have h3 : ‖A (e i)‖ ≤ ‖A‖ := by simpa [hn] using A.le_opNorm (e i)
    have h4 : ‖(A - A') (e i)‖ ≤ ‖A - A'‖ := by simpa [hn] using (A - A').le_opNorm (e i)
    rw [hn, mul_one] at h1 h2
    calc _ ≤ |(T - T') ![A (e i), e i]| + |T' ![(A - A') (e i), e i]| := abs_add_le _ _
      _ ≤ ‖T - T'‖ * ‖A (e i)‖ + ‖T'‖ * ‖(A - A') (e i)‖ := add_le_add h1 h2
      _ ≤ _ := by gcongr
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Nondiv

end BasicElliptic
