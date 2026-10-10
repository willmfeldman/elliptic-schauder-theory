/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Holder
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import BasicElliptic.Holder.Algebra
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Hölder algebra for the linear `C^{2,α}` theorem

Small closure properties of `HolderOnWith` used to show that the second derivatives recovered
from the equation are Hölder:

* `Div.holderOnWith_bilinear`: `x ↦ B (f x) (g x)` for a bounded bilinear `B` and bounded Hölder
  factors, with an explicit constant (products, inner products, operator application).
* `Div.holderOnWith_finset_sum`, `Div.holderOnWith_inv_of_le`: finite sums and reciprocals of
  functions bounded below.
* `Div.holderOnWith_of_lipschitzOnWith`: Lipschitz on a bounded set gives `α`-Hölder (`α ≤ 1`).
* `Div.exists_holderOnWith_of_locally`: on a compact set, a function that is Hölder near every
  point (with constants depending on the point) is Hölder (Lebesgue number lemma).

The declarations live in the namespace `BasicElliptic.Div`.
-/

public section

open Metric Set Filter
open scoped NNReal Topology

namespace BasicElliptic.Div

section General

variable {X : Type*} [PseudoMetricSpace X] {α : ℝ≥0} {s : Set X}

/-- **Bounded bilinear images of bounded Hölder factors**: if `‖f‖ ≤ A`, `‖g‖ ≤ B` on `s`, then
`x ↦ Bl (f x) (g x)` is Hölder with constant `‖Bl‖ (A [g] + B [f])`. -/
theorem holderOnWith_bilinear {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Bl : F →L[ℝ] G →L[ℝ] H) {f : X → F} {g : X → G} {Cf Cg A B : ℝ≥0}
    (hf : HolderOnWith Cf α f s) (hg : HolderOnWith Cg α g s) (hfA : ∀ x ∈ s, ‖f x‖ ≤ A)
    (hgB : ∀ x ∈ s, ‖g x‖ ≤ B) :
    HolderOnWith (‖Bl‖₊ * (A * Cg + B * Cf)) α (fun x ↦ Bl (f x) (g x)) s := by
  refine holderOnWith_iff_dist_le.2 fun x hx y hy ↦ ?_
  have h1 := hf.dist_le hx hy
  have h2 := hg.dist_le hx hy
  rw [dist_eq_norm] at h1 h2 ⊢
  have e : Bl (f x) (g x) - Bl (f y) (g y) = Bl (f x) (g x - g y) + Bl (f x - f y) (g y) := by
    simp only [map_sub, sub_apply]; abel
  rw [e]
  have hB0 : 0 ≤ ‖Bl‖ := norm_nonneg _
  calc ‖Bl (f x) (g x - g y) + Bl (f x - f y) (g y)‖
      ≤ ‖Bl‖ * ‖f x‖ * ‖g x - g y‖ + ‖Bl‖ * ‖f x - f y‖ * ‖g y‖ :=
        (norm_add_le _ _).trans (add_le_add (Bl.le_opNorm₂ _ _) (Bl.le_opNorm₂ _ _))
    _ ≤ ‖Bl‖ * A * (Cg * dist x y ^ (α : ℝ)) + ‖Bl‖ * (Cf * dist x y ^ (α : ℝ)) * B := by
        gcongr
        · exact hfA x hx
        · exact hgB y hy
    _ = ((‖Bl‖₊ * (A * Cg + B * Cf) : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
        push_cast; ring

/-- Finite sums of Hölder functions. -/
theorem holderOnWith_finset_sum {F : Type*} [SeminormedAddCommGroup F] {ι : Type*}
    (t : Finset ι) {f : ι → X → F} {C : ι → ℝ≥0}
    (h : ∀ i ∈ t, HolderOnWith (C i) α (f i) s) :
    HolderOnWith (∑ i ∈ t, C i) α (fun x ↦ ∑ i ∈ t, f i x) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using holderOnWith_const (0 : F) 0 α s
  | insert j t hj ih =>
    simp only [Finset.sum_insert hj]
    exact holderOnWith_add (h j (Finset.mem_insert_self j t))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Reciprocals of Hölder functions bounded below by `c > 0`. -/
theorem holderOnWith_inv_of_le {d : X → ℝ} {C : ℝ≥0} {c : ℝ} (hc : 0 < c)
    (hd : HolderOnWith C α d s) (hdc : ∀ x ∈ s, c ≤ d x) :
    HolderOnWith (Real.toNNReal (C / c ^ 2)) α (fun x ↦ (d x)⁻¹) s := by
  refine holderOnWith_of_dist_le (by positivity) fun x hx y hy ↦ ?_
  have hx0 : 0 < d x := hc.trans_le (hdc x hx)
  have hy0 : 0 < d y := hc.trans_le (hdc y hy)
  have h1 := hd.dist_le hx hy
  rw [Real.dist_eq] at h1 ⊢
  have e : (d x)⁻¹ - (d y)⁻¹ = (d y - d x) / (d x * d y) := by field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  have hc2 : c ^ 2 ≤ d x * d y := by
    rw [sq]; exact mul_le_mul (hdc x hx) (hdc y hy) hc.le hx0.le
  rw [div_le_iff₀ (mul_pos hx0 hy0)]
  calc |d x - d y| ≤ C * dist x y ^ (α : ℝ) := h1
    _ = C / c ^ 2 * dist x y ^ (α : ℝ) * c ^ 2 := by field_simp
    _ ≤ C / c ^ 2 * dist x y ^ (α : ℝ) * (d x * d y) := by
        gcongr

/-- A Lipschitz function on a set of diameter at most `D` is `α`-Hölder for `α ≤ 1`. -/
theorem holderOnWith_of_lipschitzOnWith {Y : Type*} [PseudoMetricSpace Y] {f : X → Y}
    {L : ℝ≥0} (hf : LipschitzOnWith L f s) (hα : α ≤ 1) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D) :
    HolderOnWith (Real.toNNReal (L * D ^ (1 - (α : ℝ)))) α f s := by
  refine holderOnWith_of_dist_le (by positivity) fun x hx y hy ↦ ?_
  have hα' : (0 : ℝ) ≤ 1 - α := by rw [sub_nonneg]; exact_mod_cast hα
  have h1 := hf.dist_le_mul x hx y hy
  have e : dist x y = dist x y ^ (1 - (α : ℝ)) * dist x y ^ (α : ℝ) := by
    rw [← Real.rpow_add' dist_nonneg (by norm_num), sub_add_cancel, Real.rpow_one]
  calc dist (f x) (f y) ≤ L * dist x y := h1
    _ = L * (dist x y ^ (1 - (α : ℝ)) * dist x y ^ (α : ℝ)) := by rw [← e]
    _ ≤ L * (D ^ (1 - (α : ℝ)) * dist x y ^ (α : ℝ)) := by
        gcongr
        exact hD x hx y hy
    _ = L * D ^ (1 - (α : ℝ)) * dist x y ^ (α : ℝ) := by ring

end General

section Compact

variable {X : Type*} [PseudoMetricSpace X] {α : ℝ≥0} {s : Set X}

/-- A Hölder function on a compact set is bounded (`α > 0`). -/
theorem exists_bound_of_holderOnWith {F : Type*} [SeminormedAddCommGroup F] {f : X → F}
    {C : ℝ≥0} (hs : IsCompact s) (hα : 0 < α) (hf : HolderOnWith C α f s) :
    ∃ A : ℝ≥0, ∀ x ∈ s, ‖f x‖ ≤ A := by
  obtain ⟨A, hA⟩ := hs.exists_bound_of_continuousOn (hf.continuousOn hα)
  exact ⟨Real.toNNReal A, fun x hx ↦ (hA x hx).trans (Real.le_coe_toNNReal A)⟩

/-- Qualitative bilinear closure on a compact set. -/
theorem exists_holderOnWith_bilinear {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (hs : IsCompact s) (hα : 0 < α) (Bl : F →L[ℝ] G →L[ℝ] H) {f : X → F} {g : X → G}
    (hf : ∃ C, HolderOnWith C α f s) (hg : ∃ C, HolderOnWith C α g s) :
    ∃ C, HolderOnWith C α (fun x ↦ Bl (f x) (g x)) s := by
  obtain ⟨Cf, hf⟩ := hf
  obtain ⟨Cg, hg⟩ := hg
  obtain ⟨A, hA⟩ := exists_bound_of_holderOnWith hs hα hf
  obtain ⟨B, hB⟩ := exists_bound_of_holderOnWith hs hα hg
  exact ⟨_, holderOnWith_bilinear Bl hf hg hA hB⟩

/-- **Local to global** on a compact set: if every point of `s` has a neighbourhood (relative to
`s`) on which `f` is `α`-Hölder, then `f` is `α`-Hölder on `s` (`α > 0`). -/
theorem exists_holderOnWith_of_locally {F : Type*} [SeminormedAddCommGroup F] {f : X → F}
    (hs : IsCompact s) (hα : 0 < α)
    (hloc : ∀ y ∈ s, ∃ ε > 0, ∃ C : ℝ≥0, HolderOnWith C α f (s ∩ ball y ε)) :
    ∃ C : ℝ≥0, HolderOnWith C α f s := by
  choose! ε hε C hC using hloc
  -- continuity, hence boundedness
  have hcont : ContinuousOn f s := fun y hy ↦
    ((hC y hy).continuousOn hα y ⟨hy, mem_ball_self (hε y hy)⟩).mono_of_mem_nhdsWithin
      (inter_mem_nhdsWithin s (ball_mem_nhds y (hε y hy)))
  obtain ⟨A, hA⟩ := hs.exists_bound_of_continuousOn hcont
  -- a finite subcover by the balls `ball y (ε y / 2)`
  obtain ⟨t, hcov⟩ := hs.elim_finite_subcover (fun y : s ↦ ball (y : X) (ε y / 2))
    (fun _ ↦ isOpen_ball) fun y hy ↦ mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (half_pos (hε y hy))⟩
  -- a Lebesgue number
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hs
    (c := fun y : t ↦ ball ((y : s) : X) (ε y / 2)) (fun _ ↦ isOpen_ball)
    (fun y hy ↦ by
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hcov hy)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hyi⟩)
  set C' : ℝ≥0 := t.sup fun i ↦ C i with hC'
  refine ⟨_, holderOnWith_of_near_far (C' := C') (B := 2 * A) C'.2 hδ (fun x hx y hy ↦ ?_)
    fun x hx y hy hxy ↦ ?_⟩
  · rw [dist_eq_norm]
    linarith [norm_sub_le (f x) (f y), hA x hx, hA y hy]
  · obtain ⟨⟨i, hi⟩, hball⟩ := hleb x hx
    have hxi : x ∈ ball (i : X) (ε i / 2) := hball (mem_ball_self hδ)
    have hyi : y ∈ ball (i : X) (ε i / 2) := hball (by rw [mem_ball, dist_comm]; exact hxy)
    have hεi := hε i i.2
    have hx' : x ∈ s ∩ ball (i : X) (ε i) := ⟨hx, ball_subset_ball (by linarith) hxi⟩
    have hy' : y ∈ s ∩ ball (i : X) (ε i) := ⟨hy, ball_subset_ball (by linarith) hyi⟩
    refine ((hC i i.2).dist_le hx' hy').trans ?_
    gcongr
    exact_mod_cast Finset.le_sup (f := fun i : s ↦ C i) hi

end Compact

section Exists

/-! ### Qualitative closure (`∃ C, HolderOnWith C α f s`) -/

variable {X : Type*} [PseudoMetricSpace X] {α : ℝ≥0} {s : Set X}

theorem exists_holderOnWith_const {F : Type*} [SeminormedAddCommGroup F] (c : F) :
    ∃ C, HolderOnWith C α (fun _ : X ↦ c) s :=
  ⟨0, holderOnWith_const c 0 α s⟩

theorem exists_holderOnWith_add {F : Type*} [SeminormedAddCommGroup F] {f g : X → F}
    (hf : ∃ C, HolderOnWith C α f s) (hg : ∃ C, HolderOnWith C α g s) :
    ∃ C, HolderOnWith C α (fun x ↦ f x + g x) s := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨C', hC'⟩ := hg
  exact ⟨_, holderOnWith_add hC hC'⟩

theorem exists_holderOnWith_neg {F : Type*} [SeminormedAddCommGroup F] {f : X → F}
    (hf : ∃ C, HolderOnWith C α f s) : ∃ C, HolderOnWith C α (fun x ↦ -f x) s := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨_, holderOnWith_neg hC⟩

theorem exists_holderOnWith_sub {F : Type*} [SeminormedAddCommGroup F] {f g : X → F}
    (hf : ∃ C, HolderOnWith C α f s) (hg : ∃ C, HolderOnWith C α g s) :
    ∃ C, HolderOnWith C α (fun x ↦ f x - g x) s := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨C', hC'⟩ := hg
  exact ⟨_, holderOnWith_sub hC hC'⟩

theorem exists_holderOnWith_sum {F : Type*} [SeminormedAddCommGroup F] {ι : Type*}
    (t : Finset ι) {f : ι → X → F} (h : ∀ i ∈ t, ∃ C, HolderOnWith C α (f i) s) :
    ∃ C, HolderOnWith C α (fun x ↦ ∑ i ∈ t, f i x) s := by
  classical
  choose! C hC using h
  exact ⟨_, holderOnWith_finset_sum t hC⟩

theorem exists_holderOnWith_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : X → F}
    (hf : ∃ C, HolderOnWith C α f s) : ∃ C, HolderOnWith C α (fun x ↦ L (f x)) s := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨_, holderOnWith_comp_lipschitzOnWith (L.lipschitzWith.lipschitzOnWith (s := univ)) hC
    (mapsTo_univ _ _)⟩

theorem exists_holderOnWith_inv {d : X → ℝ} {c : ℝ} (hc : 0 < c)
    (hd : ∃ C, HolderOnWith C α d s) (hdc : ∀ x ∈ s, c ≤ d x) :
    ∃ C, HolderOnWith C α (fun x ↦ (d x)⁻¹) s := by
  obtain ⟨C, hC⟩ := hd
  exact ⟨_, holderOnWith_inv_of_le hc hC hdc⟩

end Exists

end BasicElliptic.Div
