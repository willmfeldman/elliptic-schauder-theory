/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Holder
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Algebra of Hölder bounds on sets

Mathlib's `HolderOnWith C α f s` (`C α : ℝ≥0`, stated with `edist`) is the predicate, and
`BasicElliptic.eHolderSeminormOn α f s` is the best constant. This file supplies the
calculus used throughout the development:

* bridges with real distances: `holderOnWith_iff_dist_le`, `holderOnWith_of_dist_le`;
* the seminorm is attained and characterizes the predicate:
  `holderOnWith_eHolderSeminormOn`, `dist_le_holderSeminormOn_mul`;
* monotonicity in the set: `eHolderSeminormOn_mono` (for the exponent use Mathlib's
  `HolderOnWith.of_le` on bounded sets);
* sums, negatives, composition with Lipschitz maps: `holderOnWith_add`, `holderOnWith_neg`,
  `holderOnWith_sub`, `holderOnWith_comp_lipschitzOnWith`;
* local to global: `holderOnWith_of_near_far` (a bound for near pairs and an oscillation bound give
  a global Hölder bound).

## Provenance

Elliptic analogues of `HolderOnPar.{add, neg, sub, const_mul, mul, of_near_far}` in
parabolic-basic-theory, `ParabolicBasic/Schauder/Holder.lean` (own repository, commit `2507d9a`),
with the parabolic distance replaced by `dist` and Mathlib's `HolderOnWith` as the predicate.
-/

public section

open Set
open scoped NNReal ENNReal

namespace BasicElliptic

section PseudoEMetric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {α : ℝ≥0} {f : X → Y}
  {s t : Set X}

/-- The Hölder seminorm is monotone in the set. -/
theorem eHolderSeminormOn_mono (hts : t ⊆ s) : eHolderSeminormOn α f t ≤ eHolderSeminormOn α f s :=
  le_iInf₂ fun _ hC ↦ eHolderSeminormOn_le_of_holderOnWith (hC.mono hts)

end PseudoEMetric

section PseudoMetric

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {C α : ℝ≥0} {f : X → Y}
  {s t : Set X}

/-- `HolderOnWith` in terms of real distances. -/
theorem holderOnWith_iff_dist_le :
    HolderOnWith C α f s ↔ ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ) := by
  refine ⟨fun h x hx y hy ↦ h.dist_le hx hy, fun h x hx y hy ↦ ?_⟩
  calc edist (f x) (f y) = ENNReal.ofReal (dist (f x) (f y)) := edist_dist _ _
    _ ≤ ENNReal.ofReal (C * dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal (h x hx y hy)
    _ = C * edist x y ^ (α : ℝ) := by
        rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg, ← edist_dist]

/-- A real Hölder bound with constant `C ≥ 0` gives `HolderOnWith C.toNNReal`. -/
theorem holderOnWith_of_dist_le {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) :
    HolderOnWith (Real.toNNReal C) α f s :=
  holderOnWith_iff_dist_le.2 fun x hx y hy ↦ by
    rw [Real.coe_toNNReal C hC]; exact h x hx y hy

/-- The set of admissible constants is closed from above. -/
theorem holderOnWith_of_forall_lt (h : ∀ C' : ℝ≥0, C < C' → HolderOnWith C' α f s) :
    HolderOnWith C α f s := by
  refine holderOnWith_iff_dist_le.2 fun x hx y hy ↦ ?_
  by_contra hlt
  push Not at hlt
  have hd : 0 < dist x y ^ (α : ℝ) := by
    rcases (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) (α : ℝ)).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hlt
      exact absurd (h (C + 1) (by simp) |>.dist_le hx hy) (by rw [← h0, mul_zero]; linarith)
    · exact h0
  set q := dist (f x) (f y) / dist x y ^ (α : ℝ)
  have hCq : (C : ℝ) < q := (lt_div_iff₀ hd).2 hlt
  set C' : ℝ := (C + q) / 2
  have hC'0 : 0 ≤ C' := by have := C.2; positivity
  have hle := (h (Real.toNNReal C') (by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hC'0]; simp only [C']; linarith)).dist_le hx hy
  rw [Real.coe_toNNReal _ hC'0] at hle
  have : dist (f x) (f y) = q * dist x y ^ (α : ℝ) := by
    simp only [q]; field_simp
  rw [this] at hle
  have : q ≤ C' := le_of_mul_le_mul_right hle hd
  simp only [C'] at this
  linarith

/-- **The Hölder seminorm is attained.** -/
theorem holderOnWith_eHolderSeminormOn (h : eHolderSeminormOn α f s ≠ ⊤) :
    HolderOnWith (eHolderSeminormOn α f s).toNNReal α f s := by
  refine holderOnWith_of_forall_lt fun C' hC' ↦ ?_
  have hlt : eHolderSeminormOn α f s < C' := by
    rw [← ENNReal.coe_toNNReal h]; exact_mod_cast hC'
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, HolderOnWith C α f s ∧ (C : ℝ≥0∞) < C' := by
    simpa [eHolderSeminormOn, iInf_lt_iff] using hlt
  exact hC.1.mono_const (by exact_mod_cast hC.2.le)

/-- With a finite seminorm, `dist (f x) (f y) ≤ [f]_α dist x y ^ α`. -/
theorem dist_le_holderSeminormOn_mul (h : eHolderSeminormOn α f s ≠ ⊤) {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) : dist (f x) (f y) ≤ holderSeminormOn α f s * dist x y ^ (α : ℝ) :=
  (holderOnWith_eHolderSeminormOn h).dist_le hx hy

/-- A real Hölder bound bounds the real seminorm. -/
theorem holderSeminormOn_le_of_dist_le {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) :
    holderSeminormOn α f s ≤ C := by
  have := holderSeminormOn_le_of_holderOnWith (holderOnWith_of_dist_le hC h)
  rwa [Real.coe_toNNReal C hC] at this

/-- **Near pairs and far pairs** (after PBT `HolderOnPar.of_near_far`): a Hölder bound for pairs
at distance `< η` and an oscillation bound `dist (f x) (f y) ≤ B` give a global Hölder bound. -/
theorem holderOnWith_of_near_far {C' η B : ℝ} (hC' : 0 ≤ C') (hη : 0 < η)
    (hB : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ B)
    (hnear : ∀ x ∈ s, ∀ y ∈ s, dist x y < η → dist (f x) (f y) ≤ C' * dist x y ^ (α : ℝ)) :
    HolderOnWith (Real.toNNReal (max C' (B * η ^ (-(α : ℝ))))) α f s := by
  refine holderOnWith_of_dist_le (le_max_of_le_left hC') fun x hx y hy ↦ ?_
  have hpd : 0 ≤ dist x y ^ (α : ℝ) := Real.rpow_nonneg dist_nonneg _
  by_cases hxy : dist x y < η
  · exact (hnear x hx y hy hxy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpd)
  · push Not at hxy
    have hB0 : 0 ≤ B := dist_nonneg.trans (hB x hx y hy)
    have h1 : 1 ≤ η ^ (-(α : ℝ)) * dist x y ^ (α : ℝ) := by
      rw [Real.rpow_neg hη.le, ← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hη _),
        one_mul]
      exact Real.rpow_le_rpow hη.le hxy α.coe_nonneg
    calc dist (f x) (f y) ≤ B := hB x hx y hy
      _ ≤ B * (η ^ (-(α : ℝ)) * dist x y ^ (α : ℝ)) := le_mul_of_one_le_right hB0 h1
      _ = B * η ^ (-(α : ℝ)) * dist x y ^ (α : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpd

/-- Composition with a Lipschitz map on the left. -/
theorem holderOnWith_comp_lipschitzOnWith {Z : Type*} [PseudoMetricSpace Z] {g : Y → Z}
    {K : ℝ≥0} {u : Set Y} (hg : LipschitzOnWith K g u) (hf : HolderOnWith C α f s)
    (hfu : MapsTo f s u) : HolderOnWith (K * C) α (g ∘ f) s := by
  refine holderOnWith_iff_dist_le.2 fun x hx y hy ↦ ?_
  calc dist (g (f x)) (g (f y)) ≤ K * dist (f x) (f y) :=
        hg.dist_le_mul _ (hfu hx) _ (hfu hy)
    _ ≤ K * (C * dist x y ^ (α : ℝ)) := mul_le_mul_of_nonneg_left (hf.dist_le hx hy) K.2
    _ = _ := by push_cast; ring

end PseudoMetric

section Normed

variable {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y] {C C' α : ℝ≥0}
  {f g : X → Y} {s : Set X}

theorem holderOnWith_const (c : Y) (C α : ℝ≥0) (s : Set X) :
    HolderOnWith C α (fun _ ↦ c) s :=
  holderOnWith_iff_dist_le.2 fun x _ y _ ↦ by
    rw [dist_self]; exact mul_nonneg C.2 (Real.rpow_nonneg dist_nonneg _)

theorem holderOnWith_add (hf : HolderOnWith C α f s) (hg : HolderOnWith C' α g s) :
    HolderOnWith (C + C') α (fun x ↦ f x + g x) s :=
  holderOnWith_iff_dist_le.2 fun x hx y hy ↦ by
    calc dist (f x + g x) (f y + g y) ≤ dist (f x) (f y) + dist (g x) (g y) :=
          dist_add_add_le _ _ _ _
      _ ≤ C * dist x y ^ (α : ℝ) + C' * dist x y ^ (α : ℝ) :=
          add_le_add (hf.dist_le hx hy) (hg.dist_le hx hy)
      _ = _ := by push_cast; ring

theorem holderOnWith_neg (hf : HolderOnWith C α f s) : HolderOnWith C α (fun x ↦ -f x) s :=
  holderOnWith_iff_dist_le.2 fun x hx y hy ↦ by rw [dist_neg_neg]; exact hf.dist_le hx hy

theorem holderOnWith_sub (hf : HolderOnWith C α f s) (hg : HolderOnWith C' α g s) :
    HolderOnWith (C + C') α (fun x ↦ f x - g x) s := by
  simpa only [sub_eq_add_neg] using holderOnWith_add hf (holderOnWith_neg hg)

section Module

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 Y]

end Module

end Normed

end BasicElliptic
