/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Basic.HalfSpace

/-!
# Uniform interior balls

`BasicElliptic.HasUniformInteriorBalls S r₁ κ`: for every `p ∈ S` and every scale `r ∈ (0, r₁]`
there is a ball of radius `κ r` contained in `S ∩ ball p r` (precisely: `ball y (κ r) ⊆ S` and
`dist y p + κ r ≤ r`). This is the geometric input of the closed-region bridge: one-sided expansions
at boundary points determine their coefficients by extraction on these balls
(`QuadPoly.two_expansions_coeff`).

* `Convex.hasUniformInteriorBalls`: a convex set containing `ball x₀ δ` and contained in
  `closedBall x₀ R` has uniform interior balls with `r₁ = R + δ`, `κ = δ / (R + δ)` (the
  homothetic image of `ball x₀ δ` with centre `p` and ratio `r / (R + δ)`).
* `exists_hasUniformInteriorBalls`: the same for bounded convex sets with nonempty interior.
-/

@[expose] public section

open Set Metric RealInnerProductSpace

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `S` contains, at every point `p ∈ S` and every scale `r ∈ (0, r₁]`, a ball of radius `κ r`
inside `ball p r` (up to the boundary sphere). -/
def HasUniformInteriorBalls (S : Set E) (r₁ κ : ℝ) : Prop :=
  ∀ p ∈ S, ∀ r, 0 < r → r ≤ r₁ → ∃ y, ball y (κ * r) ⊆ S ∧ dist y p + κ * r ≤ r

/-- **Convex bodies have uniform interior balls.** -/
theorem Convex.hasUniformInteriorBalls {S : Set E} (hS : Convex ℝ S) {x₀ : E} {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 ≤ R) (hball : ball x₀ δ ⊆ S) (hSR : ∀ p ∈ S, dist p x₀ ≤ R) :
    HasUniformInteriorBalls S (R + δ) (δ / (R + δ)) := by
  intro p hp r hr hrr
  have hRδ : 0 < R + δ := by linarith
  set l := r / (R + δ) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := (div_le_one hRδ).2 hrr
  have hκ : δ / (R + δ) * r = l * δ := by rw [hl]; ring
  refine ⟨p + l • (x₀ - p), ?_, ?_⟩
  · intro z hz
    rw [hκ, mem_ball, dist_eq_norm] at hz
    set w := x₀ + l⁻¹ • (z - (p + l • (x₀ - p)))
    have hw : w ∈ S := hball <| by
      rw [mem_ball, dist_eq_norm, show w - x₀ = l⁻¹ • (z - (p + l • (x₀ - p))) by
        simp only [w]; abel, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl0),
        inv_mul_lt_iff₀ hl0]
      linarith
    have := hS.add_smul_sub_mem hp hw ⟨hl0.le, hl1⟩
    convert this using 1
    rw [show w - p = (x₀ - p) + l⁻¹ • (z - (p + l • (x₀ - p))) by simp only [w]; abel,
      smul_add, smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
    abel
  · rw [hκ, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hl0,
      ← dist_eq_norm, dist_comm]
    calc l * dist p x₀ + l * δ ≤ l * R + l * δ := by gcongr; exact hSR p hp
      _ = r := by rw [hl]; field_simp

/-- **Bounded convex sets with nonempty interior have uniform interior balls.** -/
theorem exists_hasUniformInteriorBalls {S : Set E} (hS : Convex ℝ S)
    (hb : Bornology.IsBounded S) (hi : (interior S).Nonempty) :
    ∃ r₁ κ : ℝ, 0 < r₁ ∧ 0 < κ ∧ κ ≤ 1 ∧ HasUniformInteriorBalls S r₁ κ := by
  obtain ⟨x₀, hx₀⟩ := hi
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  obtain ⟨R, hR⟩ := hb.subset_closedBall x₀
  have hR0 : 0 ≤ R := by
    have := hR (interior_subset hx₀); rw [mem_closedBall, dist_self] at this; exact this
  refine ⟨R + δ, δ / (R + δ), by linarith, by positivity, (div_le_one (by linarith)).2
    (by linarith), Convex.hasUniformInteriorBalls hS hδ hR0 (hball.trans interior_subset)
    fun p hp ↦ hR hp⟩

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Inner

end BasicElliptic
