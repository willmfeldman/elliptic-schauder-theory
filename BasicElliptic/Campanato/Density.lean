/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Basic.HalfSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Interior measure density ("type A" regions)

A set `S` in a finite-dimensional real inner product space `E` (`d = finrank ℝ E`) has
*density `c₀` up to scale `ρ₀`* (`BasicElliptic.HasDensity S c₀ ρ₀`) if

  `c₀ ρ^d ≤ |B_ρ(p) ∩ S|` for all `p ∈ S` and `0 < ρ ≤ ρ₀`.

These are Campanato's "type A" regions (Giaquinta–Martinazzi), on which
`BasicElliptic.holderOnWith_of_campanato` runs.

* `BasicElliptic.HasDensity.of_convex`: a convex set containing a ball `B_r(c)` and contained in
  `closedBall c D` has density `|B_1| (r / (2 (D + r)))^d` up to scale `2 (D + r)`. For `p ∈ S`,
  the ball `B_{λ r}(p + λ (c - p))`, `λ = ρ / (2 (D + r))`, lies in `B_ρ(p) ∩ S`.
* `BasicElliptic.halfBall_density`: `halfBall ν x R` with `‖ν‖ = 1`, `⟪x, ν⟫ ≥ 0` has density
  `|B_1| / 14^d` up to scale `R` (it contains `B_{R/4}(x + (R/2) ν)`).
* `BasicElliptic.closedBall_density`: `closedBall x R` has density `|B_1| / 4^d` up to scale `R`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace Module

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `S` has density `c₀` up to scale `ρ₀`: `c₀ ρ^d ≤ |B_ρ(p) ∩ S|` for `p ∈ S`, `0 < ρ ≤ ρ₀`. -/
@[expose] def HasDensity (S : Set E) (c₀ ρ₀ : ℝ) : Prop :=
  ∀ p ∈ S, ∀ ρ ∈ Ioc 0 ρ₀, c₀ * ρ ^ finrank ℝ E ≤ volume.real (ball p ρ ∩ S)

theorem HasDensity.mono_scale {S : Set E} {c₀ ρ₀ ρ₁ : ℝ} (h : HasDensity S c₀ ρ₀)
    (hρ : ρ₁ ≤ ρ₀) : HasDensity S c₀ ρ₁ :=
  fun p hp ρ hρ' ↦ h p hp ρ ⟨hρ'.1, hρ'.2.trans hρ⟩

/-- The volume of the unit ball, as a real number. -/
noncomputable def unitBallVolume (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  volume.real (ball (0 : E) 1)

theorem unitBallVolume_pos : 0 < unitBallVolume E :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- `|B_r(x)| = r^d |B_1|`. -/
theorem measureReal_ball_eq {x : E} {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = r ^ finrank ℝ E * unitBallVolume E := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), unitBallVolume, measureReal_def]

/-- A convex set containing `B_r(c)` and within distance `D` of `c` has density
`|B_1| (r / (2 (D + r)))^d` up to scale `2 (D + r)`. -/
theorem HasDensity.of_convex {S : Set E} (hS : Convex ℝ S) {c : E} {r D : ℝ} (hr : 0 < r)
    (hball : ball c r ⊆ S) (hD : ∀ p ∈ S, dist p c ≤ D) :
    HasDensity S (unitBallVolume E * (r / (2 * (D + r))) ^ finrank ℝ E) (2 * (D + r)) := by
  intro p hp ρ hρ
  have hD0 : 0 ≤ D := le_trans dist_nonneg (hD p hp)
  have hDr : 0 < 2 * (D + r) := by positivity
  set l : ℝ := ρ / (2 * (D + r)) with hl
  have hl0 : 0 < l := div_pos hρ.1 hDr
  have hl1 : l ≤ 1 := (div_le_one hDr).2 hρ.2
  set m : E := p + l • (c - p) with hm
  have hsub : ball m (l * r) ⊆ ball p ρ ∩ S := by
    intro y hy
    rw [mem_ball] at hy
    constructor
    · rw [mem_ball]
      have hmp : dist m p = l * dist c p := by
        rw [hm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hl0, dist_eq_norm]
      have hcp : dist c p ≤ D := by rw [dist_comm]; exact hD p hp
      calc dist y p ≤ dist y m + dist m p := dist_triangle _ _ _
        _ < l * r + l * D := by
            rw [hmp]; exact add_lt_add_of_lt_of_le hy (mul_le_mul_of_nonneg_left hcp hl0.le)
        _ = ρ / 2 := by rw [hl]; field_simp; ring
        _ ≤ ρ := by linarith [hρ.1]
    · set z : E := p + l⁻¹ • (y - p) with hz
      have hzc : z ∈ ball c r := by
        rw [mem_ball, dist_eq_norm]
        have : z - c = l⁻¹ • (y - m) := by
          refine (eq_inv_smul_iff₀ hl0.ne').2 ?_
          rw [hz, hm, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
          module
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl0), ← dist_eq_norm,
          inv_mul_lt_iff₀ hl0]
        exact hy
      have hyz : y = p + l • (z - p) := by
        rw [hz, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hl0.ne', one_smul,
          add_sub_cancel]
      rw [hyz]
      exact hS.add_smul_sub_mem hp (hball hzc) ⟨hl0.le, hl1⟩
  calc unitBallVolume E * (r / (2 * (D + r))) ^ finrank ℝ E * ρ ^ finrank ℝ E
      = (l * r) ^ finrank ℝ E * unitBallVolume E := by
        rw [hl, mul_comm (ρ / _) r, mul_div_assoc', mul_div_right_comm, mul_pow]; ring
    _ = volume.real (ball m (l * r)) := (measureReal_ball_eq (by positivity)).symm
    _ ≤ volume.real (ball p ρ ∩ S) :=
        measureReal_mono hsub ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne

/-- The constant `|B_1| / 14^d` of `halfBall_density`. -/
noncomputable def halfBallDensityConst (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  unitBallVolume E * (1 / 14) ^ finrank ℝ E

theorem halfBallDensityConst_pos : 0 < halfBallDensityConst E :=
  mul_pos unitBallVolume_pos (by positivity)

/-- **Density of half balls.** For `‖ν‖ = 1` and `⟪x, ν⟫ ≥ 0`, `halfBall ν x R` has density
`|B_1| / 14^d` up to scale `R`. -/
theorem halfBall_density {ν x : E} {R : ℝ} (hν : ‖ν‖ = 1) (hR : 0 < R) (hx : 0 ≤ ⟪x, ν⟫) :
    HasDensity (halfBall ν x R) (halfBallDensityConst E) R := by
  have hball : ball (x + (R / 2) • ν) (R / 4) ⊆ halfBall ν x R := by
    intro y hy
    rw [mem_ball] at hy
    have hxc : dist (x + (R / 2) • ν) x = R / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hν, Real.norm_eq_abs,
        abs_of_pos (by positivity), mul_one]
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall]
      linarith [dist_triangle y (x + (R / 2) • ν) x]
    · rw [mem_halfSpace]
      have h1 : ⟪y, ν⟫ = ⟪x, ν⟫ + R / 2 + ⟪y - (x + (R / 2) • ν), ν⟫ := by
        rw [inner_sub_left, inner_add_left, real_inner_smul_left,
          real_inner_self_of_norm_eq_one hν]
        ring
      have h2 : |⟪y - (x + (R / 2) • ν), ν⟫| ≤ R / 4 := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [hν, mul_one, ← dist_eq_norm]
        exact hy.le
      linarith [neg_abs_le ⟪y - (x + (R / 2) • ν), ν⟫]
  have hD : ∀ p ∈ halfBall ν x R, dist p (x + (R / 2) • ν) ≤ 3 * R / 2 := by
    intro p hp
    have hxc : dist x (x + (R / 2) • ν) = R / 2 := by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, Real.norm_eq_abs,
        abs_of_pos (by positivity), mul_one]
    linarith [dist_triangle p x (x + (R / 2) • ν), (mem_halfBall.1 hp).1]
  have h := HasDensity.of_convex (convex_halfBall ν x R) (by positivity) hball hD
  have hc : R / 4 / (2 * (3 * R / 2 + R / 4)) = 1 / 14 := by field_simp; ring
  rw [hc] at h
  exact h.mono_scale (by linarith)

/-- **Density of balls.** `closedBall x R` has density `|B_1| / 4^d` up to scale `R`. -/
theorem closedBall_density {x : E} {R : ℝ} (hR : 0 < R) :
    HasDensity (closedBall x R) (unitBallVolume E * (1 / 4) ^ finrank ℝ E) R := by
  have h := HasDensity.of_convex (convex_closedBall x R) hR ball_subset_closedBall
    (fun p hp ↦ mem_closedBall.1 hp)
  have hc : R / (2 * (R + R)) = 1 / 4 := by field_simp; ring
  rw [hc] at h
  exact h.mono_scale (by linarith)

end BasicElliptic
