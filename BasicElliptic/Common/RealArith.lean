/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Real-arithmetic helpers shared by the divergence-form files

Moved here from private copies in `Div/Interior/GradientCampanato.lean`,
`Div/Boundary/Decay.lean`, `Div/Interior/LocalHolder.lean` and `Div/Boundary/LocalHolder.lean`.

* `BasicElliptic.sqrt_sum_four_sq_le`: `√(a² + b² + c² + e²) ≤ a + b + c + e` for `a, b, c, e ≥ 0`.
* `BasicElliptic.gradCampanatoCoeff` and `BasicElliptic.gradCampanato_raw_bound_le`: the algebra
  turning the raw transported decay bound into `C ρ^{d+2α} Q X` (`gradient_campanato_at_point` in
  `Div/Interior/GradientCampanato.lean`, the boundary decay in `Div/Boundary/Decay.lean`).
-/

public section

namespace BasicElliptic

/-- `√(a² + b² + c² + e²) ≤ a + b + c + e` for nonnegative reals. -/
theorem sqrt_sum_four_sq_le {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) : √(a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) ≤ a + b + c + e := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha he, mul_nonneg hb hc,
    mul_nonneg hb he, mul_nonneg hc he]

/-- The coefficient `Q(s, l)` collecting the powers of `s = √Λ`, `l = √lam` in
`Div.gradient_campanato_at_point`. -/
noncomputable def gradCampanatoCoeff (vB s l α : ℝ) : ℝ :=
  vB * s ^ 2 * s ^ (2 * α) + s ^ 2 * s ^ (2 * α) / l ^ 4 + s ^ (2 * α) / l ^ 2 +
    s ^ (-(2 - 2 * α))

theorem gradCampanatoCoeff_nonneg {vB s l α : ℝ} (hvB : 0 ≤ vB) (hs : 0 ≤ s) :
    0 ≤ gradCampanatoCoeff vB s l α := by
  unfold gradCampanatoCoeff
  have := Real.rpow_nonneg hs (2 * α)
  have := Real.rpow_nonneg hs (-(2 - 2 * α))
  positivity

/-- The algebra turning the raw bound of the transported decay into `C ρ^{d+2α} Q X`. -/
theorem gradCampanato_raw_bound_le {d : ℕ} {α s l δ ρ Cd vB M₀ Ka KG Mf : ℝ} (hs : 0 < s)
    (hl : 0 < l) (hδ : 0 < δ) (hρ : 0 < ρ) (hCd : 0 ≤ Cd) (hvB : 0 ≤ vB) :
    Cd * ((ρ / (δ / s)) ^ ((d : ℝ) + 2 * α) * ((s * M₀) ^ 2 * ((δ / s) ^ d * vB)) +
        ρ ^ ((d : ℝ) + 2 * α) * ((Ka * s ^ α / l ^ 2) ^ 2 * (s * M₀) ^ 2 +
          (KG * s ^ α / l) ^ 2 + Mf ^ 2 * (δ / s) ^ (2 - 2 * α))) ≤
      Cd * ρ ^ ((d : ℝ) + 2 * α) * gradCampanatoCoeff vB s l α *
        (M₀ ^ 2 * δ ^ (-(2 * α)) + Ka ^ 2 * M₀ ^ 2 + KG ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * α)) := by
  set b : ℝ := (d : ℝ) + 2 * α
  set R := δ / s with hR
  have hR0 : 0 < R := div_pos hδ hs
  have e1 : (ρ / R) ^ b * R ^ d = ρ ^ b * (s ^ (2 * α) * δ ^ (-(2 * α))) := by
    rw [Real.div_rpow hρ.le hR0.le, div_mul_eq_mul_div, mul_div_assoc]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_sub hR0, show (d : ℝ) - b = -(2 * α) by ring,
      hR, Real.div_rpow hδ.le hs.le, Real.rpow_neg hs.le, div_inv_eq_mul, mul_comm]
  have e2 : (s ^ α) ^ 2 = s ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; congr 1; push_cast; ring
  have e3 : R ^ (2 - 2 * α) = δ ^ (2 - 2 * α) * s ^ (-(2 - 2 * α)) := by
    rw [hR, Real.div_rpow hδ.le hs.le, Real.rpow_neg hs.le, div_eq_mul_inv]
  have hρb : 0 ≤ ρ ^ b := Real.rpow_nonneg hρ.le _
  have hs2 : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs.le _
  have hs3 : 0 ≤ s ^ (-(2 - 2 * α)) := Real.rpow_nonneg hs.le _
  have hδ1 : 0 ≤ δ ^ (-(2 * α)) := Real.rpow_nonneg hδ.le _
  have hδ2 : 0 ≤ δ ^ (2 - 2 * α) := Real.rpow_nonneg hδ.le _
  have hlhs : (ρ / R) ^ b * ((s * M₀) ^ 2 * (R ^ d * vB)) +
      ρ ^ b * ((Ka * s ^ α / l ^ 2) ^ 2 * (s * M₀) ^ 2 + (KG * s ^ α / l) ^ 2 +
        Mf ^ 2 * R ^ (2 - 2 * α)) =
      ρ ^ b * ((vB * s ^ 2 * s ^ (2 * α)) * (M₀ ^ 2 * δ ^ (-(2 * α))) +
        (s ^ 2 * s ^ (2 * α) / l ^ 4) * (Ka ^ 2 * M₀ ^ 2) + (s ^ (2 * α) / l ^ 2) * KG ^ 2 +
        s ^ (-(2 - 2 * α)) * (Mf ^ 2 * δ ^ (2 - 2 * α))) := by
    have : (ρ / R) ^ b * ((s * M₀) ^ 2 * (R ^ d * vB)) =
        ((ρ / R) ^ b * R ^ d) * ((s * M₀) ^ 2 * vB) := by ring
    rw [this, e1, e3]
    have e4 : (Ka * s ^ α / l ^ 2) ^ 2 = Ka ^ 2 * (s ^ α) ^ 2 / l ^ 4 := by ring
    have e5 : (KG * s ^ α / l) ^ 2 = KG ^ 2 * (s ^ α) ^ 2 / l ^ 2 := by ring
    rw [e4, e5, e2]
    ring
  rw [hlhs, mul_assoc Cd, mul_assoc Cd, mul_assoc (ρ ^ b)]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hρb) hCd
  have hQ : ∀ c x : ℝ, 0 ≤ x → c ≤ gradCampanatoCoeff vB s l α →
      c * x ≤ gradCampanatoCoeff vB s l α * x :=
    fun c x hx hc ↦ mul_le_mul_of_nonneg_right hc hx
  have hq1 : vB * s ^ 2 * s ^ (2 * α) ≤ gradCampanatoCoeff vB s l α := by
    unfold gradCampanatoCoeff; have : 0 ≤ s ^ 2 * s ^ (2 * α) / l ^ 4 := by positivity
    have : 0 ≤ s ^ (2 * α) / l ^ 2 := by positivity
    linarith
  have hq2 : s ^ 2 * s ^ (2 * α) / l ^ 4 ≤ gradCampanatoCoeff vB s l α := by
    unfold gradCampanatoCoeff; have : 0 ≤ vB * s ^ 2 * s ^ (2 * α) := by positivity
    have : 0 ≤ s ^ (2 * α) / l ^ 2 := by positivity
    linarith
  have hq3 : s ^ (2 * α) / l ^ 2 ≤ gradCampanatoCoeff vB s l α := by
    unfold gradCampanatoCoeff; have : 0 ≤ vB * s ^ 2 * s ^ (2 * α) := by positivity
    have : 0 ≤ s ^ 2 * s ^ (2 * α) / l ^ 4 := by positivity
    linarith
  have hq4 : s ^ (-(2 - 2 * α)) ≤ gradCampanatoCoeff vB s l α := by
    unfold gradCampanatoCoeff; have : 0 ≤ vB * s ^ 2 * s ^ (2 * α) := by positivity
    have : 0 ≤ s ^ 2 * s ^ (2 * α) / l ^ 4 := by positivity
    have : 0 ≤ s ^ (2 * α) / l ^ 2 := by positivity
    linarith
  have := hQ _ (M₀ ^ 2 * δ ^ (-(2 * α))) (by positivity) hq1
  have := hQ _ (Ka ^ 2 * M₀ ^ 2) (by positivity) hq2
  have := hQ _ (KG ^ 2) (by positivity) hq3
  have := hQ _ (Mf ^ 2 * δ ^ (2 - 2 * α)) (by positivity) hq4
  linarith

end BasicElliptic
