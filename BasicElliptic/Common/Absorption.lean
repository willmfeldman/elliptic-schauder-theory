/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The absorption lemma

`BasicElliptic.le_of_absorption` is the "hole filling" absorption lemma (Simon 1997, *Schauder
estimates by scaling*, and Giaquinta–Martinazzi; see References). If `Q ≥ 0` is bounded
on `[r/2, r]` and

  `Q ρ ≤ θ Q ρ' + A (ρ' - ρ)^{-γ} + B` for `r/2 ≤ ρ < ρ' ≤ r`,

with `0 ≤ θ < 1`, `γ > 0` and `A, B ≥ 0`, then `Q (r/2) ≤ C(θ, γ) (A r^{-γ} + B)`.

The boundedness of `Q` is a hypothesis: in applications it is discharged by a
qualitative first pass.

## Proof

Take the radii `ρ_k = r - (r/2) τ^k`, where `τ^γ = (1 + θ)/2`. Then
`ρ_{k+1} - ρ_k = (1 - τ) τ^k r / 2`, and iterating the hypothesis `k` times gives
`Q ρ_0 ≤ θ^k Q ρ_k + (A W + B) (1 - q^k) / (1 - q)` with `q = θ τ^{-γ} < 1` and
`W = ((1 - τ) r / 2)^{-γ}`. Let `k → ∞`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
* L. Simon, *Schauder estimates by scaling*, Calc. Var. Partial Differential Equations 5 (1997),
  391–407.
-/

public section

open Filter Topology Set

namespace BasicElliptic

/-- The ratio `τ = ((1 + θ) / 2)^{1/γ}` of the geometric radii in `le_of_absorption`. -/
noncomputable def absorbRatio (θ γ : ℝ) : ℝ := ((1 + θ) / 2) ^ γ⁻¹

/-- The constant of the absorption lemma `le_of_absorption`; it depends only on `θ` and `γ`. -/
noncomputable def absorbConst (θ γ : ℝ) : ℝ :=
  (((1 - absorbRatio θ γ) / 2) ^ (-γ) + 1) / (1 - 2 * θ / (1 + θ))

private theorem pow_rpow_comm {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ) (y : ℝ) :
    (τ ^ k) ^ y = (τ ^ y) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hτ, ← Real.rpow_mul hτ,
    mul_comm]

/-- **Absorption lemma** (Simon; Giaquinta–Martinazzi). -/
theorem le_of_absorption {Q : ℝ → ℝ} {r θ γ A B : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hγ : 0 < γ)
    (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hQ : ∀ ρ ρ', r / 2 ≤ ρ → ρ < ρ' → ρ' ≤ r → Q ρ ≤ θ * Q ρ' + A * (ρ' - ρ) ^ (-γ) + B)
    (hbdd : BddAbove (Q '' Icc (r / 2) r)) (hnn : ∀ ρ ∈ Icc (r / 2) r, 0 ≤ Q ρ) :
    Q (r / 2) ≤ absorbConst θ γ * (A * r ^ (-γ) + B) := by
  set t : ℝ := (1 + θ) / 2 with ht
  set τ : ℝ := absorbRatio θ γ with hτdef
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht]; linarith
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos ht0 _
  have hτ1 : τ < 1 := Real.rpow_lt_one ht0.le ht1 (inv_pos.2 hγ)
  have hτγ : τ ^ γ = t := Real.rpow_inv_rpow ht0.le hγ.ne'
  -- the ratio `q = θ τ^{-γ} = 2θ / (1 + θ) < 1`
  set q : ℝ := 2 * θ / (1 + θ) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  have hτnγ : τ ^ (-γ) = t⁻¹ := by rw [Real.rpow_neg hτ0.le, hτγ]
  have hθq : θ * t⁻¹ = q := by rw [hq, ht]; field_simp
  have htinv : 1 ≤ t⁻¹ := one_le_inv_iff₀.2 ⟨ht0, ht1.le⟩
  -- radii
  set ρ : ℕ → ℝ := fun k ↦ r - r / 2 * τ ^ k with hρ
  have hτk1 : ∀ k : ℕ, τ ^ k ≤ 1 := fun k ↦ pow_le_one₀ hτ0.le hτ1.le
  have hρmem : ∀ k, ρ k ∈ Icc (r / 2) r := fun k ↦ by
    have := hτk1 k
    have : 0 < τ ^ k := pow_pos hτ0 k
    constructor <;> simp only [hρ] <;> nlinarith
  have hρ0 : ρ 0 = r / 2 := by simp only [hρ, pow_zero]; ring
  have hdiff : ∀ k, ρ (k + 1) - ρ k = (1 - τ) * r / 2 * τ ^ k := fun k ↦ by
    simp only [hρ, pow_succ]; ring
  set W : ℝ := ((1 - τ) * r / 2) ^ (-γ) with hW
  have hW0 : 0 ≤ W := Real.rpow_nonneg (by nlinarith) _
  have hWr : W = ((1 - τ) / 2) ^ (-γ) * r ^ (-γ) := by
    rw [hW, show (1 - τ) * r / 2 = (1 - τ) / 2 * r by ring,
      Real.mul_rpow (by linarith) hr.le]
  have hstep : ∀ k, Q (ρ k) ≤ θ * Q (ρ (k + 1)) + A * W * t⁻¹ ^ k + B := fun k ↦ by
    have hlt : ρ k < ρ (k + 1) := by
      have := hdiff k
      have : 0 < (1 - τ) * r / 2 * τ ^ k := by
        have := pow_pos hτ0 k
        have : 0 < 1 - τ := by linarith
        positivity
      linarith
    have h := hQ (ρ k) (ρ (k + 1)) (hρmem k).1 hlt (hρmem (k + 1)).2
    rw [hdiff, Real.mul_rpow (by nlinarith) (pow_nonneg hτ0.le k), pow_rpow_comm hτ0.le,
      hτnγ, ← hW] at h
    linarith
  -- the iterated inequality
  set K : ℝ := A * W + B with hK
  have hK0 : 0 ≤ K := by positivity
  have hiter : ∀ k : ℕ, Q (r / 2) ≤ θ ^ k * Q (ρ k) + K * (1 - q ^ k) / (1 - q) := by
    intro k
    induction k with
    | zero => simp [hρ0]
    | succ k ih =>
      have hs := hstep k
      have hθk : 0 ≤ θ ^ k := pow_nonneg hθ0 k
      have hqk : θ ^ k * t⁻¹ ^ k = q ^ k := by rw [← mul_pow, hθq]
      have hθkq : θ ^ k ≤ q ^ k := by
        rw [← hqk]; exact le_mul_of_one_le_right hθk (one_le_pow₀ htinv)
      have h1 : θ ^ k * Q (ρ k) ≤ θ ^ (k + 1) * Q (ρ (k + 1)) + K * q ^ k := by
        calc θ ^ k * Q (ρ k) ≤ θ ^ k * (θ * Q (ρ (k + 1)) + A * W * t⁻¹ ^ k + B) :=
              mul_le_mul_of_nonneg_left hs hθk
          _ = θ ^ (k + 1) * Q (ρ (k + 1)) + A * W * q ^ k + θ ^ k * B := by
              rw [← hqk]; ring
          _ ≤ θ ^ (k + 1) * Q (ρ (k + 1)) + K * q ^ k := by
              rw [hK]; nlinarith [mul_le_mul_of_nonneg_left hθkq hB]
      have h2 : K * (1 - q ^ k) / (1 - q) + K * q ^ k = K * (1 - q ^ (k + 1)) / (1 - q) := by
        field_simp [(by linarith : (1 - q) ≠ 0)]
        ring
      linarith
  -- pass to the limit
  obtain ⟨U, hU⟩ := hbdd
  have hQU : ∀ k, Q (ρ k) ≤ U := fun k ↦ hU ⟨ρ k, hρmem k, rfl⟩
  have hQ0 : ∀ k, 0 ≤ Q (ρ k) := fun k ↦ hnn _ (hρmem k)
  have hbound : ∀ k : ℕ, Q (r / 2) ≤ θ ^ k * U + K / (1 - q) := by
    intro k
    have h := hiter k
    have hθk : 0 ≤ θ ^ k := pow_nonneg hθ0 k
    have : K * (1 - q ^ k) / (1 - q) ≤ K / (1 - q) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      have := pow_nonneg hq0 k
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (hQU k) hθk]
  have hlim : Tendsto (fun k : ℕ ↦ θ ^ k * U + K / (1 - q)) atTop (𝓝 (0 * U + K / (1 - q))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).mul_const U).add_const _
  have hfin : Q (r / 2) ≤ K / (1 - q) := by
    simpa using ge_of_tendsto' hlim hbound
  refine hfin.trans ?_
  rw [absorbConst, ← hτdef, ← hq, hK, hWr, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have hc0 : 0 ≤ ((1 - τ) / 2) ^ (-γ) := Real.rpow_nonneg (by linarith) _
  have hr0 : 0 ≤ r ^ (-γ) := Real.rpow_nonneg hr.le _
  nlinarith [mul_nonneg hA hr0, mul_nonneg hc0 hB]

/-- `absorbConst θ γ ≥ 1` for `0 ≤ θ < 1`, `γ > 0` (apply the absorption lemma to `Q ≡ 1`). -/
theorem one_le_absorbConst {θ γ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hγ : 0 < γ) :
    1 ≤ absorbConst θ γ := by
  have h := le_of_absorption (Q := fun _ ↦ (1 : ℝ)) (r := 1) (θ := θ) (A := 0) (B := 1)
    hθ0 hθ hγ one_pos le_rfl zero_le_one
    (fun _ _ _ _ _ ↦ by simp only [mul_one, zero_mul, add_zero]; linarith)
    ⟨1, by rintro _ ⟨_, _, rfl⟩; exact le_rfl⟩ (fun _ _ ↦ zero_le_one)
  simpa using h

/-- Absorption on `[s, T]` (shift of `le_of_absorption` from `[r/2, r]`, `r = 2 (T - s)`). -/
theorem le_of_absorption_shift {Q : ℝ → ℝ} {s T θ γ A B : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hγ : 0 < γ) (hsT : s < T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hQ : ∀ ρ ρ', s ≤ ρ → ρ < ρ' → ρ' ≤ T → Q ρ ≤ θ * Q ρ' + A * (ρ' - ρ) ^ (-γ) + B)
    (hbdd : BddAbove (Q '' Icc s T)) (hnn : ∀ ρ ∈ Icc s T, 0 ≤ Q ρ) :
    Q s ≤ absorbConst θ γ * (A * (2 * (T - s)) ^ (-γ) + B) := by
  have h := le_of_absorption (Q := fun t ↦ Q (t + 2 * s - T)) (r := 2 * (T - s)) hθ0 hθ hγ
    (by linarith) hA hB
    (fun ρ ρ' h1 h2 h3 ↦ by
      have := hQ (ρ + 2 * s - T) (ρ' + 2 * s - T) (by linarith) (by linarith) (by linarith)
      simpa only [show ρ' + 2 * s - T - (ρ + 2 * s - T) = ρ' - ρ by ring] using this)
    (by
      obtain ⟨M, hM⟩ := hbdd
      exact ⟨M, by
        rintro _ ⟨t, ht, rfl⟩
        exact hM ⟨t + 2 * s - T, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩⟩)
    (fun ρ hρ ↦ hnn _ ⟨by linarith [hρ.1], by linarith [hρ.2]⟩)
  simpa only [show 2 * (T - s) / 2 + 2 * s - T = s by ring] using h

end BasicElliptic
