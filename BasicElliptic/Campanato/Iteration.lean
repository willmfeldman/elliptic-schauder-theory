/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The Campanato iteration lemma

`BasicElliptic.campanato_iteration` is Giaquinta–Martinazzi, *An Introduction to the Regularity
Theory for Elliptic Systems…*, in the form with `ε = 0` (the smallness of the
coefficients is kept in `B`). Let `φ ≥ 0` be nondecreasing on `(0, R₀]` with

  `φ ρ ≤ A (ρ / R)^a φ R + B R^b` for `0 < ρ ≤ R ≤ R₀`,

where `0 < b < a`, `A, B ≥ 0`. Then `φ ρ ≤ C ((ρ / R)^b φ R + B ρ^b)` with `C = C(A, a, b)`.

## Proof

Put `γ = (a + b) / 2` and choose `τ ∈ (0, 1)` with `τ^{(a - b)/2} = 1 / (2 (A + 1))`, so
`A τ^a ≤ τ^γ`. With `s = τ^b`, `t = τ^γ < s` and `D = 1 / (s - t)`, induction gives
`φ (τ^k R) ≤ s^k (φ R + D B R^b)`. For `τ^{k+1} R < ρ ≤ τ^k R`, monotonicity and
`s^k ≤ τ^{-b} (ρ / R)^b` conclude.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
-/

public section

open Set

namespace BasicElliptic

/-- The ratio `τ = (2 (A + 1))^{-2/(a-b)}` of the geometric radii in `campanato_iteration`. -/
noncomputable def iterRatio (A a b : ℝ) : ℝ := (2 * (A + 1))⁻¹ ^ ((a - b) / 2)⁻¹

/-- The constant of the iteration lemma `campanato_iteration`; it depends only on `A`, `a`, `b`. -/
noncomputable def iterConst (A a b : ℝ) : ℝ :=
  iterRatio A a b ^ (-b) / (iterRatio A a b ^ b - iterRatio A a b ^ ((a + b) / 2))

theorem iterRatio_pos {A : ℝ} (a b : ℝ) (hA : 0 ≤ A) : 0 < iterRatio A a b :=
  Real.rpow_pos_of_pos (inv_pos.2 (by linarith)) _

theorem iterRatio_lt_one {A a b : ℝ} (hA : 0 ≤ A) (hab : b < a) : iterRatio A a b < 1 :=
  Real.rpow_lt_one (inv_pos.2 (by linarith)).le (inv_lt_one_of_one_lt₀ (by linarith))
    (inv_pos.2 (by linarith))

theorem iterConst_pos {A a b : ℝ} (hA : 0 ≤ A) (hab : b < a) : 0 < iterConst A a b := by
  have hτ0 := iterRatio_pos a b hA
  have hts : iterRatio A a b ^ ((a + b) / 2) < iterRatio A a b ^ b :=
    Real.rpow_lt_rpow_of_exponent_gt hτ0 (iterRatio_lt_one hA hab) (by linarith)
  exact div_pos (Real.rpow_pos_of_pos hτ0 _) (sub_pos.2 hts)

theorem iterConst_nonneg {A a b : ℝ} (hA : 0 ≤ A) (hab : b < a) : 0 ≤ iterConst A a b :=
  (iterConst_pos hA hab).le

private theorem pow_rpow_comm' {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ) (y : ℝ) :
    (τ ^ k) ^ y = (τ ^ y) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hτ, ← Real.rpow_mul hτ,
    mul_comm]

/-- **Iteration lemma** (Giaquinta–Martinazzi, with `ε = 0`). -/
theorem campanato_iteration {φ : ℝ → ℝ} {A B a b R₀ : ℝ} (hb : 0 < b) (hab : b < a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hmono : MonotoneOn φ (Ioc 0 R₀))
    (hφ : ∀ ρ ∈ Ioc 0 R₀, 0 ≤ φ ρ)
    (hstep : ∀ ρ R, 0 < ρ → ρ ≤ R → R ≤ R₀ → φ ρ ≤ A * (ρ / R) ^ a * φ R + B * R ^ b) :
    ∀ ρ R, 0 < ρ → ρ ≤ R → R ≤ R₀ →
      φ ρ ≤ iterConst A a b * ((ρ / R) ^ b * φ R + B * ρ ^ b) := by
  intro ρ R hρ hρR hRR₀
  have hR : 0 < R := hρ.trans_le hρR
  set τ := iterRatio A a b with hτdef
  set γ : ℝ := (a + b) / 2 with hγ
  have hab2 : 0 < (a - b) / 2 := by linarith
  have hc0 : 0 < (2 * (A + 1))⁻¹ := by positivity
  have hc1 : (2 * (A + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hc0 _
  have hτ1 : τ < 1 := Real.rpow_lt_one hc0.le hc1 (inv_pos.2 hab2)
  have hτab : τ ^ ((a - b) / 2) = (2 * (A + 1))⁻¹ := Real.rpow_inv_rpow hc0.le hab2.ne'
  set s : ℝ := τ ^ b with hs
  set t : ℝ := τ ^ γ with ht
  have hs0 : 0 < s := Real.rpow_pos_of_pos hτ0 _
  have hs1 : s ≤ 1 := Real.rpow_le_one hτ0.le hτ1.le hb.le
  have ht0 : 0 < t := Real.rpow_pos_of_pos hτ0 _
  have hts : t < s := Real.rpow_lt_rpow_of_exponent_gt hτ0 hτ1 (by rw [hγ]; linarith)
  have hAτ : A * τ ^ a ≤ t := by
    have : τ ^ a = t * (2 * (A + 1))⁻¹ := by
      rw [ht, ← hτab, ← Real.rpow_add hτ0, hγ]; congr 1; ring
    rw [this, ← mul_assoc, mul_comm A t, mul_assoc]
    have : A * (2 * (A + 1))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
    nlinarith
  set D : ℝ := 1 / (s - t) with hD
  have hst : 0 < s - t := by linarith
  have hD1 : 1 ≤ D := by rw [hD, le_div_iff₀ hst]; linarith
  set X : ℝ := φ R + D * B * R ^ b with hX
  have hRmem : R ∈ Ioc 0 R₀ := ⟨hR, hRR₀⟩
  have hRb : 0 ≤ R ^ b := Real.rpow_nonneg hR.le _
  have hXD : D * B * R ^ b ≤ X := by have := hφ R hRmem; linarith
  have hτk : ∀ k : ℕ, τ ^ k * R ∈ Ioc 0 R₀ := fun k ↦
    ⟨by positivity, (mul_le_of_le_one_left hR.le (pow_le_one₀ hτ0.le hτ1.le)).trans hRR₀⟩
  -- the geometric decay along `τ^k R`
  have hgeom : ∀ k : ℕ, φ (τ ^ k * R) ≤ s ^ k * X := by
    intro k
    induction k with
    | zero =>
      have : 0 ≤ D * B * R ^ b := by have := hst.le; positivity
      simp only [pow_zero, one_mul, hX]
      linarith
    | succ k ih =>
      have hk0 := hτk k
      have h := hstep (τ ^ (k + 1) * R) (τ ^ k * R) (hτk (k + 1)).1
        (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hτ0.le hτ1.le k.le_succ) hR.le)
        hk0.2
      have hq : τ ^ (k + 1) * R / (τ ^ k * R) = τ := by
        field_simp; ring
      rw [hq, Real.mul_rpow (pow_nonneg hτ0.le k) hR.le, pow_rpow_comm' hτ0.le] at h
      have hφk := hφ _ hk0
      have hsk : 0 ≤ s ^ k := pow_nonneg hs0.le k
      calc φ (τ ^ (k + 1) * R)
          ≤ A * τ ^ a * φ (τ ^ k * R) + B * (s ^ k * R ^ b) := h
        _ ≤ t * (s ^ k * X) + B * (s ^ k * R ^ b) := by
            have := (mul_le_mul_of_nonneg_right hAτ hφk).trans
              (mul_le_mul_of_nonneg_left ih ht0.le)
            linarith
        _ = s ^ k * (t * X + B * R ^ b) := by ring
        _ ≤ s ^ k * (s * X) := by
            apply mul_le_mul_of_nonneg_left _ hsk
            have : B * R ^ b ≤ (s - t) * X := by
              have h' := mul_le_mul_of_nonneg_left hXD hst.le
              rw [hD] at h'
              field_simp at h'
              linarith
            linarith
        _ = s ^ (k + 1) * X := by ring
  -- interpolate between consecutive scales
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one (div_pos hρ hR)
    ((div_le_one hR).2 hρR) hτ0 hτ1
  have hρk : ρ ≤ τ ^ k * R := by rwa [div_le_iff₀ hR] at hk2
  have h1 : φ ρ ≤ s ^ k * X :=
    (hmono ⟨hρ, hρR.trans hRR₀⟩ (hτk k) hρk).trans (hgeom k)
  have hX0 : 0 ≤ X := le_trans (by positivity) hXD
  have h2 : s ^ k ≤ τ ^ (-b) * (ρ / R) ^ b := by
    have h3 : s ^ (k + 1) ≤ (ρ / R) ^ b := by
      rw [hs, ← pow_rpow_comm' hτ0.le]
      exact Real.rpow_le_rpow (by positivity) hk1.le hb.le
    have h4 : τ ^ (-b) * s = 1 := by
      rw [hs, Real.rpow_neg hτ0.le, inv_mul_cancel₀ hs0.ne']
    calc s ^ k = τ ^ (-b) * s ^ (k + 1) := by rw [pow_succ, ← mul_assoc, mul_comm _ (s ^ k),
          mul_assoc, h4, mul_one]
      _ ≤ τ ^ (-b) * (ρ / R) ^ b :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hτ0.le _)
  have hρRb : (ρ / R) ^ b * R ^ b = ρ ^ b := by
    rw [← Real.mul_rpow (by positivity) hR.le, div_mul_cancel₀ _ hR.ne']
  have hτb : 0 ≤ τ ^ (-b) := Real.rpow_nonneg hτ0.le _
  have hxb : 0 ≤ (ρ / R) ^ b := Real.rpow_nonneg (by positivity) _
  have hφR := hφ R hRmem
  calc φ ρ ≤ τ ^ (-b) * (ρ / R) ^ b * X := h1.trans (mul_le_mul_of_nonneg_right h2 hX0)
    _ = τ ^ (-b) * ((ρ / R) ^ b * φ R + D * (B * ρ ^ b)) := by
        rw [hX, ← hρRb]; ring
    _ ≤ τ ^ (-b) * (D * ((ρ / R) ^ b * φ R) + D * (B * ρ ^ b)) := by
        have := le_mul_of_one_le_left (mul_nonneg hxb hφR) hD1
        gcongr
    _ = iterConst A a b * ((ρ / R) ^ b * φ R + B * ρ ^ b) := by
        rw [iterConst, ← hτdef, hD, ← hs, ← hγ, ← ht]; ring

end BasicElliptic
