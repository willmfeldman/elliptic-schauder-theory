/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The Campanato iteration lemma with a small multiplicative term

`BasicElliptic.campanato_iteration_eps` is Giaquinta–Martinazzi, *An Introduction to the
Regularity Theory…*, **with** the `ε` term (`campanato_iteration` is the case
`ε = 0`). Let `φ ≥ 0` be nondecreasing on `(0, R₀]` with

  `φ ρ ≤ A ((ρ / R)^a + ε) φ R + B R^b` for `0 < ρ ≤ R ≤ R₀`,

where `0 < b < a` and `A, B ≥ 0`. If `ε ≤ ε₀(A, a, b) = τ^a`, then
`φ ρ ≤ C ((ρ / R)^b φ R + B ρ^b)` with `C = C(A, a, b)`.

It is the iteration step of the `C¹ ⇒ C^{1,α}` Campanato argument for quasilinear problems
where `ε` is the oscillation of `DΦ(∇w)` on small balls.

## Proof

As for `campanato_iteration`, with `A` replaced by `2A`: put `γ = (a + b)/2` and choose `τ ∈ (0, 1)`
with `τ^{(a-b)/2} = 1/(2(2A + 1))`, so `2A τ^a ≤ τ^γ`; for `ε ≤ τ^a` the step at ratio `τ` reads
`φ(τ R) ≤ τ^γ φ R + B R^b`. With `s = τ^b`, `t = τ^γ < s`, `D = 1/(s - t)`, induction
gives `φ (τ^k R) ≤ s^k (φ R + D B R^b)`, and monotonicity interpolates between consecutive scales.

## Provenance

Adapted from `BasicElliptic.campanato_iteration` (`Campanato/Iteration.lean`); its constants
are not exposed, so the ratio and constant are redefined here.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
-/

public section

open Set

namespace BasicElliptic

/-- The ratio `τ = (2 (2A + 1))^{-2/(a-b)}` of `campanato_iteration_eps`. -/
noncomputable def iterRatioEps (A a b : ℝ) : ℝ := (2 * (2 * A + 1))⁻¹ ^ ((a - b) / 2)⁻¹

/-- The admissible size `ε₀ = τ^a` of the multiplicative term in `campanato_iteration_eps`. -/
noncomputable def iterEpsilon (A a b : ℝ) : ℝ := iterRatioEps A a b ^ a

/-- The constant of `campanato_iteration_eps`; it depends only on `A`, `a`, `b`. -/
noncomputable def iterConstEps (A a b : ℝ) : ℝ :=
  iterRatioEps A a b ^ (-b) / (iterRatioEps A a b ^ b - iterRatioEps A a b ^ ((a + b) / 2))

private theorem pow_rpow_comm'' {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ) (y : ℝ) :
    (τ ^ k) ^ y = (τ ^ y) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hτ, ← Real.rpow_mul hτ,
    mul_comm]

theorem iterEpsilon_pos {A a b : ℝ} (hA : 0 ≤ A) : 0 < iterEpsilon A a b :=
  Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by positivity) _) _

theorem iterConstEps_nonneg {A a b : ℝ} (hA : 0 ≤ A) (hab : b < a) :
    0 ≤ iterConstEps A a b := by
  have hab2 : 0 < (a - b) / 2 := by linarith
  have hc0 : 0 < (2 * (2 * A + 1))⁻¹ := by positivity
  have hc1 : (2 * (2 * A + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hτ0 : 0 < iterRatioEps A a b := Real.rpow_pos_of_pos hc0 _
  have hτ1 : iterRatioEps A a b < 1 := Real.rpow_lt_one hc0.le hc1 (inv_pos.2 hab2)
  have hts : iterRatioEps A a b ^ ((a + b) / 2) < iterRatioEps A a b ^ b :=
    Real.rpow_lt_rpow_of_exponent_gt hτ0 hτ1 (by linarith)
  exact div_nonneg (Real.rpow_nonneg hτ0.le _) (by linarith)

/-- **Iteration lemma with an `ε` term** (Giaquinta–Martinazzi). -/
theorem campanato_iteration_eps {φ : ℝ → ℝ} {A B a b ε R₀ : ℝ} (hb : 0 < b) (hab : b < a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : ε ≤ iterEpsilon A a b)
    (hmono : MonotoneOn φ (Ioc 0 R₀)) (hφ : ∀ ρ ∈ Ioc 0 R₀, 0 ≤ φ ρ)
    (hstep : ∀ ρ R, 0 < ρ → ρ ≤ R → R ≤ R₀ →
      φ ρ ≤ A * ((ρ / R) ^ a + ε) * φ R + B * R ^ b) :
    ∀ ρ R, 0 < ρ → ρ ≤ R → R ≤ R₀ →
      φ ρ ≤ iterConstEps A a b * ((ρ / R) ^ b * φ R + B * ρ ^ b) := by
  intro ρ R hρ hρR hRR₀
  have hR : 0 < R := hρ.trans_le hρR
  set τ := iterRatioEps A a b with hτdef
  set γ : ℝ := (a + b) / 2 with hγ
  have hab2 : 0 < (a - b) / 2 := by linarith
  have hc0 : 0 < (2 * (2 * A + 1))⁻¹ := by positivity
  have hc1 : (2 * (2 * A + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hc0 _
  have hτ1 : τ < 1 := Real.rpow_lt_one hc0.le hc1 (inv_pos.2 hab2)
  have hτab : τ ^ ((a - b) / 2) = (2 * (2 * A + 1))⁻¹ := Real.rpow_inv_rpow hc0.le hab2.ne'
  set s : ℝ := τ ^ b with hs
  set t : ℝ := τ ^ γ with ht
  have hs0 : 0 < s := Real.rpow_pos_of_pos hτ0 _
  have ht0 : 0 < t := Real.rpow_pos_of_pos hτ0 _
  have hts : t < s := Real.rpow_lt_rpow_of_exponent_gt hτ0 hτ1 (by rw [hγ]; linarith)
  have hAτ : A * (τ ^ a + ε) ≤ t := by
    have hεa : ε ≤ τ ^ a := hε
    have : τ ^ a = t * (2 * (2 * A + 1))⁻¹ := by
      rw [ht, ← hτab, ← Real.rpow_add hτ0, hγ]; congr 1; ring
    have h2 : A * (τ ^ a + ε) ≤ (2 * A) * τ ^ a := by nlinarith
    refine h2.trans ?_
    rw [this, ← mul_assoc, mul_comm (2 * A) t, mul_assoc]
    have : 2 * A * (2 * (2 * A + 1))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
    nlinarith
  set D : ℝ := 1 / (s - t) with hD
  have hst : 0 < s - t := by linarith
  have hs1 : s ≤ 1 := Real.rpow_le_one hτ0.le hτ1.le hb.le
  have hD1 : 1 ≤ D := by rw [hD, le_div_iff₀ hst]; linarith
  set X : ℝ := φ R + D * B * R ^ b with hX
  have hRmem : R ∈ Ioc 0 R₀ := ⟨hR, hRR₀⟩
  have hXD : D * B * R ^ b ≤ X := by have := hφ R hRmem; linarith
  have hτk : ∀ k : ℕ, τ ^ k * R ∈ Ioc 0 R₀ := fun k ↦
    ⟨by positivity, (mul_le_of_le_one_left hR.le (pow_le_one₀ hτ0.le hτ1.le)).trans hRR₀⟩
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
      rw [hq, Real.mul_rpow (pow_nonneg hτ0.le k) hR.le, pow_rpow_comm'' hτ0.le] at h
      have hφk := hφ _ hk0
      have hsk : 0 ≤ s ^ k := pow_nonneg hs0.le k
      calc φ (τ ^ (k + 1) * R)
          ≤ A * (τ ^ a + ε) * φ (τ ^ k * R) + B * (s ^ k * R ^ b) := h
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
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one (div_pos hρ hR)
    ((div_le_one hR).2 hρR) hτ0 hτ1
  have hρk : ρ ≤ τ ^ k * R := by rwa [div_le_iff₀ hR] at hk2
  have h1 : φ ρ ≤ s ^ k * X :=
    (hmono ⟨hρ, hρR.trans hRR₀⟩ (hτk k) hρk).trans (hgeom k)
  have hX0 : 0 ≤ X := le_trans (by positivity) hXD
  have h2 : s ^ k ≤ τ ^ (-b) * (ρ / R) ^ b := by
    have h3 : s ^ (k + 1) ≤ (ρ / R) ^ b := by
      rw [hs, ← pow_rpow_comm'' hτ0.le]
      exact Real.rpow_le_rpow (by positivity) hk1.le hb.le
    have h4 : τ ^ (-b) * s = 1 := by
      rw [hs, Real.rpow_neg hτ0.le, inv_mul_cancel₀ hs0.ne']
    calc s ^ k = τ ^ (-b) * s ^ (k + 1) := by rw [pow_succ, ← mul_assoc, mul_comm _ (s ^ k),
          mul_assoc, h4, mul_one]
      _ ≤ τ ^ (-b) * (ρ / R) ^ b :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hτ0.le _)
  have hρRb : (ρ / R) ^ b * R ^ b = ρ ^ b := by
    rw [← Real.mul_rpow (by positivity) hR.le, div_mul_cancel₀ _ hR.ne']
  have hxb : 0 ≤ (ρ / R) ^ b := Real.rpow_nonneg (by positivity) _
  have hφR := hφ R hRmem
  calc φ ρ ≤ τ ^ (-b) * (ρ / R) ^ b * X := h1.trans (mul_le_mul_of_nonneg_right h2 hX0)
    _ = τ ^ (-b) * ((ρ / R) ^ b * φ R + D * (B * ρ ^ b)) := by
        rw [hX, ← hρRb]; ring
    _ ≤ τ ^ (-b) * (D * ((ρ / R) ^ b * φ R) + D * (B * ρ ^ b)) := by
        have := le_mul_of_one_le_left (mul_nonneg hxb hφR) hD1
        gcongr
    _ = iterConstEps A a b * ((ρ / R) ^ b * φ R + B * ρ ^ b) := by
        rw [iterConstEps, ← hτdef, hD, ← hs, ← hγ, ← ht]; ring

end BasicElliptic
