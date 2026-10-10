/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Interior.Iterate
public import BasicElliptic.Normalize.ChangeOfVariables
public import BasicElliptic.Defs.Elliptic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Freezing the coefficients: the pointwise expansion of a nondivergence solution

Let `w ∈ C²(U)` solve `tr (a D²w) + ⟪b, ∇w⟫ = f` on the open set `U` (`Nondiv.IsSolOn`), and fix
`x₀` with
`closedBall x₀ R ⊆ U`. With `a₀ = a(x₀)`,
```
tr (a₀ D²w) = g,   g(y) := f(y) − ⟪b(y), ∇w(y)⟫ − tr ((a(y) − a₀) D²w(y)).
```
Given bounds `‖D²w‖ ≤ M₂` on `B_R(x₀)` and `‖Dw(x₀)‖ ≤ M₁`, the right-hand side `g` is Hölder **at
`x₀`** (only): `|g(y) − g(x₀)| ≤ H₀ |y − x₀|^α` (`Nondiv.abs_frozenRHS_sub_le`), with
`H₀ = [f] + [b] (M₁ + M₂ R) + ‖b(x₀)‖ M₂ R^{1−α} + d [a] M₂`. The `C²` hypothesis enters only
through the bound `M₂`, which the caller proves finite on a compact ball.

The normalization `T z = x₀ + M z` with `M M† = sym a₀` (`exists_sqrt_symPart`) turns
`tr (a₀ D²)` into the Laplacian (`Nondiv.laplacian_comp_affine_eq_frozen`; the skew part of `a₀`
drops out since `D²w` is symmetric), and `Nondiv.expansion_of_laplacian` gives

* `Nondiv.expansion_at_point`: a quadratic `P` with
  `|w(y) − P(y − x₀)| ≤ C N (|y − x₀| / R)^{2+α}` for `|y − x₀| < κ R`, and
  `R ‖DP(0)‖ + R² ‖quad P‖ ≤ C N`, where
  `N = M₀ + R² (M_f + M_b M₁) + R^{2+α} H₀`, `M₀ ≥ sup_{B_R(x₀)} |w − w(x₀)|`, and
  `C, κ > 0` depend only on `E, α, lam, Λ`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001. (GT)

## Provenance

The pointwise-Hölder freezing is the elliptic counterpart of the source normalization (N₂) of
parabolic-basic-theory, `ParabolicBasic/Schauder/Iteration/Interior.lean` (own repository, commit
`2507d9a800377e91c591862286b2ba2d6464d918`), where the heat operator has constant coefficients;
the variable-coefficient freezing follows GT (the constant-coefficient case).
-/

public section

open Metric Set Filter Topology Module InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Traces against the Hessian -/

/-- `∑ᵢ B (K eᵢ) eᵢ = 0` for a symmetric bilinear `B` and a skew `K`. -/
theorem sum_apply_skew_eq_zero (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v v', B v v' = B v' v)
    (K : E →L[ℝ] E) (hK : adjoint K = -K) :
    ∑ i, B (K (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = 0 := by
  set e := stdOrthonormalBasis ℝ E
  have hexp : ∀ i, B (K (e i)) (e i) = ∑ j, ⟪e j, K (e i)⟫ * B (e j) (e i) := fun i ↦ by
    conv_lhs => rw [← e.sum_repr' (K (e i))]
    simp [map_sum, map_smul]
  have hskew : ∀ i j, ⟪e j, K (e i)⟫ = -⟪e i, K (e j)⟫ := fun i j ↦ by
    rw [← adjoint_inner_left, hK, neg_apply, inner_neg_left, real_inner_comm]
  have hS : ∑ i, B (K (e i)) (e i) = -∑ i, B (K (e i)) (e i) := by
    calc ∑ i, B (K (e i)) (e i) = ∑ i, ∑ j, ⟪e j, K (e i)⟫ * B (e j) (e i) :=
          Finset.sum_congr rfl fun i _ ↦ hexp i
      _ = ∑ j, ∑ i, ⟪e j, K (e i)⟫ * B (e j) (e i) := Finset.sum_comm
      _ = ∑ j, ∑ i, -(⟪e i, K (e j)⟫ * B (e i) (e j)) :=
          Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by
            rw [hskew i j, hB]; ring
      _ = -∑ j, ∑ i, ⟪e i, K (e j)⟫ * B (e i) (e j) := by simp [Finset.sum_neg_distrib]
      _ = -∑ i, B (K (e i)) (e i) := by
          congr 1; exact (Finset.sum_congr rfl fun i _ ↦ hexp i).symm
  linarith

/-- `|∑ᵢ B (A eᵢ) eᵢ| ≤ dim E · ‖B‖ ‖A‖`. -/
theorem abs_sum_apply_le (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    |∑ i, B (A (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i)| ≤
      finrank ℝ E * (‖B‖ * ‖A‖) := by
  set e := stdOrthonormalBasis ℝ E
  have h1 : ∀ i, |B (A (e i)) (e i)| ≤ ‖B‖ * ‖A‖ := fun i ↦ by
    have hn : ‖e i‖ = 1 := e.orthonormal.1 i
    rw [← Real.norm_eq_abs]
    calc ‖B (A (e i)) (e i)‖ ≤ ‖B‖ * ‖A (e i)‖ * ‖e i‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * (‖A‖ * ‖e i‖) * ‖e i‖ := by gcongr; exact A.le_opNorm _
      _ = ‖B‖ * ‖A‖ := by rw [hn]; ring
  calc |∑ i, B (A (e i)) (e i)| ≤ ∑ i, |B (A (e i)) (e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (finrank ℝ E), ‖B‖ * ‖A‖ := Finset.sum_le_sum fun i _ ↦ h1 i
    _ = finrank ℝ E * (‖B‖ * ‖A‖) := by simp

omit [FiniteDimensional ℝ E] in
/-- The second derivative of a function `C²` at a point is symmetric. -/
theorem fderiv_fderiv_comm {w : E → ℝ} {y : E} (hw : ContDiffAt ℝ 2 w y) (v v' : E) :
    fderiv ℝ (fderiv ℝ w) y v v' = fderiv ℝ (fderiv ℝ w) y v' v :=
  ContDiffAt.isSymmSndFDerivAt hw (by simp) v v'

omit [FiniteDimensional ℝ E] in
theorem iteratedFDerivWithin_two_apply_of_isOpen {w : E → ℝ} {U : Set E} (hU : IsOpen U)
    {y : E} (hy : y ∈ U) (v v' : E) :
    iteratedFDerivWithin ℝ 2 w U y ![v, v'] = fderiv ℝ (fderiv ℝ w) y v v' := by
  rw [iteratedFDerivWithin_of_isOpen 2 hU hy, iteratedFDeriv_two_apply]
  simp

omit [FiniteDimensional ℝ E] in
theorem norm_fderiv_fderiv_eq (w : E → ℝ) (y : E) :
    ‖fderiv ℝ (fderiv ℝ w) y‖ = ‖iteratedFDeriv ℝ 2 w y‖ := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]

theorem inner_gradientWithin_of_isOpen {w : E → ℝ} {U : Set E} (hU : IsOpen U) {y : E}
    (hy : y ∈ U) (v : E) : ⟪v, gradientWithin w U y⟫ = fderiv ℝ w y v := by
  rw [gradientWithin, fderivWithin_of_isOpen hU hy, real_inner_comm, toDual_symm_apply]

/-! ### The Laplacian of the normalized function -/

/-- **Normalization of the frozen operator.** If `M⁻¹ a₀ M⁻† = I + K` with `K` skew and
`T z = x₀ + M z ∈ U` (`U` open, `w ∈ C²(U)`), then
`Δ (w ∘ T)(z) = ∑ᵢ D²w(T z)(a₀ eᵢ, eᵢ) = tr (a₀ D²w(T z))`. -/
theorem laplacian_comp_affine_eq_frozen {U : Set E} (hU : IsOpen U) {w : E → ℝ}
    (hw : ContDiffOn ℝ 2 w U) (a₀ : E →L[ℝ] E) (M : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (hconj : (M.symm : E →L[ℝ] E) ∘L a₀ ∘L adjoint (M.symm : E →L[ℝ] E) = 1 + K)
    (hK : adjoint K = -K) (x₀ : E) {z : E} (hz : x₀ + M z ∈ U) :
    Δ (fun z ↦ w (x₀ + M z)) z =
      ∑ i, fderiv ℝ (fderiv ℝ w) (x₀ + M z) (a₀ (stdOrthonormalBasis ℝ E i))
        (stdOrthonormalBasis ℝ E i) := by
  set e := stdOrthonormalBasis ℝ E
  have hT : Continuous fun z ↦ x₀ + M z := continuous_const.add M.continuous
  have hV : IsOpen ((fun z ↦ x₀ + M z) ⁻¹' U) := hU.preimage hT
  have hzV : z ∈ (fun z ↦ x₀ + M z) ⁻¹' U := hz
  have key := Nondiv.op_comp_affine (a := fun _ ↦ a₀) (b := fun _ ↦ (0 : E))
    (hw.differentiableOn (by norm_num)) hU.uniqueDiffOn M x₀ hz
  simp only [Nondiv.op, map_zero, inner_zero_left, add_zero, hconj] at key
  simp only [iteratedFDerivWithin_two_apply_of_isOpen hV hzV,
    iteratedFDerivWithin_two_apply_of_isOpen hU hz] at key
  rw [← key, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- `w ∘ T` is `C²` at `z`
  have hwT : ContDiffAt ℝ 2 (fun z ↦ w (x₀ + M z)) z :=
    (hw.contDiffAt (hU.mem_nhds hz)).comp z (contDiff_const.add M.contDiff).contDiffAt
  set B := fderiv ℝ (fderiv ℝ fun z ↦ w (x₀ + M z)) z
  have hsplit : ∀ i, B ((1 + K) (e i)) (e i) = B (e i) (e i) + B (K (e i)) (e i) := fun i ↦ by
    rw [add_apply, one_apply_eq_self, map_add, add_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib,
    sum_apply_skew_eq_zero B (fderiv_fderiv_comm hwT) K hK, add_zero]

/-! ### The frozen right-hand side is Hölder at the base point -/

/-- **The frozen right-hand side.** For a solution of `tr (a D²w) + ⟪b, ∇w⟫ = f` on the open set
`U`, the function `g(y) = tr (a(x₀) D²w(y))` satisfies `|g(y) − g(x₀)| ≤ H₀ |y − x₀|^α` on
`B_R(x₀) ⊆ U`, with `H₀ = K_f + K_b (M₁ + M₂ R) + M_b M₂ R^{1−α} + d K_a M₂`, and
`|g(x₀)| ≤ M_f + M_b M₁`. Only Hölder continuity **at `x₀`** of `a, b, f` is used. -/
theorem abs_frozenRHS_sub_le {U : Set E} (hU : IsOpen U) {a : E → E →L[ℝ] E} {b : E → E}
    {f w : E → ℝ} (hsol : IsSolOn a b f U w) {x₀ : E} {R α M₁ M₂ Mb Mf Ka Kb Kf : ℝ}
    (hα : 0 < α ∧ α < 1) (hR : 0 < R) (hBU : ball x₀ R ⊆ U)
    (ha : ∀ y ∈ ball x₀ R, ‖a y - a x₀‖ ≤ Ka * dist y x₀ ^ α)
    (hb : ∀ y ∈ ball x₀ R, ‖b y - b x₀‖ ≤ Kb * dist y x₀ ^ α)
    (hf : ∀ y ∈ ball x₀ R, |f y - f x₀| ≤ Kf * dist y x₀ ^ α)
    (hbx : ‖b x₀‖ ≤ Mb) (hfx : |f x₀| ≤ Mf)
    (hM₁ : ‖fderiv ℝ w x₀‖ ≤ M₁) (hM₂ : ∀ y ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 w y‖ ≤ M₂) :
    (∀ y ∈ ball x₀ R,
      |∑ i, fderiv ℝ (fderiv ℝ w) y (a x₀ (stdOrthonormalBasis ℝ E i))
          (stdOrthonormalBasis ℝ E i) -
        ∑ i, fderiv ℝ (fderiv ℝ w) x₀ (a x₀ (stdOrthonormalBasis ℝ E i))
          (stdOrthonormalBasis ℝ E i)| ≤
        (Kf + Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - α) + finrank ℝ E * Ka * M₂) *
          dist y x₀ ^ α) ∧
    |∑ i, fderiv ℝ (fderiv ℝ w) x₀ (a x₀ (stdOrthonormalBasis ℝ E i))
        (stdOrthonormalBasis ℝ E i)| ≤ Mf + Mb * M₁ := by
  set e := stdOrthonormalBasis ℝ E
  have hx₀ : x₀ ∈ ball x₀ R := mem_ball_self hR
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ x₀ hx₀)
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans hbx
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans hM₁
  -- the equation, in fderiv form
  have heq : ∀ y ∈ ball x₀ R, ∑ i, fderiv ℝ (fderiv ℝ w) y (a x₀ (e i)) (e i) =
      f y - fderiv ℝ w y (b y) - ∑ i, fderiv ℝ (fderiv ℝ w) y ((a y - a x₀) (e i)) (e i) := by
    intro y hy
    have h := hsol.2 y (hBU hy)
    simp only [Nondiv.op, iteratedFDerivWithin_two_apply_of_isOpen hU (hBU hy),
      inner_gradientWithin_of_isOpen hU (hBU hy)] at h
    have hs : ∀ i, fderiv ℝ (fderiv ℝ w) y (a y (e i)) (e i) =
        fderiv ℝ (fderiv ℝ w) y (a x₀ (e i)) (e i) +
          fderiv ℝ (fderiv ℝ w) y ((a y - a x₀) (e i)) (e i) := fun i ↦ by
      rw [← add_apply, ← map_add, ← add_apply, add_sub_cancel]
    rw [Finset.sum_congr rfl fun i _ ↦ hs i, Finset.sum_add_distrib] at h
    linarith
  have hB : ∀ y ∈ ball x₀ R, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M₂ := fun y hy ↦ by
    rw [norm_fderiv_fderiv_eq]; exact hM₂ y hy
  have hgx : ∑ i, fderiv ℝ (fderiv ℝ w) x₀ (a x₀ (e i)) (e i) = f x₀ - fderiv ℝ w x₀ (b x₀) := by
    rw [heq x₀ hx₀]; simp
  refine ⟨fun y hy ↦ ?_, ?_⟩
  · have hd : dist y x₀ < R := mem_ball.1 hy
    have hd0 : 0 ≤ dist y x₀ := dist_nonneg
    -- mean value bound for `Dw`
    have hC2 : ∀ z ∈ ball x₀ R, ContDiffAt ℝ 2 w z := fun z hz ↦
      hsol.1.contDiffAt (hU.mem_nhds (hBU hz))
    have hmv : ‖fderiv ℝ w y - fderiv ℝ w x₀‖ ≤ M₂ * ‖y - x₀‖ :=
      (convex_ball x₀ R).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz ↦ ((hC2 z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
          (by norm_num)) hB hx₀ hy
    rw [← dist_eq_norm (fderiv ℝ w y), ← dist_eq_norm y] at hmv
    have hDy : ‖fderiv ℝ w y‖ ≤ M₁ + M₂ * R := by
      have := norm_le_norm_add_norm_sub' (fderiv ℝ w y) (fderiv ℝ w x₀)
      rw [← dist_eq_norm] at this
      nlinarith [mul_le_mul_of_nonneg_left hd.le hM₂0]
    have hlin : dist y x₀ ≤ R ^ (1 - α) * dist y x₀ ^ α := by
      rcases hd0.eq_or_lt with h0 | h0
      · rw [← h0, Real.zero_rpow hα.1.ne', mul_zero]
      · calc dist y x₀ = dist y x₀ ^ (1 - α) * dist y x₀ ^ α := by
              rw [← Real.rpow_add h0]; simp
          _ ≤ R ^ (1 - α) * dist y x₀ ^ α := by
              gcongr; linarith [hα.2]
    have hda : 0 ≤ dist y x₀ ^ α := Real.rpow_nonneg hd0 _
    -- the three terms
    have t1 := hf y hy
    have t2 : |fderiv ℝ w y (b y) - fderiv ℝ w x₀ (b x₀)| ≤
        (Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - α)) * dist y x₀ ^ α := by
      have e : fderiv ℝ w y (b y) - fderiv ℝ w x₀ (b x₀) =
          fderiv ℝ w y (b y - b x₀) + (fderiv ℝ w y - fderiv ℝ w x₀) (b x₀) := by
        simp [map_sub]
      rw [e]
      have a1 : |fderiv ℝ w y (b y - b x₀)| ≤ (M₁ + M₂ * R) * (Kb * dist y x₀ ^ α) := by
        rw [← Real.norm_eq_abs]
        exact (le_opNorm _ _).trans (mul_le_mul hDy (hb y hy) (norm_nonneg _)
          (by positivity))
      have a2 : |(fderiv ℝ w y - fderiv ℝ w x₀) (b x₀)| ≤
          M₂ * (R ^ (1 - α) * dist y x₀ ^ α) * Mb := by
        rw [← Real.norm_eq_abs]
        refine (le_opNorm _ _).trans (mul_le_mul ?_ hbx (norm_nonneg _) (by positivity))
        rw [← dist_eq_norm]
        exact hmv.trans (mul_le_mul_of_nonneg_left hlin hM₂0)
      calc _ ≤ |fderiv ℝ w y (b y - b x₀)| + |(fderiv ℝ w y - fderiv ℝ w x₀) (b x₀)| :=
            abs_add_le _ _
        _ ≤ _ := by nlinarith
    have t3 : |∑ i, fderiv ℝ (fderiv ℝ w) y ((a y - a x₀) (e i)) (e i)| ≤
        finrank ℝ E * Ka * M₂ * dist y x₀ ^ α := by
      refine (abs_sum_apply_le _ _).trans ?_
      have := mul_le_mul (hB y hy) (ha y hy) (norm_nonneg _) hM₂0
      have hdim : (0 : ℝ) ≤ finrank ℝ E := by positivity
      calc (finrank ℝ E : ℝ) * (‖fderiv ℝ (fderiv ℝ w) y‖ * ‖a y - a x₀‖) ≤
            finrank ℝ E * (M₂ * (Ka * dist y x₀ ^ α)) := by gcongr
        _ = _ := by ring
    rw [heq y hy, hgx]
    have hrw : f y - fderiv ℝ w y (b y) -
          ∑ i, fderiv ℝ (fderiv ℝ w) y ((a y - a x₀) (e i)) (e i) -
          (f x₀ - fderiv ℝ w x₀ (b x₀)) =
        (f y - f x₀) - (fderiv ℝ w y (b y) - fderiv ℝ w x₀ (b x₀)) -
          ∑ i, fderiv ℝ (fderiv ℝ w) y ((a y - a x₀) (e i)) (e i) := by ring
    rw [hrw]
    calc _ ≤ |(f y - f x₀) - (fderiv ℝ w y (b y) - fderiv ℝ w x₀ (b x₀))| +
          |∑ i, fderiv ℝ (fderiv ℝ w) y ((a y - a x₀) (e i)) (e i)| := abs_sub _ _
      _ ≤ |f y - f x₀| + |fderiv ℝ w y (b y) - fderiv ℝ w x₀ (b x₀)| +
          |∑ i, fderiv ℝ (fderiv ℝ w) y ((a y - a x₀) (e i)) (e i)| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by nlinarith
  · rw [hgx]
    have : |fderiv ℝ w x₀ (b x₀)| ≤ M₁ * Mb := by
      rw [← Real.norm_eq_abs]
      exact (le_opNorm _ _).trans (mul_le_mul hM₁ hbx (norm_nonneg _) hM₁0)
    calc _ ≤ |f x₀| + |fderiv ℝ w x₀ (b x₀)| := abs_sub _ _
      _ ≤ _ := by nlinarith

/-! ### The pointwise expansion -/

/-- **Pointwise expansion of a nondivergence solution**. Let `0 < α < 1` and
`0 < lam ≤ Λ`. There are `C ≥ 0` and `κ > 0`, depending only on `E, α, lam, Λ`, such that the
following holds. Let `w` solve `tr (a D²w) + ⟪b, ∇w⟫ = f` on the open set `U ⊇ B̄_R(x₀)`, with
`a(x₀)` elliptic (`lam`, `Λ`), `a, b, f` Hölder **at `x₀`** with constants `K_a, K_b, K_f` on
`B_R(x₀)`, `‖b(x₀)‖ ≤ M_b`, `|f(x₀)| ≤ M_f`, `‖Dw(x₀)‖ ≤ M₁`, `|w − w(x₀)| ≤ M₀` and
`‖D²w‖ ≤ M₂` on `B_R(x₀)`. Put
`N = M₀ + R² (M_f + M_b M₁) + R^{2+α} (K_f + K_b (M₁ + M₂ R) + M_b M₂ R^{1−α} + d K_a M₂)`.
Then there is a quadratic polynomial `P` with `R ‖DP(0)‖ + R² ‖quad P‖ ≤ C N` and
`|w(y) − P(y − x₀)| ≤ C N (|y − x₀| / R)^{2+α}` for `|y − x₀| < κ R`. -/
theorem expansion_at_point [Nontrivial E] {α : ℝ} (hα : 0 < α ∧ α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ (U : Set E) (a : E → E →L[ℝ] E) (b : E → E) (f w : E → ℝ)
      (x₀ : E) (R M₀ M₁ M₂ Mb Mf Ka Kb Kf : ℝ),
      IsOpen U → 0 < R → closedBall x₀ R ⊆ U → IsSolOn a b f U w →
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x₀ ξ, ξ⟫) → ‖a x₀‖ ≤ Λ →
      (∀ y ∈ ball x₀ R, ‖a y - a x₀‖ ≤ Ka * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R, ‖b y - b x₀‖ ≤ Kb * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R, |f y - f x₀| ≤ Kf * dist y x₀ ^ α) →
      0 ≤ Ka → 0 ≤ Kb → 0 ≤ Kf →
      ‖b x₀‖ ≤ Mb → |f x₀| ≤ Mf → ‖fderiv ℝ w x₀‖ ≤ M₁ →
      (∀ y ∈ ball x₀ R, |w y - w x₀| ≤ M₀) →
      (∀ y ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 w y‖ ≤ M₂) →
      ∃ P : QuadPoly E,
        R * ‖P.lin‖ + R ^ 2 * ‖P.quad‖ ≤
          C * (M₀ + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) *
            (Kf + Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - α) + finrank ℝ E * Ka * M₂)) ∧
        ∀ y, dist y x₀ < κ * R →
          |w y - P.eval (y - x₀)| ≤
            C * (M₀ + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) *
              (Kf + Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - α) + finrank ℝ E * Ka * M₂)) *
              (dist y x₀ / R) ^ (2 + α) := by
  obtain ⟨C₀, hC₀, hexp⟩ := expansion_of_laplacian (E := E) hα
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  set s := √Λ with hs_def
  set t := √lam with ht_def
  have hs : 0 < s := Real.sqrt_pos.2 hΛ
  have ht : 0 < t := Real.sqrt_pos.2 hlam
  have hts : t ≤ s := Real.sqrt_le_sqrt hlamΛ
  have hs2 : s ^ 2 = Λ := Real.sq_sqrt hΛ.le
  have ht2 : t ^ 2 = lam := Real.sq_sqrt hlam.le
  set Q := s / t with hQ_def
  have hQ1 : 1 ≤ Q := (one_le_div ht).2 hts
  set K₁ := max 1 (1 / lam) with hK₁
  have hK₁1 : 1 ≤ K₁ := le_max_left _ _
  have hγ : (0 : ℝ) < 2 + α := by linarith [hα.1]
  refine ⟨C₀ * K₁ * (Q + Q ^ 2 + Q ^ (2 + α)), t / s, by positivity, by positivity, ?_⟩
  intro U a b f w x₀ R M₀ M₁ M₂ Mb Mf Ka Kb Kf hU hR hBU hsol hell hbd ha hb hf hKa hKb hKf hbx
    hfx hM₁ hM₀ hM₂
  have hx₀ : x₀ ∈ ball x₀ R := mem_ball_self hR
  have hM₀0 : 0 ≤ M₀ := by simpa using hM₀ x₀ hx₀
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ x₀ hx₀)
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans hbx
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans hM₁
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans hfx
  set H₀ := Kf + Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - α) + finrank ℝ E * Ka * M₂ with hH₀
  have hH₀0 : 0 ≤ H₀ := by positivity
  set N := M₀ + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) * H₀ with hN
  have hN0 : 0 ≤ N := by positivity
  -- the normalization `M`
  obtain ⟨M, -, hMn, hMn', hconj, hK⟩ := exists_sqrt_symPart hlam hell hbd
  have hMz : ∀ z, ‖M z‖ ≤ s * ‖z‖ := fun z ↦
    ((M : E →L[ℝ] E).le_opNorm z).trans (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))
  have hMz' : ∀ y, ‖M.symm y‖ ≤ ‖y‖ / t := fun y ↦ by
    have := ((M.symm : E →L[ℝ] E).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hMn' (norm_nonneg _))
    simpa [one_div, div_eq_inv_mul] using this
  set r := R / s with hr_def
  have hr : 0 < r := by positivity
  have hsr : s * r = R := by rw [hr_def]; field_simp
  have hdist : ∀ z, dist (x₀ + M z) x₀ = ‖M z‖ := fun z ↦ by
    rw [dist_eq_norm, add_sub_cancel_left]
  have hmapsC : MapsTo (fun z ↦ x₀ + M z) (closedBall 0 r) (closedBall x₀ R) := fun z hz ↦ by
    rw [mem_closedBall, hdist, ← hsr]
    exact (hMz z).trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hz) hs.le)
  have hmapsB : MapsTo (fun z ↦ x₀ + M z) (ball 0 r) (ball x₀ R) := fun z hz ↦ by
    rw [mem_ball, hdist, ← hsr]
    exact (hMz z).trans_lt (mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hz) hs)
  have hBU' : ball x₀ R ⊆ U := ball_subset_closedBall.trans hBU
  -- the frozen right-hand side
  obtain ⟨hg, hσ⟩ := abs_frozenRHS_sub_le hU hsol hα hR hBU' ha hb hf hbx hfx hM₁ hM₂
  set e := stdOrthonormalBasis ℝ E
  set σ := ∑ i, fderiv ℝ (fderiv ℝ w) x₀ (a x₀ (e i)) (e i) with hσdef
  -- the normalized function
  set u : E → ℝ := fun z ↦ w (x₀ + M z) - w x₀ with hu_def
  have hT : ContDiff ℝ 2 fun z ↦ x₀ + M z := contDiff_const.add M.contDiff
  have huc : ContinuousOn u (closedBall 0 r) :=
    (hsol.1.continuousOn.comp hT.continuous.continuousOn (hmapsC.mono_right hBU)).sub
      continuousOn_const
  have hu2 : ContDiffOn ℝ 2 u (ball 0 r) :=
    (hsol.1.comp hT.contDiffOn (hmapsB.mono_right hBU')).sub contDiffOn_const
  have hu0 : ∀ z ∈ ball (0 : E) r, |u z| ≤ M₀ := fun z hz ↦ hM₀ _ (hmapsB hz)
  have hΔ : ∀ z ∈ ball (0 : E) r, |Δ u z - σ| ≤ H₀ * s ^ α * ‖z‖ ^ α := by
    intro z hz
    have hTz : x₀ + M z ∈ U := hBU' (hmapsB hz)
    have hwT : ContDiffAt ℝ 2 (fun z ↦ w (x₀ + M z)) z :=
      (hsol.1.contDiffAt (hU.mem_nhds hTz)).comp z hT.contDiffAt
    have hΔu : Δ u z = Δ (fun z ↦ w (x₀ + M z)) z := by
      rw [hu_def, show (fun z ↦ w (x₀ + M z) - w x₀) =
        (fun z ↦ w (x₀ + M z)) - fun _ ↦ w x₀ from rfl,
        ContDiffAt.laplacian_sub (f₁ := fun z ↦ w (x₀ + M z)) (f₂ := fun _ ↦ w x₀) hwT
          contDiffAt_const, laplacian_const, Pi.zero_apply, sub_zero]
    rw [hΔu, laplacian_comp_affine_eq_frozen hU hsol.1 (a x₀) M _ hconj hK x₀ hTz]
    refine (hg _ (hmapsB hz)).trans ?_
    rw [hdist]
    have hle : ‖M z‖ ^ α ≤ s ^ α * ‖z‖ ^ α := by
      rw [← Real.mul_rpow hs.le (norm_nonneg _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hMz z) hα.1.le
    calc H₀ * ‖M z‖ ^ α ≤ H₀ * (s ^ α * ‖z‖ ^ α) := mul_le_mul_of_nonneg_left hle hH₀0
      _ = H₀ * s ^ α * ‖z‖ ^ α := by ring
  obtain ⟨P', -, hP'c, hP'e⟩ := hexp u r M₀ σ (H₀ * s ^ α) hr (by positivity) huc hu2 hu0 hΔ
  -- comparison of the two normalizing quantities
  set N' := M₀ + r ^ 2 * |σ| + r ^ (2 + α) * (H₀ * s ^ α) with hN'
  have hN'N : N' ≤ K₁ * N := by
    have hr2 : r ^ 2 = R ^ 2 / Λ := by rw [hr_def, div_pow, hs2]
    have hrγ : r ^ (2 + α) * s ^ α = R ^ (2 + α) / Λ := by
      rw [hr_def, Real.div_rpow hR.le hs.le, Real.rpow_add hs, Real.rpow_two, hs2]
      field_simp
    have hΛK : 1 / Λ ≤ K₁ := (one_div_le_one_div_of_le hlam hlamΛ).trans (le_max_right _ _)
    have h1 : r ^ 2 * |σ| ≤ K₁ * (R ^ 2 * (Mf + Mb * M₁)) := by
      rw [hr2]
      calc R ^ 2 / Λ * |σ| ≤ R ^ 2 / Λ * (Mf + Mb * M₁) := by gcongr
        _ = 1 / Λ * (R ^ 2 * (Mf + Mb * M₁)) := by ring
        _ ≤ K₁ * (R ^ 2 * (Mf + Mb * M₁)) := by gcongr
    have h2 : r ^ (2 + α) * (H₀ * s ^ α) ≤ K₁ * (R ^ (2 + α) * H₀) := by
      calc r ^ (2 + α) * (H₀ * s ^ α) = 1 / Λ * (R ^ (2 + α) * H₀) := by
            rw [mul_comm H₀, ← mul_assoc, hrγ]; ring
        _ ≤ K₁ * (R ^ (2 + α) * H₀) := by gcongr
    have h3 : M₀ ≤ K₁ * M₀ := le_mul_of_one_le_left hM₀0 hK₁1
    rw [hN', hN, mul_add, mul_add]; linarith
  have hN'0 : 0 ≤ N' := by positivity
  -- the polynomial in the original coordinates
  set P : QuadPoly E := P'.compCLM (M.symm : E →L[ℝ] E) + ⟨w x₀, 0, 0⟩ with hP
  refine ⟨P, ?_, fun y hy ↦ ?_⟩
  · have hl : ‖P.lin‖ ≤ ‖P'.lin‖ / t := by
      have := P'.norm_lin_compCLM_le (M.symm : E →L[ℝ] E)
      simp only [hP, QuadPoly.add_lin, add_zero]
      refine this.trans ?_
      calc ‖P'.lin‖ * ‖(M.symm : E →L[ℝ] E)‖ ≤ ‖P'.lin‖ * (1 / t) := by gcongr
        _ = ‖P'.lin‖ / t := by ring
    have hq : ‖P.quad‖ ≤ ‖P'.quad‖ / t ^ 2 := by
      have := P'.norm_quad_compCLM_le (M.symm : E →L[ℝ] E)
      simp only [hP, QuadPoly.add_quad, add_zero]
      refine this.trans ?_
      calc ‖P'.quad‖ * ‖(M.symm : E →L[ℝ] E)‖ * ‖(M.symm : E →L[ℝ] E)‖ ≤
            ‖P'.quad‖ * (1 / t) * (1 / t) := by gcongr
        _ = ‖P'.quad‖ / t ^ 2 := by ring
    have hRt : R / t = Q * r := by rw [hQ_def, hr_def]; field_simp
    have hRt2 : R ^ 2 / t ^ 2 = Q ^ 2 * r ^ 2 := by rw [← div_pow, hRt, mul_pow]
    calc R * ‖P.lin‖ + R ^ 2 * ‖P.quad‖ ≤ R * (‖P'.lin‖ / t) + R ^ 2 * (‖P'.quad‖ / t ^ 2) := by
          gcongr
      _ = Q * (r * ‖P'.lin‖) + Q ^ 2 * (r ^ 2 * ‖P'.quad‖) := by
          rw [show R * (‖P'.lin‖ / t) = R / t * ‖P'.lin‖ by ring,
            show R ^ 2 * (‖P'.quad‖ / t ^ 2) = R ^ 2 / t ^ 2 * ‖P'.quad‖ by ring, hRt, hRt2]
          ring
      _ ≤ (Q + Q ^ 2) * (r * ‖P'.lin‖) + (Q + Q ^ 2) * (r ^ 2 * ‖P'.quad‖) := by
          have h1 : 0 ≤ r * ‖P'.lin‖ := mul_nonneg hr.le (norm_nonneg _)
          have h2 : 0 ≤ r ^ 2 * ‖P'.quad‖ := mul_nonneg (sq_nonneg r) (norm_nonneg _)
          have hQ0 : 0 ≤ Q ^ 2 := sq_nonneg Q
          exact add_le_add (mul_le_mul_of_nonneg_right (by linarith) h1)
            (mul_le_mul_of_nonneg_right (by linarith) h2)
      _ ≤ (Q + Q ^ 2) * (|P'.const| + r * ‖P'.lin‖ + r ^ 2 * ‖P'.quad‖) := by
          rw [← mul_add]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [abs_nonneg P'.const]
      _ ≤ (Q + Q ^ 2) * (C₀ * N') := by gcongr
      _ ≤ (Q + Q ^ 2) * (C₀ * (K₁ * N)) := by gcongr
      _ = C₀ * K₁ * (Q + Q ^ 2) * N := by ring
      _ ≤ C₀ * K₁ * (Q + Q ^ 2 + Q ^ (2 + α)) * N := by
          have : 0 ≤ Q ^ (2 + α) := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hN0
  · set z := M.symm (y - x₀) with hz_def
    have hTz : x₀ + M z = y := by rw [hz_def, M.apply_symm_apply, add_sub_cancel]
    have hzn : ‖z‖ ≤ dist y x₀ / t := by rw [dist_eq_norm]; exact hMz' _
    have hzr : ‖z‖ < r := by
      refine hzn.trans_lt ?_
      rw [div_lt_iff₀ ht]
      calc dist y x₀ < t / s * R := hy
        _ = r * t := by rw [hr_def]; ring
    have hPe : P.eval (y - x₀) = P'.eval z + w x₀ := by
      rw [hP, QuadPoly.eval_add, QuadPoly.eval_compCLM]
      simp [QuadPoly.eval, z]
    have hb' := hP'e z hzr
    have hu_z : u z = w y - w x₀ := by simp only [hu_def, hTz]
    rw [hu_z] at hb'
    rw [hPe, show w y - (P'.eval z + w x₀) = w y - w x₀ - P'.eval z by ring]
    have hzr' : ‖z‖ / r ≤ Q * (dist y x₀ / R) := by
      rw [div_le_iff₀ hr]
      calc ‖z‖ ≤ dist y x₀ / t := hzn
        _ = Q * (dist y x₀ / R) * r := by rw [hQ_def, hr_def]; field_simp
    calc |w y - w x₀ - P'.eval z| ≤ C₀ * N' * (‖z‖ / r) ^ (2 + α) := hb'
      _ ≤ C₀ * (K₁ * N) * (Q * (dist y x₀ / R)) ^ (2 + α) := by
          gcongr
      _ = C₀ * K₁ * Q ^ (2 + α) * N * (dist y x₀ / R) ^ (2 + α) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
      _ ≤ C₀ * K₁ * (Q + Q ^ 2 + Q ^ (2 + α)) * N * (dist y x₀ / R) ^ (2 + α) := by
          have : 0 ≤ (dist y x₀ / R) ^ (2 + α) := by positivity
          have : 0 ≤ C₀ * K₁ := by positivity
          gcongr
          have : 0 ≤ Q ^ 2 := sq_nonneg Q
          linarith

end Nondiv

end BasicElliptic
