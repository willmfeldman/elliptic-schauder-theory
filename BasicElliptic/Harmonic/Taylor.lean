/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Harmonic.Estimates

/-!
# Taylor bounds for harmonic functions

Let `E` be a finite-dimensional real inner product space. For `h` harmonic on a neighbourhood of
`closedBall x r` with `|h| ≤ M` there, `ρ ≤ r/2` and `y ∈ closedBall x ρ`
(`BasicElliptic.harmonic_taylor_le`):

* `|h y − h x| ≤ C M (ρ/r)`;
* `|h y − h x − Dh(x)(y − x)| ≤ C M (ρ/r)²`;
* `|h y − h x − Dh(x)(y − x) − ½ D²h(x)(y − x, y − x)| ≤ C M (ρ/r)³`.

This is the sup-norm (Taylor) form of the harmonic decay, the elliptic analogue of the caloric
bounds `IsSmoothCaloricOn.taylor{0,1,2}_le` of parabolic-basic-theory.

## Proof

Restrict to the segment: `φ(s) = h(x + s v)`, `v = y − x`. Its derivatives are iterated
directional derivatives `D_v^k h`, which are harmonic (`HarmonicOnNhd.fderiv_apply`). Applying the
gradient bound three times on nested balls of radius `r/6` gives
`|D_v^k h| ≤ 6^k C₁^k M (ρ/r)^k` on `closedBall x (r/2)` for `k ≤ 3`, and the one-dimensional
Taylor bounds conclude.

## Provenance

The one-dimensional Taylor bounds (`abs_taylor1_le_of_hasDerivAt_Icc`,
`abs_taylor2_le_of_hasDerivAt_Icc`) are copied from parabolic-basic-theory (W. M. Feldman),
`ParabolicBasic/Caloric/BernsteinTaylor.lean`; the rest is new.
-/

open InnerProductSpace Metric Set Filter Topology

public section

namespace BasicElliptic

/-! ### One-dimensional Taylor bounds -/

/-- Mean value inequality on `[0, x] ⊆ [0, 1]`. -/
private theorem abs_sub_le_of_hasDerivAt_Icc {φ φ' : ℝ → ℝ} {K x : ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' s) s) (hx : x ∈ Icc (0 : ℝ) 1)
    (hb : ∀ s ∈ Icc (0 : ℝ) x, |φ' s| ≤ K) : |φ x - φ 0| ≤ K * x := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (f' := φ') (a := 0) (b := x)
    (C := K) (fun y hy ↦ (hφ y ⟨hy.1, hy.2.trans hx.2⟩).hasDerivWithinAt)
    (fun y hy ↦ by rw [Real.norm_eq_abs]; exact hb y ⟨hy.1, hy.2.le⟩)
    x ⟨hx.1, le_rfl⟩
  rwa [Real.norm_eq_abs, sub_zero] at this

/-- First-order Taylor bound on `[0, x] ⊆ [0, 1]`. -/
private theorem abs_taylor1_le_of_hasDerivAt_Icc {φ φ1 φ2 : ℝ → ℝ} {K x : ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (hφ1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ2 s| ≤ K) (hx : x ∈ Icc (0 : ℝ) 1) :
    |φ x - φ 0 - x * φ1 0| ≤ K * x ^ 2 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  have hψ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s ↦ φ s - s * φ1 0) (φ1 s - φ1 0) s :=
    fun s hs ↦ (hφ s hs).sub (hasDerivAt_mul_const (φ1 0))
  have := abs_sub_le_of_hasDerivAt_Icc (K := K * x) hψ hx fun s hs ↦
    (abs_sub_le_of_hasDerivAt_Icc hφ1 ⟨hs.1, hs.2.trans hx.2⟩ fun y hy ↦
      hb y ⟨hy.1, hy.2.trans (hs.2.trans hx.2)⟩).trans (mul_le_mul_of_nonneg_left hs.2 hK)
  have e : φ x - φ 0 - x * φ1 0 = (φ x - x * φ1 0) - (φ 0 - 0 * φ1 0) := by ring
  rw [e]
  calc _ ≤ K * x * x := this
    _ = K * x ^ 2 := by ring

/-- Second-order Taylor bound on `[0, x] ⊆ [0, 1]`. -/
private theorem abs_taylor2_le_of_hasDerivAt_Icc {φ φ1 φ2 φ3 : ℝ → ℝ} {K x : ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (hφ1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (hφ2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ2 (φ3 s) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ3 s| ≤ K) (hx : x ∈ Icc (0 : ℝ) 1) :
    |φ x - φ 0 - x * φ1 0 - x ^ 2 / 2 * φ2 0| ≤ K * x ^ 3 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  have hsq : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2 * φ2 0) (s * φ2 0) s := fun s ↦ by
    have := ((hasDerivAt_pow 2 s).div_const 2).mul_const (φ2 0)
    convert this using 1
    push_cast
    ring
  have hψ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s ↦ φ s - s * φ1 0 - s ^ 2 / 2 * φ2 0)
      (φ1 s - φ1 0 - s * φ2 0) s :=
    fun s hs ↦ ((hφ s hs).sub (hasDerivAt_mul_const (φ1 0))).sub (hsq s)
  have := abs_sub_le_of_hasDerivAt_Icc (K := K * x ^ 2) hψ hx fun s hs ↦
    (abs_taylor1_le_of_hasDerivAt_Icc hφ1 hφ2 hb ⟨hs.1, hs.2.trans hx.2⟩).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hs.2 2) hK)
  have e : φ x - φ 0 - x * φ1 0 - x ^ 2 / 2 * φ2 0 =
      (φ x - x * φ1 0 - x ^ 2 / 2 * φ2 0) - (φ 0 - 0 * φ1 0 - 0 ^ 2 / 2 * φ2 0) := by ring
  rw [e]
  calc _ ≤ K * x ^ 2 * x := this
    _ = K * x ^ 3 := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The derivative along the line `s ↦ x + s v`. -/
private theorem hasDerivAt_comp_line {f : E → ℝ} {x v : E} {s : ℝ}
    (hf : DifferentiableAt ℝ f (x + s • v)) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • v)) (fderiv ℝ f (x + s • v) v) s := by
  have hγ : HasDerivAt (fun s : ℝ ↦ x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt s hγ

/-- One step of the derivative bound: if `g` is harmonic on `V ⊇ closedBall x R` with
`|g| ≤ K` on `closedBall x R`, then `|D_v g| ≤ C₁ K ‖v‖ / t` on `closedBall x (R - t)`. -/
private theorem abs_fderiv_apply_le {C₁ : ℝ} (hC₁ : ∀ (u : E → ℝ) (x₀ : E) (r M : ℝ), 0 < r →
      HarmonicOnNhd u (closedBall x₀ r) → (∀ y ∈ closedBall x₀ r, |u y| ≤ M) →
      ‖fderiv ℝ u x₀‖ ≤ C₁ * M / r)
    {g : E → ℝ} {x : E} {R t K : ℝ} (ht : 0 < t) (hg : HarmonicOnNhd g (closedBall x R))
    (hK : ∀ z ∈ closedBall x R, |g z| ≤ K) (v : E) :
    ∀ z ∈ closedBall x (R - t), |fderiv ℝ g z v| ≤ C₁ * K / t * ‖v‖ := by
  intro z hz
  have hsub : closedBall z t ⊆ closedBall x R := closedBall_subset_closedBall' (by
    rw [mem_closedBall] at hz; linarith)
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (hC₁ g z t K ht (hg.mono hsub) fun w hw ↦ hK w (hsub hw)) (norm_nonneg _))

variable (E) in
/-- **Taylor bounds for harmonic functions** (sup-norm form of the harmonic decay). There is
`C = C(E) ≥ 0` such that, for `h` harmonic on a neighbourhood of `closedBall x r` with `|h| ≤ M`
there, `ρ ≤ r/2` and `y ∈ closedBall x ρ`, the Taylor remainders of order `0, 1, 2` at `x` are
bounded by `C M (ρ/r)^{k+1}`. -/
theorem harmonic_taylor_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : E → ℝ) (x : E) (r ρ M : ℝ), 0 < r → ρ ≤ r / 2 →
      HarmonicOnNhd h (closedBall x r) → (∀ y ∈ closedBall x r, |h y| ≤ M) →
      ∀ y ∈ closedBall x ρ,
        |h y - h x| ≤ C * M * (ρ / r) ∧
        |h y - h x - fderiv ℝ h x (y - x)| ≤ C * M * (ρ / r) ^ 2 ∧
        |h y - h x - fderiv ℝ h x (y - x) - 1 / 2 * fderiv ℝ (fderiv ℝ h) x (y - x) (y - x)| ≤
          C * M * (ρ / r) ^ 3 := by
  obtain ⟨C₁, hC₁, hest⟩ := exists_norm_fderiv_le_div_of_harmonic E
  refine ⟨6 * C₁ + 36 * C₁ ^ 2 + 216 * C₁ ^ 3, by positivity,
    fun h x r ρ M hr hρr hh hM y hy ↦ ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x (mem_closedBall_self hr.le))
  have hρ : 0 ≤ ρ := dist_nonneg.trans (mem_closedBall.1 hy)
  set v := y - x with hv
  have hvρ : ‖v‖ ≤ ρ := by rw [hv, ← dist_eq_norm]; exact mem_closedBall.1 hy
  -- the open set of harmonic points and the iterated directional derivatives
  set U := {z | HarmonicAt h z}
  have hU : IsOpen U := isOpen_setOfPred_harmonicAt h
  have hhU : HarmonicOnNhd h U := fun z hz ↦ hz
  have hBU : closedBall x r ⊆ U := fun z hz ↦ hh z hz
  set w1 : E → ℝ := fun z ↦ fderiv ℝ h z v with hw1
  set w2 : E → ℝ := fun z ↦ fderiv ℝ w1 z v with hw2
  set w3 : E → ℝ := fun z ↦ fderiv ℝ w2 z v with hw3
  have hw1U : HarmonicOnNhd w1 U := HarmonicOnNhd.fderiv_apply hU hhU v
  have hw2U : HarmonicOnNhd w2 U := HarmonicOnNhd.fderiv_apply hU hw1U v
  have hr6 : 0 < r / 6 := by positivity
  -- bounds on nested balls
  have hb1 : ∀ z ∈ closedBall x (r - r / 6), |w1 z| ≤ C₁ * M / (r / 6) * ‖v‖ :=
    abs_fderiv_apply_le hest hr6 hh hM v
  have hb2 : ∀ z ∈ closedBall x (r - r / 6 - r / 6),
      |w2 z| ≤ C₁ * (C₁ * M / (r / 6) * ‖v‖) / (r / 6) * ‖v‖ :=
    abs_fderiv_apply_le hest hr6 (hw1U.mono ((closedBall_subset_closedBall (by linarith)).trans
      hBU)) hb1 v
  have hb3 : ∀ z ∈ closedBall x (r - r / 6 - r / 6 - r / 6),
      |w3 z| ≤ C₁ * (C₁ * (C₁ * M / (r / 6) * ‖v‖) / (r / 6) * ‖v‖) / (r / 6) * ‖v‖ :=
    abs_fderiv_apply_le hest hr6 (hw2U.mono ((closedBall_subset_closedBall (by linarith)).trans
      hBU)) hb2 v
  -- the segment stays in `closedBall x (r / 2)`
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • v ∈ closedBall x (r / 2) := fun s hs ↦ by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hs.1]
    nlinarith [norm_nonneg v, hs.2]
  have hsegU : ∀ s ∈ Icc (0 : ℝ) 1, x + s • v ∈ U := fun s hs ↦
    hBU (closedBall_subset_closedBall (by linarith) (hseg s hs))
  have hd : ∀ {g : E → ℝ}, HarmonicOnNhd g U → ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ g (x + s • v)) (fderiv ℝ g (x + s • v) v) s := fun hg s hs ↦
    hasDerivAt_comp_line ((hg _ (hsegU s hs)).1.differentiableAt (by norm_num))
  have h1x : ‖(1 : ℝ) • v‖ = ‖v‖ := by simp
  have hpt : x + (1 : ℝ) • v = y := by simp [hv]
  have hx0 : x + (0 : ℝ) • v = x := by simp
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k : ℝ, r / 2 ≤ k → x + s • v ∈ closedBall x k :=
    fun s hs k hk ↦ closedBall_subset_closedBall hk (hseg s hs)
  -- the three Taylor bounds along the segment
  have hρr' : ρ / r ≤ 1 := by rw [div_le_one hr]; linarith
  have hq0 : 0 ≤ ρ / r := div_nonneg hρ hr.le
  have hvr : ‖v‖ / r ≤ ρ / r := div_le_div_of_nonneg_right hvρ hr.le
  -- degree 0
  have T0 := abs_sub_le_of_hasDerivAt_Icc (hd hhU) hone (K := C₁ * M / (r / 6) * ‖v‖)
    fun s hs ↦ hb1 _ (hmem s ⟨hs.1, hs.2⟩ _ (by linarith))
  -- degree 1
  have T1 := abs_taylor1_le_of_hasDerivAt_Icc (hd hhU) (hd hw1U) (x := 1)
    (K := C₁ * (C₁ * M / (r / 6) * ‖v‖) / (r / 6) * ‖v‖)
    (fun s hs ↦ hb2 _ (hmem s hs _ (by linarith))) hone
  -- degree 2
  have T2 := abs_taylor2_le_of_hasDerivAt_Icc (hd hhU) (hd hw1U) (hd hw2U) (x := 1)
    (K := C₁ * (C₁ * (C₁ * M / (r / 6) * ‖v‖) / (r / 6) * ‖v‖) / (r / 6) * ‖v‖)
    (fun s hs ↦ hb3 _ (hmem s hs _ (by linarith))) hone
  simp only [hpt, hx0, one_mul, one_pow, mul_one] at T0 T1 T2
  -- identify the second directional derivative with the Hessian
  have hD2 : fderiv ℝ w1 x v = fderiv ℝ (fderiv ℝ h) x v v :=
    fderiv_apply_const_apply ((hh x (mem_closedBall_self hr.le)).1.fderiv_right (m := 1)
      (by norm_num) |>.differentiableAt (by norm_num)) v v
  rw [hD2] at T2
  -- compare the constants
  have hK1 : C₁ * M / (r / 6) * ‖v‖ ≤ 6 * C₁ * M * (ρ / r) := by
    have : C₁ * M / (r / 6) * ‖v‖ = 6 * C₁ * M * (‖v‖ / r) := by field_simp
    rw [this]; gcongr
  have hK2 : C₁ * (C₁ * M / (r / 6) * ‖v‖) / (r / 6) * ‖v‖ ≤ 36 * C₁ ^ 2 * M * (ρ / r) ^ 2 := by
    have : C₁ * (C₁ * M / (r / 6) * ‖v‖) / (r / 6) * ‖v‖ = 36 * C₁ ^ 2 * M * (‖v‖ / r) ^ 2 := by
      field_simp; ring
    rw [this]; gcongr
  have hK3 : C₁ * (C₁ * (C₁ * M / (r / 6) * ‖v‖) / (r / 6) * ‖v‖) / (r / 6) * ‖v‖ ≤
      216 * C₁ ^ 3 * M * (ρ / r) ^ 3 := by
    have : C₁ * (C₁ * (C₁ * M / (r / 6) * ‖v‖) / (r / 6) * ‖v‖) / (r / 6) * ‖v‖ =
        216 * C₁ ^ 3 * M * (‖v‖ / r) ^ 3 := by
      field_simp; ring
    rw [this]; gcongr
  set C := 6 * C₁ + 36 * C₁ ^ 2 + 216 * C₁ ^ 3
  have hpow : ∀ n : ℕ, 0 ≤ M * (ρ / r) ^ n := fun n ↦ by positivity
  refine ⟨T0.trans (hK1.trans ?_), ?_, ?_⟩
  · have : 0 ≤ (36 * C₁ ^ 2 + 216 * C₁ ^ 3) * M * (ρ / r) := by positivity
    nlinarith
  · refine (le_of_eq_of_le (by ring_nf) T1).trans (hK2.trans ?_)
    have : 0 ≤ (6 * C₁ + 216 * C₁ ^ 3) * (M * (ρ / r) ^ 2) := by positivity
    nlinarith
  · refine (le_of_eq_of_le (by ring_nf) T2).trans (hK3.trans ?_)
    have : 0 ≤ (6 * C₁ + 36 * C₁ ^ 2) * (M * (ρ / r) ^ 3) := by positivity
    nlinarith

end BasicElliptic
