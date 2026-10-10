/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Boundary.Step
public import BasicElliptic.Nondiv.Interior.Iterate

/-!
# The boundary iteration at a flat point

`ν` is a unit vector, `γ = 2 + α` with `0 < α < 1`, `B_r⁺ = halfBall ν 0 r` (closed) and
`ball 0 r ∩ openHalfSpace ν` its interior. Normal derivatives at flat points are
right-derivatives of `t ↦ u (z + t • ν)` at `0`.

* `Nondiv.iterate_step_halfBall`: one step at scale `ρⁿ`, for an abstract improvement-of-flatness
  hypothesis with a polynomial class `K` and a boundary predicate `B` (shared by the Neumann and
  Dirichlet iterations).
* `Nondiv.expansion_at_origin_halfBall`: the assembled iteration (the limit polynomial is
  `Nondiv.exists_limit_poly`), for a class `K` closed under sums, scalar multiples and
  rescalings, and a boundary predicate preserved by subtracting members of `K` and rescaling.
* `Nondiv.expansion_at_origin_neumann`: if `|u − P₀| ≤ 1` (`P₀` even, `tr P₀ = σ`),
  `|Δu(z) − σ| ≤ δ₀ |z|^α` and `|∂_ν u(z)| ≤ δ₀ |z|^{1+α}` on the flat part, then a quadratic `P`
  with `tr P = σ` satisfies `|u(z) − P(z)| ≤ A |z|^{2+α}` on `B₁⁺`.
* `Nondiv.expansion_at_origin_dirichlet`: the same with `u = 0` on the flat part and `P₀`
  vanishing there.

The source hypothesis is the pointwise Hölder bound at the base point `0` only.

## Provenance

The half-ball analogue of `Nondiv.iterate_step` / `Nondiv.expansion_at_origin`
(`Nondiv/Interior/Iterate.lean`), themselves ports of parabolic-basic-theory
`ParabolicBasic/Schauder/Iteration/Iterate.lean` (own repository).
-/

public section

open Metric Set Filter Topology Module InnerProductSpace
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem smul_mem_halfBall {ν : E} {r s : ℝ} (hr : 0 < r) {y : E} (hy : y ∈ halfBall ν (0 : E) s) :
    r • y ∈ halfBall ν (0 : E) (r * s) := by
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy.1) hr.le
  · rw [mem_halfSpace, real_inner_smul_left]; exact mul_nonneg hr.le hy.2

omit [FiniteDimensional ℝ E] in
theorem smul_mem_ball_inter_openHalfSpace {ν : E} {r s : ℝ} (hr : 0 < r) {y : E}
    (hy : y ∈ ball (0 : E) s ∩ openHalfSpace ν) :
    r • y ∈ ball (0 : E) (r * s) ∩ openHalfSpace ν := by
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hy.1) hr
  · rw [mem_openHalfSpace, real_inner_smul_left]; exact mul_pos hr hy.2

/-- **Boundary iteration, step.** Suppose an improvement-of-flatness statement holds on the half
ball at radius `ρ` for functions satisfying a boundary predicate `B`, with corrections in a class
`K` (`hflat`). Let `u ∈ C(B̄₁⁺) ∩ C²(B₁⁺)` with `|Δu(z) − σ| ≤ ρ^γ/4 |z|^α`, and let `P` (with
`tr P = σ`) approximate `u` to order `(ρⁿ)^γ` on `B_{ρⁿ}⁺`, the rescaled error satisfying `B`.
Then there is `Q ∈ K` as in `hflat` such that `P + (ρⁿ)^γ Q(ρ^{-n} ·)` approximates `u` to order
`(ρ^{n+1})^γ` on `B_{ρ^{n+1}}⁺`. -/
theorem iterate_step_halfBall {α ρ C₀ σ : ℝ} {ν : E} (hα : 0 ≤ α) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K : QuadPoly E → Prop} {B : (E → ℝ) → Prop}
    (hflat : ∀ {v : E → ℝ}, ContinuousOn v (halfBall ν 0 1) →
      ContDiffOn ℝ 2 v (ball 0 1 ∩ openHalfSpace ν) → (∀ z ∈ halfBall ν (0 : E) 1, |v z| ≤ 1) →
      (∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ v z| ≤ ρ ^ (2 + α) / 4) → B v →
      ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧ K Q ∧
        ∀ z ∈ halfBall ν (0 : E) ρ, |v z - Q.eval z| ≤ ρ ^ (2 + α))
    {u : E → ℝ} (hu : ContinuousOn u (halfBall ν 0 1))
    (hu2 : ContDiffOn ℝ 2 u (ball 0 1 ∩ openHalfSpace ν))
    (hH : ∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ u z - σ| ≤ ρ ^ (2 + α) / 4 * ‖z‖ ^ α)
    (n : ℕ) {P : QuadPoly E} (hPtr : P.trace = σ)
    (hB : B fun y ↦ (u ((ρ ^ n) • y) - P.eval ((ρ ^ n) • y)) / (ρ ^ n) ^ (2 + α))
    (hP : ∀ z ∈ halfBall ν (0 : E) (ρ ^ n), |u z - P.eval z| ≤ (ρ ^ n) ^ (2 + α)) :
    ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧ K Q ∧
      ∀ z ∈ halfBall ν (0 : E) (ρ ^ (n + 1)),
        |u z - (P + ((ρ ^ n) ^ (2 + α)) • Q.rescale (ρ ^ n)⁻¹).eval z| ≤
          (ρ ^ (n + 1)) ^ (2 + α) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ρ ^ n := ⟨_, rfl⟩
  rw [← hr] at hP hB ⊢
  have hr0 : 0 < r := hr ▸ pow_pos hρ0 n
  have hr1 : r ≤ 1 := hr ▸ pow_le_one₀ hρ0.le hρ1
  have hrγ : 0 < r ^ (2 + α) := Real.rpow_pos_of_pos hr0 _
  have hnorm : ∀ y : E, ‖r • y‖ = r * ‖y‖ := fun y ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  have hmapsC : MapsTo (fun y : E ↦ r • y) (halfBall ν 0 1) (halfBall ν 0 r) := fun y hy ↦ by
    simpa using smul_mem_halfBall hr0 hy
  have hmapsC1 : MapsTo (fun y : E ↦ r • y) (halfBall ν 0 1) (halfBall ν 0 1) :=
    hmapsC.mono_right (halfBall_mono ν 0 hr1)
  have hmapsB : MapsTo (fun y : E ↦ r • y) (ball 0 1 ∩ openHalfSpace ν)
      (ball 0 r ∩ openHalfSpace ν) := fun y hy ↦ by
    simpa using smul_mem_ball_inter_openHalfSpace hr0 hy
  have hBr1 : ball (0 : E) r ∩ openHalfSpace ν ⊆ ball 0 1 ∩ openHalfSpace ν :=
    inter_subset_inter_left _ (ball_subset_ball hr1)
  have hU : IsOpen (ball (0 : E) 1 ∩ openHalfSpace ν) :=
    isOpen_ball.inter (isOpen_openHalfSpace ν)
  set w : E → ℝ := fun y ↦ (u (r • y) - P.eval (r • y)) / r ^ (2 + α) with hw
  have hsc : ContDiff ℝ 2 fun y : E ↦ r • y := contDiff_const_smul r
  have hwc : ContinuousOn w (halfBall ν 0 1) :=
    ((hu.comp hsc.continuous.continuousOn hmapsC1).sub
      (P.continuous_eval.comp hsc.continuous).continuousOn).div_const _
  have hw2 : ContDiffOn ℝ 2 w (ball 0 1 ∩ openHalfSpace ν) :=
    ((hu2.comp hsc.contDiffOn fun y hy ↦ hBr1 (hmapsB hy)).sub
      (P.contDiff_eval.comp hsc).contDiffOn).div_const _
  have hw1 : ∀ y ∈ halfBall ν (0 : E) 1, |w y| ≤ 1 := fun y hy ↦ by
    rw [hw, abs_div, abs_of_pos hrγ, div_le_one hrγ]
    exact hP _ (hmapsC hy)
  have hwΔ : ∀ y ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ w y| ≤ ρ ^ (2 + α) / 4 := fun y hy ↦ by
    have hry := hmapsB hy
    have hat : ContDiffAt ℝ 2 u (r • y) := hu2.contDiffAt (hU.mem_nhds (hBr1 hry))
    rw [hw, laplacian_rescale_sub P r _ hat, hPtr]
    have hb := hH _ (hBr1 hry)
    have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.1 hy.1
    have e1 : ‖r • y‖ ^ α ≤ r ^ α := by
      rw [hnorm, Real.mul_rpow hr0.le (norm_nonneg _)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hr0.le _)
        (Real.rpow_le_one (norm_nonneg _) hy1.le hα)
    have e2 : r ^ 2 * r ^ α / r ^ (2 + α) = 1 := by
      rw [Real.rpow_add hr0, Real.rpow_two, div_self (by positivity)]
    rw [abs_div, abs_mul, abs_of_pos hrγ, abs_of_nonneg (sq_nonneg r)]
    have hδ : 0 ≤ ρ ^ (2 + α) / 4 := by positivity
    calc r ^ 2 * |Δ u (r • y) - σ| / r ^ (2 + α)
        ≤ r ^ 2 * (ρ ^ (2 + α) / 4 * r ^ α) / r ^ (2 + α) := by
          gcongr; exact hb.trans (mul_le_mul_of_nonneg_left e1 hδ)
      _ = ρ ^ (2 + α) / 4 * (r ^ 2 * r ^ α / r ^ (2 + α)) := by ring
      _ = ρ ^ (2 + α) / 4 := by rw [e2, mul_one]
  obtain ⟨Q, hQtr, hQc, hQK, hQap⟩ := hflat hwc hw2 hw1 hwΔ hB
  refine ⟨Q, hQtr, hQc, hQK, fun z hz ↦ ?_⟩
  set y : E := r⁻¹ • z with hy
  have hSy : r • y = z := by rw [hy, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  have hyρ : y ∈ halfBall ν (0 : E) ρ := by
    have := smul_mem_halfBall (inv_pos.2 hr0) hz
    rwa [pow_succ, ← hr, ← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul] at this
  have hQy := hQap y hyρ
  simp only [hw, hSy] at hQy
  have hne : r ^ (2 + α) ≠ 0 := hrγ.ne'
  have e : u z - (P + (r ^ (2 + α)) • Q.rescale r⁻¹).eval z =
      r ^ (2 + α) * ((u z - P.eval z) / r ^ (2 + α) - Q.eval y) := by
    rw [QuadPoly.eval_add, QuadPoly.eval_smul, QuadPoly.eval_rescale, ← hy, mul_sub,
      mul_div_cancel₀ _ hne]
    ring
  rw [e, abs_mul, abs_of_pos hrγ]
  calc r ^ (2 + α) * |(u z - P.eval z) / r ^ (2 + α) - Q.eval y| ≤ r ^ (2 + α) * ρ ^ (2 + α) := by
        gcongr
    _ = (ρ ^ (n + 1)) ^ (2 + α) := by
      rw [pow_succ, Real.mul_rpow (pow_nonneg hρ0.le n) hρ0.le, hr]

/-- **Boundary iteration, expansion at the origin** (abstract form). Let `hflat` be an
improvement-of-flatness statement on the half ball at radius `ρ ∈ (0, 1/4]` with constant `C₀`,
for functions satisfying `B`, with corrections in a class `K` closed under sums, scalar multiples
and rescalings. If `u ∈ C(B̄₁⁺) ∩ C²(B₁⁺)`, `P₀ ∈ K` has trace `σ`, `|u − P₀| ≤ 1` on `B₁⁺`,
`|Δu(z) − σ| ≤ ρ^γ/4 |z|^α`, and every rescaled error `(u − P)(ρⁿ ·)/(ρⁿ)^γ` with `P ∈ K`
satisfies `B`, then there is a quadratic `P` with `tr P = σ`,
`sumNorm P ≤ sumNorm P₀ + C₀/(1 − ρ^α)` and `|u(z) − P(z)| ≤ A |z|^γ` on `B₁⁺ ∩ {|z| < 1}`,
`A = (1 + C₀/(1 − ρ^α))/ρ^γ`. -/
theorem expansion_at_origin_halfBall {α ρ C₀ σ : ℝ} {ν : E} (hα : 0 < α ∧ α < 1)
    (hρ0 : 0 < ρ) (hρq : ρ ≤ 1 / 4) (hC₀ : 0 ≤ C₀)
    {K : QuadPoly E → Prop} (hKadd : ∀ P Q, K P → K Q → K (P + Q))
    (hKsmul : ∀ (c : ℝ) P, K P → K (c • P)) (hKresc : ∀ (c : ℝ) P, K P → K (P.rescale c))
    {B : (E → ℝ) → Prop}
    (hflat : ∀ {v : E → ℝ}, ContinuousOn v (halfBall ν 0 1) →
      ContDiffOn ℝ 2 v (ball 0 1 ∩ openHalfSpace ν) → (∀ z ∈ halfBall ν (0 : E) 1, |v z| ≤ 1) →
      (∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ v z| ≤ ρ ^ (2 + α) / 4) → B v →
      ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧ K Q ∧
        ∀ z ∈ halfBall ν (0 : E) ρ, |v z - Q.eval z| ≤ ρ ^ (2 + α))
    {u : E → ℝ} {P₀ : QuadPoly E} (hu : ContinuousOn u (halfBall ν 0 1))
    (hu2 : ContDiffOn ℝ 2 u (ball 0 1 ∩ openHalfSpace ν)) (hP₀ : P₀.trace = σ) (hK₀ : K P₀)
    (hu₀ : ∀ z ∈ halfBall ν (0 : E) 1, |u z - P₀.eval z| ≤ 1)
    (hH : ∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ u z - σ| ≤ ρ ^ (2 + α) / 4 * ‖z‖ ^ α)
    (hB : ∀ (n : ℕ) (P : QuadPoly E), K P →
      B fun y ↦ (u ((ρ ^ n) • y) - P.eval ((ρ ^ n) • y)) / (ρ ^ n) ^ (2 + α)) :
    ∃ P : QuadPoly E, P.trace = σ ∧ P.sumNorm ≤ P₀.sumNorm + C₀ / (1 - ρ ^ α) ∧
      ∀ z ∈ halfSpace ν, ‖z‖ < 1 →
        |u z - P.eval z| ≤ (1 + C₀ / (1 - ρ ^ α)) / ρ ^ (2 + α) * ‖z‖ ^ (2 + α) := by
  have hρ1 : ρ < 1 := by linarith
  have hρα1 : ρ ^ α < 1 := Real.rpow_lt_one hρ0.le hρ1 hα.1
  have h1r : 0 < 1 - ρ ^ α := by linarith
  have hγ0 : (0 : ℝ) < 2 + α := by linarith
  have hC₁ : 0 ≤ C₀ / (1 - ρ ^ α) := div_nonneg hC₀ h1r.le
  have hstep : ∀ (n : ℕ) (P : QuadPoly E), (P.trace = σ ∧ K P ∧
      ∀ z ∈ halfBall ν (0 : E) (ρ ^ n), |u z - P.eval z| ≤ (ρ ^ n) ^ (2 + α)) →
      ∃ Q : QuadPoly E, Q.trace = 0 ∧ Q.sumNorm ≤ C₀ ∧ K Q ∧
        ∀ z ∈ halfBall ν (0 : E) (ρ ^ (n + 1)),
          |u z - (P + ((ρ ^ n) ^ (2 + α)) • Q.rescale (ρ ^ n)⁻¹).eval z| ≤
            (ρ ^ (n + 1)) ^ (2 + α) :=
    fun n P hP ↦ iterate_step_halfBall hα.1.le hρ0 hρ1.le hflat hu hu2 hH n hP.1
      (hB n P hP.2.1) hP.2.2
  choose! Qf hQf using hstep
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → QuadPoly E, seq 0 = P₀ ∧ ∀ n,
      seq (n + 1) = seq n + ((ρ ^ n) ^ (2 + α)) • (Qf n (seq n)).rescale (ρ ^ n)⁻¹ :=
    ⟨fun n ↦ Nat.rec P₀
      (fun n P ↦ P + ((ρ ^ n) ^ (2 + α)) • (Qf n P).rescale (ρ ^ n)⁻¹) n,
      rfl, fun _ ↦ rfl⟩
  have hI : ∀ n, (seq n).trace = σ ∧ K (seq n) ∧
      ∀ z ∈ halfBall ν (0 : E) (ρ ^ n), |u z - (seq n).eval z| ≤ (ρ ^ n) ^ (2 + α) := by
    intro n
    induction n with
    | zero =>
      rw [hseq0]
      refine ⟨hP₀, hK₀, fun z hz ↦ ?_⟩
      rw [pow_zero, Real.one_rpow]
      exact hu₀ z (by simpa using hz)
    | succ n ih =>
      obtain ⟨hQs, -, hQK, hQb⟩ := hQf n (seq n) ih
      refine ⟨?_, ?_, ?_⟩
      · rw [hseqs, QuadPoly.trace_add, QuadPoly.trace_smul, QuadPoly.trace_rescale, hQs, ih.1]
        ring
      · rw [hseqs]; exact hKadd _ _ ih.2.1 (hKsmul _ _ (hKresc _ _ hQK))
      · rw [hseqs]; exact hQb
  obtain ⟨P', hP'tr, hP'c, hP'tail⟩ := exists_limit_poly hα.1 hρ0 hρ1 seq
    (fun n ↦ Qf n (seq n)) hseqs (fun n ↦ (hQf n _ (hI n)).2.1) (fun n ↦ (hI n).1)
  refine ⟨P', hP'tr, by rwa [hseq0] at hP'c, ?_⟩
  -- extend the error by zero off the half space and use the all-scales lemma
  set f : E → ℝ := fun z ↦ if 0 ≤ ⟪z, ν⟫ then u z - P'.eval z else 0 with hf
  have hall : ∀ n : ℕ, ∀ z ∈ ball (0 : E) (ρ ^ n),
      |f z| ≤ (1 + C₀ / (1 - ρ ^ α)) * (ρ ^ n) ^ (2 + α) := by
    intro n z hz
    by_cases hzh : 0 ≤ ⟪z, ν⟫
    · simp only [hf, hzh, ↓reduceIte]
      have a := (hI n).2.2 z ⟨ball_subset_closedBall hz, hzh⟩
      have b := hP'tail n z hz
      calc |u z - P'.eval z| ≤ |u z - (seq n).eval z| + |(seq n).eval z - P'.eval z| :=
            abs_sub_le _ _ _
        _ ≤ _ := by rw [add_mul, one_mul]; exact add_le_add a b
    · simp only [hf, hzh, ↓reduceIte, abs_zero]
      positivity
  intro z hzh hz
  have := abs_le_of_forall_scale hρ0 hρ1 hγ0 (by linarith) hall z hz
  simpa [hf, mem_halfSpace.1 hzh] using this

variable [Nontrivial E]

/-- **Neumann expansion at the origin.** For `α ∈ (0, 1)` there are `δ₀ > 0`, `C₁ ≥ 0`, `A ≥ 0`
(depending only on `E` and `α`) such that: if `‖ν‖ = 1`, `u ∈ C(B̄₁⁺) ∩ C²(B₁⁺)`, `P₀` is even
with trace `σ`, `|u − P₀| ≤ 1` on `B₁⁺`, `|Δu(z) − σ| ≤ δ₀ |z|^α` in the open half ball and the
inward normal derivative satisfies `|∂_ν u(z)| ≤ δ₀ |z|^{1+α}` at flat points of `B₁`, then there
is a quadratic `P` with `tr P = σ`, `sumNorm P ≤ sumNorm P₀ + C₁` and `|u(z) − P(z)| ≤ A |z|^{2+α}`
for `z ∈ halfSpace ν`, `|z| < 1`. -/
theorem expansion_at_origin_neumann {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ δ₀ C₁ A : ℝ, 0 < δ₀ ∧ 0 ≤ C₁ ∧ 0 ≤ A ∧ ∀ {ν : E}, ‖ν‖ = 1 →
      ∀ {u : E → ℝ} {σ : ℝ} {P₀ : QuadPoly E},
      ContinuousOn u (halfBall ν 0 1) → ContDiffOn ℝ 2 u (ball 0 1 ∩ openHalfSpace ν) →
      P₀.trace = σ → IsEvenPoly ν P₀ →
      (∀ z ∈ halfBall ν (0 : E) 1, |u z - P₀.eval z| ≤ 1) →
      (∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ u z - σ| ≤ δ₀ * ‖z‖ ^ α) →
      (∀ z ∈ ball (0 : E) 1, z ∈ flatPart ν → ∃ d : ℝ,
        HasDerivWithinAt (fun t : ℝ ↦ u (z + t • ν)) d (Ici 0) 0 ∧
          |d| ≤ δ₀ * ‖z‖ ^ (1 + α)) →
      ∃ P : QuadPoly E, P.trace = σ ∧ P.sumNorm ≤ P₀.sumNorm + C₁ ∧
        ∀ z ∈ halfSpace ν, ‖z‖ < 1 → |u z - P.eval z| ≤ A * ‖z‖ ^ (2 + α) := by
  obtain ⟨ρ, C₀, hρ0, hρq, hC₀, hflat⟩ := improvement_of_flatness_neumann (E := E) hα
  have hρ1 : ρ < 1 := by linarith
  have hρα1 : ρ ^ α < 1 := Real.rpow_lt_one hρ0.le hρ1 hα.1
  have h1r : 0 < 1 - ρ ^ α := by linarith
  have hργ : 0 < ρ ^ (2 + α) := Real.rpow_pos_of_pos hρ0 _
  have hC₁ : 0 ≤ C₀ / (1 - ρ ^ α) := div_nonneg hC₀ h1r.le
  refine ⟨ρ ^ (2 + α) / 4, C₀ / (1 - ρ ^ α), (1 + C₀ / (1 - ρ ^ α)) / ρ ^ (2 + α),
    by positivity, hC₁, div_nonneg (by linarith) hργ.le, ?_⟩
  intro ν hν u σ P₀ hu hu2 hP₀ hK₀ hu₀ hH hN
  refine expansion_at_origin_halfBall hα hρ0 hρq hC₀ (K := IsEvenPoly ν)
    (fun P Q hP hQ ↦ hP.add hQ) (fun c P hP ↦ hP.smul c) (fun c P hP ↦ hP.rescale c)
    (B := fun v ↦ ∀ z ∈ ball (0 : E) 1, z ∈ flatPart ν → ∃ d : ℝ,
      HasDerivWithinAt (fun t : ℝ ↦ v (z + t • ν)) d (Ici 0) 0 ∧ |d| ≤ ρ ^ (2 + α) / 4)
    (fun hv hv2 hv1 hvΔ hvB ↦ hflat hν hv hv2 hv1 hvΔ hvB) hu hu2 hP₀ hK₀ hu₀ hH ?_
  intro n P hP z hz hzf
  set r : ℝ := ρ ^ n with hr
  have hr0 : 0 < r := pow_pos hρ0 n
  have hr1 : r ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  have hrγ : 0 < r ^ (2 + α) := Real.rpow_pos_of_pos hr0 _
  have hrz : r • z ∈ ball (0 : E) 1 := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    calc r * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact mem_ball_zero_iff.1 hz
  have hrzf : r • z ∈ flatPart ν := by
    simp only [mem_flatPart, real_inner_smul_left, mem_flatPart.1 hzf, mul_zero]
  obtain ⟨d, hd, hdb⟩ := hN _ hrz hrzf
  have hPd := (hP.hasDerivAt_line hν hrzf).hasDerivWithinAt (s := Ici (0 : ℝ))
  have hdiff := hd.sub hPd
  -- compose with `t ↦ r t`
  have hlin : HasDerivWithinAt (fun t : ℝ ↦ r * t) r (Ici 0) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r |>.hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ ↦ r * t) (Ici 0) (Ici 0) := fun t ht ↦
    mul_nonneg hr0.le ht
  have hdiff0 : HasDerivWithinAt (fun t : ℝ ↦ u (r • z + t • ν) - P.eval (r • z + t • ν))
      (d - 0) (Ici 0) (r * 0) := by rw [mul_zero]; exact hdiff
  have hcomp := (hdiff0.comp (0 : ℝ) hlin hmaps).div_const (r ^ (2 + α))
  refine ⟨(d - 0) * r / r ^ (2 + α), ?_, ?_⟩
  · convert hcomp using 2 with t
    simp only [Function.comp_apply, smul_add, smul_smul]
  · -- the bound
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    have hrzn : ‖r • z‖ = r * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    rw [hrzn, Real.mul_rpow hr0.le (norm_nonneg _)] at hdb
    have hzα : ‖z‖ ^ (1 + α) ≤ 1 := Real.rpow_le_one (norm_nonneg _) hz1 (by linarith)
    have e : r * r ^ (1 + α) = r ^ (2 + α) := by
      rw [show (2 : ℝ) + α = 1 + (1 + α) by ring, Real.rpow_add hr0 1 (1 + α), Real.rpow_one]
    rw [sub_zero, abs_div, abs_mul, abs_of_pos hr0, abs_of_pos hrγ, div_le_iff₀ hrγ]
    calc |d| * r ≤ ρ ^ (2 + α) / 4 * (r ^ (1 + α) * ‖z‖ ^ (1 + α)) * r := by gcongr
      _ = ρ ^ (2 + α) / 4 * ‖z‖ ^ (1 + α) * (r * r ^ (1 + α)) := by ring
      _ ≤ ρ ^ (2 + α) / 4 * 1 * (r * r ^ (1 + α)) := by gcongr
      _ = ρ ^ (2 + α) / 4 * r ^ (2 + α) := by rw [e, mul_one]

/-- **Dirichlet expansion at the origin.** For `α ∈ (0, 1)` there are `δ₀ > 0`, `C₁ ≥ 0`,
`A ≥ 0` (depending only on `E` and `α`) such that: if `‖ν‖ = 1`, `u ∈ C(B̄₁⁺) ∩ C²(B₁⁺)` with
`u = 0` on the flat part, `P₀` vanishes on the flat part and has trace `σ`, `|u − P₀| ≤ 1` on
`B₁⁺` and `|Δu(z) − σ| ≤ δ₀ |z|^α` in the open half ball, then there is a quadratic `P` with
`tr P = σ`, `sumNorm P ≤ sumNorm P₀ + C₁` and `|u(z) − P(z)| ≤ A |z|^{2+α}` for
`z ∈ halfSpace ν`, `|z| < 1`. -/
theorem expansion_at_origin_dirichlet {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ∃ δ₀ C₁ A : ℝ, 0 < δ₀ ∧ 0 ≤ C₁ ∧ 0 ≤ A ∧ ∀ {ν : E}, ‖ν‖ = 1 →
      ∀ {u : E → ℝ} {σ : ℝ} {P₀ : QuadPoly E},
      ContinuousOn u (halfBall ν 0 1) → ContDiffOn ℝ 2 u (ball 0 1 ∩ openHalfSpace ν) →
      P₀.trace = σ → VanishesOnFlat ν P₀ →
      (∀ z ∈ halfBall ν (0 : E) 1, |u z - P₀.eval z| ≤ 1) →
      (∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ u z - σ| ≤ δ₀ * ‖z‖ ^ α) →
      (∀ z ∈ halfBall ν (0 : E) 1, z ∈ flatPart ν → u z = 0) →
      ∃ P : QuadPoly E, P.trace = σ ∧ P.sumNorm ≤ P₀.sumNorm + C₁ ∧
        ∀ z ∈ halfSpace ν, ‖z‖ < 1 → |u z - P.eval z| ≤ A * ‖z‖ ^ (2 + α) := by
  obtain ⟨ρ, C₀, hρ0, hρq, hC₀, hflat⟩ := improvement_of_flatness_dirichlet (E := E) hα
  have hρ1 : ρ < 1 := by linarith
  have hρα1 : ρ ^ α < 1 := Real.rpow_lt_one hρ0.le hρ1 hα.1
  have h1r : 0 < 1 - ρ ^ α := by linarith
  have hργ : 0 < ρ ^ (2 + α) := Real.rpow_pos_of_pos hρ0 _
  have hC₁ : 0 ≤ C₀ / (1 - ρ ^ α) := div_nonneg hC₀ h1r.le
  refine ⟨ρ ^ (2 + α) / 4, C₀ / (1 - ρ ^ α), (1 + C₀ / (1 - ρ ^ α)) / ρ ^ (2 + α),
    by positivity, hC₁, div_nonneg (by linarith) hργ.le, ?_⟩
  intro ν hν u σ P₀ hu hu2 hP₀ hK₀ hu₀ hH hD
  refine expansion_at_origin_halfBall hα hρ0 hρq hC₀ (K := VanishesOnFlat ν)
    (fun P Q hP hQ ↦ hP.add hQ) (fun c P hP ↦ hP.smul c) (fun c P hP ↦ hP.rescale c)
    (B := fun v ↦ ∀ z ∈ halfBall ν (0 : E) 1, z ∈ flatPart ν → v z = 0)
    (fun hv hv2 hv1 hvΔ hvB ↦ hflat hν hv hv2 hv1 hvΔ hvB) hu hu2 hP₀ hK₀ hu₀ hH ?_
  intro n P hP z hz hzf
  have hr0 : 0 < ρ ^ n := pow_pos hρ0 n
  have hr1 : ρ ^ n ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  have hrz : (ρ ^ n) • z ∈ halfBall ν (0 : E) 1 :=
    halfBall_mono ν 0 (by simpa using hr1) (smul_mem_halfBall hr0 hz)
  have hrzf : (ρ ^ n) • z ∈ flatPart ν := by
    simp only [mem_flatPart, real_inner_smul_left, mem_flatPart.1 hzf, mul_zero]
  simp only [hD _ hrz hrzf, hP _ hrzf, sub_self, zero_div]

end Nondiv

end BasicElliptic
