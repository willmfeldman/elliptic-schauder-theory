/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Poly.Quadratic
public import BasicElliptic.Basic.HalfSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Coefficient extraction for quadratic polynomials, and the two-expansion comparison

* `QuadPoly.coeff_bound`: if `|P| ≤ ε` on a set `T` containing the origin and a ball `ball y t`,
  then `|const| ≤ ε`, `‖hess‖ ≤ 32 ε / t²` and `‖lin‖ ≤ 2 ε / t + ‖hess‖ ‖y‖` (finite differences
  inside the ball; the ball need not be centred at the origin, which is what makes one-sided
  expansions usable).
* `QuadPoly.two_expansions`: two order-`γ` expansions (`γ ≤ 3`) of the same function `u` on a set
  `S`, at points `p, p'` with `δ = dist p p'`, differ after recentring by at most `9 A δ^γ` on
  `{z | p' + z ∈ S, ‖z‖ ≤ δ}`; `QuadPoly.two_expansions_coeff` extracts the coefficient bounds
  from an interior ball of radius `κ δ` of `S ∩ closedBall p' δ`.

## Provenance

Elliptic, coordinate-free adaptation of `CaloricPoly.coeff_bound`, `eq_zero_of_abs_eval_le`,
`two_expansions`, `two_expansions_coeff` in parabolic-basic-theory,
`ParabolicBasic/Schauder/PolyExtract.lean` (own repository, commit
`2507d9a800377e91c591862286b2ba2d6464d918`). Changes: `pdist` → `dist`; coordinate second
differences → polarization of `hess`; extraction on an arbitrary ball inside the set instead of
the centred cylinder (needed for half balls and closed regions).
-/

@[expose] public section

open Set Metric Filter Topology RealInnerProductSpace

namespace BasicElliptic

namespace QuadPoly

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The restriction of `P` to the line `σ ↦ y + σ v`. -/
theorem eval_add_smul (P : QuadPoly E) (y v : E) (σ : ℝ) :
    P.eval (y + σ • v) =
      P.eval y + σ * (P.lin v + P.hess y v) + (1 / 2 : ℝ) * σ ^ 2 * P.hess v v := by
  simp only [eval_eq_hess, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [P.hess_comm v y]; ring

/-- Second and first differences along a unit-ball direction inside `ball y t`. -/
theorem abs_hess_self_le {P : QuadPoly E} {y : E} {t ε : ℝ} (ht : 0 < t)
    (h : ∀ z ∈ ball y t, |P.eval z| ≤ ε) {v : E} (hv : ‖v‖ ≤ 1) :
    |P.hess v v| ≤ 16 * ε / t ^ 2 ∧ |P.lin v + P.hess y v| ≤ 2 * ε / t := by
  set s := t / 2 with hs
  have hs0 : 0 < s := by positivity
  have hmem : ∀ σ : ℝ, |σ| ≤ s → y + σ • v ∈ ball y t := by
    intro σ hσ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |σ| * ‖v‖ ≤ s * 1 := by gcongr
      _ < t := by rw [hs]; linarith
  have h1 := abs_le.1 (h _ (hmem s (by rw [abs_of_pos hs0])))
  have h2 := abs_le.1 (h _ (hmem (-s) (by rw [abs_neg, abs_of_pos hs0])))
  have h0 := abs_le.1 (h y (mem_ball_self ht))
  rw [eval_add_smul] at h1 h2
  constructor
  · rw [show 16 * ε / t ^ 2 = 4 * ε / s ^ 2 by rw [hs]; field_simp; ring,
      le_div_iff₀ (by positivity), ← abs_of_pos (by positivity : (0 : ℝ) < s ^ 2), ← abs_mul,
      abs_le]
    constructor <;> nlinarith
  · rw [show 2 * ε / t = ε / s by rw [hs]; field_simp, le_div_iff₀ hs0,
      ← abs_of_pos hs0, ← abs_mul, abs_le]
    constructor <;> nlinarith

/-- **Hessian extraction.** -/
theorem norm_hess_le {P : QuadPoly E} {y : E} {t ε : ℝ} (ht : 0 < t)
    (h : ∀ z ∈ ball y t, |P.eval z| ≤ ε) : ‖P.hess‖ ≤ 32 * ε / t ^ 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (h y (mem_ball_self ht))
  have hC : 0 ≤ 32 * ε / t ^ 2 := by positivity
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun v hv ↦ ?_
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun w hw ↦ ?_
  set a : E := (1 / 2 : ℝ) • (v + w)
  set b : E := (1 / 2 : ℝ) • (v - w)
  have hnorm : ∀ x : E, ‖x‖ ≤ 2 → ‖(1 / 2 : ℝ) • x‖ ≤ 1 := fun x hx ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]; linarith
  have ha : ‖a‖ ≤ 1 := hnorm _ ((norm_add_le _ _).trans (by rw [hv, hw]; norm_num))
  have hb : ‖b‖ ≤ 1 := hnorm _ ((norm_sub_le _ _).trans (by rw [hv, hw]; norm_num))
  have key : P.hess v w = P.hess a a - P.hess b b := by
    simp only [a, b, map_smul, map_add, map_sub, add_apply,
      sub_apply, smul_apply, smul_eq_mul]
    rw [P.hess_comm w v]; ring
  rw [Real.norm_eq_abs, key]
  calc |P.hess a a - P.hess b b| ≤ |P.hess a a| + |P.hess b b| := abs_sub _ _
    _ ≤ 16 * ε / t ^ 2 + 16 * ε / t ^ 2 :=
        add_le_add (abs_hess_self_le ht h ha).1 (abs_hess_self_le ht h hb).1
    _ = 32 * ε / t ^ 2 := by ring

/-- **Gradient extraction.** -/
theorem norm_lin_le {P : QuadPoly E} {y : E} {t ε : ℝ} (ht : 0 < t)
    (h : ∀ z ∈ ball y t, |P.eval z| ≤ ε) : ‖P.lin‖ ≤ 2 * ε / t + ‖P.hess‖ * ‖y‖ := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (h y (mem_ball_self ht))
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv ↦ ?_
  rw [Real.norm_eq_abs]
  have h1 := (abs_hess_self_le ht h hv.le).2
  have h2 : |P.hess y v| ≤ ‖P.hess‖ * ‖y‖ := by
    have := P.hess.le_opNorm₂ y v
    rw [hv, mul_one, Real.norm_eq_abs] at this
    exact this
  calc |P.lin v| = |(P.lin v + P.hess y v) - P.hess y v| := by ring_nf
    _ ≤ |P.lin v + P.hess y v| + |P.hess y v| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-- **Coefficient extraction** on a set `T` containing the origin and a ball `ball y t`. -/
theorem coeff_bound {P : QuadPoly E} {T : Set E} {y : E} {t ε : ℝ} (ht : 0 < t) (h0 : 0 ∈ T)
    (hT : ball y t ⊆ T) (h : ∀ z ∈ T, |P.eval z| ≤ ε) :
    |P.const| ≤ ε ∧ ‖P.hess‖ ≤ 32 * ε / t ^ 2 ∧ ‖P.lin‖ ≤ 2 * ε / t + ‖P.hess‖ * ‖y‖ := by
  have h' : ∀ z ∈ ball y t, |P.eval z| ≤ ε := fun z hz ↦ h z (hT hz)
  exact ⟨by simpa using h 0 h0, norm_hess_le ht h', norm_lin_le ht h'⟩

/-- **Two expansions.** Two order-`γ` expansions (`0 ≤ γ ≤ 3`) of `u` on `S`, at `p` and `p'`
with `2 dist p p' < ρ₀`, differ after recentring by at most `9 A δ^γ`, `δ = dist p p'`, on the
part of `S - p'` in `closedBall 0 δ`. -/
theorem two_expansions {S : Set E} {u : E → ℝ} {P Q : QuadPoly E} {p p' : E} {γ A ρ₀ : ℝ}
    (hγ : 0 ≤ γ) (hγ3 : γ ≤ 3) (hA : 0 ≤ A)
    (hP : ∀ q ∈ S, dist q p < ρ₀ → |u q - P.eval (q - p)| ≤ A * dist q p ^ γ)
    (hQ : ∀ q ∈ S, dist q p' < ρ₀ → |u q - Q.eval (q - p')| ≤ A * dist q p' ^ γ)
    (hδ : 2 * dist p p' < ρ₀) :
    ∀ z, p' + z ∈ S → ‖z‖ ≤ dist p p' →
      |(P.shift (p' - p) - Q).eval z| ≤ 9 * A * dist p p' ^ γ := by
  intro z hz hzδ
  set δ := dist p p'
  set q := p' + z with hqdef
  have hq' : dist q p' = ‖z‖ := by simp [q, dist_eq_norm]
  have hδ0 : 0 ≤ δ := dist_nonneg
  have hqp : dist q p ≤ 2 * δ := by
    calc dist q p ≤ dist q p' + dist p' p := dist_triangle _ _ _
      _ ≤ δ + δ := by rw [dist_comm p' p, hq']; linarith
      _ = 2 * δ := by ring
  have e1 := hP q hz (by linarith)
  have e2 := hQ q hz (by rw [hq']; linarith)
  have hqp' : q - p' = z := by simp [q]
  have hqp2 : q - p = z + (p' - p) := by simp only [q]; abel
  rw [hqp'] at e2
  rw [hqp2] at e1
  rw [eval_sub, eval_shift]
  have hpow1 : dist q p ^ γ ≤ (2 * δ) ^ γ := Real.rpow_le_rpow dist_nonneg hqp hγ
  have hpow2 : dist q p' ^ γ ≤ δ ^ γ :=
    Real.rpow_le_rpow dist_nonneg (by rw [hq']; exact hzδ) hγ
  have h2γ : (2 * δ) ^ γ ≤ 8 * δ ^ γ := by
    rw [Real.mul_rpow (by norm_num) hδ0]
    gcongr
    calc (2 : ℝ) ^ γ ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ3
      _ = 8 := by rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]; norm_num
  calc |P.eval (z + (p' - p)) - Q.eval z|
      ≤ |u q - P.eval (z + (p' - p))| + |u q - Q.eval z| := by
        have := abs_sub_le (P.eval (z + (p' - p))) (u q) (Q.eval z)
        rwa [abs_sub_comm (P.eval (z + (p' - p))) (u q)] at this
    _ ≤ A * dist q p ^ γ + A * dist q p' ^ γ := add_le_add e1 e2
    _ ≤ A * (8 * δ ^ γ) + A * δ ^ γ := by gcongr; exact hpow1.trans h2γ
    _ = 9 * A * δ ^ γ := by ring

/-- **Two expansions, coefficient form.** If moreover `S` contains a ball `ball y (κ δ)` inside
`closedBall p' δ`, then `‖D²P - D²Q‖ ≤ (288/κ²) A δ^{γ-2}` and
`‖DP(p' - p) - DQ(0)‖ ≤ (18/κ + 288/κ²) A δ^{γ-1}`. -/
theorem two_expansions_coeff {S : Set E} {u : E → ℝ} {P Q : QuadPoly E} {p p' : E}
    {γ A ρ₀ κ : ℝ} {y : E} (hγ : 0 ≤ γ) (hγ3 : γ ≤ 3) (hA : 0 ≤ A)
    (hP : ∀ q ∈ S, dist q p < ρ₀ → |u q - P.eval (q - p)| ≤ A * dist q p ^ γ)
    (hQ : ∀ q ∈ S, dist q p' < ρ₀ → |u q - Q.eval (q - p')| ≤ A * dist q p' ^ γ)
    (hδ : 2 * dist p p' < ρ₀) (hp' : p' ∈ S) (hκ : 0 < κ) (hδ0 : 0 < dist p p')
    (hy : ball y (κ * dist p p') ⊆ S) (hyp : dist y p' + κ * dist p p' ≤ dist p p') :
    ‖P.hess - Q.hess‖ ≤ 288 / κ ^ 2 * A * dist p p' ^ (γ - 2) ∧
      ‖P.lin + P.hess (p' - p) - Q.lin‖ ≤ (18 / κ + 288 / κ ^ 2) * A * dist p p' ^ (γ - 1) := by
  set δ := dist p p' with hδdef
  have hR := two_expansions hγ hγ3 hA hP hQ hδ
  set T : Set E := {z | p' + z ∈ S ∧ ‖z‖ ≤ δ}
  have h0 : (0 : E) ∈ T := ⟨by simpa using hp', by simp [hδ0.le]⟩
  have hball : ball (y - p') (κ * δ) ⊆ T := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    refine ⟨hy ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, show p' + z - y = z - (y - p') by abel]; exact hz
    · calc ‖z‖ = ‖(z - (y - p')) + (y - p')‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - (y - p')‖ + ‖y - p'‖ := norm_add_le _ _
        _ ≤ δ := by rw [← dist_eq_norm y p']; linarith
  obtain ⟨-, hH, hL⟩ := coeff_bound (by positivity) h0 hball fun z hz ↦ hR z hz.1 hz.2
  have hyn : ‖y - p'‖ ≤ δ := by
    rw [← dist_eq_norm]; nlinarith [mul_pos hκ hδ0]
  simp only [hess_sub, hess_shift, sub_lin, shift_lin] at hH hL
  have e2 : δ ^ (γ - 2) = δ ^ γ / δ ^ 2 := by rw [Real.rpow_sub hδ0, Real.rpow_two]
  have e1 : δ ^ (γ - 1) = δ ^ γ / δ := by rw [Real.rpow_sub hδ0, Real.rpow_one]
  have hX : 0 ≤ δ ^ γ := Real.rpow_nonneg hδ0.le _
  have hH' : ‖P.hess - Q.hess‖ ≤ 288 / κ ^ 2 * A * δ ^ (γ - 2) := by
    refine hH.trans_eq ?_
    rw [e2]; field_simp; ring
  refine ⟨hH', ?_⟩
  calc ‖P.lin + P.hess (p' - p) - Q.lin‖
      ≤ 2 * (9 * A * δ ^ γ) / (κ * δ) + ‖P.hess - Q.hess‖ * ‖y - p'‖ := hL
    _ ≤ 2 * (9 * A * δ ^ γ) / (κ * δ) + 288 / κ ^ 2 * A * δ ^ (γ - 2) * δ := by
        gcongr
    _ = (18 / κ + 288 / κ ^ 2) * A * δ ^ (γ - 1) := by
        rw [e1, e2]; field_simp; ring

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Inner

end QuadPoly

end BasicElliptic
