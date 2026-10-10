/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Interior.Freeze
public import BasicElliptic.Poly.Extract
public import BasicElliptic.Holder.Algebra

/-!
# Tools for the scaled nondivergence estimate

* `Nondiv.fderiv_fderiv_eq_hess_of_expansion`: if `w` is `C²` at `x₀` and a quadratic `P`
  satisfies `|w(y) − P(y − x₀)| ≤ A |y − x₀|^γ` near `x₀` with `γ > 2`, then
  `D²w(x₀) = hess P`. (The second-order difference quotient
  `Convex.isLittleO_alternate_sum_square` identifies `D²w(x₀)(v, v)`; polarization.)
* `Nondiv.norm_fderiv_le_of_osc` (interpolation): `‖Dw(y₀)‖ ≤ O / s + M s` if `|w − w(y₀)| ≤ O`
  and `‖D²w‖ ≤ M` on `closedBall y₀ s`.
* `Nondiv.abs_sub_le_regionOsc`: `|w y − w y'| ≤ osc_S w` for `w` continuous on a compact `S`.
-/

public section

open Metric Set Filter Topology Module Asymptotics ContinuousLinearMap
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Identification of the Hessian -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A function bounded by `B h^γ` (`γ > 2`) near `0⁺` is `o(h²)`. -/
private theorem isLittleO_sq_of_abs_le_rpow {φ : ℝ → ℝ} {B γ : ℝ} (hγ : 2 < γ)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), |φ t| ≤ B * t ^ γ) :
    φ =o[𝓝[>] (0 : ℝ)] fun t ↦ t ^ 2 := by
  have h1 : φ =O[𝓝[>] (0 : ℝ)] fun t ↦ t ^ γ := by
    refine IsBigO.of_bound B ?_
    filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
    exact ht
  have h2 : (fun t : ℝ ↦ t ^ γ) =o[𝓝[>] (0 : ℝ)] fun t ↦ t ^ 2 := by
    have hlim : Tendsto (fun t : ℝ ↦ t ^ (γ - 2)) (𝓝[>] 0) (𝓝 0) := by
      have : ContinuousAt (fun t : ℝ ↦ t ^ (γ - 2)) 0 :=
        Real.continuousAt_rpow_const 0 (γ - 2) (Or.inr (by linarith))
      simpa [Real.zero_rpow (by linarith : γ - 2 ≠ 0)] using
        this.tendsto.mono_left nhdsWithin_le_nhds
    have h3 : (fun t : ℝ ↦ t ^ (γ - 2)) =o[𝓝[>] (0 : ℝ)] fun _ ↦ (1 : ℝ) :=
      (isLittleO_one_iff ℝ).2 hlim
    have h4 := (isBigO_refl (fun t : ℝ ↦ t ^ 2) (𝓝[>] (0 : ℝ))).mul_isLittleO h3
    refine (h4.congr' ?_ ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← Real.rpow_two, ← Real.rpow_add (mem_Ioi.1 ht)]
      ring_nf
    · simp
  exact h1.trans_isLittleO h2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem eq_zero_of_isLittleO_sq {c : ℝ}
    (h : (fun t : ℝ ↦ t ^ 2 * c) =o[𝓝[>] (0 : ℝ)] fun t ↦ t ^ 2) : c = 0 := by
  have h1 := h.tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ ↦ t ^ 2 * c / t ^ 2) (𝓝[>] 0) (𝓝 c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have : t ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
    change c = t ^ 2 * c / t ^ 2
    rw [mul_div_right_comm, div_self this, one_mul]
  exact tendsto_nhds_unique h2 h1

omit [FiniteDimensional ℝ E] in
/-- **Identification of the Hessian.** If `w` is `C²` at `x₀` and
`|w(y) − P(y − x₀)| ≤ A |y − x₀|^γ` for `|y − x₀| < ρ₀`, with `γ > 2`, then
`D²w(x₀) = hess P`. -/
theorem fderiv_fderiv_eq_hess_of_expansion {w : E → ℝ} {x₀ : E} {P : QuadPoly E}
    {A ρ₀ γ : ℝ} (hγ : 2 < γ) (hρ₀ : 0 < ρ₀) (hw : ContDiffAt ℝ 2 w x₀)
    (hP : ∀ y, dist y x₀ < ρ₀ → |w y - P.eval (y - x₀)| ≤ A * dist y x₀ ^ γ) :
    fderiv ℝ (fderiv ℝ w) x₀ = P.hess := by
  set B := fderiv ℝ (fderiv ℝ w) x₀ with hBdef
  -- a ball on which `w` is `C²`
  obtain ⟨ρ₁, hρ₁, hρ₁w⟩ := Metric.eventually_nhds_iff_ball.1 (hw.eventually (by simp))
  set ρ := min ρ₁ ρ₀ with hρ
  have hρ0 : 0 < ρ := lt_min hρ₁ hρ₀
  have hf : ∀ y ∈ interior (ball x₀ ρ), HasFDerivAt w (fderiv ℝ w y) y := fun y hy ↦ by
    rw [interior_eq_iff_isOpen.2 isOpen_ball] at hy
    exact ((hρ₁w y (ball_subset_ball (min_le_left _ _) hy)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hx : HasFDerivWithinAt (fderiv ℝ w) B (interior (ball x₀ ρ)) x₀ :=
    ((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
      |>.hasFDerivWithinAt
  -- the diagonal values agree for small `v`
  have hdiag : ∀ v : E, ‖v‖ < ρ / 4 → B v v = P.hess v v := by
    intro v hv
    have h4v : x₀ + (4 : ℝ) • v ∈ interior (ball x₀ ρ) := by
      rw [interior_eq_iff_isOpen.2 isOpen_ball, mem_ball, dist_eq_norm, add_sub_cancel_left,
        norm_smul]
      norm_num; linarith
    have hL := (convex_ball x₀ ρ).isLittleO_alternate_sum_square hf (mem_ball_self hρ0) hx
      h4v h4v
    -- the remainders `w(x₀ + t u) − P(t u)`
    have hrem : ∀ c : ℝ, 0 ≤ c → c ≤ 4 →
        (fun t : ℝ ↦ w (x₀ + t • (c • v)) - P.eval (t • (c • v))) =o[𝓝[>] (0 : ℝ)]
          fun t ↦ t ^ 2 := by
      intro c hc0 hc4
      refine isLittleO_sq_of_abs_le_rpow (B := A * (c * ‖v‖) ^ γ) hγ ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      have hd : dist (x₀ + t • (c • v)) x₀ = t * (c * ‖v‖) := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos ht.1, abs_of_nonneg hc0]
      have hlt : dist (x₀ + t • (c • v)) x₀ < ρ₀ := by
        rw [hd]
        have : c * ‖v‖ < ρ₀ := by
          have := min_le_right ρ₁ ρ₀
          nlinarith [norm_nonneg v]
        nlinarith [ht.1, ht.2, norm_nonneg v]
      have := hP _ hlt
      rw [add_sub_cancel_left] at this
      rw [hd, Real.mul_rpow ht.1.le (by positivity)] at this
      calc _ ≤ A * (t ^ γ * (c * ‖v‖) ^ γ) := this
        _ = A * (c * ‖v‖) ^ γ * t ^ γ := by ring
    have h4 := hrem 4 (by norm_num) le_rfl
    have h2 := hrem 2 (by norm_num) (by norm_num)
    have h3 := hrem 3 (by norm_num) (by norm_num)
    -- the polynomial part of the alternate sum
    have hpoly : ∀ t : ℝ, P.eval (t • ((4 : ℝ) • v)) + P.eval (t • ((2 : ℝ) • v)) -
        P.eval (t • ((3 : ℝ) • v)) - P.eval (t • ((3 : ℝ) • v)) = t ^ 2 * P.quad v v := by
      intro t
      simp only [QuadPoly.eval, map_smul, smul_apply, smul_eq_mul]
      ring
    have hsum : (fun t : ℝ ↦ t ^ 2 * (P.quad v v - B v v)) =o[𝓝[>] (0 : ℝ)] fun t ↦ t ^ 2 := by
      have := ((hL.sub h4).sub h2).add (h3.add h3)
      refine this.congr' (Eventually.of_forall fun t ↦ ?_) EventuallyEq.rfl
      have e1 : t • ((2 : ℕ) • v + (2 : ℕ) • v) = t • ((4 : ℝ) • v) := by
        congr 1; rw [← add_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]; norm_num
      have e2 : t • (v + v) = t • ((2 : ℝ) • v) := by rw [two_smul]
      have e3 : t • ((2 : ℕ) • v + v) = t • ((3 : ℝ) • v) := by
        congr 1; rw [← Nat.cast_smul_eq_nsmul ℝ]; module
      have e4 : t • (v + (2 : ℕ) • v) = t • ((3 : ℝ) • v) := by
        congr 1; rw [← Nat.cast_smul_eq_nsmul ℝ]; module
      simp only [e1, e2, e3, e4, smul_eq_mul]
      have := hpoly t
      linear_combination this
    have := eq_zero_of_isLittleO_sq hsum
    rw [QuadPoly.hess_self]
    linarith
  -- symmetry and polarization
  have hBs : ∀ v v', B v v' = B v' v := fderiv_fderiv_comm hw
  have hdiag' : ∀ v : E, B v v = P.hess v v := by
    intro v
    obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ‖c • v‖ < ρ / 4 := by
      refine ⟨ρ / (8 * (‖v‖ + 1)), by positivity, ?_⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    have := hdiag _ hc
    simp only [map_smul, smul_apply, smul_eq_mul] at this
    have hc2 : c * c ≠ 0 := by positivity
    have : c * c * B v v = c * c * P.hess v v := by linarith
    exact mul_left_cancel₀ hc2 this
  ext v v'
  have h1 := hdiag' (v + v')
  simp only [map_add, add_apply] at h1
  rw [hdiag' v, hdiag' v', hBs v' v, P.hess_comm v' v] at h1
  linarith

/-! ### Interpolation and oscillation -/

omit [FiniteDimensional ℝ E] in
/-- **Mean value bound for `Dw`.** -/
theorem norm_fderiv_sub_le_of_closedBall {U : Set E} (hU : IsOpen U) {w : E → ℝ}
    (hw : ContDiffOn ℝ 2 w U) {y₀ : E} {s M : ℝ} (hBU : closedBall y₀ s ⊆ U)
    (hM : ∀ y ∈ closedBall y₀ s, ‖iteratedFDeriv ℝ 2 w y‖ ≤ M) :
    ∀ y ∈ closedBall y₀ s, ‖fderiv ℝ w y - fderiv ℝ w y₀‖ ≤ M * ‖y - y₀‖ := by
  intro y hy
  have hy₀ : y₀ ∈ closedBall y₀ s := mem_closedBall_self (dist_nonneg.trans (mem_closedBall.1 hy))
  have hC2 : ∀ z ∈ closedBall y₀ s, ContDiffAt ℝ 2 w z := fun z hz ↦
    hw.contDiffAt (hU.mem_nhds (hBU hz))
  exact (convex_closedBall y₀ s).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ ((hC2 z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (fun z hz ↦ by rw [norm_fderiv_fderiv_eq]; exact hM z hz) hy₀ hy

omit [FiniteDimensional ℝ E] in
/-- **Interpolation.** If `w ∈ C²(U)`, `closedBall y₀ s ⊆ U`, `|w − w(y₀)| ≤ O` and
`‖D²w‖ ≤ M` on `closedBall y₀ s`, then `‖Dw(y₀)‖ ≤ O / s + M s`. -/
theorem norm_fderiv_le_of_osc {U : Set E} (hU : IsOpen U) {w : E → ℝ}
    (hw : ContDiffOn ℝ 2 w U) {y₀ : E} {s O M : ℝ} (hs : 0 < s) (hBU : closedBall y₀ s ⊆ U)
    (hO : ∀ y ∈ closedBall y₀ s, |w y - w y₀| ≤ O)
    (hM : ∀ y ∈ closedBall y₀ s, ‖iteratedFDeriv ℝ 2 w y‖ ≤ M) :
    ‖fderiv ℝ w y₀‖ ≤ O / s + M * s := by
  have hy₀ : y₀ ∈ closedBall y₀ s := mem_closedBall_self hs.le
  have hO0 : 0 ≤ O := by simpa using hO y₀ hy₀
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y₀ hy₀)
  set L := fderiv ℝ w y₀
  have hmv := norm_fderiv_sub_le_of_closedBall hU hw hBU hM
  have hC2 : ∀ z ∈ closedBall y₀ s, ContDiffAt ℝ 2 w z := fun z hz ↦
    hw.contDiffAt (hU.mem_nhds (hBU hz))
  -- `ψ y = w y − L (y − y₀)` has small derivative on the ball
  have hψ : ∀ z ∈ closedBall y₀ s, HasFDerivWithinAt (fun y ↦ w y - L (y - y₀))
      (fderiv ℝ w z - L) (closedBall y₀ s) z := fun z hz ↦ by
    have h1 := ((hC2 z hz).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasFDerivAt (fun y ↦ L (y - y₀)) L z := by
      have e : (fun y ↦ L (y - y₀)) = fun y ↦ L y - L y₀ := funext fun y ↦ map_sub L y y₀
      rw [e]
      exact (L.hasFDerivAt (x := z)).sub_const (L y₀)
    exact (h1.sub h2).hasFDerivWithinAt
  have hψb : ∀ z ∈ closedBall y₀ s, ‖fderiv ℝ w z - L‖ ≤ M * s := fun z hz ↦
    (hmv z hz).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hz) hM0)
  have key : ∀ h : E, ‖h‖ = s → |L h| ≤ O + M * s ^ 2 := by
    intro h hh
    have hyh : y₀ + h ∈ closedBall y₀ s := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hh]
    have := (convex_closedBall y₀ s).norm_image_sub_le_of_norm_hasFDerivWithin_le hψ hψb hy₀
      hyh
    simp only [add_sub_cancel_left, sub_self, map_zero, sub_zero, hh] at this
    rw [Real.norm_eq_abs] at this
    have h2 := hO _ hyh
    calc |L h| = |(w (y₀ + h) - w y₀) - (w (y₀ + h) - L h - w y₀)| := by ring_nf
      _ ≤ |w (y₀ + h) - w y₀| + |w (y₀ + h) - L h - w y₀| := abs_sub _ _
      _ ≤ O + M * s * s := add_le_add h2 this
      _ = O + M * s ^ 2 := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rcases eq_or_ne h 0 with rfl | hne
  · simp
  have hn : 0 < ‖h‖ := norm_pos_iff.2 hne
  set h' : E := (s / ‖h‖) • h with hh'
  have hh'n : ‖h'‖ = s := by
    rw [hh', norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp
  have hLh : L h = (‖h‖ / s) * L h' := by
    rw [hh', map_smul, smul_eq_mul, ← mul_assoc]; field_simp
  rw [Real.norm_eq_abs, hLh, abs_mul, abs_of_pos (by positivity)]
  calc ‖h‖ / s * |L h'| ≤ ‖h‖ / s * (O + M * s ^ 2) := by gcongr; exact key h' hh'n
    _ = (O / s + M * s) * ‖h‖ := by field_simp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On a compact set, the oscillation bounds all differences. -/
theorem abs_sub_le_regionOsc {w : E → ℝ} {S : Set E} (hS : IsCompact S)
    (hw : ContinuousOn w S) {y y' : E} (hy : y ∈ S) (hy' : y' ∈ S) :
    |w y - w y'| ≤ regionOsc w S := by
  have hc := hS.image_of_continuousOn hw
  have ha := hc.bddAbove
  have hb := hc.bddBelow
  rw [regionOsc_def, abs_le]
  have h1 := le_csSup ha (mem_image_of_mem w hy)
  have h2 := le_csSup ha (mem_image_of_mem w hy')
  have h3 := csInf_le hb (mem_image_of_mem w hy)
  have h4 := csInf_le hb (mem_image_of_mem w hy')
  constructor <;> linarith

omit [FiniteDimensional ℝ E] in
/-- `‖D²w(p) − D²w(q)‖` in multilinear form is bounded by the bilinear form. -/
theorem norm_iteratedFDeriv_two_sub_le (w : E → ℝ) (p q : E) :
    ‖iteratedFDeriv ℝ 2 w p - iteratedFDeriv ℝ 2 w q‖ ≤
      ‖fderiv ℝ (fderiv ℝ w) p - fderiv ℝ (fderiv ℝ w) q‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m ↦ ?_
  rw [sub_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
    Fin.prod_univ_two, ← sub_apply, ← sub_apply, ← mul_assoc]
  exact ContinuousLinearMap.le_opNorm₂ _ _ _

omit [FiniteDimensional ℝ E] in
theorem norm_hess_le_norm_quad (P : QuadPoly E) : ‖P.hess‖ ≤ ‖P.quad‖ := by
  unfold QuadPoly.hess
  calc ‖(1 / 2 : ℝ) • (P.quad + P.quad.flip)‖ ≤ ‖(1 / 2 : ℝ)‖ * ‖P.quad + P.quad.flip‖ :=
        norm_smul_le _ _
    _ ≤ 1 / 2 * (‖P.quad‖ + ‖P.quad.flip‖) := by
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; gcongr; exact norm_add_le _ _
    _ = ‖P.quad‖ := by rw [ContinuousLinearMap.opNorm_flip]; ring

/-! ### The weighted Hessian bound (absorption) -/

/-- The decomposition of the normalizing quantity of `expansion_at_point` into products of
scale-invariant factors. -/
private theorem frozenN_eq {α R osc Mf Mb Kf Kb Ka M₁ M₂ d : ℝ} (hR0 : 0 < R) :
    osc + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) * (Kf + Kb * (M₁ + M₂ * R) +
        Mb * M₂ * R ^ (1 - α) + d * Ka * M₂) =
      osc + R ^ 2 * Mf + R ^ (2 + α) * Kf + (R * Mb) * (R * M₁) +
        (R ^ (1 + α) * Kb) * (R * M₁) + (R ^ (1 + α) * Kb) * (R ^ 2 * M₂) +
        (R * Mb) * (R ^ 2 * M₂) + d * (Ka * R ^ α) * (R ^ 2 * M₂) := by
  have hRγ : R ^ (2 + α) = R ^ (1 + α) * R := by
    have e : (2 : ℝ) + α = (1 + α) + 1 := by ring
    rw [e, Real.rpow_add hR0, Real.rpow_one]
  have hRγ' : R ^ (2 + α) = R ^ α * R ^ 2 := by
    rw [Real.rpow_add hR0, Real.rpow_two]; ring
  have hRγ'' : R ^ (2 + α) * R ^ (1 - α) = R * R ^ 2 := by
    have e : (2 : ℝ) + α + (1 - α) = (3 : ℕ) := by push_cast; ring
    rw [← Real.rpow_add hR0, e, Real.rpow_natCast]; ring
  have e1 : R ^ (2 + α) * (Kb * (M₁ + M₂ * R)) =
      (R ^ (1 + α) * Kb) * (R * M₁) + (R ^ (1 + α) * Kb) * (R ^ 2 * M₂) := by
    rw [hRγ]; ring
  have e2 : R ^ (2 + α) * (Mb * M₂ * R ^ (1 - α)) = (R * Mb) * (R ^ 2 * M₂) := by
    rw [show R ^ (2 + α) * (Mb * M₂ * R ^ (1 - α)) =
      (R ^ (2 + α) * R ^ (1 - α)) * (Mb * M₂) by ring, hRγ'']; ring
  have e3 : R ^ (2 + α) * (d * Ka * M₂) = d * (Ka * R ^ α) * (R ^ 2 * M₂) := by
    rw [hRγ']; ring
  have e4 : R ^ (2 + α) * (Kf + Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - α) + d * Ka * M₂) =
      R ^ (2 + α) * Kf + R ^ (2 + α) * (Kb * (M₁ + M₂ * R)) +
      R ^ (2 + α) * (Mb * M₂ * R ^ (1 - α)) + R ^ (2 + α) * (d * Ka * M₂) := by ring
  rw [e4, e1, e2, e3]; ring

/-- The arithmetic of the one-point inequality in `weighted_hessian_bound`. -/
private theorem point_bound_arith {α ε θ K' d C R r osc Mf Mb Kf Kb Ka M₁ M₂ Φ N₀ X s d₀ F : ℝ}
    (hα0 : 0 < α) (hR0 : 0 < R) (hRr : R ≤ ε * r) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hθ0 : 0 < θ) (hC : 0 ≤ C) (hK'0 : 0 ≤ K') (hd0 : 0 ≤ d) (hd₀ : 0 < d₀)
    (hMf0 : 0 ≤ Mf) (hMb0 : 0 ≤ Mb) (hKa0 : 0 ≤ Ka) (hKb0 : 0 ≤ Kb) (hKf0 : 0 ≤ Kf)
    (hM₁0 : 0 ≤ M₁) (hΦ0 : 0 ≤ Φ) (hR : R = ε * d₀ / 2) (hM₂ : M₂ = 4 * Φ / d₀ ^ 2)
    (hs : s = θ * d₀ / 2) (hDw : M₁ ≤ osc / s + M₂ * s) (hrMb : r * Mb ≤ K')
    (hrKb : r ^ (1 + α) * Kb ≤ K') (hrKa : Ka * r ^ α ≤ K')
    (hN₀ : N₀ = osc + r ^ 2 * Mf + r ^ (2 + α) * Kf)
    (hX : R ^ 2 * X ≤ C * (osc + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) * (Kf + Kb * (M₁ + M₂ * R) +
      Mb * M₂ * R ^ (1 - α) + d * Ka * M₂)))
    (hF : F = d₀ ^ 2 * X) (hθs : 8 * C * K' * θ ≤ 1 / 4)
    (hεs : 4 * C * K' * (2 * ε + d * ε ^ α) ≤ 1 / 4) :
    F ≤ (4 * C / ε ^ 2 + 8 * C * K' / θ) * N₀ + Φ / 2 := by
  have hRr' : R ≤ r := hRr.trans (mul_le_of_le_one_left hr.le hε1)
  have ha1 : R ^ 2 * Mf ≤ r ^ 2 * Mf := by gcongr
  have ha2 : R ^ (2 + α) * Kf ≤ r ^ (2 + α) * Kf := by gcongr
  have hc : R * Mb ≤ ε * K' := by
    calc R * Mb ≤ ε * r * Mb := by gcongr
      _ = ε * (r * Mb) := by ring
      _ ≤ ε * K' := by gcongr
  have hdd : R ^ (1 + α) * Kb ≤ ε * K' := by
    have h1 : R ^ (1 + α) ≤ ε * r ^ (1 + α) := by
      calc R ^ (1 + α) ≤ (ε * r) ^ (1 + α) := by gcongr
        _ = ε ^ (1 + α) * r ^ (1 + α) := Real.mul_rpow hε0.le hr.le
        _ ≤ ε * r ^ (1 + α) := by
            gcongr
            calc ε ^ (1 + α) ≤ ε ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
              _ = ε := Real.rpow_one ε
    calc R ^ (1 + α) * Kb ≤ ε * r ^ (1 + α) * Kb := by gcongr
      _ = ε * (r ^ (1 + α) * Kb) := by ring
      _ ≤ ε * K' := by gcongr
  have he : Ka * R ^ α ≤ ε ^ α * K' := by
    calc Ka * R ^ α ≤ Ka * (ε * r) ^ α := by gcongr
      _ = ε ^ α * (Ka * r ^ α) := by rw [Real.mul_rpow hε0.le hr.le]; ring
      _ ≤ ε ^ α * K' := by gcongr
  have hf2 : R ^ 2 * M₂ = ε ^ 2 * Φ := by
    rw [hM₂, hR]; field_simp; ring
  have hg : R * M₁ ≤ ε * osc / θ + ε * θ * Φ := by
    calc R * M₁ ≤ R * (osc / s + M₂ * s) := by gcongr
      _ = ε * osc / θ + ε * θ * Φ := by rw [hR, hs, hM₂]; field_simp; ring
  have hRM₁ : 0 ≤ R * M₁ := by positivity
  have hRM₂ : 0 ≤ R ^ 2 * M₂ := by rw [hf2]; positivity
  have hN := frozenN_eq (α := α) (osc := osc) (Mf := Mf) (Mb := Mb) (Kf := Kf) (Kb := Kb) (Ka := Ka)
    (M₁ := M₁) (M₂ := M₂) (d := d) hR0
  have hNle : osc + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) * (Kf + Kb * (M₁ + M₂ * R) +
        Mb * M₂ * R ^ (1 - α) + d * Ka * M₂) ≤
      N₀ + 2 * ε * K' * (ε * osc / θ + ε * θ * Φ) +
        (2 * ε * K' + d * ε ^ α * K') * (ε ^ 2 * Φ) := by
    rw [hN, ← hf2]
    have t1 : (R * Mb) * (R * M₁) ≤ ε * K' * (R * M₁) := by gcongr
    have t2 : (R ^ (1 + α) * Kb) * (R * M₁) ≤ ε * K' * (R * M₁) := by gcongr
    have t3 : (R ^ (1 + α) * Kb) * (R ^ 2 * M₂) ≤ ε * K' * (R ^ 2 * M₂) := by gcongr
    have t4 : (R * Mb) * (R ^ 2 * M₂) ≤ ε * K' * (R ^ 2 * M₂) := by gcongr
    have t5 : d * (Ka * R ^ α) * (R ^ 2 * M₂) ≤ d * (ε ^ α * K') * (R ^ 2 * M₂) := by gcongr
    have t6 : 2 * ε * K' * (R * M₁) ≤ 2 * ε * K' * (ε * osc / θ + ε * θ * Φ) := by gcongr
    rw [hN₀]
    linarith
  have hFX : F = 4 / ε ^ 2 * (R ^ 2 * X) := by
    rw [hF, hR]; field_simp; ring
  rw [hFX]
  have hε2 : 0 < 4 / ε ^ 2 := by positivity
  have hstep := mul_le_mul_of_nonneg_left (hX.trans (mul_le_mul_of_nonneg_left hNle hC)) hε2.le
  refine hstep.trans ?_
  have hosc : osc ≤ N₀ := by
    rw [hN₀]; have : 0 ≤ r ^ 2 * Mf := by positivity
    have : 0 ≤ r ^ (2 + α) * Kf := by positivity
    linarith
  have e : 4 / ε ^ 2 * (C * (N₀ + 2 * ε * K' * (ε * osc / θ + ε * θ * Φ) +
        (2 * ε * K' + d * ε ^ α * K') * (ε ^ 2 * Φ))) =
      4 * C / ε ^ 2 * N₀ + 8 * C * K' / θ * osc +
        (8 * C * K' * θ + 4 * C * K' * (2 * ε + d * ε ^ α)) * Φ := by
    field_simp; ring
  rw [e]
  have h1 : 8 * C * K' / θ * osc ≤ 8 * C * K' / θ * N₀ := by gcongr
  have h2 : (8 * C * K' * θ + 4 * C * K' * (2 * ε + d * ε ^ α)) * Φ ≤ 1 / 2 * Φ := by
    gcongr; linarith
  linarith

/-- **Weighted interior bound for `D²w`** (absorption). Let `0 < α < 1`,
`0 < lam ≤ Λ` and `K` be given. There is `C₁ ≥ 0` such that for every solution of
`tr (a D²w) + ⟪b, ∇w⟫ = f` on `ball x r` under the hypotheses of
`Nondiv.SchauderBallEstimateStatement`, and every `ρ ∈ (0, r)`,
`(ρ − |y − x|)² ‖D²w(y)‖ ≤ C₁ (osc_{B̄_r} w + r² M_f + r^{2+α} K_f)` on `ball x ρ`.

The supremum `Φ` of the left side over `ball x ρ` is **finite** because `D²w` is continuous on
the compact `closedBall x ρ ⊆ ball x r`; the frozen expansion at each `y₀` with radius
`ε (ρ − |y₀ − x|) / 2` gives `Φ ≤ C_A N₀ + Φ / 2`. -/
theorem weighted_hessian_bound [Nontrivial E] {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    {lam Λ : ℝ} (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (K : ℝ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (x : E) (r : ℝ) (Ka Kb Kf : ℝ≥0) (Mb Mf : ℝ)
      (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ) (w : E → ℝ),
      0 < r → IsUniformlyElliptic lam Λ a (ball x r) →
      HolderOnWith Ka α a (ball x r) → (Ka : ℝ) * r ^ (α : ℝ) ≤ K →
      HolderOnWith Kb α b (ball x r) → (∀ y ∈ ball x r, ‖b y‖ ≤ Mb) →
      r * Mb + r ^ (1 + (α : ℝ)) * Kb ≤ K →
      HolderOnWith Kf α f (ball x r) → (∀ y ∈ ball x r, |f y| ≤ Mf) →
      ContinuousOn w (closedBall x r) → IsSolOn a b f (ball x r) w →
      ∀ ρ, 0 < ρ → ρ < r → ∀ y ∈ ball x ρ,
        (ρ - dist y x) ^ 2 * ‖iteratedFDeriv ℝ 2 w y‖ ≤
          C₁ * (regionOsc w (closedBall x r) + r ^ 2 * Mf + r ^ (2 + (α : ℝ)) * Kf) := by
  have hα : 0 < (α : ℝ) ∧ (α : ℝ) < 1 := ⟨hα0, hα1⟩
  obtain ⟨C, κ, hC, hκ, hexp⟩ := expansion_at_point (E := E) hα hlam hlamΛ
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set d : ℝ := (finrank ℝ E : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  set θ : ℝ := 1 / (32 * C * K' + 1) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by positivity)]; nlinarith [mul_nonneg hC hK'0]
  have hθs : 8 * C * K' * θ ≤ 1 / 4 := by
    rw [hθ, mul_one_div, div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg hC hK'0]
  set t : ℝ := 1 / (16 * C * K' * (2 + d) + 1) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]; nlinarith [mul_nonneg (mul_nonneg hC hK'0) hd0]
  set ε : ℝ := t ^ (1 / (α : ℝ)) with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos ht0 _
  have hε1 : ε ≤ 1 := Real.rpow_le_one ht0.le ht1 (by positivity)
  have hεα : ε ^ (α : ℝ) = t := by
    rw [hε, ← Real.rpow_mul ht0.le, one_div_mul_cancel (ne_of_gt hα.1), Real.rpow_one]
  have hεεα : ε ≤ ε ^ (α : ℝ) := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ (α : ℝ) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hα1.le
  have hεs : 4 * C * K' * (2 * ε + d * ε ^ (α : ℝ)) ≤ 1 / 4 := by
    have h1 : 2 * ε + d * ε ^ (α : ℝ) ≤ (2 + d) * t := by rw [← hεα]; nlinarith
    calc 4 * C * K' * (2 * ε + d * ε ^ (α : ℝ)) ≤ 4 * C * K' * ((2 + d) * t) := by
          gcongr
      _ = 4 * C * K' * (2 + d) / (16 * C * K' * (2 + d) + 1) := by rw [ht]; ring
      _ ≤ 1 / 4 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg (mul_nonneg hC hK'0) hd0]
  set C_A : ℝ := 4 * C / ε ^ 2 + 8 * C * K' / θ with hCA
  have hCA0 : 0 ≤ C_A := by positivity
  refine ⟨2 * C_A, by positivity, ?_⟩
  intro x r Ka Kb Kf Mb Mf a b f w hr hell ha haK hb hMb hbK hf hMf hwc hsol ρ hρ hρr
  -- elementary consequences of the hypotheses
  have hxr : x ∈ ball x r := mem_ball_self hr
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans (hMb x hxr)
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf x hxr)
  have hrMb : r * Mb ≤ K' := by
    have : 0 ≤ r ^ (1 + (α : ℝ)) * Kb := by positivity
    exact le_max_of_le_left (by linarith)
  have hrKb : r ^ (1 + (α : ℝ)) * Kb ≤ K' := by
    have : 0 ≤ r * Mb := by positivity
    exact le_max_of_le_left (by linarith)
  have hrKa : (Ka : ℝ) * r ^ (α : ℝ) ≤ K' := le_max_of_le_left haK
  set osc := regionOsc w (closedBall x r) with hosc
  have hoscle : ∀ y ∈ closedBall x r, ∀ y' ∈ closedBall x r, |w y - w y'| ≤ osc :=
    fun y hy y' hy' ↦ abs_sub_le_regionOsc (isCompact_closedBall x r) hwc hy hy'
  have hosc0 : 0 ≤ osc := by
    simpa using hoscle x (mem_closedBall_self hr.le) x (mem_closedBall_self hr.le)
  set N₀ := osc + r ^ 2 * Mf + r ^ (2 + (α : ℝ)) * Kf with hN₀
  have hN₀0 : 0 ≤ N₀ := by positivity
  have hU : IsOpen (ball x r) := isOpen_ball
  have hcD2 : ContinuousOn (iteratedFDeriv ℝ 2 w) (ball x r) :=
    (hsol.1.continuousOn_iteratedFDerivWithin le_rfl hU.uniqueDiffOn).congr
      fun y hy ↦ (iteratedFDerivWithin_of_isOpen 2 hU hy).symm
  have hρU : closedBall x ρ ⊆ ball x r := closedBall_subset_ball hρr
  -- the weighted quantity and its finiteness
  set F : E → ℝ := fun y ↦ (ρ - dist y x) ^ 2 * ‖iteratedFDeriv ℝ 2 w y‖ with hFdef
  obtain ⟨B₂, hB₂⟩ := (isCompact_closedBall x ρ).exists_bound_of_continuousOn (hcD2.mono hρU)
  have hFbdd : BddAbove (F '' ball x ρ) := by
    refine ⟨ρ ^ 2 * B₂, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 : 0 ≤ ρ - dist y x := by linarith [mem_ball.1 hy]
    have h2 : ρ - dist y x ≤ ρ := by linarith [dist_nonneg (x := y) (y := x)]
    have h3 := hB₂ y (ball_subset_closedBall hy)
    simp only [hFdef]
    gcongr
  set Φ := sSup (F '' ball x ρ) with hΦ
  have hFΦ : ∀ y ∈ ball x ρ, F y ≤ Φ := fun y hy ↦ le_csSup hFbdd (mem_image_of_mem F hy)
  have hΦ0 : 0 ≤ Φ := (by positivity : 0 ≤ F x).trans (hFΦ x (mem_ball_self hρ))
  -- the region where the weight is at least `d₀ / 2`
  have hregion : ∀ y₀ ∈ ball x ρ, ∀ y, dist y y₀ ≤ (ρ - dist y₀ x) / 2 →
      y ∈ ball x ρ ∧ ‖iteratedFDeriv ℝ 2 w y‖ ≤ 4 * Φ / (ρ - dist y₀ x) ^ 2 := by
    intro y₀ hy₀ y hy
    have hd₀ : 0 < ρ - dist y₀ x := by linarith [mem_ball.1 hy₀]
    have hyx : dist y x ≤ dist y y₀ + dist y₀ x := dist_triangle _ _ _
    have hw1 : (ρ - dist y₀ x) / 2 ≤ ρ - dist y x := by linarith
    have hyρ : y ∈ ball x ρ := mem_ball.2 (by linarith)
    refine ⟨hyρ, ?_⟩
    have hFy := hFΦ y hyρ
    simp only [hFdef] at hFy
    rw [le_div_iff₀ (by positivity)]
    have h2 : ((ρ - dist y₀ x) / 2) ^ 2 ≤ (ρ - dist y x) ^ 2 := by gcongr
    nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 w y)]
  -- the key one-point inequality
  have hkey : ∀ y₀ ∈ ball x ρ, F y₀ ≤ C_A * N₀ + Φ / 2 := by
    intro y₀ hy₀
    obtain ⟨d₀, hd₀def⟩ : ∃ d₀, d₀ = ρ - dist y₀ x := ⟨_, rfl⟩
    have hd₀ : 0 < d₀ := by rw [hd₀def]; linarith [mem_ball.1 hy₀]
    have hd₀ρ : d₀ ≤ ρ := by rw [hd₀def]; linarith [dist_nonneg (x := y₀) (y := x)]
    have hy₀U : y₀ ∈ ball x r := ball_subset_ball hρr.le hy₀
    have hreg := hregion y₀ hy₀
    rw [← hd₀def] at hreg
    obtain ⟨R, hR⟩ : ∃ R, R = ε * d₀ / 2 := ⟨_, rfl⟩
    have hR0 : 0 < R := by rw [hR]; positivity
    have hRd : R ≤ d₀ / 2 := by
      rw [hR]; have := mul_le_mul_of_nonneg_right hε1 hd₀.le; linarith
    have hRr : R ≤ ε * r := by
      rw [hR]; have := mul_le_mul_of_nonneg_left (hd₀ρ.trans hρr.le) hε0.le; linarith
    have hRr' : R ≤ r := hRr.trans (mul_le_of_le_one_left hr.le hε1)
    have hBU : closedBall y₀ R ⊆ ball x r := fun y hy ↦
      ball_subset_ball hρr.le (hreg y ((mem_closedBall.1 hy).trans hRd)).1
    obtain ⟨M₂, hM₂⟩ : ∃ M₂, M₂ = 4 * Φ / d₀ ^ 2 := ⟨_, rfl⟩
    have hM₂b : ∀ y ∈ ball y₀ R, ‖iteratedFDeriv ℝ 2 w y‖ ≤ M₂ := fun y hy ↦
      hM₂ ▸ (hreg y ((mem_ball.1 hy).le.trans hRd)).2
    -- interpolation for `Dw(y₀)`
    obtain ⟨s, hs⟩ : ∃ s, s = θ * d₀ / 2 := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; positivity
    have hsd : s ≤ d₀ / 2 := by
      rw [hs]; have := mul_le_mul_of_nonneg_right hθ1 hd₀.le; linarith
    have hDw : ‖fderiv ℝ w y₀‖ ≤ osc / s + M₂ * s :=
      norm_fderiv_le_of_osc hU hsol.1 hs0
        (fun y hy ↦ ball_subset_ball hρr.le (hreg y ((mem_closedBall.1 hy).trans hsd)).1)
        (fun y hy ↦ hoscle y (ball_subset_closedBall (ball_subset_ball hρr.le
          (hreg y ((mem_closedBall.1 hy).trans hsd)).1)) y₀
          (ball_subset_closedBall hy₀U))
        (fun y hy ↦ hM₂ ▸ (hreg y ((mem_closedBall.1 hy).trans hsd)).2)
    obtain ⟨M₁, hM₁⟩ : ∃ M₁, M₁ = ‖fderiv ℝ w y₀‖ := ⟨_, rfl⟩
    rw [← hM₁] at hDw
    -- the frozen expansion at `y₀`
    obtain ⟨P, hPc, hPe⟩ := hexp (ball x r) a b f w y₀ R osc M₁ M₂ Mb Mf Ka Kb Kf hU hR0 hBU
      hsol (hell y₀ hy₀U).1 (hell y₀ hy₀U).2
      (fun y hy ↦ by
        rw [← dist_eq_norm]; exact ha.dist_le (hBU (ball_subset_closedBall hy)) hy₀U)
      (fun y hy ↦ by
        rw [← dist_eq_norm]; exact hb.dist_le (hBU (ball_subset_closedBall hy)) hy₀U)
      (fun y hy ↦ by
        rw [← Real.dist_eq]; exact hf.dist_le (hBU (ball_subset_closedBall hy)) hy₀U)
      Ka.2 Kb.2 Kf.2 (hMb y₀ hy₀U) (hMf y₀ hy₀U) hM₁.ge
      (fun y hy ↦ hoscle y (ball_subset_closedBall (hBU (ball_subset_closedBall hy))) y₀
        (ball_subset_closedBall hy₀U))
      hM₂b
    -- identification of the Hessian
    have hC2 : ContDiffAt ℝ 2 w y₀ := hsol.1.contDiffAt (hU.mem_nhds hy₀U)
    have hγ : 2 < 2 + (α : ℝ) := by linarith
    have hid := fderiv_fderiv_eq_hess_of_expansion hγ (mul_pos hκ hR0) hC2 (fun y hy ↦ by
      have := hPe y hy
      rw [Real.div_rpow dist_nonneg hR0.le] at this
      calc _ ≤ _ := this
        _ = C * (osc + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + (α : ℝ)) * (Kf + Kb * (M₁ + M₂ * R) +
              Mb * M₂ * R ^ (1 - (α : ℝ)) + finrank ℝ E * Ka * M₂)) / R ^ (2 + (α : ℝ)) *
              dist y y₀ ^ (2 + (α : ℝ)) := by ring)
    have hD2 : R ^ 2 * ‖iteratedFDeriv ℝ 2 w y₀‖ ≤ C * (osc + R ^ 2 * (Mf + Mb * M₁) +
        R ^ (2 + (α : ℝ)) * (Kf + Kb * (M₁ + M₂ * R) + Mb * M₂ * R ^ (1 - (α : ℝ)) +
          finrank ℝ E * Ka * M₂)) := by
      rw [← norm_fderiv_fderiv_eq, hid]
      refine le_trans ?_ hPc
      have : R ^ 2 * ‖P.hess‖ ≤ R ^ 2 * ‖P.quad‖ :=
        mul_le_mul_of_nonneg_left (norm_hess_le_norm_quad P) (by positivity)
      have h0 : 0 ≤ R * ‖P.lin‖ := mul_nonneg hR0.le (norm_nonneg _)
      linarith
    have hFy₀ : F y₀ = d₀ ^ 2 * ‖iteratedFDeriv ℝ 2 w y₀‖ := by
      simp only [hFdef]; rw [← hd₀def]
    have hM₁0 : 0 ≤ M₁ := hM₁ ▸ norm_nonneg _
    rw [hCA]
    exact point_bound_arith hα0 hR0 hRr hr hε0 hε1 hθ0 hC hK'0 hd0 hd₀ hMf0 hMb0 Ka.2 Kb.2
      Kf.2 hM₁0 hΦ0 hR hM₂ hs hDw hrMb hrKb hrKa hN₀ hD2 hFy₀ hθs hεs
  -- absorption: `Φ ≤ C_A N₀ + Φ / 2`
  have hΦle : Φ ≤ C_A * N₀ + Φ / 2 :=
    csSup_le ((nonempty_ball.2 hρ).image F) (by rintro _ ⟨y, hy, rfl⟩; exact hkey y hy)
  intro y hy
  have := hFΦ y hy
  simp only [hFdef] at this
  linarith

/-! ### The scaled estimate -/

/-- The arithmetic of the normalizing quantity at the scale `R = r/8`. -/
private theorem ball_bound_arith {α r R osc Mf Mb Kf Kb Ka M₁ M₂ d K' C₁ N₀ : ℝ}
    (hα0 : 0 < α) (hr : 0 < r) (hR : R = r / 8) (hosc0 : 0 ≤ osc) (hMf0 : 0 ≤ Mf)
    (hMb0 : 0 ≤ Mb) (hKa0 : 0 ≤ Ka) (hKb0 : 0 ≤ Kb) (hKf0 : 0 ≤ Kf) (hM₁0 : 0 ≤ M₁)
    (hd0 : 0 ≤ d) (hK'0 : 0 ≤ K') (hC₁ : 0 ≤ C₁) (hrMb : r * Mb ≤ K')
    (hrKb : r ^ (1 + α) * Kb ≤ K') (hrKa : Ka * r ^ α ≤ K')
    (hN₀ : N₀ = osc + r ^ 2 * Mf + r ^ (2 + α) * Kf) (hM₂ : M₂ = 16 * C₁ * N₀ / r ^ 2)
    (hM₁ : M₁ ≤ osc / (r / 8) + M₂ * (r / 8)) :
    osc + R ^ 2 * (Mf + Mb * M₁) + R ^ (2 + α) * (Kf + Kb * (M₁ + M₂ * R) +
        Mb * M₂ * R ^ (1 - α) + d * Ka * M₂) ≤
      (1 + 2 * K' * (1 + C₁) + (2 + d) * K' * C₁) * N₀ := by
  have hR0 : 0 < R := by rw [hR]; positivity
  have hRr : R ≤ r := by rw [hR]; linarith
  have hN₀0 : 0 ≤ N₀ := by rw [hN₀]; positivity
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  rw [frozenN_eq hR0]
  have ha1 : R ^ 2 * Mf ≤ r ^ 2 * Mf := by gcongr
  have ha2 : R ^ (2 + α) * Kf ≤ r ^ (2 + α) * Kf := by gcongr
  have hc : R * Mb ≤ K' := le_trans (by gcongr) hrMb
  have hdd : R ^ (1 + α) * Kb ≤ K' := le_trans (by gcongr) hrKb
  have he : Ka * R ^ α ≤ K' := le_trans (by gcongr) hrKa
  have hg : R * M₁ ≤ (1 + C₁) * N₀ := by
    have h1 : R * M₁ ≤ R * (osc / (r / 8) + M₂ * (r / 8)) := by gcongr
    have h2 : R * (osc / (r / 8) + M₂ * (r / 8)) = osc + C₁ * N₀ / 4 := by
      rw [hR, hM₂]; field_simp; ring
    have h3 : osc ≤ N₀ := by
      rw [hN₀]; have : 0 ≤ r ^ 2 * Mf := by positivity
      have : 0 ≤ r ^ (2 + α) * Kf := by positivity
      linarith
    nlinarith
  have hf : R ^ 2 * M₂ ≤ C₁ * N₀ := by
    have : R ^ 2 * M₂ = C₁ * N₀ / 4 := by rw [hR, hM₂]; field_simp; ring
    rw [this]; nlinarith
  have hRM₁ : 0 ≤ R * M₁ := by positivity
  have hRM₂ : 0 ≤ R ^ 2 * M₂ := by positivity
  have t1 : (R * Mb) * (R * M₁) ≤ K' * ((1 + C₁) * N₀) := mul_le_mul hc hg hRM₁ hK'0
  have t2 : (R ^ (1 + α) * Kb) * (R * M₁) ≤ K' * ((1 + C₁) * N₀) := mul_le_mul hdd hg hRM₁ hK'0
  have t3 : (R ^ (1 + α) * Kb) * (R ^ 2 * M₂) ≤ K' * (C₁ * N₀) := mul_le_mul hdd hf hRM₂ hK'0
  have t4 : (R * Mb) * (R ^ 2 * M₂) ≤ K' * (C₁ * N₀) := mul_le_mul hc hf hRM₂ hK'0
  have t5 : d * (Ka * R ^ α) * (R ^ 2 * M₂) ≤ d * K' * (C₁ * N₀) :=
    mul_le_mul (mul_le_mul_of_nonneg_left he hd0) hf hRM₂ (by positivity)
  rw [hN₀] at t1 t2 t3 t4 t5 ⊢
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- **Hölder bound for `D²w` from uniform expansions.** If at every `p ∈ S` the quadratic `P p`
expands `w` to order `2 + α` with constant `A` on `ball p (κ R)`, `D²w(p) = hess (P p)`, and
`‖D²w‖ ≤ M₂` on `S`, then `D²w` is `α`-Hölder on `S` with constant
`288 A + 2 M₂ (2 / (κ R))^α`. -/
theorem dist_iteratedFDeriv_two_le_of_expansions {w : E → ℝ} {S : Set E} {P : E → QuadPoly E}
    {α : ℝ≥0} {κ R A M₂ : ℝ} (hα1 : (α : ℝ) ≤ 1) (hκ : 0 < κ) (hR0 : 0 < R) (hA0 : 0 ≤ A)
    (hM₂0 : 0 ≤ M₂)
    (hPe : ∀ p ∈ S, ∀ y, dist y p < κ * R →
      |w y - (P p).eval (y - p)| ≤ A * dist y p ^ (2 + (α : ℝ)))
    (hPid : ∀ p ∈ S, fderiv ℝ (fderiv ℝ w) p = (P p).hess)
    (hD2 : ∀ p ∈ S, ‖iteratedFDeriv ℝ 2 w p‖ ≤ M₂) :
    ∀ p ∈ S, ∀ q ∈ S, dist (iteratedFDeriv ℝ 2 w p) (iteratedFDeriv ℝ 2 w q) ≤
      (288 * A + 2 * M₂ * (2 / (κ * R)) ^ (α : ℝ)) * dist p q ^ (α : ℝ) := by
  intro p hp q hq
  have hT0 : 0 ≤ 2 * M₂ * (2 / (κ * R)) ^ (α : ℝ) * dist p q ^ (α : ℝ) := by positivity
  have hT1 : 0 ≤ 288 * A * dist p q ^ (α : ℝ) := by positivity
  rcases (dist_nonneg (x := p) (y := q)).eq_or_lt with h0 | h0
  · rw [dist_eq_zero.1 h0.symm, dist_self]
    positivity
  by_cases hnear : 2 * dist p q < κ * R
  · have hc := (QuadPoly.two_expansions_coeff (S := univ) (u := w) (κ := 1) (y := q)
      (by positivity) (by linarith) hA0 (fun y _ hy ↦ hPe p hp y hy)
      (fun y _ hy ↦ hPe q hq y hy) hnear (mem_univ q) one_pos h0 (subset_univ _)
      (by rw [dist_self]; linarith)).1
    rw [dist_eq_norm]
    refine (norm_iteratedFDeriv_two_sub_le w p q).trans ?_
    rw [hPid p hp, hPid q hq]
    refine hc.trans ?_
    rw [show (2 : ℝ) + α - 2 = α by ring, one_pow, div_one]
    linarith
  · push Not at hnear
    have h1 : 1 ≤ (2 / (κ * R)) ^ (α : ℝ) * dist p q ^ (α : ℝ) := by
      rw [← Real.mul_rpow (by positivity) dist_nonneg]
      refine Real.one_le_rpow ?_ (by positivity)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    rw [dist_eq_norm]
    calc ‖iteratedFDeriv ℝ 2 w p - iteratedFDeriv ℝ 2 w q‖
        ≤ ‖iteratedFDeriv ℝ 2 w p‖ + ‖iteratedFDeriv ℝ 2 w q‖ := norm_sub_le _ _
      _ ≤ 2 * M₂ := by linarith [hD2 p hp, hD2 q hq]
      _ ≤ 2 * M₂ * ((2 / (κ * R)) ^ (α : ℝ) * dist p q ^ (α : ℝ)) :=
          le_mul_of_one_le_right (by positivity) h1
      _ ≤ _ := by linarith

/-- The constant of the scaled estimate. -/
private theorem final_const_eq {α r κ R A M₂ H C C_B C₁ N₀ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hR : R = r / 8) (hA : A = C * (C_B * N₀) / R ^ (2 + α)) (hM₂ : M₂ = 16 * C₁ * N₀ / r ^ 2)
    (hH : H = 288 * A + 2 * M₂ * (2 / (κ * R)) ^ α) :
    r ^ (2 + α) * H = (288 * 8 ^ (2 + α) * C * C_B + 32 * C₁ * (16 / κ) ^ α) * N₀ := by
  have hr8 : R ^ (2 + α) = r ^ (2 + α) / 8 ^ (2 + α) := by
    rw [hR, Real.div_rpow hr.le (by norm_num)]
  have hκR : (2 / (κ * R)) ^ α = (16 / κ) ^ α / r ^ α := by
    rw [← Real.div_rpow (by positivity) hr.le, hR]
    congr 1; field_simp; ring
  have hrγ : r ^ (2 + α) = r ^ 2 * r ^ α := by
    rw [Real.rpow_add hr, Real.rpow_two]
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have h8 : 0 < (8 : ℝ) ^ (2 + α) := by positivity
  rw [hH, hA, hM₂, hκR, hr8, hrγ]
  field_simp
  ring

/-- **The scaled interior estimate in a nontrivial space**. Under the hypotheses
of `Nondiv.SchauderBallEstimateStatement` (with `lam ≤ Λ`),
`r² ‖D²w(x)‖ + r^{2+α} [D²w]_{α,B̄_{r/2}} ≤ C (osc_{B̄_r} w + r² M_f + r^{2+α} K_f)`.
The `D²w` bounds come from the absorption `weighted_hessian_bound`; the Hölder bound from two
frozen expansions at nearby points (`QuadPoly.two_expansions_coeff`) and the `D²w` bound at
distant points. -/
theorem ball_estimate_of_nontrivial [Nontrivial E] {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    {lam Λ : ℝ} (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : E) (r : ℝ) (Ka Kb Kf : ℝ≥0) (Mb Mf : ℝ)
      (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ) (w : E → ℝ),
      0 < r → IsUniformlyElliptic lam Λ a (ball x r) →
      HolderOnWith Ka α a (ball x r) → (Ka : ℝ) * r ^ (α : ℝ) ≤ K →
      HolderOnWith Kb α b (ball x r) → (∀ y ∈ ball x r, ‖b y‖ ≤ Mb) →
      r * Mb + r ^ (1 + (α : ℝ)) * Kb ≤ K →
      HolderOnWith Kf α f (ball x r) → (∀ y ∈ ball x r, |f y| ≤ Mf) →
      ContinuousOn w (closedBall x r) → IsSolOn a b f (ball x r) w →
      r ^ 2 * ‖iteratedFDeriv ℝ 2 w x‖ +
          r ^ (2 + (α : ℝ)) * holderSeminormOn α (iteratedFDeriv ℝ 2 w) (closedBall x (r / 2)) ≤
        C * (regionOsc w (closedBall x r) + r ^ 2 * Mf + r ^ (2 + (α : ℝ)) * Kf) := by
  have hα : 0 < (α : ℝ) ∧ (α : ℝ) < 1 := ⟨hα0, hα1⟩
  obtain ⟨C₁, hC₁, hW⟩ := weighted_hessian_bound (E := E) hα0 hα1 hlam hlamΛ K
  obtain ⟨C, κ, hC, hκ, hexp⟩ := expansion_at_point (E := E) hα hlam hlamΛ
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set d : ℝ := (finrank ℝ E : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  set C_B := 1 + 2 * K' * (1 + C₁) + (2 + d) * K' * C₁ with hCB
  have hCB0 : 0 ≤ C_B := by positivity
  refine ⟨2 * C₁ + 288 * 8 ^ (2 + (α : ℝ)) * C * C_B + 32 * C₁ * (16 / κ) ^ (α : ℝ),
    by positivity, ?_⟩
  intro x r Ka Kb Kf Mb Mf a b f w hr hell ha haK hb hMb hbK hf hMf hwc hsol
  have hxr : x ∈ ball x r := mem_ball_self hr
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans (hMb x hxr)
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf x hxr)
  have hrMb : r * Mb ≤ K' := by
    have : 0 ≤ r ^ (1 + (α : ℝ)) * Kb := by positivity
    exact le_max_of_le_left (by linarith)
  have hrKb : r ^ (1 + (α : ℝ)) * Kb ≤ K' := by
    have : 0 ≤ r * Mb := by positivity
    exact le_max_of_le_left (by linarith)
  have hrKa : (Ka : ℝ) * r ^ (α : ℝ) ≤ K' := le_max_of_le_left haK
  set osc := regionOsc w (closedBall x r) with hosc
  have hoscle : ∀ y ∈ closedBall x r, ∀ y' ∈ closedBall x r, |w y - w y'| ≤ osc :=
    fun y hy y' hy' ↦ abs_sub_le_regionOsc (isCompact_closedBall x r) hwc hy hy'
  have hosc0 : 0 ≤ osc := by
    simpa using hoscle x (mem_closedBall_self hr.le) x (mem_closedBall_self hr.le)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, N₀ = osc + r ^ 2 * Mf + r ^ (2 + (α : ℝ)) * Kf := ⟨_, rfl⟩
  rw [← hN₀]
  have hN₀0 : 0 ≤ N₀ := by rw [hN₀]; positivity
  have hU : IsOpen (ball x r) := isOpen_ball
  -- `D²w` bounds from the absorption
  have hW' := hW x r Ka Kb Kf Mb Mf a b f w hr hell ha haK hb hMb hbK hf hMf hwc hsol
    (7 * r / 8) (by positivity) (by linarith)
  rw [← hosc, ← hN₀] at hW'
  have hD2x : r ^ 2 * ‖iteratedFDeriv ℝ 2 w x‖ ≤ 2 * C₁ * N₀ := by
    have h := hW' x (mem_ball_self (by positivity))
    rw [dist_self, sub_zero] at h
    have h0 : 0 ≤ ‖iteratedFDeriv ℝ 2 w x‖ := norm_nonneg _
    nlinarith
  obtain ⟨M₂, hM₂⟩ : ∃ M₂, M₂ = 16 * C₁ * N₀ / r ^ 2 := ⟨_, rfl⟩
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  have hD2b : ∀ y, dist y x ≤ 5 * r / 8 → ‖iteratedFDeriv ℝ 2 w y‖ ≤ M₂ := by
    intro y hy
    have h := hW' y (mem_ball.2 (by linarith))
    have h1 : r / 4 ≤ 7 * r / 8 - dist y x := by linarith
    have h2 : (r / 4) ^ 2 * ‖iteratedFDeriv ℝ 2 w y‖ ≤ C₁ * N₀ :=
      le_trans (by gcongr) h
    rw [hM₂, le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 w y)]
  -- frozen expansions at the points of `closedBall x (r/2)`
  obtain ⟨R, hR⟩ : ∃ R, R = r / 8 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  obtain ⟨A, hA⟩ : ∃ A, A = C * (C_B * N₀) / R ^ (2 + (α : ℝ)) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hγ : 2 < 2 + (α : ℝ) := by linarith
  have hpt : ∀ p ∈ closedBall x (r / 2), ∃ P : QuadPoly E,
      (∀ y, dist y p < κ * R → |w y - P.eval (y - p)| ≤ A * dist y p ^ (2 + (α : ℝ))) ∧
      fderiv ℝ (fderiv ℝ w) p = P.hess := by
    intro p hp
    have hpx : dist p x ≤ r / 2 := mem_closedBall.1 hp
    have hpU : p ∈ ball x r := mem_ball.2 (by linarith)
    have hBU : closedBall p R ⊆ ball x r := fun y hy ↦ by
      have := dist_triangle y p x
      rw [mem_closedBall] at hy; rw [mem_ball]; rw [hR] at hy; linarith
    have hB58 : ∀ y ∈ closedBall p R, dist y x ≤ 5 * r / 8 := fun y hy ↦ by
      have := dist_triangle y p x
      rw [mem_closedBall] at hy; rw [hR] at hy; linarith
    have hDw : ‖fderiv ℝ w p‖ ≤ osc / (r / 8) + M₂ * (r / 8) :=
      norm_fderiv_le_of_osc hU hsol.1 (by positivity) (hR ▸ hBU)
        (fun y hy ↦ hoscle y (ball_subset_closedBall (hBU (hR ▸ hy))) p
          (ball_subset_closedBall hpU))
        (fun y hy ↦ hD2b y (hB58 y (hR ▸ hy)))
    obtain ⟨P, -, hPe⟩ := hexp (ball x r) a b f w p R osc ‖fderiv ℝ w p‖ M₂ Mb Mf Ka Kb Kf hU
      hR0 hBU hsol (hell p hpU).1 (hell p hpU).2
      (fun y hy ↦ by
        rw [← dist_eq_norm]; exact ha.dist_le (hBU (ball_subset_closedBall hy)) hpU)
      (fun y hy ↦ by
        rw [← dist_eq_norm]; exact hb.dist_le (hBU (ball_subset_closedBall hy)) hpU)
      (fun y hy ↦ by
        rw [← Real.dist_eq]; exact hf.dist_le (hBU (ball_subset_closedBall hy)) hpU)
      Ka.2 Kb.2 Kf.2 (hMb p hpU) (hMf p hpU) le_rfl
      (fun y hy ↦ hoscle y (ball_subset_closedBall (hBU (ball_subset_closedBall hy))) p
        (ball_subset_closedBall hpU))
      (fun y hy ↦ hD2b y (hB58 y (ball_subset_closedBall hy)))
    have hNp := ball_bound_arith hα0 hr hR hosc0 hMf0 hMb0 Ka.2 Kb.2 Kf.2 (norm_nonneg _) hd0
      hK'0 hC₁ hrMb hrKb hrKa hN₀ hM₂ hDw
    have hPe' : ∀ y, dist y p < κ * R → |w y - P.eval (y - p)| ≤ A * dist y p ^ (2 + (α : ℝ)) := by
      intro y hy
      refine (hPe y hy).trans ?_
      rw [Real.div_rpow dist_nonneg hR0.le, hA]
      have hRγ : 0 < R ^ (2 + (α : ℝ)) := by positivity
      have hdγ : 0 ≤ dist y p ^ (2 + (α : ℝ)) := by positivity
      calc _ ≤ C * (C_B * N₀) * (dist y p ^ (2 + (α : ℝ)) / R ^ (2 + (α : ℝ))) := by
            gcongr
            exact hNp
        _ = _ := by ring
    exact ⟨P, hPe', fderiv_fderiv_eq_hess_of_expansion hγ (mul_pos hκ hR0)
      (hsol.1.contDiffAt (hU.mem_nhds hpU)) hPe'⟩
  choose! P hPe hPid using hpt
  -- the Hölder bound on `closedBall x (r/2)`
  obtain ⟨H, hH⟩ : ∃ H, H = 288 * A + 2 * M₂ * (2 / (κ * R)) ^ (α : ℝ) := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hHol := hH ▸ dist_iteratedFDeriv_two_le_of_expansions (α := α) hα.2.le hκ hR0 hA0 hM₂0
    hPe hPid
    (fun y hy ↦ hD2b y (by linarith [mem_closedBall.1 hy]))
  have hsemi : holderSeminormOn α (iteratedFDeriv ℝ 2 w) (closedBall x (r / 2)) ≤ H :=
    holderSeminormOn_le_of_dist_le hH0 hHol
  -- assembling the constants
  have hrH := final_const_eq (α := (α : ℝ)) hr hκ hR hA hM₂ hH
  calc r ^ 2 * ‖iteratedFDeriv ℝ 2 w x‖ +
        r ^ (2 + (α : ℝ)) * holderSeminormOn α (iteratedFDeriv ℝ 2 w) (closedBall x (r / 2))
      ≤ 2 * C₁ * N₀ + r ^ (2 + (α : ℝ)) * H := by gcongr
    _ = _ := by rw [hrH]; ring

omit [FiniteDimensional ℝ E] in
/-- Uniform ellipticity at one point of a nontrivial space forces `lam ≤ Λ`. -/
theorem lam_le_of_isUniformlyElliptic [Nontrivial E] {lam Λ : ℝ} {a : E → E →L[ℝ] E}
    {s : Set E} (hell : IsUniformlyElliptic lam Λ a s) {z : E} (hz : z ∈ s) : lam ≤ Λ := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  obtain ⟨h1, h2⟩ := hell z hz
  have hξ2 : 0 < ‖ξ‖ ^ 2 := by positivity
  have h3 : ⟪a z ξ, ξ⟫ ≤ Λ * ‖ξ‖ ^ 2 := by
    calc ⟪a z ξ, ξ⟫ ≤ ‖a z ξ‖ * ‖ξ‖ := real_inner_le_norm _ _
      _ ≤ ‖a z‖ * ‖ξ‖ * ‖ξ‖ := by gcongr; exact (a z).le_opNorm ξ
      _ ≤ Λ * ‖ξ‖ * ‖ξ‖ := by gcongr
      _ = Λ * ‖ξ‖ ^ 2 := by ring
  exact le_of_mul_le_mul_right ((h1 ξ).trans h3) hξ2

end Nondiv

end BasicElliptic
