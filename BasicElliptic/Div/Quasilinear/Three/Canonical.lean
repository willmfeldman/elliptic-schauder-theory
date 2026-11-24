/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Estimate

/-!
# Within-derivatives on half balls and on the half space; Hessians from tangential rows

* Near a point of the open ball `ball c ρ`, the half ball `halfBall ν c ρ` coincides with the half
  space `halfSpace ν`, so within-derivatives (of any order, nested or iterated) at such points
  can be computed within `halfSpace ν`. This lets estimates proved on different half balls be
  compared.
* `Div.norm_le_of_tangential_approx`: `Div.norm_le_of_tangential` with an approximate equation
  `|Σ_j H(b_j, A b_j)| ≤ R`.
* `Div.regionOsc_le_of_norm_fderivWithin_le`: on a convex set of diameter `≤ 2 r`, a gradient bound
  `η` gives `osc ≤ 2 r η`.
-/

public section

open Metric Set Filter RealInnerProductSpace
open scoped Topology

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Half balls are half spaces near interior points -/

theorem halfBall_eventuallyEq_halfSpace {ν c z : E} {ρ : ℝ} (hz : z ∈ ball c ρ) :
    halfBall ν c ρ =ᶠ[𝓝 z] halfSpace ν := by
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [isOpen_ball.mem_nhds hz] with p hp
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨ball_subset_closedBall hp, h⟩⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderivWithin_halfBall_eq {ν c z : E} {ρ : ℝ} (f : E → F) (hz : z ∈ ball c ρ) :
    fderivWithin ℝ f (halfBall ν c ρ) z = fderivWithin ℝ f (halfSpace ν) z :=
  fderivWithin_congr_set (halfBall_eventuallyEq_halfSpace hz)

theorem fderivWithin_halfBall_eventuallyEq {ν c z : E} {ρ : ℝ} (f : E → F) (hz : z ∈ ball c ρ) :
    fderivWithin ℝ f (halfBall ν c ρ) =ᶠ[𝓝 z] fderivWithin ℝ f (halfSpace ν) := by
  filter_upwards [isOpen_ball.mem_nhds hz] with p hp
  exact fderivWithin_halfBall_eq f hp

theorem fderivWithin_congr_of_eventuallyEq_nhds {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f₁ f : E → G} {s : Set E} {z : E} (h : f₁ =ᶠ[𝓝 z] f) :
    fderivWithin ℝ f₁ s z = fderivWithin ℝ f s z :=
  (h.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h.eq_of_nhds

/-- Second within-derivatives on two half balls, at a point of both open balls. -/
theorem fderivWithin_fderivWithin_halfBall_eq {ν c c' z : E} {ρ ρ' : ℝ} (f : E → F)
    (hz : z ∈ ball c ρ) (hz' : z ∈ ball c' ρ') :
    fderivWithin ℝ (fderivWithin ℝ f (halfBall ν c ρ)) (halfBall ν c' ρ') z =
      fderivWithin ℝ (fderivWithin ℝ f (halfSpace ν)) (halfSpace ν) z := by
  rw [fderivWithin_halfBall_eq _ hz']
  exact fderivWithin_congr_of_eventuallyEq_nhds (fderivWithin_halfBall_eventuallyEq f hz)

theorem fderivWithin_fderivWithin_halfBall_eventuallyEq {ν c c' z : E} {ρ ρ' : ℝ} (f : E → F)
    (hz : z ∈ ball c ρ) (hz' : z ∈ ball c' ρ') :
    fderivWithin ℝ (fderivWithin ℝ f (halfBall ν c ρ)) (halfBall ν c' ρ') =ᶠ[𝓝 z]
      fderivWithin ℝ (fderivWithin ℝ f (halfSpace ν)) (halfSpace ν) := by
  filter_upwards [isOpen_ball.mem_nhds hz, isOpen_ball.mem_nhds hz'] with p hp hp'
  exact fderivWithin_fderivWithin_halfBall_eq f hp hp'

/-! ### The Hessian from its tangential rows and an approximate equation -/

/-- If `H` is symmetric, `|Σ_j H(b_j, A b_j)| ≤ R` with `A` symmetric, `lam`-elliptic and
`‖A‖ ≤ Λ`, and `‖H e‖ ≤ T ‖e‖` for tangential `e`, then
`‖H‖ ≤ 2 T (1 + d Λ / lam) + R / lam`. -/
theorem norm_le_of_tangential_approx {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {ν : E} (hν : ‖ν‖ = 1) (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : ∀ u v, H u v = H v u)
    {A : E →L[ℝ] E} (hA : (A : E →ₗ[ℝ] E).IsSymmetric) {lam Λ : ℝ} (hlam : 0 < lam)
    (hell : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫) (hAΛ : ‖A‖ ≤ Λ) {R : ℝ}
    (heq : |∑ j, H (b j) (A (b j))| ≤ R) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ e : E, ⟪e, ν⟫ = 0 → ‖H e‖ ≤ T * ‖e‖) :
    ‖H‖ ≤ 2 * T * (1 + Fintype.card ι * Λ / lam) + R / lam := by
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hAΛ
  have hR : 0 ≤ R := (abs_nonneg _).trans heq
  set P : E → E := fun ξ ↦ ξ - ⟪ξ, ν⟫ • ν with hP
  have hPν : ∀ ξ, ⟪P ξ, ν⟫ = 0 := fun ξ ↦ by
    rw [hP, inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]
  have hPn : ∀ ξ, ‖P ξ‖ ≤ ‖ξ‖ := fun ξ ↦ by
    have h1 : ‖P ξ‖ ^ 2 = ‖ξ‖ ^ 2 - ⟪ξ, ν⟫ ^ 2 := by
      rw [hP, @norm_sub_sq_real, norm_smul, hν, real_inner_smul_right, Real.norm_eq_abs,
        mul_one, sq_abs]
      ring
    have h2 : ‖P ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by rw [h1]; nlinarith [sq_nonneg ⟪ξ, ν⟫]
    nlinarith [norm_nonneg (P ξ), norm_nonneg ξ]
  have hdec : ∀ ξ, ξ = P ξ + ⟪ξ, ν⟫ • ν := fun ξ ↦ by simp [hP]
  set h := H ν ν with hh
  set HT : E → E → ℝ := fun ξ η ↦ H ξ (P η) + ⟪η, ν⟫ * H (P ξ) ν with hHT
  have hsplit : ∀ ξ η, H ξ η = HT ξ η + ⟪ξ, ν⟫ * ⟪η, ν⟫ * h := fun ξ η ↦ by
    have e1 : H ξ η = H ξ (P η) + ⟪η, ν⟫ * H ξ ν := by
      conv_lhs => rw [hdec η]
      rw [map_add, map_smul, smul_eq_mul]
    have e2 : H ξ ν = H (P ξ) ν + ⟪ξ, ν⟫ * h := by
      conv_lhs => rw [hdec ξ]
      rw [map_add, map_smul, add_apply, FunLike.coe_smul,
        Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, hHT]; ring
  have hHTb : ∀ ξ η, |HT ξ η| ≤ 2 * T * ‖ξ‖ * ‖η‖ := fun ξ η ↦ by
    have h1 : |H ξ (P η)| ≤ T * ‖ξ‖ * ‖η‖ := by
      rw [hH, ← Real.norm_eq_abs]
      calc ‖H (P η) ξ‖ ≤ ‖H (P η)‖ * ‖ξ‖ := (H (P η)).le_opNorm ξ
        _ ≤ T * ‖P η‖ * ‖ξ‖ := by gcongr; exact hT _ (hPν η)
        _ ≤ T * ‖η‖ * ‖ξ‖ := by gcongr; exact hPn η
        _ = T * ‖ξ‖ * ‖η‖ := by ring
    have h2 : |⟪η, ν⟫ * H (P ξ) ν| ≤ T * ‖ξ‖ * ‖η‖ := by
      rw [abs_mul]
      have h3 : |⟪η, ν⟫| ≤ ‖η‖ := by simpa [hν] using abs_real_inner_le_norm η ν
      have h4 : |H (P ξ) ν| ≤ T * ‖ξ‖ := by
        rw [← Real.norm_eq_abs]
        calc ‖H (P ξ) ν‖ ≤ ‖H (P ξ)‖ * ‖ν‖ := (H (P ξ)).le_opNorm ν
          _ ≤ T * ‖P ξ‖ * 1 := by rw [hν]; gcongr; exact hT _ (hPν ξ)
          _ ≤ T * ‖ξ‖ := by rw [mul_one]; gcongr; exact hPn ξ
      calc |⟪η, ν⟫| * |H (P ξ) ν| ≤ ‖η‖ * (T * ‖ξ‖) :=
            mul_le_mul h3 h4 (abs_nonneg _) (norm_nonneg _)
        _ = T * ‖ξ‖ * ‖η‖ := by ring
    calc |HT ξ η| ≤ |H ξ (P η)| + |⟪η, ν⟫ * H (P ξ) ν| := abs_add_le _ _
      _ ≤ 2 * T * ‖ξ‖ * ‖η‖ := by linarith
  have hsumA : ∑ j, ⟪b j, ν⟫ * ⟪A (b j), ν⟫ = ⟪A ν, ν⟫ := by
    rw [real_inner_comm, ← b.sum_inner_mul_inner ν (A ν)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hs := hA (b j) ν
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [real_inner_comm (b j) ν, hs]
  have hAν : lam ≤ ⟪A ν, ν⟫ := by simpa [hν] using hell ν
  have hheq : ⟪A ν, ν⟫ * h = ∑ j, H (b j) (A (b j)) - ∑ j, HT (b j) (A (b j)) := by
    have : ∑ j, H (b j) (A (b j)) =
        ∑ j, (HT (b j) (A (b j)) + ⟪b j, ν⟫ * ⟪A (b j), ν⟫ * h) :=
      Finset.sum_congr rfl fun j _ ↦ hsplit _ _
    rw [this, Finset.sum_add_distrib, ← Finset.sum_mul, hsumA]
    ring
  have hsumb : |∑ j, HT (b j) (A (b j))| ≤ 2 * T * (Fintype.card ι * Λ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |HT (b j) (A (b j))| ≤ ∑ _j : ι, 2 * T * Λ := Finset.sum_le_sum fun j _ ↦ by
          refine (hHTb _ _).trans ?_
          rw [(b.orthonormal.1 j), mul_one]
          gcongr
          exact ((A.le_opNorm _).trans (by rw [b.orthonormal.1 j, mul_one])).trans hAΛ
      _ = 2 * T * (Fintype.card ι * Λ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hhb : |h| ≤ (2 * T * (Fintype.card ι * Λ) + R) / lam := by
    rw [le_div_iff₀ hlam]
    have : |⟪A ν, ν⟫ * h| ≤ 2 * T * (Fintype.card ι * Λ) + R := by
      rw [hheq]
      calc _ ≤ |∑ j, H (b j) (A (b j))| + |∑ j, HT (b j) (A (b j))| := abs_sub _ _
        _ ≤ _ := by linarith
    rw [abs_mul, abs_of_pos (hlam.trans_le hAν)] at this
    nlinarith [abs_nonneg h]
  have hK0 : 0 ≤ 2 * T * (1 + Fintype.card ι * Λ / lam) + R / lam := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun ξ ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun η ↦ ?_
  rw [Real.norm_eq_abs, hsplit]
  have h3 : |⟪ξ, ν⟫ * ⟪η, ν⟫ * h| ≤ ‖ξ‖ * ‖η‖ * ((2 * T * (Fintype.card ι * Λ) + R) / lam) := by
    rw [abs_mul, abs_mul]
    have hξ : |⟪ξ, ν⟫| ≤ ‖ξ‖ := by simpa [hν] using abs_real_inner_le_norm ξ ν
    have hη : |⟪η, ν⟫| ≤ ‖η‖ := by simpa [hν] using abs_real_inner_le_norm η ν
    gcongr
  calc |HT ξ η + ⟪ξ, ν⟫ * ⟪η, ν⟫ * h| ≤ |HT ξ η| + |⟪ξ, ν⟫ * ⟪η, ν⟫ * h| := abs_add_le _ _
    _ ≤ 2 * T * ‖ξ‖ * ‖η‖ + ‖ξ‖ * ‖η‖ * ((2 * T * (Fintype.card ι * Λ) + R) / lam) :=
        add_le_add (hHTb ξ η) h3
    _ = (2 * T * (1 + Fintype.card ι * Λ / lam) + R / lam) * ‖ξ‖ * ‖η‖ := by
        field_simp; ring

/-! ### Oscillation from a gradient bound -/

theorem regionOsc_le_of_norm_fderivWithin_le {w : E → ℝ} {s : Set E} (hsc : Convex ℝ s)
    (hne : s.Nonempty) (hw : DifferentiableOn ℝ w s) {η D : ℝ}
    (hη : ∀ y ∈ s, ‖fderivWithin ℝ w s y‖ ≤ η) (hD : ∀ a ∈ s, ∀ b ∈ s, ‖a - b‖ ≤ D) :
    regionOsc w s ≤ D * η := by
  have hη0 : 0 ≤ η := by obtain ⟨a, ha⟩ := hne; exact (norm_nonneg _).trans (hη a ha)
  have hlip : ∀ a ∈ s, ∀ b ∈ s, w a - w b ≤ D * η := fun a ha b hb ↦ by
    have := hsc.norm_image_sub_le_of_norm_fderivWithin_le hw hη hb ha
    rw [Real.norm_eq_abs] at this
    calc w a - w b ≤ |w a - w b| := le_abs_self _
      _ ≤ η * ‖a - b‖ := this
      _ ≤ η * D := by gcongr; exact hD a ha b hb
      _ = D * η := by ring
  obtain ⟨b₀, hb₀⟩ := hne
  have hA : BddAbove (w '' s) := ⟨w b₀ + D * η, by
    rintro _ ⟨a, ha, rfl⟩; linarith [hlip a ha b₀ hb₀]⟩
  have hsup : ∀ b ∈ s, sSup (w '' s) ≤ w b + D * η := fun b hb ↦
    csSup_le ⟨w b₀, b₀, hb₀, rfl⟩ (by rintro _ ⟨a, ha, rfl⟩; linarith [hlip a ha b hb])
  have hinf : sSup (w '' s) - D * η ≤ sInf (w '' s) :=
    le_csInf ⟨w b₀, b₀, hb₀, rfl⟩ (by rintro _ ⟨b, hb, rfl⟩; linarith [hsup b hb])
  rw [regionOsc_def]; linarith

end BasicElliptic.Div
