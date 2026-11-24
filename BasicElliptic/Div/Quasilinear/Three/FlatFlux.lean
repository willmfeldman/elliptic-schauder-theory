/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.Three.FirstOrder
import BasicElliptic.Div.Quasilinear.Flux
import BasicElliptic.Holder.Algebra

/-!
# The constant normal flux at a flat point, and the first-order estimate

* `Div.inner_apply_gradientWithin_eq_zero`: the conormal condition `⟪Φ(∇w(z)), ν⟫ = 0` holds
  pointwise at a flat centre `z` (from the flux bound `Div.sq_inner_mul_pow_le_of_flux` and the
  continuity of `∇w`).
* `Div.flat_flux_estimate`: at a flat centre, `s |⟪Φ(0), ν⟫| ≤ C osc w`. With
  `n = DΦ(0) ν`, the conormal condition gives `∂_n w(z) = -⟪Φ(0), ν⟫ + O(M |∇w(z)|²)`; along the
  segment `z + τ n` the `C^{1,1/2}` bound controls `w(z + τ n) - w(z) - τ ∂_n w(z)`; the
  first-order estimate with the flux `⟪Φ(0), ν⟫ ν` bounds `|∇w(z)|` and `[∇w]_{1/2}` by
  `osc w + s |⟪Φ(0), ν⟫|`, and the flux term is absorbed for small `τ` and small `η`.
* `Div.first_order_estimate`: `r ‖Dw(x)‖ + r^{3/2} [Dw]_{1/2, halfBall ν x (κ r)} ≤ C osc w`,
  uniformly in the structure: away from the flat part every constant flux drops out; near it the
  flux term is bounded by `Div.flat_flux_estimate` at the foot point.
-/

public section

open MeasureTheory Metric Set RealInnerProductSpace Module
open scoped NNReal Gradient ContDiff

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Differences of a function on a compact set are bounded by its oscillation. -/
theorem abs_sub_le_regionOsc {f : E → ℝ} {s : Set E} (hs : IsCompact s)
    (hf : ContinuousOn f s) {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    |f a - f b| ≤ regionOsc f s := by
  have hA : BddAbove (f '' s) := (hs.image_of_continuousOn hf).bddAbove
  have hB : BddBelow (f '' s) := (hs.image_of_continuousOn hf).bddBelow
  have h1 : ∀ c ∈ s, f c ≤ sSup (f '' s) := fun c hc ↦ le_csSup hA ⟨c, hc, rfl⟩
  have h2 : ∀ c ∈ s, sInf (f '' s) ≤ f c := fun c hc ↦ csInf_le hB ⟨c, hc, rfl⟩
  rw [regionOsc_def, abs_le]
  constructor <;> linarith [h1 a ha, h1 b hb, h2 a ha, h2 b hb]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem regionOsc_nonneg_of_compact {f : E → ℝ} {s : Set E} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hne : s.Nonempty) : 0 ≤ regionOsc f s := by
  obtain ⟨a, ha⟩ := hne
  have := abs_sub_le_regionOsc hs hf ha ha
  rw [sub_self, abs_zero] at this
  exact this

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem regionOsc_mono_of_compact {f : E → ℝ} {s t : Set E} (hst : s ⊆ t) (ht : IsCompact t)
    (hf : ContinuousOn f t) (hne : s.Nonempty) : regionOsc f s ≤ regionOsc f t :=
  regionOsc_mono hst hne (ht.image_of_continuousOn hf).bddAbove
    (ht.image_of_continuousOn hf).bddBelow

omit [MeasurableSpace E] [BorelSpace E] in
theorem chordCoeff_self_zero (Φ : E → E) : chordCoeff Φ 0 0 = fderiv ℝ Φ 0 := by
  simp [chordCoeff_eq, intervalIntegral.integral_const]

/-! ### The pointwise conormal condition -/

/-- **The conormal condition at a flat centre.** -/
theorem inner_apply_gradientWithin_eq_zero {ν : E} (hν : ‖ν‖ = 1) {Φ : E → E} {U : Set E}
    (hΦ : ContDiffOn ℝ 1 Φ U) {z : E} {s : ℝ} {w : E → ℝ} (hs : 0 < s)
    (hz : ⟪z, ν⟫ = 0) (h : IsQuasilinearConormalSolOn ν Φ z s w)
    (hrange : ∀ y ∈ halfBall ν z s, gradientWithin w (halfBall ν z s) y ∈ U) :
    ⟪Φ (gradientWithin w (halfBall ν z s) z), ν⟫ = 0 := by
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  obtain ⟨Cf, hCf, hflux⟩ := sq_inner_mul_pow_le_of_flux (E := E) hν
  set B := halfBall ν z s with hB
  set g := gradientWithin w B with hg
  have hzs : -s < ⟪z, ν⟫ := by rw [hz]; linarith
  have hgc : ContinuousOn g B := continuousOn_gradientWithin_halfBall hν hs hzs h.1
  have hQc : ContinuousOn (fun y ↦ Φ (g y)) B := hΦ.continuousOn.comp hgc hrange
  have hzB : z ∈ B := ⟨mem_closedBall_self hs.le, by rw [mem_halfSpace, hz]⟩
  set v := Φ (g z) with hv
  set gv := ⟪v, ν⟫ with hgv
  set vB := unitBallVolume E with hvB
  have hvB0 : 0 < vB := unitBallVolume_pos
  by_contra hne
  have hpos : 0 < |gv| := abs_pos.2 hne
  set ε := |gv| / (2 * (Cf * vB + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨ρ₀, hρ₀, hρ₀'⟩ := Metric.continuousWithinAt_iff.1 (hQc z hzB) ε hε0
  set ρ := min (ρ₀ / 2) s with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) hs
  have hρs : ρ ≤ s := min_le_right _ _
  have hzρ : -ρ < ⟪z, ν⟫ := by rw [hz]; linarith
  have hres := h.restrict hν hρ0 hzρ (closedBall_subset_closedBall hρs) (ball_subset_ball hρs)
  have hsub : halfBall ν z ρ ⊆ B := halfBall_mono ν z hρs
  have hus := uniqueDiffOn_halfBall hν hρ0 hzρ
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have heq : ∀ y ∈ halfBall ν z ρ, gradientWithin w (halfBall ν z ρ) y = g y :=
    fun y hy ↦ gradientWithin_eq_of_subset hsub (hus y hy) (hwB y (hsub hy))
  have hQc' : ContinuousOn (fun y ↦ Φ (gradientWithin w (halfBall ν z ρ) y)) (halfBall ν z ρ) :=
    hΦ.continuousOn.comp (continuousOn_gradientWithin_halfBall hν hρ0 hzρ hres.1)
      fun y hy ↦ by rw [heq y hy]; exact hrange y (hsub hy)
  have hfl := hflux z ρ _ v hz hρ0 hQc' fun φ hφ ↦ hres.2 φ hφ
  have hpt : ∀ y ∈ halfBall ν z ρ,
      ‖Φ (gradientWithin w (halfBall ν z ρ) y) - v‖ ^ 2 ≤ ε ^ 2 := fun y hy ↦ by
    rw [heq y hy, ← dist_eq_norm]
    refine pow_le_pow_left₀ dist_nonneg (hρ₀' (hsub hy) ?_).le 2
    exact (mem_closedBall.1 hy.1).trans_lt (by
      have := min_le_left (ρ₀ / 2) s; linarith)
  have hvol : volume.real (halfBall ν z ρ) ≤ ρ ^ finrank ℝ E * vB := by
    rw [← measureReal_ball_eq hρ0, measureReal_def, measureReal_def,
      measure_congr (halfBall_ae_eq hν0 z ρ)]
    exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono inter_subset_left)
  have hfin : volume (halfBall ν z ρ) ≠ ⊤ := (isCompact_halfBall ν z ρ).measure_lt_top.ne
  have hint : ∫ y in halfBall ν z ρ, ‖Φ (gradientWithin w (halfBall ν z ρ) y) - v‖ ^ 2 ≤
      ε ^ 2 * (ρ ^ finrank ℝ E * vB) := by
    calc _ ≤ ∫ _y in halfBall ν z ρ, ε ^ 2 :=
          setIntegral_mono_on (((hQc'.sub continuousOn_const).norm.pow 2).integrableOn_compact
            (isCompact_halfBall ν z ρ)) (integrableOn_const hfin)
            (measurableSet_halfBall ν z ρ) hpt
      _ = ε ^ 2 * volume.real (halfBall ν z ρ) := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := by gcongr
  have hsd : 0 < ρ ^ finrank ℝ E := pow_pos hρ0 _
  have h1 : gv ^ 2 * ρ ^ finrank ℝ E ≤ Cf * vB * ε ^ 2 * ρ ^ finrank ℝ E := by
    calc gv ^ 2 * ρ ^ finrank ℝ E ≤ Cf * _ := hfl
      _ ≤ Cf * (ε ^ 2 * (ρ ^ finrank ℝ E * vB)) := by gcongr
      _ = Cf * vB * ε ^ 2 * ρ ^ finrank ℝ E := by ring
  have h2 : gv ^ 2 ≤ Cf * vB * ε ^ 2 := le_of_mul_le_mul_right h1 hsd
  have hk : 0 < Cf * vB + 1 := by positivity
  have h3 : Cf * vB * ε ^ 2 < gv ^ 2 := by
    rw [hε, div_pow, ← sq_abs gv]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    have hk2 : Cf * vB ≤ (2 * (Cf * vB + 1)) ^ 2 / 4 := by nlinarith
    nlinarith [sq_nonneg |gv|, mul_pos (pow_pos hpos 2) hk]
  linarith

/-! ### The constant normal flux at a flat centre -/

set_option maxHeartbeats 800000 in
-- a long proof with many explicit constants and nonlinear arithmetic
variable (E) in
/-- **The constant normal flux at a flat centre**: `s |⟪Φ(0), ν⟫| ≤ C osc w`, uniformly in the
structure. -/
theorem flat_flux_estimate {ν : E} (hν : ‖ν‖ = 1) {lam M δ : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M)
    (hδ : 0 < δ) :
    ∃ η > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → E), StructureBounds Φ lam M δ →
      ∀ (z : E) (s : ℝ) (w : E → ℝ), 0 < s → ⟪z, ν⟫ = 0 →
      IsQuasilinearConormalSolOn ν Φ z s w →
      (∀ y ∈ halfBall ν z s, ‖gradientWithin w (halfBall ν z s) y‖ ≤ η) →
      s * |⟪Φ 0, ν⟫| ≤ C * regionOsc w (halfBall ν z s) := by
  obtain ⟨ηF, hηF, κ, hκ, hκ2, CF, hCF, hF⟩ := first_order_estimate_flux E hν hlam hM hδ
  set K := (M + 1) * (CF + 1) with hK
  have hK0 : 0 < K := by positivity
  set β := κ / (4 * K) with hβ
  have hβ0 : 0 < β := by positivity
  set θ := min (1 / 2) (β ^ 2) with hθ
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
  have hsθ : √θ ≤ β := by
    rw [show β = √(β ^ 2) from (Real.sqrt_sq hβ0.le).symm]
    exact Real.sqrt_le_sqrt (min_le_right _ _)
  set η := min (min ηF (δ / 2)) β with hη
  have hη0 : 0 < η := lt_min (lt_min hηF (by positivity)) hβ0
  have hηF' : η ≤ ηF := (min_le_left _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hηβ : η ≤ β := min_le_right _ _
  refine ⟨η, hη0, 1 + 2 * (M + 1) / (θ * κ), by positivity, ?_⟩
  intro Φ hS z s w hs hz h hgrad
  set B := halfBall ν z s with hB
  set g := gradientWithin w B with hg
  set g₀ := ⟪Φ 0, ν⟫ with hg₀
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  have hzs : -s < ⟪z, ν⟫ := by rw [hz]; linarith
  have hz0 : 0 ≤ ⟪z, ν⟫ := hz.ge
  have hzB : z ∈ B := ⟨mem_closedBall_self hs.le, hz0⟩
  have hBc : IsCompact B := isCompact_halfBall ν z s
  have hwc : ContinuousOn w B := h.1.continuousOn
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  set osc := regionOsc w B with hosc
  have hosc0 : 0 ≤ osc := regionOsc_nonneg_of_compact hBc hwc ⟨z, hzB⟩
  -- the first-order estimate with the flux `g₀ ν`
  have hflux : ∀ φ, IsTestFn (ball z s) φ → ∫ y in B, ⟪Φ 0 - g₀ • ν, ∇ φ y⟫ = 0 :=
    fun φ hφ ↦ setIntegral_halfBall_inner_const_eq_zero (by
      rw [inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]) hφ
  obtain ⟨hfin, hFe⟩ := hF Φ hS z s w (g₀ • ν) hs hz0 h
    (fun y hy ↦ (hgrad y hy).trans hηF') hflux
  rw [norm_smul, hν, mul_one, Real.norm_eq_abs] at hFe
  set s₂ := κ * s with hs₂
  have hs₂0 : 0 < s₂ := by positivity
  set sem := holderSeminormOn (1 / 2) (fderivWithin ℝ w B) (halfBall ν z (s₂ / 2)) with hsem
  have hsem0 : 0 ≤ sem := holderSeminormOn_nonneg _ _ _
  set Q := osc + s * |g₀| with hQ
  set p := g z with hp
  have hpn : ‖fderivWithin ℝ w B z‖ = ‖p‖ := norm_fderivWithin_eq_norm_gradientWithin _ _ _
  have h32 : s₂ ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) = s₂ * √s₂ := by
    rw [show (1 + ((1 / 2 : ℝ≥0) : ℝ)) = 1 + 1 / 2 by norm_num, Real.rpow_add hs₂0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [h32, hpn] at hFe
  have hsq0 : 0 ≤ √s₂ := Real.sqrt_nonneg _
  have hI : s₂ * ‖p‖ ≤ CF * Q := by
    have : 0 ≤ s₂ * √s₂ * sem := by positivity
    linarith
  have hII : s₂ * √s₂ * sem ≤ CF * Q := by
    have : 0 ≤ s₂ * ‖p‖ := by positivity
    linarith
  -- the conormal direction `n = DΦ(0) ν`
  have h0δ : (0 : E) ∈ ball (0 : E) δ := mem_ball_self hδ
  set A₀ := fderiv ℝ Φ 0 with hA₀
  set n := A₀ ν with hn
  have hnM : ‖n‖ ≤ M := by
    have := A₀.le_opNorm ν
    rw [hν, mul_one] at this
    exact this.trans (hS.bound 0 h0δ).1
  have hnν : lam ≤ ⟪n, ν⟫ := by
    have := hS.ell 0 h0δ ν
    rwa [hν, one_pow, mul_one] at this
  -- the segment
  set t := θ * s₂ with ht
  have ht0 : 0 < t := by positivity
  have hts₂ : t ≤ s₂ / 2 := by
    rw [ht]; exact (mul_le_mul_of_nonneg_right hθ1 hs₂0.le).trans_eq (by ring)
  set τ := t / (M + 1) with hτ
  have hτ0 : 0 < τ := by positivity
  set z' := z + τ • n with hz'
  have hτn : ‖τ • n‖ ≤ t := by
    rw [norm_smul, Real.norm_of_nonneg hτ0.le, hτ]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  set S := halfBall ν z t with hSdef
  have hSsub : S ⊆ halfBall ν z (s₂ / 2) := halfBall_mono ν z hts₂
  have hs₂s : s₂ / 2 ≤ s := by
    have : κ * s ≤ s := mul_le_of_le_one_left hs.le (by linarith)
    linarith
  have hSB : S ⊆ B := hSsub.trans (halfBall_mono ν z hs₂s)
  have hz'S : z' ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, hz', dist_eq_norm, add_sub_cancel_left]; exact hτn
    · rw [mem_halfSpace, hz', inner_add_left, hz, zero_add, real_inner_smul_left]
      exact mul_nonneg hτ0.le (hlam.le.trans hnν)
  have hzS : z ∈ S := ⟨mem_closedBall_self ht0.le, hz0⟩
  -- the mean value inequality for `w - Dw(z)`
  set D₀ := fderivWithin ℝ w B z with hD₀
  have hderiv : ∀ y ∈ S, HasFDerivWithinAt (fun y ↦ w y - D₀ y)
      (fderivWithin ℝ w B y - D₀) S y := fun y hy ↦
    (((hwB y (hSB hy)).hasFDerivWithinAt).mono hSB).sub D₀.hasFDerivWithinAt
  have hbound : ∀ y ∈ S, ‖fderivWithin ℝ w B y - D₀‖ ≤ sem * √t := fun y hy ↦ by
    have := dist_le_holderSeminormOn_mul hfin (hSsub hy) (hSsub hzS)
    rw [dist_eq_norm, show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow] at this
    refine this.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hsem0)
    exact mem_closedBall.1 hy.1
  have hmv := (convex_halfBall ν z t).norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv
    hbound hzS hz'S
  have hDn : D₀ n = ⟪p, n⟫ := by
    rw [hp, hg, gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hsymA := hS.sym 0 h0δ p ν
  simp only [ContinuousLinearMap.coe_coe] at hsymA
  have hD₀n : D₀ (τ • n) = τ * ⟪A₀ p, ν⟫ := by
    rw [map_smul, smul_eq_mul, hDn, hn, hsymA]
  -- the conormal condition at `z`
  have hrange : ∀ y ∈ B, g y ∈ ball (0 : E) δ := fun y hy ↦
    mem_ball_zero_iff.2 (((hgrad y hy).trans hηδ).trans_lt (by linarith))
  have hcon := inner_apply_gradientWithin_eq_zero hν hS.contDiffOn_one hs hz h hrange
  set K₀ := closedBall (0 : E) (δ / 2) with hK₀
  have hK₀U : K₀ ⊆ ball (0 : E) δ := closedBall_subset_ball (by linarith)
  have hpK : p ∈ K₀ := mem_closedBall_zero_iff.2 ((hgrad z hzB).trans hηδ)
  have h0K : (0 : E) ∈ K₀ := mem_closedBall_self (by positivity)
  have hchord := norm_chordCoeff_sub_le isOpen_ball (convex_ball _ _) hS.contDiffOn_one
    (convex_closedBall _ _) hK₀U hM (fun a ha b hb ↦ hS.norm_fderiv_sub_le (hK₀U ha) (hK₀U hb))
    hpK h0K h0K h0K
  rw [chordCoeff_self_zero, sub_zero, sub_self, norm_zero, add_zero] at hchord
  have hΦp := sub_eq_chordCoeff_apply isOpen_ball (convex_ball _ _) hS.contDiffOn_one
    (hK₀U hpK) (hK₀U h0K)
  rw [sub_zero] at hΦp
  have hlin : |g₀ + ⟪A₀ p, ν⟫| ≤ M * ‖p‖ ^ 2 := by
    have e : g₀ + ⟪A₀ p, ν⟫ = -⟪(chordCoeff Φ p 0 - A₀) p, ν⟫ := by
      have : ⟪Φ p, ν⟫ = 0 := hcon
      have e' : (chordCoeff Φ p 0 - A₀) p = chordCoeff Φ p 0 p - A₀ p := rfl
      rw [e', inner_sub_left, ← hΦp, inner_sub_left, hg₀]
      linarith
    rw [e, abs_neg]
    calc |⟪(chordCoeff Φ p 0 - A₀) p, ν⟫| ≤ ‖(chordCoeff Φ p 0 - A₀) p‖ * ‖ν‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖chordCoeff Φ p 0 - A₀‖ * ‖p‖ := by
          rw [hν, mul_one]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖p‖ * ‖p‖ := by gcongr
      _ = M * ‖p‖ ^ 2 := by ring
  have hpη : ‖p‖ ≤ η := hgrad z hzB
  -- `τ |g₀| ≤ τ M η ‖p‖ + osc + sem √t t`
  have hosc' : |w z' - w z| ≤ osc := abs_sub_le_regionOsc hBc hwc (hSB hz'S) hzB
  have hmain : τ * |g₀| ≤ τ * (M * η * ‖p‖) + osc + sem * √t * t := by
    have e1 : |w z' - w z - D₀ (τ • n)| ≤ sem * √t * t := by
      have hz'z : z' - z = τ • n := by rw [hz']; abel
      have h1 : w z' - D₀ z' - (w z - D₀ z) = w z' - w z - D₀ (τ • n) := by
        rw [← hz'z, map_sub]; ring
      rw [← Real.norm_eq_abs, ← h1]
      refine hmv.trans ?_
      rw [hz'z]
      exact mul_le_mul_of_nonneg_left hτn (by positivity)
    rw [hD₀n] at e1
    have e2 : τ * |g₀ + ⟪A₀ p, ν⟫| ≤ τ * (M * η * ‖p‖) := by
      gcongr
      calc |g₀ + ⟪A₀ p, ν⟫| ≤ M * ‖p‖ ^ 2 := hlin
        _ = M * ‖p‖ * ‖p‖ := by ring
        _ ≤ M * η * ‖p‖ := by gcongr
    have e3 : τ * |g₀| ≤ τ * |g₀ + ⟪A₀ p, ν⟫| + |τ * ⟪A₀ p, ν⟫| := by
      rw [← abs_of_pos hτ0, ← abs_mul, ← abs_mul, abs_of_pos hτ0]
      calc |τ * g₀| = |τ * (g₀ + ⟪A₀ p, ν⟫) - τ * ⟪A₀ p, ν⟫| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have e4 : |τ * ⟪A₀ p, ν⟫| ≤ osc + sem * √t * t := by
      calc |τ * ⟪A₀ p, ν⟫| = |(w z' - w z) - (w z' - w z - τ * ⟪A₀ p, ν⟫)| := by ring_nf
        _ ≤ |w z' - w z| + |w z' - w z - τ * ⟪A₀ p, ν⟫| := abs_sub _ _
        _ ≤ _ := add_le_add hosc' e1
    linarith
  -- absorption
  have hMη : M * η * CF ≤ κ / 4 := by
    calc M * η * CF ≤ (M + 1) * β * (CF + 1) := by gcongr <;> linarith
      _ = κ / 4 := by rw [hβ, hK]; field_simp
  have hθb : √θ * CF ≤ κ / (4 * (M + 1)) := by
    calc √θ * CF ≤ β * (CF + 1) := by gcongr; linarith
      _ = κ / (4 * (M + 1)) := by rw [hβ, hK]; field_simp
  have hτdef : τ * (M + 1) = θ * s₂ := by rw [hτ, ht]; field_simp
  have hst : √t = √θ * √s₂ := Real.sqrt_mul hθ0.le _
  -- term by term
  have T1 : τ * (M * η * ‖p‖) * (M + 1) ≤ θ * (κ / 4) * Q := by
    calc τ * (M * η * ‖p‖) * (M + 1) = θ * (M * η) * (s₂ * ‖p‖) := by
          linear_combination (M * η * ‖p‖) * hτdef
      _ ≤ θ * (M * η) * (CF * Q) := by gcongr
      _ = θ * (M * η * CF) * Q := by ring
      _ ≤ θ * (κ / 4) * Q := by gcongr
  have T2 : sem * √t * t * (M + 1) ≤ θ * (κ / 4) * Q := by
    calc sem * √t * t * (M + 1) = θ * (√θ * (M + 1)) * (s₂ * √s₂ * sem) := by
          rw [hst, ht]; ring
      _ ≤ θ * (√θ * (M + 1)) * (CF * Q) := by gcongr
      _ = θ * ((M + 1) * (√θ * CF)) * Q := by ring
      _ ≤ θ * ((M + 1) * (κ / (4 * (M + 1)))) * Q := by gcongr
      _ = θ * (κ / 4) * Q := by field_simp
  have hfin' : θ * κ * s * |g₀| ≤ θ * (κ / 2) * Q + (M + 1) * osc := by
    have := mul_le_mul_of_nonneg_right hmain (by positivity : (0 : ℝ) ≤ M + 1)
    have e : τ * |g₀| * (M + 1) = θ * κ * s * |g₀| := by
      rw [hs₂] at hτdef; linear_combination |g₀| * hτdef
    rw [e] at this
    nlinarith
  rw [hQ] at hfin'
  have hθκ : 0 < θ * κ := by positivity
  have key : θ * κ * (s * |g₀|) ≤ θ * κ * osc + 2 * (M + 1) * osc := by nlinarith
  rw [show (1 + 2 * (M + 1) / (θ * κ)) * osc = (θ * κ * osc + 2 * (M + 1) * osc) / (θ * κ) by
    field_simp]
  rw [le_div_iff₀ hθκ]
  linarith

/-! ### The first-order estimate -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Arithmetic for unscaling: from `k r A + (k r)^{3/2} S ≤ Q` with `k ≥ k₀ > 0`. -/
theorem unscale_aux {k k₀ r A S Q : ℝ} (hk₀ : 0 < k₀) (hk : k₀ ≤ k) (hr : 0 < r) (hA : 0 ≤ A)
    (hS : 0 ≤ S) (h : k * r * A + (k * r) ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) * S ≤ Q) :
    r * A ≤ Q / k₀ ∧ r * √r * S ≤ Q / (k₀ * √k₀) := by
  have hk0 : 0 < k := hk₀.trans_le hk
  have h32 : (k * r) ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) = k * √k * (r * √r) := by
    rw [show (1 + ((1 / 2 : ℝ≥0) : ℝ)) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.sqrt_eq_rpow, Real.sqrt_mul hk0.le]
    ring
  rw [h32] at h
  have h1 : 0 ≤ k * √k * (r * √r) * S := by positivity
  have h2 : 0 ≤ k * r * A := by positivity
  have hsk : √k₀ ≤ √k := Real.sqrt_le_sqrt hk
  have hsk0 : 0 < √k₀ := Real.sqrt_pos.2 hk₀
  constructor
  · rw [le_div_iff₀ hk₀]
    calc r * A * k₀ ≤ r * A * k := by gcongr
      _ = k * r * A := by ring
      _ ≤ Q := by linarith
  · rw [le_div_iff₀ (by positivity)]
    calc r * √r * S * (k₀ * √k₀) ≤ r * √r * S * (k * √k) := by gcongr
      _ = k * √k * (r * √r) * S := by ring
      _ ≤ Q := by linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The real Hölder seminorm is monotone in the set when the larger one is finite. -/
theorem holderSeminormOn_mono_of_ne_top {F : Type*} [NormedAddCommGroup F] {α : ℝ≥0}
    {f : E → F} {s t : Set E} (hst : s ⊆ t) (ht : eHolderSeminormOn α f t ≠ ⊤) :
    holderSeminormOn α f s ≤ holderSeminormOn α f t :=
  ENNReal.toReal_mono ht (eHolderSeminormOn_mono hst)

set_option maxHeartbeats 800000 in
-- a long proof with many explicit constants and nonlinear arithmetic
variable (E) in
/-- **The first-order estimate, uniform in the structure**: at a centre in the closed half
space, `r ‖Dw(x)‖ ≤ C osc w` and `r^{3/2} [Dw]_{1/2, halfBall ν x (κ r)} ≤ C osc w`. -/
theorem first_order_estimate {ν : E} (hν : ‖ν‖ = 1) {lam M δ : ℝ} (hlam : 0 < lam)
    (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ η > 0, ∃ κ > 0, κ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → E),
      StructureBounds Φ lam M δ → ∀ (x : E) (r : ℝ) (w : E → ℝ), 0 < r →
      0 ≤ ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x r w →
      (∀ y ∈ halfBall ν x r, ‖gradientWithin w (halfBall ν x r) y‖ ≤ η) →
      eHolderSeminormOn (1 / 2) (fderivWithin ℝ w (halfBall ν x r)) (halfBall ν x (κ * r)) ≠ ⊤ ∧
      r * ‖fderivWithin ℝ w (halfBall ν x r) x‖ ≤ C * regionOsc w (halfBall ν x r) ∧
      r * √r * holderSeminormOn (1 / 2) (fderivWithin ℝ w (halfBall ν x r))
        (halfBall ν x (κ * r)) ≤ C * regionOsc w (halfBall ν x r) := by
  obtain ⟨ηF, hηF, κF, hκF, hκF2, CF, hCF, hF⟩ := first_order_estimate_flux E hν hlam hM hδ
  obtain ⟨ηK, hηK, CK, hCK, hK⟩ := flat_flux_estimate E hν hlam hM hδ
  set k₀ := κF / 2 with hk₀
  have hk₀0 : 0 < k₀ := by positivity
  set C₁ := CF * (1 + 2 * CK) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨min ηF ηK, lt_min hηF hηK, κF / 4, by positivity, by linarith,
    C₁ / k₀ + C₁ / (k₀ * √k₀), by positivity, ?_⟩
  intro Φ hS x r w hr hx0 h hgrad
  set B := halfBall ν x r with hB
  have hx : -r < ⟪x, ν⟫ := by linarith
  have hBc : IsCompact B := isCompact_halfBall ν x r
  have hwc : ContinuousOn w B := h.1.continuousOn
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  have hxB : x ∈ B := ⟨mem_closedBall_self hr.le, hx0⟩
  set osc := regionOsc w B with hosc
  have hosc0 : 0 ≤ osc := regionOsc_nonneg_of_compact hBc hwc ⟨x, hxB⟩
  have hgradF : ∀ y ∈ B, ‖gradientWithin w B y‖ ≤ ηF := fun y hy ↦
    (hgrad y hy).trans (min_le_left _ _)
  -- a restricted solution keeps the gradient bound
  have hres : ∀ (z : E) (s : ℝ), 0 < s → -s < ⟪z, ν⟫ → closedBall z s ⊆ closedBall x r →
      ball z s ⊆ ball x r → IsQuasilinearConormalSolOn ν Φ z s w ∧
        ∀ y ∈ halfBall ν z s, ‖gradientWithin w (halfBall ν z s) y‖ ≤ min ηF ηK :=
    fun z s hs hzs hc hb ↦ by
      have hsub : halfBall ν z s ⊆ B := inter_subset_inter_left _ hc
      refine ⟨h.restrict hν hs hzs hc hb, fun y hy ↦ ?_⟩
      rw [gradientWithin_eq_of_subset hsub (uniqueDiffOn_halfBall hν hs hzs y hy)
        (hwB y (hsub hy))]
      exact hgrad y (hsub hy)
  -- in both cases: `k r A + (k r)^{3/2} S ≤ C₁ osc` with `k ≥ k₀` and `S` over a larger set
  have hmain : ∃ k, k₀ ≤ k ∧ ∃ T : Set E, halfBall ν x (κF / 4 * r) ⊆ T ∧
      eHolderSeminormOn (1 / 2) (fderivWithin ℝ w B) T ≠ ⊤ ∧
      k * r * ‖fderivWithin ℝ w B x‖ + (k * r) ^ (1 + ((1 / 2 : ℝ≥0) : ℝ)) *
        holderSeminormOn (1 / 2) (fderivWithin ℝ w B) T ≤ C₁ * osc := by
    rcases le_or_gt (r / 2) ⟪x, ν⟫ with hfar | hnear
    · -- away from the flat part: every constant flux drops out
      set ρ := r / 2 with hρ
      have hρ0 : 0 < ρ := by positivity
      have hxρ : -ρ < ⟪x, ν⟫ := by linarith
      obtain ⟨hsolρ, hgρ⟩ := hres x ρ hρ0 hxρ (closedBall_subset_closedBall (by linarith))
        (ball_subset_ball (by linarith))
      have hsubρ : halfBall ν x ρ ⊆ B := halfBall_mono ν x (by linarith)
      obtain ⟨hfin, hest⟩ := hF Φ hS x ρ w 0 hρ0 hx0 hsolρ
        (fun y hy ↦ (hgρ y hy).trans (min_le_left _ _)) fun φ hφ ↦ by
          rw [sub_zero]; exact setIntegral_halfBall_inner_const_eq_zero_of_le hν hfar hφ
      have hD := fderivWithin_halfBall_eqOn hν hρ0 hxρ hsubρ hwB
      have hTsub : halfBall ν x (κF * ρ / 2) ⊆ halfBall ν x ρ :=
        halfBall_mono ν x (by nlinarith)
      rw [hD ⟨mem_closedBall_self hρ0.le, hx0⟩, holderSeminormOn_congr (hD.mono hTsub)] at hest
      rw [eHolderSeminormOn_congr (hD.mono hTsub)] at hfin
      have hoscρ : regionOsc w (halfBall ν x ρ) ≤ osc :=
        regionOsc_mono_of_compact hsubρ hBc hwc ⟨x, ⟨mem_closedBall_self hρ0.le, hx0⟩⟩
      refine ⟨κF / 2, le_rfl, halfBall ν x (κF * ρ / 2), le_of_eq (by congr 1; ring), hfin, ?_⟩
      have e : κF / 2 * r = κF * ρ := by rw [hρ]; ring
      rw [e]
      refine hest.trans ?_
      rw [norm_zero, mul_zero, add_zero]
      calc CF * regionOsc w (halfBall ν x ρ) ≤ CF * osc := by gcongr
        _ ≤ C₁ * osc := by
            gcongr
            rw [hC₁]; nlinarith
    · -- near the flat part: the flux term at the foot point
      have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
      set z := x - ⟪x, ν⟫ • ν with hz
      have hzν : ⟪z, ν⟫ = 0 := by
        rw [hz, inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]
      have hdz : dist z x = ⟪x, ν⟫ := by
        rw [hz, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
          Real.norm_of_nonneg hx0]
      have hr2 : 0 < r / 2 := by positivity
      obtain ⟨hsolz, hgz⟩ := hres z (r / 2) hr2 (by rw [hzν]; linarith)
        (closedBall_subset_closedBall' (by rw [hdz]; linarith))
        (ball_subset_ball' (by rw [hdz]; linarith))
      have hKz := hK Φ hS z (r / 2) w hr2 hzν hsolz fun y hy ↦ (hgz y hy).trans (min_le_right _ _)
      have hsubz : halfBall ν z (r / 2) ⊆ B :=
        inter_subset_inter_left _ (closedBall_subset_closedBall' (by rw [hdz]; linarith))
      have hoscz : regionOsc w (halfBall ν z (r / 2)) ≤ osc :=
        regionOsc_mono_of_compact hsubz hBc hwc ⟨z, ⟨mem_closedBall_self hr2.le,
          by rw [mem_halfSpace, hzν]⟩⟩
      set g₀ := ⟪Φ 0, ν⟫ with hg₀
      have hg₀b : r * |g₀| ≤ 2 * CK * osc := by
        have : r / 2 * |g₀| ≤ CK * osc := hKz.trans (by gcongr)
        linarith
      obtain ⟨hfin, hest⟩ := hF Φ hS x r w (g₀ • ν) hr hx0 h hgradF fun φ hφ ↦
        setIntegral_halfBall_inner_const_eq_zero (by
          rw [inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]) hφ
      rw [norm_smul, hν, mul_one, Real.norm_eq_abs] at hest
      refine ⟨κF, by linarith, halfBall ν x (κF * r / 2), halfBall_mono ν x (by nlinarith),
        hfin, hest.trans ?_⟩
      rw [hC₁]
      nlinarith
  obtain ⟨k, hk, T, hTsub, hfinT, hkest⟩ := hmain
  obtain ⟨h1, h2⟩ := unscale_aux hk₀0 hk hr (norm_nonneg _) (holderSeminormOn_nonneg _ _ _) hkest
  have hsemT := holderSeminormOn_mono_of_ne_top hTsub hfinT
  refine ⟨ne_top_of_le_ne_top hfinT (eHolderSeminormOn_mono hTsub), ?_, ?_⟩
  · refine h1.trans ?_
    have : 0 ≤ C₁ / (k₀ * √k₀) * osc := by positivity
    rw [add_mul, mul_div_right_comm]
    linarith
  · calc r * √r * holderSeminormOn (1 / 2) (fderivWithin ℝ w B) (halfBall ν x (κF / 4 * r))
        ≤ r * √r * holderSeminormOn (1 / 2) (fderivWithin ℝ w B) T := by gcongr
      _ ≤ C₁ * osc / (k₀ * √k₀) := h2
      _ ≤ (C₁ / k₀ + C₁ / (k₀ * √k₀)) * osc := by
          have : 0 ≤ C₁ / k₀ * osc := by positivity
          rw [add_mul, mul_div_right_comm]
          linarith

end BasicElliptic.Div
