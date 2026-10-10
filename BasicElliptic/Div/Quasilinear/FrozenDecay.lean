/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.FrozenStep
public import BasicElliptic.Campanato.IterationEps
public import BasicElliptic.Campanato.Holder
import BasicElliptic.Holder.Algebra

/-!
# Campanato decay and local `C^{1,1/2}` for `C¹` quasilinear solutions with small `DΦ - 1`

Under `Div.SmallOscData` (`DΦ` is `ε`-close to the identity on a ball `N` containing the range
of `∇w`) with `ε ≤ ε₀`:

* `Div.interior_frozen_decay`, `Div.flat_frozen_decay`: the Campanato quantity
  `ψ(ρ) = ∫ ‖∇w - (∇w)_ρ‖²` over balls in the open half ball, resp. half balls centred on the
  flat part, decays like `(ρ/s)^{d+1}`. Proof: the frozen-coefficient steps
  (`Div/Quasilinear/FrozenStep.lean`) and the iteration lemma with an `ε` term
  (`campanato_iteration_eps`, exponents `d + 2 > d + 1`).
* `Div.holderOnWith_gradientWithin_of_smallOsc`: `∇w` is `1/2`-Hölder on
  `halfBall ν z₀ (R/16)`. Proof: the decay at every point of the small half ball (the patching of
  `campanato_patch` in `Div/Boundary/Patch.lean`: interior balls far from the flat part, interior
  balls near it started from the flat decay at the foot point, and balls meeting the flat part
  enlarged to half balls centred at the foot point), then Campanato's characterization
  (`holderOnWith_of_campanato`).
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient Topology NNReal

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Mean-square oscillation helpers -/

/-- The mean-square oscillation over `T₁` is at most the quadratic deviation from any constant
over `T₂ ⊇ T₁`. -/
theorem osc_le_of_subset {g : E → E} {T₁ T₂ K : Set E} (hK : IsCompact K)
    (hg : ContinuousOn g K) (hT₂K : T₂ ⊆ K) (h12 : T₁ ⊆ T₂) (c : E) :
    ∫ y in T₁, ‖g y - ⨍ y' in T₁, g y'‖ ^ 2 ≤ ∫ y in T₂, ‖g y - c‖ ^ 2 := by
  obtain ⟨hi1, hi2⟩ := integrableOn_of_continuousOn_compact hg hK subset_rfl (h12.trans hT₂K)
  have hfin : volume T₁ ≠ ⊤ :=
    ((measure_mono (h12.trans hT₂K)).trans_lt hK.measure_lt_top).ne
  refine (setIntegral_norm_sub_setAverage_sq_le hfin hi1 hi2 c).trans ?_
  refine setIntegral_mono_set ?_ (Eventually.of_forall fun _ ↦ sq_nonneg _) h12.eventuallyLE
  exact ((((hg.sub continuousOn_const).norm.pow 2).integrableOn_compact hK).mono_set hT₂K)

/-- The crude bound `∫_T ‖g - g_T‖² ≤ η² |T|` when `‖g - q₀‖ ≤ η` on `T`. -/
theorem osc_le_crude {g : E → E} {T K : Set E} (hK : IsCompact K) (hg : ContinuousOn g K)
    (hTK : T ⊆ K) (hTm : MeasurableSet T) {q₀ : E} {η : ℝ}
    (hq : ∀ y ∈ T, ‖g y - q₀‖ ≤ η) :
    ∫ y in T, ‖g y - ⨍ y' in T, g y'‖ ^ 2 ≤ η ^ 2 * volume.real T := by
  refine (osc_le_of_subset hK hg hTK subset_rfl q₀).trans ?_
  have hfin : volume T ≠ ⊤ := ((measure_mono hTK).trans_lt hK.measure_lt_top).ne
  calc ∫ y in T, ‖g y - q₀‖ ^ 2 ≤ ∫ y in T, η ^ 2 :=
        setIntegral_mono_on ((((hg.sub continuousOn_const).norm.pow 2).integrableOn_compact
          hK).mono_set hTK) (integrableOn_const hfin) hTm fun y hy ↦
          pow_le_pow_left₀ (norm_nonneg _) (hq y hy) 2
    _ = η ^ 2 * volume.real T := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- The mean-square oscillation only depends on the values on the set. -/
theorem osc_congr {f g : E → E} {T : Set E} (hT : MeasurableSet T) (h : EqOn f g T) :
    ∫ y in T, ‖f y - ⨍ y' in T, f y'‖ ^ 2 = ∫ y in T, ‖g y - ⨍ y' in T, g y'‖ ^ 2 := by
  rw [setAverage_congr_fun hT (Eventually.of_forall fun y hy ↦ h hy)]
  exact setIntegral_congr_fun hT fun y hy ↦ by simp only [h hy]

/-- `ε₀ = min 1 √(iterEpsilon A a b)`. -/
private theorem sq_le_iterEpsilon {A a b ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (h : ε ≤ min 1 √(iterEpsilon A a b)) : ε ^ 2 ≤ iterEpsilon A a b := by
  have h1 : ε ≤ √(iterEpsilon A a b) := h.trans (min_le_right _ _)
  have h2 := pow_le_pow_left₀ hε h1 2
  rwa [Real.sq_sqrt (iterEpsilon_pos hA).le] at h2

private theorem min_one_sqrt_pos {A a b : ℝ} (hA : 0 ≤ A) :
    0 < min 1 √(iterEpsilon A a b) :=
  lt_min one_pos (Real.sqrt_pos.2 (iterEpsilon_pos hA))

/-! ### Decay -/

variable (E) in
/-- **Interior decay** for small `DΦ - 1`: `ψ(ρ) ≤ C (ρ/s)^{d+1} ψ(s)` on balls
`B_s(z) ⊆ B_R(x) ∩ {⟪·, ν⟫ > 0}`. -/
theorem interior_frozen_decay :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : E) (Φ : E → E) (U : Set E) (q₀ : E) (η ε : ℝ)
      (x z : E) (R s ρ : ℝ) (w : E → ℝ), ‖ν‖ = 1 → SmallOscData Φ U q₀ η ε → ε ≤ ε₀ →
      0 < R → -R < ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x R w →
      (∀ y ∈ halfBall ν x R, gradientWithin w (halfBall ν x R) y ∈ closedBall q₀ η) →
      ball z s ⊆ ball x R ∩ openHalfSpace ν → 0 < ρ → ρ ≤ s →
      ∫ y in ball z ρ, ‖gradientWithin w (halfBall ν x R) y -
          ⨍ y' in ball z ρ, gradientWithin w (halfBall ν x R) y'‖ ^ 2 ≤
        C * (ρ / s) ^ (finrank ℝ E + 1) *
          ∫ y in ball z s, ‖gradientWithin w (halfBall ν x R) y -
            ⨍ y' in ball z s, gradientWithin w (halfBall ν x R) y'‖ ^ 2 := by
  obtain ⟨CI, hCI, hstep⟩ := interior_frozen_step E
  set a : ℝ := ((finrank ℝ E + 2 : ℕ) : ℝ) with ha
  set b : ℝ := ((finrank ℝ E + 1 : ℕ) : ℝ) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hab : b < a := by rw [ha, hb]; exact_mod_cast (by omega : finrank ℝ E + 1 < finrank ℝ E + 2)
  refine ⟨min 1 √(iterEpsilon CI a b), min_one_sqrt_pos hCI, iterConstEps CI a b,
    iterConstEps_nonneg hCI hab, ?_⟩
  intro ν Φ U q₀ η ε x z R s ρ w hν hD hε hR hx h hrange hzs hρ hρs
  have hs : 0 < s := hρ.trans_le hρs
  set B := halfBall ν x R with hB
  set gW := gradientWithin w B with hgW
  have hgc : ContinuousOn gW B := continuousOn_gradientWithin_halfBall hν hR hx h.1
  have hcl : closedBall z s ⊆ B := closedBall_subset_halfBall_of_ball_subset hs hzs
  set ψ : ℝ → ℝ := fun t ↦ ∫ y in ball z t, ‖gW y - ⨍ y' in ball z t, gW y'‖ ^ 2 with hψ
  have hmono : MonotoneOn ψ (Ioc 0 s) := fun t₁ h₁ t₂ h₂ h12 ↦
    osc_le_of_subset (isCompact_closedBall z s) (hgc.mono hcl)
      (ball_subset_closedBall.trans (closedBall_subset_closedBall h₂.2))
      (ball_subset_ball h12) _
  have hnn : ∀ t ∈ Ioc 0 s, 0 ≤ ψ t := fun t _ ↦
    setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hst : ∀ ρ' r', 0 < ρ' → ρ' ≤ r' → r' ≤ s →
      ψ ρ' ≤ CI * ((ρ' / r') ^ a + ε ^ 2) * ψ r' + 0 * r' ^ b := by
    intro ρ' r' hρ' hρr' hr's
    have := hstep ν Φ U q₀ η ε x z R r' ρ' w hν hD hR hx h hrange
      ((ball_subset_ball hr's).trans hzs) hρ' hρr'
    rw [ha, Real.rpow_natCast, zero_mul, add_zero, mul_assoc]
    exact this
  have hit := campanato_iteration_eps hb0 hab hCI le_rfl
    (sq_le_iterEpsilon hCI hD.nonneg hε) hmono hnn hst ρ s hρ hρs le_rfl
  rw [hb, Real.rpow_natCast, zero_mul, add_zero, ← mul_assoc] at hit
  exact hit

variable (E) in
/-- **Flat decay** for small `DΦ - 1`: with `ψ(t) = ∫_{B_t(z) ∩ H} ‖∇w - (∇w)_{B_t(z) ∩ H}‖²`
for `z` on the flat part and `halfBall ν z s` inside the domain, `ψ(ρ) ≤ C (ρ/s)^{d+1} ψ(s)`. -/
theorem flat_frozen_decay {ν : E} (hν : ‖ν‖ = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → E) (U : Set E) (q₀ : E) (η ε : ℝ)
      (x z : E) (R s ρ : ℝ) (w : E → ℝ), SmallOscData Φ U q₀ η ε → ε ≤ ε₀ →
      0 < R → -R < ⟪x, ν⟫ → IsQuasilinearConormalSolOn ν Φ x R w →
      (∀ y ∈ halfBall ν x R, gradientWithin w (halfBall ν x R) y ∈ closedBall q₀ η) →
      ⟪z, ν⟫ = 0 → closedBall z s ⊆ closedBall x R → ball z s ⊆ ball x R → 0 < ρ → ρ ≤ s →
      ∫ y in ball z ρ ∩ halfSpace ν, ‖gradientWithin w (halfBall ν x R) y -
          ⨍ y' in ball z ρ ∩ halfSpace ν, gradientWithin w (halfBall ν x R) y'‖ ^ 2 ≤
        C * (ρ / s) ^ (finrank ℝ E + 1) *
          ∫ y in ball z s ∩ halfSpace ν, ‖gradientWithin w (halfBall ν x R) y -
            ⨍ y' in ball z s ∩ halfSpace ν, gradientWithin w (halfBall ν x R) y'‖ ^ 2 := by
  obtain ⟨CF, hCF, hstep⟩ := flat_frozen_step E hν
  set a : ℝ := ((finrank ℝ E + 2 : ℕ) : ℝ) with ha
  set b : ℝ := ((finrank ℝ E + 1 : ℕ) : ℝ) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hab : b < a := by rw [ha, hb]; exact_mod_cast (by omega : finrank ℝ E + 1 < finrank ℝ E + 2)
  refine ⟨min 1 √(iterEpsilon CF a b), min_one_sqrt_pos hCF, iterConstEps CF a b,
    iterConstEps_nonneg hCF hab, ?_⟩
  intro Φ U q₀ η ε x z R s ρ w hD hε hR hx h hrange hz hcl hbl hρ hρs
  have hs : 0 < s := hρ.trans_le hρs
  set B := halfBall ν x R with hB
  set gW := gradientWithin w B with hgW
  have hgc : ContinuousOn gW B := continuousOn_gradientWithin_halfBall hν hR hx h.1
  have hsub : ∀ {t}, t ≤ s → halfBall ν z t ⊆ B := fun {t} ht ↦
    inter_subset_inter_left _ ((closedBall_subset_closedBall ht).trans hcl)
  have hsub' : ∀ {t}, ball z t ∩ halfSpace ν ⊆ halfBall ν z t := fun {t} y hy ↦
    ⟨ball_subset_closedBall hy.1, hy.2⟩
  have hmeas : ∀ t, MeasurableSet (ball z t ∩ halfSpace ν) := fun t ↦
    measurableSet_ball.inter (measurableSet_halfSpace ν)
  set ψ : ℝ → ℝ := fun t ↦
    ∫ y in ball z t ∩ halfSpace ν, ‖gW y - ⨍ y' in ball z t ∩ halfSpace ν, gW y'‖ ^ 2 with hψ
  have hmono : MonotoneOn ψ (Ioc 0 s) := fun t₁ h₁ t₂ h₂ h12 ↦
    osc_le_of_subset (isCompact_halfBall ν x R) hgc (hsub'.trans (hsub h₂.2))
      (inter_subset_inter_left _ (ball_subset_ball h12)) _
  have hnn : ∀ t ∈ Ioc 0 s, 0 ≤ ψ t := fun t _ ↦
    setIntegral_nonneg (hmeas t) fun _ _ ↦ sq_nonneg _
  have hst : ∀ ρ' r', 0 < ρ' → ρ' ≤ r' → r' ≤ s →
      ψ ρ' ≤ CF * ((ρ' / r') ^ a + ε ^ 2) * ψ r' + 0 * r' ^ b := by
    intro ρ' r' hρ' hρr' hr's
    have hr' : 0 < r' := hρ'.trans_le hρr'
    have hz' : -r' < ⟪z, ν⟫ := by rw [hz]; linarith
    have hres := h.restrict hν hr' hz' ((closedBall_subset_closedBall hr's).trans hcl)
      ((ball_subset_ball hr's).trans hbl)
    have hu := uniqueDiffOn_halfBall hν hr' hz'
    have heq : EqOn (gradientWithin w (halfBall ν z r')) gW (halfBall ν z r') := fun y hy ↦
      gradientWithin_eq_of_subset (hsub hr's) (hu y hy)
        (h.1.differentiableOn one_ne_zero y (hsub hr's hy))
    have := hstep Φ U q₀ η ε z r' ρ' w hD hz hres
      (fun y hy ↦ by rw [heq hy]; exact hrange y (hsub hr's hy)) hρ' hρr'
    rw [osc_congr (hmeas ρ') (heq.mono (hsub'.trans (halfBall_mono ν z hρr'))),
      osc_congr (hmeas r') (heq.mono hsub')] at this
    rw [ha, Real.rpow_natCast, zero_mul, add_zero, mul_assoc]
    exact this
  have hit := campanato_iteration_eps hb0 hab hCF le_rfl
    (sq_le_iterEpsilon hCF hD.nonneg hε) hmono hnn hst ρ s hρ hρs le_rfl
  rw [hb, Real.rpow_natCast, zero_mul, add_zero, ← mul_assoc] at hit
  exact hit

/-! ### Local Hölder continuity -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem inner_ge_of_dist {ν p y : E} (hν : ‖ν‖ = 1) {s : ℝ} (hy : y ∈ ball p s) :
    ⟪p, ν⟫ - s < ⟪y, ν⟫ := by
  have h1 : |⟪y - p, ν⟫| ≤ ‖y - p‖ := by
    simpa [hν] using abs_real_inner_le_norm (y - p) ν
  have h2 : ‖y - p‖ < s := by rw [← dist_eq_norm]; exact hy
  rw [inner_sub_left] at h1
  linarith [neg_abs_le (⟪y, ν⟫ - ⟪p, ν⟫)]

variable (E) in
/-- **Local `C^{1,1/2}` for small `DΦ - 1`**: under `Div.SmallOscData` with `ε ≤ ε₀(E, ν)`, a
`C¹` quasilinear conormal solution on `halfBall ν z₀ R` (`⟪z₀, ν⟫ ≥ 0`) whose gradient lies in
`closedBall q₀ η` has a `1/2`-Hölder gradient on `halfBall ν z₀ (R/16)`. -/
theorem holderOnWith_gradientWithin_of_smallOsc {ν : E} (hν : ‖ν‖ = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (Φ : E → E) (U : Set E) (q₀ : E) (η ε : ℝ)
      (z₀ : E) (R : ℝ) (w : E → ℝ), SmallOscData Φ U q₀ η ε → ε ≤ ε₀ → 0 < R → 0 ≤ ⟪z₀, ν⟫ →
      IsQuasilinearConormalSolOn ν Φ z₀ R w →
      (∀ y ∈ halfBall ν z₀ R, gradientWithin w (halfBall ν z₀ R) y ∈ closedBall q₀ η) →
      HolderOnWith (Real.toNNReal (C₀ * η / √R)) (1 / 2 : ℝ≥0)
        (gradientWithin w (halfBall ν z₀ R)) (halfBall ν z₀ (R / 16)) := by
  obtain ⟨ε₁, hε₁, CI, hCI, hint⟩ := interior_frozen_decay E
  obtain ⟨ε₂, hε₂, CF, hCF, hflat⟩ := flat_frozen_decay E hν
  obtain ⟨Ch, hcamp⟩ := holderOnWith_of_campanato (E := E) E (1 / 2) (by norm_num) (by norm_num)
  set κ : ℝ := 16 * CI * unitBallVolume E +
    2 * (CI + 1) * (2 ^ (finrank ℝ E + 1)) ^ 2 * CF * unitBallVolume E with hκ
  have hκ0 : 0 ≤ κ := by have := (unitBallVolume_pos (E := E)).le; positivity
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, max Ch 0 * √(κ / halfBallDensityConst E),
    mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _), ?_⟩
  intro Φ U q₀ η ε z₀ R w hD hε hR hz₀ h hrange
  have hεI : ε ≤ ε₁ := hε.trans (min_le_left _ _)
  have hεF : ε ≤ ε₂ := hε.trans (min_le_right _ _)
  have hR' : -R < ⟪z₀, ν⟫ := by linarith
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  set D := halfBall ν z₀ R with hDdef
  set G₀ := gradientWithin w D with hG₀
  have hDc : IsCompact D := isCompact_halfBall ν z₀ R
  have hgc : ContinuousOn G₀ D := continuousOn_gradientWithin_halfBall hν hR hR' h.1
  have hq : ∀ y ∈ D, ‖G₀ y - q₀‖ ≤ η := fun y hy ↦ by
    rw [← dist_eq_norm]; exact hrange y hy
  have hη : 0 ≤ η := hD.pos.le
  set θ := R / 16 with hθdef
  have hθ : 0 < θ := by positivity
  set Sf := R / 2 with hSf
  have hSf0 : 0 < Sf := by positivity
  set d := finrank ℝ E
  set vB := unitBallVolume E
  have hvB : 0 < vB := unitBallVolume_pos
  set c₀ := halfBallDensityConst E
  have hc₀ : 0 < c₀ := halfBallDensityConst_pos
  set S := halfBall ν z₀ θ with hS
  set KF := CF * 2 ^ (d + 1) * η ^ 2 * vB * Sf ^ d / Sf ^ (d + 1) with hKF
  set K := CI * η ^ 2 * vB * θ ^ d / θ ^ (d + 1) + CI * KF * 2 ^ (d + 1) + KF * 2 ^ (d + 1)
    with hK
  have hKF0 : 0 ≤ KF := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hHm : ∀ t, MeasurableSet (ball z₀ t ∩ halfSpace ν) := fun t ↦
    measurableSet_ball.inter (measurableSet_halfSpace ν)
  -- the flat decay at foot points, from the crude bound at scale `Sf`
  have hflat' : ∀ pb : E, ⟪pb, ν⟫ = 0 → dist pb z₀ ≤ 2 * θ → ∀ τ, 0 < τ → τ ≤ Sf →
      ∫ y in ball pb τ ∩ halfSpace ν, ‖G₀ y - ⨍ y' in ball pb τ ∩ halfSpace ν, G₀ y'‖ ^ 2 ≤
        KF * τ ^ (d + 1) := by
    intro pb hpb hdist τ hτ hτS
    have hcl : closedBall pb Sf ⊆ closedBall z₀ R := closedBall_subset_closedBall' (by linarith)
    have hbl : ball pb Sf ⊆ ball z₀ R := ball_subset_ball' (by linarith)
    have hHD : ball pb Sf ∩ halfSpace ν ⊆ D := fun y hy ↦
      ⟨hcl (ball_subset_closedBall hy.1), hy.2⟩
    have h1 := hflat Φ U q₀ η ε z₀ pb R Sf τ w hD hεF hR hR' h hrange hpb hcl hbl hτ hτS
    have h2 := osc_le_crude hDc hgc hHD (measurableSet_ball.inter (measurableSet_halfSpace ν))
      (fun y hy ↦ hq y (hHD hy))
    have h3 : volume.real (ball pb Sf ∩ halfSpace ν) ≤ Sf ^ d * vB := by
      rw [← measureReal_ball_eq hSf0]
      exact measureReal_mono inter_subset_left measure_ball_lt_top.ne
    have h4 : CF * (τ / Sf) ^ (finrank ℝ E + 1) ≥ 0 := by positivity
    calc _ ≤ CF * (τ / Sf) ^ (finrank ℝ E + 1) * _ := h1
      _ ≤ CF * (τ / Sf) ^ (finrank ℝ E + 1) * (η ^ 2 * (Sf ^ d * vB)) := by
          gcongr; exact h2.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
      _ = CF * η ^ 2 * vB * Sf ^ d / Sf ^ (d + 1) * τ ^ (d + 1) := by
          rw [div_pow]; field_simp; ring
      _ ≤ KF * τ ^ (d + 1) := by
          rw [hKF]
          have : CF * η ^ 2 * vB * Sf ^ d / Sf ^ (d + 1) ≤
              CF * 2 ^ (d + 1) * η ^ 2 * vB * Sf ^ d / Sf ^ (d + 1) := by
            have h2d : (1 : ℝ) ≤ 2 ^ (d + 1) := one_le_pow₀ (by norm_num)
            gcongr
            nlinarith [show 0 ≤ CF from hCF]
          exact mul_le_mul_of_nonneg_right this (by positivity)
  -- the interior decay, from scale `s'`
  have hint' : ∀ p : E, dist p z₀ ≤ θ → ∀ s', 0 < s' → s' ≤ θ → s' ≤ ⟪p, ν⟫ →
      ball p s' ⊆ ball z₀ R ∩ openHalfSpace ν := by
    intro p hp s' hs' hs'θ hs'h y hy
    refine ⟨?_, mem_openHalfSpace.2 (by linarith [inner_ge_of_dist hν hy])⟩
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y p z₀]
  have hball_D : ∀ {p : E} {s'}, ball p s' ⊆ ball z₀ R ∩ openHalfSpace ν → ball p s' ⊆ D :=
    fun hsub y hy ↦ ⟨ball_subset_closedBall (hsub hy).1,
      openHalfSpace_subset_halfSpace ν (hsub hy).2⟩
  -- the key Campanato bound at every point of `S`
  have KC : ∀ p ∈ S, ∀ t, 0 < t → t ≤ θ → ∃ c : E,
      ∫ y in ball p t ∩ halfSpace ν, ‖G₀ y - c‖ ^ 2 ≤ K * t ^ (d + 1) := by
    intro p hp t ht htθ
    have hpz : dist p z₀ ≤ θ := mem_closedBall.1 (mem_halfBall.1 hp).1
    set h₀ := ⟪p, ν⟫ with hh₀
    have hh0 : 0 ≤ h₀ := (mem_halfBall.1 hp).2
    set pb := p - h₀ • ν with hpb
    have hpbν : ⟪pb, ν⟫ = 0 := by
      rw [hpb, inner_sub_left, real_inner_smul_left, hν1, mul_one, ← hh₀, sub_self]
    have hppb : dist p pb = h₀ := by
      rw [hpb, dist_eq_norm, sub_sub_cancel, norm_smul, hν, mul_one, Real.norm_of_nonneg hh0]
    have htd : 0 ≤ t ^ (d + 1) := by positivity
    have hK1 : 0 ≤ CI * η ^ 2 * vB * θ ^ d / θ ^ (d + 1) := by positivity
    have hK2 : 0 ≤ CI * KF * 2 ^ (d + 1) := by positivity
    have hK3 : 0 ≤ KF * 2 ^ (d + 1) := by positivity
    rcases lt_or_ge h₀ t with hht | hth
    · -- the ball meets (or nearly meets) the flat part: enlarge to a half ball at `pb`
      refine ⟨⨍ y' in ball pb (2 * t) ∩ halfSpace ν, G₀ y', ?_⟩
      have hdist : dist pb z₀ ≤ 2 * θ := by
        linarith [dist_triangle pb p z₀, dist_comm p pb]
      have hsub : ball p t ∩ halfSpace ν ⊆ ball pb (2 * t) ∩ halfSpace ν := by
        rintro y ⟨hy1, hy2⟩
        refine ⟨?_, hy2⟩
        rw [mem_ball] at hy1 ⊢; linarith [dist_triangle y p pb]
      have hHD : ball pb (2 * t) ∩ halfSpace ν ⊆ D := by
        rintro y ⟨hy1, hy2⟩
        refine ⟨?_, hy2⟩
        rw [mem_closedBall]; rw [mem_ball] at hy1
        linarith [dist_triangle y pb z₀]
      calc ∫ y in ball p t ∩ halfSpace ν, ‖G₀ y - ⨍ y' in ball pb (2 * t) ∩ halfSpace ν, G₀ y'‖ ^ 2
          ≤ ∫ y in ball pb (2 * t) ∩ halfSpace ν,
              ‖G₀ y - ⨍ y' in ball pb (2 * t) ∩ halfSpace ν, G₀ y'‖ ^ 2 :=
            setIntegral_mono_set ((((hgc.sub continuousOn_const).norm.pow 2).integrableOn_compact
              hDc).mono_set hHD) (Eventually.of_forall fun _ ↦ sq_nonneg _) hsub.eventuallyLE
        _ ≤ KF * (2 * t) ^ (d + 1) := hflat' pb hpbν hdist (2 * t) (by positivity)
            (by rw [hSf, hθdef] at *; linarith)
        _ = KF * 2 ^ (d + 1) * t ^ (d + 1) := by rw [mul_pow]; ring
        _ ≤ K * t ^ (d + 1) := by
            apply mul_le_mul_of_nonneg_right _ htd; rw [hK]; linarith
    · -- an interior ball
      refine ⟨⨍ y' in ball p t, G₀ y', ?_⟩
      have hh₀pos : 0 < h₀ := ht.trans_le hth
      have hset : ball p t ∩ halfSpace ν = ball p t := inter_eq_left.2 fun y hy ↦
        mem_halfSpace.2 (by linarith [inner_ge_of_dist hν hy])
      rw [hset]
      set ψ := fun s' ↦ ∫ y in ball p s', ‖G₀ y - ⨍ y' in ball p s', G₀ y'‖ ^ 2 with hψ
      change ψ t ≤ _
      rcases le_or_gt θ h₀ with hθh | hhθ
      · have hsub := hint' p hpz θ hθ le_rfl hθh
        have h1 := hint ν Φ U q₀ η ε z₀ p R θ t w hν hD hεI hR hR' h hrange hsub ht htθ
        have h2 := osc_le_crude hDc hgc (hball_D hsub) measurableSet_ball
          (fun y hy ↦ hq y (hball_D hsub hy))
        rw [measureReal_ball_eq hθ] at h2
        calc ψ t ≤ CI * (t / θ) ^ (finrank ℝ E + 1) * ψ θ := h1
          _ ≤ CI * (t / θ) ^ (finrank ℝ E + 1) * (η ^ 2 * (θ ^ d * vB)) := by gcongr
          _ = CI * η ^ 2 * vB * θ ^ d / θ ^ (d + 1) * t ^ (d + 1) := by
              rw [div_pow]; field_simp; ring
          _ ≤ K * t ^ (d + 1) := by
              apply mul_le_mul_of_nonneg_right _ htd; rw [hK]; linarith
      · have hsub := hint' p hpz h₀ hh₀pos hhθ.le le_rfl
        have h1 := hint ν Φ U q₀ η ε z₀ p R h₀ t w hν hD hεI hR hR' h hrange hsub ht hth
        have hdist : dist pb z₀ ≤ 2 * θ := by
          linarith [dist_triangle pb p z₀, dist_comm p pb]
        have hsub2 : ball p h₀ ⊆ ball pb (2 * h₀) ∩ halfSpace ν := fun y hy ↦
          ⟨by rw [mem_ball] at hy ⊢; linarith [dist_triangle y p pb],
            openHalfSpace_subset_halfSpace ν (hsub hy).2⟩
        have hHD : ball pb (2 * h₀) ∩ halfSpace ν ⊆ D := by
          rintro y ⟨hy1, hy2⟩
          refine ⟨?_, hy2⟩
          rw [mem_closedBall]; rw [mem_ball] at hy1
          linarith [dist_triangle y pb z₀]
        have h2 := osc_le_of_subset hDc hgc hHD hsub2
          (⨍ y' in ball pb (2 * h₀) ∩ halfSpace ν, G₀ y')
        have h3 := hflat' pb hpbν hdist (2 * h₀) (by positivity)
          (by rw [hSf, hθdef] at *; linarith)
        have h4 : ψ h₀ ≤ KF * (2 * h₀) ^ (d + 1) := h2.trans h3
        calc ψ t ≤ CI * (t / h₀) ^ (finrank ℝ E + 1) * ψ h₀ := h1
          _ ≤ CI * (t / h₀) ^ (finrank ℝ E + 1) * (KF * (2 * h₀) ^ (d + 1)) := by gcongr
          _ = CI * KF * 2 ^ (d + 1) * t ^ (d + 1) := by
              rw [div_pow, mul_pow]; field_simp; ring
          _ ≤ K * t ^ (d + 1) := by
              apply mul_le_mul_of_nonneg_right _ htd; rw [hK]; linarith
  -- Campanato on `S`
  set M := √(K / c₀) with hM
  have hdens : HasDensity S c₀ θ := halfBall_density hν hθ hz₀
  have hSD : S ⊆ D := halfBall_mono ν z₀ (by rw [hθdef]; linarith)
  have hcampS : ∀ p ∈ S, ∀ ρ ∈ Ioc 0 θ,
      ⨍ y in ball p ρ ∩ S, ‖G₀ y - ⨍ z in ball p ρ ∩ S, G₀ z‖ ^ 2 ≤
        M ^ 2 * ρ ^ (2 * (1 / 2 : ℝ)) := by
    intro p hp ρ hρ
    obtain ⟨c, hc⟩ := KC p hp ρ hρ.1 hρ.2
    have hpz : dist p z₀ ≤ θ := mem_closedBall.1 (mem_halfBall.1 hp).1
    have hT2 : ball p ρ ∩ halfSpace ν ⊆ D := by
      rintro y ⟨hy1, hy2⟩
      refine ⟨?_, hy2⟩
      rw [mem_closedBall]; rw [mem_ball] at hy1
      linarith [dist_triangle y p z₀, hρ.2]
    have h1 := osc_le_of_subset hDc hgc hT2
      (inter_subset_inter_right _ (halfBall_subset_halfSpace ν z₀ θ)) c
    have hvol := hdens p hp ρ hρ
    have hρd : 0 < ρ ^ d := pow_pos hρ.1 _
    rw [setAverage_eq, smul_eq_mul, show (2 * (1 / 2 : ℝ)) = 1 by norm_num, Real.rpow_one,
      hM, Real.sq_sqrt (by positivity)]
    have hv0 : 0 < volume.real (ball p ρ ∩ S) := lt_of_lt_of_le (by positivity) hvol
    rw [inv_mul_le_iff₀ hv0]
    calc _ ≤ K * ρ ^ (d + 1) := h1.trans hc
      _ = K / c₀ * ρ * (c₀ * ρ ^ d) := by field_simp; ring
      _ ≤ K / c₀ * ρ * volume.real (ball p ρ ∩ S) := by
          gcongr
          exact mul_nonneg (div_nonneg hK0 hc₀.le) hρ.1.le
      _ = volume.real (ball p ρ ∩ S) * (K / c₀ * ρ) := mul_comm _ _
  have hH := hcamp ν z₀ θ M G₀ hν hθ hz₀ (Real.sqrt_nonneg _) (hgc.mono hSD) hcampS
  have hKeq : K = κ * η ^ 2 / R := by
    rw [hK, hKF, hκ, hθdef, hSf]
    field_simp
    ring
  have hMeq : M = √(κ / c₀) * η / √R := by
    rw [hM, hKeq, show κ * η ^ 2 / R / c₀ = κ / c₀ * η ^ 2 / R by ring,
      Real.sqrt_div' _ hR.le, Real.sqrt_mul' _ (sq_nonneg η), Real.sqrt_sq hη]
  refine holderOnWith_iff_dist_le.2 fun p hp q hq ↦ ?_
  rw [dist_eq_norm, Real.coe_toNNReal', show (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 by norm_num]
  refine (hH p hp q hq).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _))
  refine le_trans ?_ (le_max_left _ _)
  rw [hMeq, show max Ch 0 * √(κ / c₀) * η / √R = max Ch 0 * (√(κ / c₀) * η / √R) by ring]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end BasicElliptic.Div
