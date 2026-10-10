/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.DifferenceQuotient
public import BasicElliptic.Div.Quasilinear.SmallOscillation
public import BasicElliptic.Div.Quasilinear.Flux
public import BasicElliptic.Div.Reflection
import BasicElliptic.Div.Interior.LocalHolder
import Mathlib.Analysis.Convex.Integral

/-!
# One frozen-coefficient comparison step for `C¹` quasilinear solutions

Let `w` be a `C¹` quasilinear conormal solution on a half ball (`∫_{B⁺} ⟪Φ(∇w), ∇φ⟫ = 0`) whose
gradient takes values in a closed ball `N = closedBall q₀ η` on which `DΦ` is `ε`-close to the
identity (`Div.SmallOscData`; after the normalization `DΦ(∇w(y₀)) = 1` this holds near any point
`y₀`). With `ψ(ρ) = ∫ ‖∇w - (∇w)_ρ‖²` over balls (interior) or half balls (flat centre):

* `Div.interior_frozen_step`: `ψ(ρ) ≤ C ((ρ/r)^{d+2} + ε²) ψ(r)` on balls `B_r(z)` inside the open
  half ball, `C = C(E)`;
* `Div.flat_frozen_step`: the same on half balls centred on the flat part, `C = C(E, ν)`.

## Proof

Freeze the coefficient at the mean gradient `m = (∇w)_r ∈ N`: with
`a(y) = chordCoeff Φ (∇w y) m = ∫₀¹ DΦ(m + t (∇w y - m)) dt` we have `‖a - 1‖ ≤ ε` and
`Φ(∇w) = Φ(m) + a (∇w - m)`, so `w - ⟪p, ·⟫` is a **linear** conormal solution with coefficient
`a` (`IsQuasilinearConormalSolOn.isConormalSolOn_sub_inner`).

* Interior: `p = m`, flux `G = -Φ(m)` is constant, and the comparison step
  (`campanato_step_small_osc`) applies on `B_r(z)` with `∫_{B_r} ‖∇w - m‖² = ψ(r)`.
* Flat centre: write `Φ(m) = c + g₀ ν` with `c ⊥ ν`. Take `p = m - g₀ ν` and
  `G = -c - g₀ (1 - a) ν`, so the flux is tangential up to `ε |g₀|`. Even reflection
  (`Div.IsConormalSolOn.evenReflect`) gives a weak solution on the full ball with `‖ã - 1‖ ≤ ε`
  and `‖Ǧ + c‖ ≤ ε |g₀|`; the comparison step bounds `ψ(ρ)` by
  `C ((ρ/r)^{d+2} + ε²) (∫_{B_r⁺} ‖∇w - p‖² + g₀² r^d)`, and the flux bound
  (`sq_inner_mul_pow_le_of_flux`, with `‖Φ(∇w) - Φ(m)‖ ≤ 2 ‖∇w - m‖`) gives
  `g₀² r^d ≤ C ψ(r)`. Without the shift by `g₀ ν` the reflected flux would jump by `2 g₀ ν`, an
  error that is not small compared with `ψ(r)`.

## Provenance

`intervalIntegrable_chord'` is the closed-ball variant of a private lemma of
`DifferenceQuotient.lean`. The ball splitting is `setIntegral_ball_eq_halfBall_add_reflect`
(`Div/Reflection.lean`).
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient ContDiff Topology NNReal

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The standing hypotheses of the small-oscillation argument: `Φ ∈ C¹(U)`, `U` open convex,
and `DΦ` is `ε`-close to the identity on the closed ball `closedBall q₀ η ⊆ U`, `ε ≤ 1`. -/
structure SmallOscData (Φ : E → E) (U : Set E) (q₀ : E) (η ε : ℝ) : Prop where
  isOpen : IsOpen U
  convex : Convex ℝ U
  contDiffOn : ContDiffOn ℝ 1 Φ U
  pos : 0 < η
  subset : closedBall q₀ η ⊆ U
  norm_sub_one_le : ∀ q ∈ closedBall q₀ η, ‖fderiv ℝ Φ q - 1‖ ≤ ε
  le_one : ε ≤ 1

namespace SmallOscData

variable {Φ : E → E} {U : Set E} {q₀ : E} {η ε : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem nonneg (hD : SmallOscData Φ U q₀ η ε) : 0 ≤ ε :=
  (norm_nonneg _).trans (hD.norm_sub_one_le q₀ (mem_closedBall_self hD.pos.le))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuousOn_fderiv (hD : SmallOscData Φ U q₀ η ε) :
    ContinuousOn (fderiv ℝ Φ) (closedBall q₀ η) :=
  (hD.contDiffOn.continuousOn_fderiv_of_isOpen hD.isOpen le_rfl).mono hD.subset

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem intervalIntegrable_chord' (hD : SmallOscData Φ U q₀ η ε) {p q : E}
    (hp : p ∈ closedBall q₀ η) (hq : q ∈ closedBall q₀ η) :
    IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ Φ (q + t • (p - q))) volume 0 1 :=
  (hD.continuousOn_fderiv.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    fun _ ht ↦ chord_mem (convex_closedBall q₀ η) hp hq ht).intervalIntegrable_of_Icc
    zero_le_one

omit [MeasurableSpace E] [BorelSpace E] in
/-- The chord coefficient is `ε`-close to the identity. -/
theorem norm_chordCoeff_sub_one_le (hD : SmallOscData Φ U q₀ η ε) {p q : E}
    (hp : p ∈ closedBall q₀ η) (hq : q ∈ closedBall q₀ η) : ‖chordCoeff Φ p q - 1‖ ≤ ε := by
  have h1 : chordCoeff Φ p q - 1 = ∫ t in (0 : ℝ)..1, (fderiv ℝ Φ (q + t • (p - q)) - 1) := by
    rw [intervalIntegral.integral_sub (hD.intervalIntegrable_chord' hp hq) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [chordCoeff_eq]
  rw [h1]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ ↦ fderiv ℝ Φ (q + t • (p - q)) - 1) (C := ε) fun t ht ↦
    hD.norm_sub_one_le _ (chord_mem (convex_closedBall q₀ η) hp hq
      (Ioc_subset_Icc_self (by simpa using ht)))
  simpa using this

omit [MeasurableSpace E] [BorelSpace E] in
theorem norm_chordCoeff_le (hD : SmallOscData Φ U q₀ η ε) {p q : E}
    (hp : p ∈ closedBall q₀ η) (hq : q ∈ closedBall q₀ η) : ‖chordCoeff Φ p q‖ ≤ 2 :=
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  (norm_le_norm_add_norm_sub' _ 1).trans (by
    linarith [hD.norm_chordCoeff_sub_one_le hp hq, hD.le_one])

omit [MeasurableSpace E] [BorelSpace E] in
/-- `Φ p - Φ q = chordCoeff Φ p q (p - q)` on `closedBall q₀ η`. -/
theorem sub_eq_chordCoeff_apply' (hD : SmallOscData Φ U q₀ η ε) {p q : E}
    (hp : p ∈ closedBall q₀ η) (hq : q ∈ closedBall q₀ η) :
    Φ p - Φ q = chordCoeff Φ p q (p - q) :=
  sub_eq_chordCoeff_apply hD.isOpen hD.convex hD.contDiffOn (hD.subset hp) (hD.subset hq)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Continuity of `y ↦ chordCoeff Φ (g y) m` for continuous `g` with values in
`closedBall q₀ η`. -/
theorem continuousOn_chordCoeff
    (hD : SmallOscData Φ U q₀ η ε) {S : Set E} {g : E → E} (hg : ContinuousOn g S)
    (hgN : MapsTo g S (closedBall q₀ η)) {m : E} (hm : m ∈ closedBall q₀ η) :
    ContinuousOn (fun y ↦ chordCoeff Φ (g y) m) S := by
  intro y₀ hy₀
  have hmem : ∀ y ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, m + t • (g y - m) ∈ closedBall q₀ η :=
    fun y hy t ht ↦ chord_mem (convex_closedBall q₀ η) (hgN hy) hm ht
  simp only [chordCoeff_eq]
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ ↦ 1 + ε)
    ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine hD.continuousOn_fderiv.comp (by fun_prop) fun t ht ↦ hmem y hy t ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · filter_upwards [self_mem_nhdsWithin] with y hy
    refine Eventually.of_forall fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact (norm_le_norm_add_norm_sub' _ 1).trans (add_le_add ContinuousLinearMap.norm_id_le
      (hD.norm_sub_one_le _ (hmem y hy t (Ioc_subset_Icc_self ht))))
  · refine Eventually.of_forall fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hc : ContinuousWithinAt (fun y ↦ m + t • (g y - m)) S y₀ :=
      continuousWithinAt_const.add (((hg y₀ hy₀).sub continuousWithinAt_const).const_smul t)
    exact ContinuousWithinAt.comp (g := fderiv ℝ Φ) (f := fun y ↦ m + t • (g y - m))
      (hD.continuousOn_fderiv _ (hmem y₀ hy₀ t (Ioc_subset_Icc_self ht))) hc
      fun y hy ↦ hmem y hy t (Ioc_subset_Icc_self ht)

end SmallOscData

/-! ### Linearization at a frozen gradient -/

/-- **Linearization.** If `a y (∇w y - p) = Φ(∇w y) + G y` on the half ball, with `G` continuous,
then `w - ⟪p, ·⟫` is a linear conormal solution with coefficient `a`, flux `G` and no source. -/
theorem IsQuasilinearConormalSolOn.isConormalSolOn_sub_inner {ν x : E} {r : ℝ} {Φ : E → E}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫)
    (h : IsQuasilinearConormalSolOn ν Φ x r w)
    (hΦc : ContinuousOn (fun y ↦ Φ (gradientWithin w (halfBall ν x r) y)) (halfBall ν x r))
    {a : E → E →L[ℝ] E} {G : E → E} (p : E) (hG : ContinuousOn G (halfBall ν x r))
    (hid : ∀ y ∈ halfBall ν x r, a y (gradientWithin w (halfBall ν x r) y - p) =
      Φ (gradientWithin w (halfBall ν x r) y) + G y) :
    IsConormalSolOn ν a G 0 x r (fun y ↦ w y - ⟪p, y⟫) := by
  set B := halfBall ν x r with hB
  have hu := uniqueDiffOn_halfBall hν hr hx
  refine ⟨h.1.sub (contDiff_const.inner ℝ contDiff_id).contDiffOn, fun φ hφ ↦ ?_⟩
  have hφc : Continuous (∇ φ) :=
    (toDual ℝ E).symm.continuous.comp (hφ.1.continuous_fderiv one_ne_zero)
  have hBc := isCompact_halfBall ν x r
  have i1 : IntegrableOn (fun y ↦ ⟪Φ (gradientWithin w B y), ∇ φ y⟫) B :=
    (hΦc.inner hφc.continuousOn).integrableOn_compact hBc
  have i2 : IntegrableOn (fun y ↦ ⟪G y, ∇ φ y⟫) B :=
    (hG.inner hφc.continuousOn).integrableOn_compact hBc
  have e : ∫ y in B, ⟪a y (gradientWithin (fun z ↦ w z - ⟪p, z⟫) B y), ∇ φ y⟫ =
      ∫ y in B, (⟪Φ (gradientWithin w B y), ∇ φ y⟫ + ⟪G y, ∇ φ y⟫) :=
    setIntegral_congr_fun (measurableSet_halfBall ν x r) fun y hy ↦ by
      rw [gradientWithin_sub_inner p (hu y hy) (h.1.differentiableOn one_ne_zero y hy), hid y hy,
        inner_add_left]
  change ∫ y in B, ⟪a y (gradientWithin (fun z ↦ w z - ⟪p, z⟫) B y), ∇ φ y⟫ =
    (∫ y in B, ⟪G y, ∇ φ y⟫) + ∫ y in B, (0 : E → ℝ) y * φ y
  rw [e, integral_add i1 i2, h.2 φ hφ, zero_add]
  simp

/-! ### Integrability helpers -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A ball inside `ball x R ∩ openHalfSpace ν` has its closure inside `halfBall ν x R`. -/
theorem closedBall_subset_halfBall_of_ball_subset {ν x z : E} {R r : ℝ} (hr : 0 < r)
    (h : ball z r ⊆ ball x R ∩ openHalfSpace ν) : closedBall z r ⊆ halfBall ν x R := by
  rw [← closure_ball z hr.ne']
  refine (closure_mono h).trans ((closure_inter_subset_inter_closure _ _).trans ?_)
  exact inter_subset_inter (closure_ball_subset_closedBall)
    ((isClosed_halfSpace ν).closure_subset_iff.2 (openHalfSpace_subset_halfSpace ν))

theorem integrableOn_of_continuousOn_compact {S K T : Set E} {g : E → E} (hg : ContinuousOn g S)
    (hK : IsCompact K) (hKS : K ⊆ S) (hTK : T ⊆ K) :
    IntegrableOn g T ∧ IntegrableOn (fun y ↦ ‖g y‖ ^ 2) T :=
  ⟨((hg.mono hKS).integrableOn_compact hK).mono_set hTK,
    (((hg.mono hKS).norm.pow 2).integrableOn_compact hK).mono_set hTK⟩

/-! ### The interior step -/

variable (E) in
/-- **Frozen-coefficient step on interior balls** (see the module docstring): with
`ψ(s) = ∫_{B_s(z)} ‖∇w - (∇w)_s‖²`, `ψ(ρ) ≤ C ((ρ/r)^{d+2} + ε²) ψ(r)` for `0 < ρ ≤ r` and
`B_r(z) ⊆ B_R(x) ∩ {⟪·, ν⟫ > 0}`; `C = C(E)`. -/
theorem interior_frozen_step :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : E) (Φ : E → E) (U : Set E) (q₀ : E) (η ε : ℝ) (x z : E)
      (R r ρ : ℝ) (w : E → ℝ), ‖ν‖ = 1 → SmallOscData Φ U q₀ η ε → 0 < R → -R < ⟪x, ν⟫ →
      IsQuasilinearConormalSolOn ν Φ x R w →
      (∀ y ∈ halfBall ν x R, gradientWithin w (halfBall ν x R) y ∈ closedBall q₀ η) →
      ball z r ⊆ ball x R ∩ openHalfSpace ν → 0 < ρ → ρ ≤ r →
      ∫ y in ball z ρ, ‖gradientWithin w (halfBall ν x R) y -
          ⨍ y' in ball z ρ, gradientWithin w (halfBall ν x R) y'‖ ^ 2 ≤
        C * (((ρ / r) ^ (finrank ℝ E + 2) + ε ^ 2) *
          ∫ y in ball z r, ‖gradientWithin w (halfBall ν x R) y -
            ⨍ y' in ball z r, gradientWithin w (halfBall ν x R) y'‖ ^ 2) := by
  obtain ⟨C, hC, hstep⟩ := campanato_step_small_osc E
  refine ⟨C, hC, ?_⟩
  intro ν Φ U q₀ η ε x z R r ρ w hν hD hR hx h hrange hzV hρ hρr
  have hr : 0 < r := hρ.trans_le hρr
  set B := halfBall ν x R with hB
  set gW := gradientWithin w B with hgW
  set V := ball x R ∩ openHalfSpace ν with hV
  have hgc : ContinuousOn gW B := continuousOn_gradientWithin_halfBall hν hR hx h.1
  have hcl : closedBall z r ⊆ B := closedBall_subset_halfBall_of_ball_subset hr hzV
  have hzB : ball z r ⊆ B := ball_subset_closedBall.trans hcl
  obtain ⟨hgi, hgi2⟩ := integrableOn_of_continuousOn_compact hgc (isCompact_closedBall z r) hcl
    ball_subset_closedBall
  -- the frozen gradient
  set m := ⨍ y in ball z r, gW y with hmdef
  have hm : m ∈ closedBall q₀ η :=
    Convex.set_average_mem (convex_closedBall q₀ η) isClosed_closedBall
      (measure_ball_pos _ _ hr).ne'
      measure_ball_lt_top.ne ((ae_restrict_iff' measurableSet_ball).2
        (Eventually.of_forall fun y hy ↦ hrange y (hzB hy))) hgi
  set a : E → E →L[ℝ] E := fun y ↦ chordCoeff Φ (gW y) m with ha
  have hac : ContinuousOn a B := hD.continuousOn_chordCoeff hgc (fun y hy ↦ hrange y hy) hm
  have hΦc : ContinuousOn (fun y ↦ Φ (gW y)) B :=
    hD.contDiffOn.continuousOn.comp hgc fun y hy ↦ hD.subset (hrange y hy)
  have hlin := h.isConormalSolOn_sub_inner hν hR hx hΦc (a := a) (G := fun _ ↦ -Φ m) m
    continuousOn_const fun y hy ↦ by
      simp only [ha]
      rw [← hD.sub_eq_chordCoeff_apply' (hrange y hy) hm]
      abel
  set w' : E → ℝ := fun y ↦ w y - ⟪m, y⟫ with hw'
  have hWV := hlin.isWeakSolOn
  have hw'c : ContDiffOn ℝ 1 w' (ball z r) := hWV.1.mono hzV
  set F := ∇ w' with hF
  have hu := uniqueDiffOn_halfBall hν hR hx
  have hFeq : ∀ y ∈ ball z r, F y = gW y - m := fun y hy ↦ by
    rw [hF, ← gradientWithin_halfBall_eq (hzV hy)]
    exact gradientWithin_sub_inner m (hu y (hzB hy)) (h.1.differentiableOn one_ne_zero y (hzB hy))
  -- the comparison step
  have hFM : ∀ y ∈ ball z r, ‖F y‖ ≤ 2 * η := fun y hy ↦ by
    rw [hFeq y hy, ← dist_eq_norm]
    have h1 := mem_closedBall.1 (hrange y (hzB hy))
    have h2 := mem_closedBall.1 hm
    linarith [dist_triangle_right (gW y) m q₀]
  have hweak : IsWeakEqOn a (fun _ ↦ -Φ m) 0 F (ball z r) (ball z r) := by
    intro φ hφ
    have key := hWV.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hzV⟩
    have h0 := fun y hy ↦ hφ.eq_zero_and_gradient_eq_zero (y := y) hy
    have hVm : MeasurableSet V := isOpen_ball.measurableSet.inter (measurableSet_openHalfSpace ν)
    rw [setIntegral_eq_of_inter_subset hVm hzV inter_subset_right
        fun y hy ↦ by simp [(h0 y hy).2],
      setIntegral_eq_of_inter_subset hVm hzV inter_subset_right fun y hy ↦ by simp [(h0 y hy).2],
      setIntegral_eq_of_inter_subset hVm hzV inter_subset_right
        fun y hy ↦ by simp [(h0 y hy).1]] at key
    exact key
  have hS := hstep z r ρ (2 * η) ε 0 F (fun _ ↦ -Φ m) (-Φ m) a hρ hρr
    ((continuousOn_gradient_of_contDiffOn isOpen_ball hw'c).aestronglyMeasurable
      measurableSet_ball) hFM (isWeakCurlFree_gradient_of_contDiffOn isOpen_ball hw'c)
    ((hac.mono hzB).aestronglyMeasurable measurableSet_ball)
    (fun y hy ↦ hD.norm_chordCoeff_sub_one_le (hrange y (hzB hy)) hm)
    aestronglyMeasurable_const (fun y _ ↦ by simp) hweak
  -- back to `∇w`
  have hρr' : ball z ρ ⊆ ball z r := ball_subset_ball hρr
  have hFr : ∫ y in ball z r, ‖F y‖ ^ 2 = ∫ y in ball z r, ‖gW y - m‖ ^ 2 :=
    setIntegral_congr_fun measurableSet_ball fun y hy ↦ by simp only [hFeq y hy]
  have hFρ : ∫ y in ball z ρ, ‖gW y - ⨍ y' in ball z ρ, gW y'‖ ^ 2 ≤
      ∫ y in ball z ρ, ‖F y - ⨍ y' in ball z ρ, F y'‖ ^ 2 := by
    refine (setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne (hgi.mono_set hρr')
      (hgi2.mono_set hρr') (m + ⨍ y' in ball z ρ, F y')).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
    simp only [hFeq y (hρr' hy)]
    congr 1
    abel_nf
  rw [hFr, zero_pow two_ne_zero, zero_mul, add_zero] at hS
  exact hFρ.trans hS

/-! ### The flat step -/

variable (E) in
/-- **Frozen-coefficient step at flat points** (see the module docstring): with
`ψ(s) = ∫_{B_s(x) ∩ H} ‖∇w - (∇w)_{B_s(x) ∩ H}‖²` (`H = halfSpace ν`, `x` on the flat part),
`ψ(ρ) ≤ C ((ρ/r)^{d+2} + ε²) ψ(r)` for `0 < ρ ≤ r`; `C = C(E, ν)`. -/
theorem flat_frozen_step {ν : E} (hν : ‖ν‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → E) (U : Set E) (q₀ : E) (η ε : ℝ) (x : E) (r ρ : ℝ)
      (w : E → ℝ), SmallOscData Φ U q₀ η ε → ⟪x, ν⟫ = 0 → IsQuasilinearConormalSolOn ν Φ x r w →
      (∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ closedBall q₀ η) →
      0 < ρ → ρ ≤ r →
      ∫ y in ball x ρ ∩ halfSpace ν, ‖gradientWithin w (halfBall ν x r) y -
          ⨍ y' in ball x ρ ∩ halfSpace ν, gradientWithin w (halfBall ν x r) y'‖ ^ 2 ≤
        C * (((ρ / r) ^ (finrank ℝ E + 2) + ε ^ 2) *
          ∫ y in ball x r ∩ halfSpace ν, ‖gradientWithin w (halfBall ν x r) y -
            ⨍ y' in ball x r ∩ halfSpace ν, gradientWithin w (halfBall ν x r) y'‖ ^ 2) := by
  obtain ⟨CA, hCA, hstep⟩ := campanato_step_small_osc E
  obtain ⟨Cf, hCf, hflux⟩ := sq_inner_mul_pow_le_of_flux E hν
  set vB := unitBallVolume E
  have hvB : 0 < vB := unitBallVolume_pos
  refine ⟨CA * (4 + 16 * vB * Cf + 4 * Cf), by positivity, ?_⟩
  intro Φ U q₀ η ε x r ρ w hD hx h hrange hρ hρr
  have hr : 0 < r := hρ.trans_le hρr
  have hxr : -r < ⟪x, ν⟫ := by rw [hx]; linarith
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  have hε := hD.nonneg
  set B := halfBall ν x r with hB
  set gW := gradientWithin w B with hgW
  set S := ball x r ∩ halfSpace ν with hS
  have hBm : MeasurableSet B := measurableSet_halfBall ν x r
  have hSm : MeasurableSet S := measurableSet_ball.inter (measurableSet_halfSpace ν)
  have hgc : ContinuousOn gW B := continuousOn_gradientWithin_halfBall hν hr hxr h.1
  have hSB : ∀ {s}, s ≤ r → ball x s ∩ halfSpace ν ⊆ B := fun {s} hs y hy ↦
    ⟨ball_subset_closedBall (ball_subset_ball hs hy.1), hy.2⟩
  have hBc : IsCompact B := isCompact_halfBall ν x r
  obtain ⟨hgi, hgi2⟩ := integrableOn_of_continuousOn_compact hgc hBc subset_rfl (hSB le_rfl)
  have hSpos : volume S ≠ 0 := by
    refine (ne_of_gt ?_)
    refine lt_of_lt_of_le ?_ (measure_mono (inter_subset_inter_right _
      (openHalfSpace_subset_halfSpace ν)))
    refine (isOpen_ball.inter (isOpen_openHalfSpace ν)).measure_pos _ ⟨x + (r / 2) • ν, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith
    · rw [mem_openHalfSpace, inner_add_left, hx, real_inner_smul_left, hν1]; linarith
  have hSfin : volume S ≠ ⊤ := (measure_mono inter_subset_left).trans_lt measure_ball_lt_top |>.ne
  -- the frozen gradient and its normal flux
  set m := ⨍ y in S, gW y with hmdef
  have hm : m ∈ closedBall q₀ η :=
    Convex.set_average_mem (convex_closedBall q₀ η) isClosed_closedBall hSpos hSfin
      ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun y hy ↦ hrange y (hSB le_rfl hy))) hgi
  set g₀ := ⟪Φ m, ν⟫ with hg₀
  set c := Φ m - g₀ • ν with hc
  have hcν : ⟪c, ν⟫ = 0 := by rw [hc, inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]
  set p := m - g₀ • ν with hp
  set a : E → E →L[ℝ] E := fun y ↦ chordCoeff Φ (gW y) m with ha
  have hac : ContinuousOn a B := hD.continuousOn_chordCoeff hgc (fun y hy ↦ hrange y hy) hm
  set G : E → E := fun y ↦ -c - g₀ • ((1 - a y) ν) with hG
  have hGc : ContinuousOn G B :=
    continuousOn_const.sub (((continuousOn_const.sub hac).clm_apply continuousOn_const).const_smul
      g₀)
  have hΦc : ContinuousOn (fun y ↦ Φ (gW y)) B :=
    hD.contDiffOn.continuousOn.comp hgc fun y hy ↦ hD.subset (hrange y hy)
  have hid : ∀ y ∈ B, a y (gW y - p) = Φ (gW y) + G y := fun y hy ↦ by
    have e1 : gW y - p = (gW y - m) + g₀ • ν := by rw [hp]; abel
    have e2 := hD.sub_eq_chordCoeff_apply' (hrange y hy) hm
    simp only [ha, hG, hc, e1, map_add, map_smul, ← e2, sub_apply,
      one_apply_eq_self, smul_sub]
    abel
  have hlin := h.isConormalSolOn_sub_inner hν hr hxr hΦc p hGc hid
  set w' : E → ℝ := fun y ↦ w y - ⟪p, y⟫ with hw'
  have hu := uniqueDiffOn_halfBall hν hr hxr
  have hgw' : ∀ y ∈ B, gradientWithin w' B y = gW y - p := fun y hy ↦
    gradientWithin_sub_inner p (hu y hy) (h.1.differentiableOn one_ne_zero y hy)
  -- bounds on the half ball
  have hdist : ∀ y ∈ B, ‖gW y - m‖ ≤ 2 * η := fun y hy ↦ by
    rw [← dist_eq_norm]
    have h1 := mem_closedBall.1 (hrange y hy)
    have h2 := mem_closedBall.1 hm
    linarith [dist_triangle_right (gW y) m q₀]
  have hgw'M : ∀ y ∈ B, ‖gradientWithin w' B y‖ ≤ 2 * η + |g₀| := fun y hy ↦ by
    rw [hgw' y hy, show gW y - p = (gW y - m) + g₀ • ν by rw [hp]; abel]
    refine (norm_add_le _ _).trans (add_le_add (hdist y hy) ?_)
    rw [norm_smul, hν, mul_one, Real.norm_eq_abs]
  have ha1 : ∀ y ∈ B, ‖a y - 1‖ ≤ ε := fun y hy ↦
    hD.norm_chordCoeff_sub_one_le (hrange y hy) hm
  have haB : ∀ y ∈ B, ‖a y‖ ≤ 2 := fun y hy ↦ hD.norm_chordCoeff_le (hrange y hy) hm
  have hGε : ∀ y ∈ B, ‖G y - -c‖ ≤ ε * |g₀| := fun y hy ↦ by
    have e : G y - -c = -(g₀ • ((1 - a y) ν)) := by
      change (-c - g₀ • ((1 - a y) ν)) - -c = _
      abel
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    refine ((1 - a y).le_opNorm ν).trans ?_
    rw [hν, mul_one, norm_sub_rev]
    exact ha1 y hy
  have hGB : ∀ y ∈ B, ‖G y‖ ≤ ‖c‖ + ε * |g₀| := fun y hy ↦ by
    have := norm_le_norm_add_norm_sub' (G y) (-c)
    rw [norm_neg] at this
    linarith [hGε y hy]
  -- even reflection
  have href := Div.IsConormalSolOn.evenReflect E ν x r 2 (‖c‖ + ε * |g₀|) 0 a G 0 w' hν hr hx
    (hac.aestronglyMeasurable hBm) haB (hGc.aestronglyMeasurable hBm) hGB
    aestronglyMeasurable_const (fun _ _ ↦ by simp) hlin
  set F := reflectField ν (gradientWithin w' B) with hF
  have hgw'c : ContinuousOn (gradientWithin w' B) B :=
    continuousOn_gradientWithin_halfBall hν hr hxr hlin.1
  have hFm : AEStronglyMeasurable F (volume.restrict (ball x r)) :=
    aestronglyMeasurable_reflectField hν hx (hgw'c.aestronglyMeasurable hBm)
  have hFM := norm_reflectField_le hν hx hgw'M
  have hS' := hstep x r ρ (2 * η + |g₀|) ε (ε * |g₀|) F (reflectField ν G) (-c)
    (reflectCoeff ν a) hρ hρr hFm hFM (isWeakCurlFree_reflectField hν hx hlin.1)
    (aestronglyMeasurable_reflectCoeff hν hx (hac.aestronglyMeasurable hBm))
    (fun y hy ↦ by
      simpa using norm_reflectCoeff_sub_one_le (K := ε) (α := 0) hν hx
        (fun y hy ↦ by simpa using ha1 y hy) y hy)
    (aestronglyMeasurable_reflectField hν hx (hGc.aestronglyMeasurable hBm))
    (fun y hy ↦ by
      have h0 := norm_reflectField_sub_le (K := ε * |g₀|) (α := 0) hν hx
        (by rw [inner_neg_left, hcν, neg_zero]) (fun y hy ↦ by simpa using hGε y hy) y hy
      rwa [Real.rpow_zero, mul_one] at h0)
    href.2
  -- lower bound: `ψ(ρ) ≤ ∫_{B_ρ} ‖F - F_ρ‖²`
  set Sρ := ball x ρ ∩ halfSpace ν with hSρ
  have hSρm : MeasurableSet Sρ := measurableSet_ball.inter (measurableSet_halfSpace ν)
  have hSρB : Sρ ⊆ B := hSB hρr
  obtain ⟨hgiρ, hgi2ρ⟩ := integrableOn_of_continuousOn_compact hgc hBc subset_rfl hSρB
  have hSρfin : volume Sρ ≠ ⊤ :=
    (measure_mono inter_subset_left).trans_lt measure_ball_lt_top |>.ne
  set mF := ⨍ y' in ball x ρ, F y' with hmF
  have hFeqH : ∀ y ∈ B, F y = gW y - p := fun y hy ↦ by
    have hy' : 0 ≤ ⟪y, ν⟫ := hy.2
    simp only [hF, reflectField, hy', ite_true]
    exact hgw' y hy
  have hFρint : IntegrableOn (fun y ↦ ‖F y - mF‖ ^ 2) (ball x ρ) := by
    have : IsFiniteMeasure (volume.restrict (ball x ρ)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    refine Integrable.of_bound (((hFm.mono_measure (Measure.restrict_mono
      (ball_subset_ball hρr) le_rfl)).sub aestronglyMeasurable_const).norm.pow 2)
      ((2 * η + |g₀| + ‖mF‖) ^ 2) ((ae_restrict_iff' measurableSet_ball).2
        (Eventually.of_forall fun y hy ↦ ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
      (add_le_add (hFM y (ball_subset_ball hρr hy)) le_rfl)) 2
  have hlow : ∫ y in Sρ, ‖gW y - ⨍ y' in Sρ, gW y'‖ ^ 2 ≤ ∫ y in ball x ρ, ‖F y - mF‖ ^ 2 := by
    have h1 := setIntegral_norm_sub_setAverage_sq_le hSρfin hgiρ hgi2ρ (p + mF)
    have h2 : ∫ y in Sρ, ‖gW y - (p + mF)‖ ^ 2 = ∫ y in Sρ, ‖F y - mF‖ ^ 2 :=
      setIntegral_congr_fun hSρm fun y hy ↦ by
        simp only [hFeqH y (hSρB hy)]
        congr 2
        abel
    have h3 : ∫ y in Sρ, ‖F y - mF‖ ^ 2 ≤ ∫ y in ball x ρ, ‖F y - mF‖ ^ 2 :=
      setIntegral_mono_set hFρint (Eventually.of_forall fun _ ↦ sq_nonneg _)
        inter_subset_left.eventuallyLE
    linarith
  -- upper bound for `∫_{B_r} ‖F‖²`
  have hcont_p : ContinuousOn (fun y ↦ ‖gW y - p‖ ^ 2) B := (hgc.sub continuousOn_const).norm.pow 2
  have hint_p : IntegrableOn (fun y ↦ ‖gW y - p‖ ^ 2) B := hcont_p.integrableOn_compact hBc
  have hint_m : IntegrableOn (fun y ↦ ‖gW y - m‖ ^ 2) B :=
    ((hgc.sub continuousOn_const).norm.pow 2).integrableOn_compact hBc
  have hsubO : ball x r ∩ openHalfSpace ν ⊆ B := fun y hy ↦
    ⟨ball_subset_closedBall hy.1, openHalfSpace_subset_halfSpace ν hy.2⟩
  have hOm : MeasurableSet (ball x r ∩ openHalfSpace ν) :=
    measurableSet_ball.inter (measurableSet_openHalfSpace ν)
  have hup1 : ∫ y in ball x r, ‖F y‖ ^ 2 ≤ 2 * ∫ y in B, ‖gW y - p‖ ^ 2 := by
    have hR : ∀ y ∈ ball x r ∩ openHalfSpace ν,
        ‖F (reflect ν y)‖ ^ 2 = ‖gW y - p‖ ^ 2 := fun y hy ↦ by
      have hneg : ¬ 0 ≤ ⟪reflect ν y, ν⟫ := by
        rw [inner_reflect hν]; linarith [mem_openHalfSpace.1 hy.2]
      simp only [hF, reflectField, hneg, ite_false, reflect_reflect, LinearIsometryEquiv.norm_map]
      rw [hgw' y (hsubO hy)]
    have hBH : ∀ y ∈ B, ‖F y‖ ^ 2 = ‖gW y - p‖ ^ 2 := fun y hy ↦ by rw [hFeqH y hy]
    have i1 : IntegrableOn (fun y ↦ ‖F y‖ ^ 2) (ball x r ∩ halfSpace ν) :=
      (hint_p.mono_set (hSB le_rfl)).congr_fun (fun y hy ↦ (hBH y (hSB le_rfl hy)).symm) hSm
    have i2 : IntegrableOn (fun y ↦ ‖F (reflect ν y)‖ ^ 2) (ball x r ∩ openHalfSpace ν) :=
      (hint_p.mono_set hsubO).congr_fun (fun y hy ↦ (hR y hy).symm) hOm
    rw [(setIntegral_ball_eq_halfBall_add_reflect hν hx i1 i2).2, setIntegral_congr_fun hBm hBH,
      setIntegral_congr_fun hOm hR]
    have : ∫ y in ball x r ∩ openHalfSpace ν, ‖gW y - p‖ ^ 2 ≤ ∫ y in B, ‖gW y - p‖ ^ 2 :=
      setIntegral_mono_set hint_p (Eventually.of_forall fun _ ↦ sq_nonneg _) hsubO.eventuallyLE
    linarith
  set ψr := ∫ y in S, ‖gW y - m‖ ^ 2 with hψr
  have hψr0 : 0 ≤ ψr := setIntegral_nonneg hSm fun _ _ ↦ sq_nonneg _
  have hBS : ∀ f : E → ℝ, ∫ y in B, f y = ∫ y in S, f y := fun f ↦
    (setIntegral_congr_set (ball_inter_halfSpace_ae_eq hν0 x r)).symm
  have hvolS : volume.real S ≤ r ^ finrank ℝ E * vB := by
    rw [← measureReal_ball_eq hr]
    exact measureReal_mono inter_subset_left measure_ball_lt_top.ne
  have hup2 : ∫ y in B, ‖gW y - p‖ ^ 2 ≤ 2 * ψr + 2 * g₀ ^ 2 * (r ^ finrank ℝ E * vB) := by
    rw [hBS]
    have hpt : ∀ y ∈ S, ‖gW y - p‖ ^ 2 ≤ 2 * ‖gW y - m‖ ^ 2 + 2 * g₀ ^ 2 := fun y _ ↦ by
      rw [show gW y - p = (gW y - m) + g₀ • ν by rw [hp]; abel]
      have := norm_add_le (gW y - m) (g₀ • ν)
      rw [norm_smul, hν, mul_one, Real.norm_eq_abs] at this
      nlinarith [norm_nonneg (gW y - m + g₀ • ν), sq_abs g₀, sq_nonneg (‖gW y - m‖ - |g₀|),
        norm_nonneg (gW y - m), abs_nonneg g₀]
    have i3 : IntegrableOn (fun y ↦ 2 * ‖gW y - m‖ ^ 2 + 2 * g₀ ^ 2) S :=
      ((hint_m.mono_set (hSB le_rfl)).const_mul 2).add
        ((continuousOn_const.integrableOn_compact hBc).mono_set (hSB le_rfl))
    calc ∫ y in S, ‖gW y - p‖ ^ 2 ≤ ∫ y in S, (2 * ‖gW y - m‖ ^ 2 + 2 * g₀ ^ 2) :=
          setIntegral_mono_on (hint_p.mono_set (hSB le_rfl)) i3 hSm hpt
      _ = 2 * ψr + 2 * g₀ ^ 2 * volume.real S := by
          rw [integral_add ((hint_m.mono_set (hSB le_rfl)).const_mul 2)
            ((continuousOn_const.integrableOn_compact hBc).mono_set (hSB le_rfl)),
            integral_const_mul, setIntegral_const, smul_eq_mul]
          ring
      _ ≤ 2 * ψr + 2 * g₀ ^ 2 * (r ^ finrank ℝ E * vB) := by gcongr
  -- the flux bound
  have hfl := hflux x r (fun y ↦ Φ (gW y)) (Φ m) hx hr hΦc (fun φ hφ ↦ h.2 φ hφ)
  have hΦm : ∫ y in B, ‖Φ (gW y) - Φ m‖ ^ 2 ≤ 4 * ψr := by
    rw [hBS, hψr, ← integral_const_mul]
    refine setIntegral_mono_on ((((hΦc.sub continuousOn_const).norm.pow 2).integrableOn_compact
      hBc).mono_set (hSB le_rfl)) ((hint_m.mono_set (hSB le_rfl)).const_mul 4) hSm
      fun y hy ↦ ?_
    have hyB := hSB le_rfl hy
    rw [hD.sub_eq_chordCoeff_apply' (hrange y hyB) hm]
    have h1 : ‖chordCoeff Φ (gW y) m (gW y - m)‖ ≤ 2 * ‖gW y - m‖ :=
      ((chordCoeff Φ (gW y) m).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (haB y hyB) (norm_nonneg _))
    nlinarith [norm_nonneg (chordCoeff Φ (gW y) m (gW y - m)), norm_nonneg (gW y - m)]
  have hX : g₀ ^ 2 * r ^ finrank ℝ E ≤ 4 * Cf * ψr := by
    refine hfl.trans ?_
    have := mul_le_mul_of_nonneg_left hΦm hCf
    linarith
  -- the algebra
  set Q := (ρ / r) ^ (finrank ℝ E + 2) + ε ^ 2 with hQ
  have hQε : ε ^ 2 ≤ Q := le_add_of_nonneg_left (by positivity)
  have hQ0 : 0 ≤ Q := (sq_nonneg ε).trans hQε
  set rd := r ^ finrank ℝ E
  have hX0 : 0 ≤ g₀ ^ 2 * rd := by positivity
  have hI : ∫ y in ball x r, ‖F y‖ ^ 2 ≤ 4 * ψr + 4 * vB * (4 * Cf * ψr) := by
    have : 4 * vB * (g₀ ^ 2 * rd) ≤ 4 * vB * (4 * Cf * ψr) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    nlinarith [hup1, hup2]
  have e1 : (ε * |g₀|) ^ 2 * rd = ε ^ 2 * (g₀ ^ 2 * rd) := by rw [mul_pow, sq_abs]; ring
  rw [e1] at hS'
  have k1 : Q * ∫ y in ball x r, ‖F y‖ ^ 2 ≤ Q * (4 * ψr + 4 * vB * (4 * Cf * ψr)) :=
    mul_le_mul_of_nonneg_left hI hQ0
  have k2 : ε ^ 2 * (g₀ ^ 2 * rd) ≤ Q * (4 * Cf * ψr) :=
    mul_le_mul hQε hX hX0 hQ0
  calc ∫ y in Sρ, ‖gW y - ⨍ y' in Sρ, gW y'‖ ^ 2 ≤ ∫ y in ball x ρ, ‖F y - mF‖ ^ 2 := hlow
    _ ≤ CA * (Q * (∫ y in ball x r, ‖F y‖ ^ 2) + ε ^ 2 * (g₀ ^ 2 * rd)) := hS'
    _ ≤ CA * (Q * (4 * ψr + 4 * vB * (4 * Cf * ψr)) + Q * (4 * Cf * ψr)) := by gcongr
    _ = CA * (4 + 16 * vB * Cf + 4 * Cf) * (Q * ψr) := by ring

end BasicElliptic.Div
