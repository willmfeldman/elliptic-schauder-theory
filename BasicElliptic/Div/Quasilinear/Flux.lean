/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Projection.GradientField
public import BasicElliptic.Div.Boundary.HalfBall
public import BasicElliptic.Normalize.ChangeOfVariables
public import BasicElliptic.Campanato.Density
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The flux bound at a flat point

`BasicElliptic.Div.sq_inner_mul_pow_le_of_flux`: fix a unit vector `ν`. There is `C = C(E, ν)` such
that, for `x` on the flat part, `r > 0`, a field `Q` continuous on `B_r⁺ = halfBall ν x r` with
**zero weak flux** (`∫_{B_r⁺} ⟪Q, ∇φ⟫ = 0` for every `φ ∈ C¹_c(B_r(x))`; the tests need not vanish
on the flat part) and any constant `v`,

`⟪v, ν⟫² r^d ≤ C ∫_{B_r⁺} ‖Q - v‖²`.

For `Q = Φ(∇w)` and `v = Φ((∇w)_r)` this bounds the normal flux of the frozen field by the
Campanato quantity of `∇w`: it is the quantitative form of the conormal condition
`⟪Φ(∇w), ν⟫ = 0` used in the small-oscillation Campanato argument at flat points.

## Proof

Let `φ₁(z) = S(1 - 4 ‖z‖²)` (`S` the smooth transition), a radial `C^∞` bump supported in
`B_{1/2}(0)`, so `Dφ₁(z) v = -8 S'(1 - 4‖z‖²) ⟪z, v⟫`, and `K(v) = ∫_{⟪z, ν⟫ ≥ 0} Dφ₁(z) v`.

* `K(u) = 0` for `u ⊥ ν`: the reflection `R` in `u^⊥` preserves the half space and the measure,
  and `Dφ₁(R z) u = -Dφ₁(z) u`.
* `K(ν) < 0`: the integrand is `≤ 0` on the half space and `< 0` near `s ν`, where
  `S'(1 - 4 s²) > 0` (mean value theorem for `S` on `[0, 1]`).
* Hence `K(v) = ⟪v, ν⟫ K(ν)`, and by scaling, with `φ_r(y) = φ₁((y - x)/r)`,
  `∫_{B_r⁺} ⟪v, ∇φ_r⟫ = r^{d-1} ⟪v, ν⟫ K(ν)`.
* Testing the zero-flux identity with `φ_r`:
  `r^{d-1} |⟪v, ν⟫| |K(ν)| = |∫_{B_r⁺} ⟪Q - v, ∇φ_r⟫| ≤ (K₁/r) ∫_{B_r⁺} ‖Q - v‖`, with
  `K₁ = sup ‖Dφ₁‖`; the arithmetic–geometric mean inequality with a parameter proportional to
  `|⟪v, ν⟫|` turns this into the claim with `C = K₁² |B_1| / K(ν)²`.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient ContDiff Topology

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The radial bump -/

/-- The radial bump `φ₁(z) = S(1 - 4 ‖z‖²)`. -/
private noncomputable def bump (z : E) : ℝ := Real.smoothTransition (1 - 4 * ‖z‖ ^ 2)

private theorem contDiff_bump : ContDiff ℝ ∞ (bump (E := E)) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

omit [InnerProductSpace ℝ E] in
private theorem bump_eq_zero {z : E} (hz : 1 / 2 ≤ ‖z‖) : bump z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith [norm_nonneg z])

private theorem fderiv_bump_apply (z v : E) :
    fderiv ℝ bump z v = -(8 * deriv Real.smoothTransition (1 - 4 * ‖z‖ ^ 2) * ⟪z, v⟫) := by
  have h1 : HasFDerivAt (fun z : E ↦ 1 - 4 * ‖z‖ ^ 2) (-(4 : ℝ) • (2 • innerSL ℝ z)) z := by
    have := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul 4).const_sub 1
    simpa [neg_smul] using this
  have h2 : HasFDerivAt (bump (E := E))
      (deriv Real.smoothTransition (1 - 4 * ‖z‖ ^ 2) • (-(4 : ℝ) • (2 • innerSL ℝ z))) z :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _
      |>.hasDerivAt.comp_hasFDerivAt z h1
  rw [h2.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

variable [FiniteDimensional ℝ E]

private theorem hasCompactSupport_bump : HasCompactSupport (bump (E := E)) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (1 / 2)) fun z hz ↦ bump_eq_zero (by
    rw [mem_closedBall, dist_zero_right, not_le] at hz; exact hz.le)

omit [FiniteDimensional ℝ E] in
private theorem continuous_fderiv_bump : Continuous (fderiv ℝ (bump (E := E))) :=
  contDiff_bump.continuous_fderiv (by simp)

variable [MeasurableSpace E] [BorelSpace E] in
private theorem integrable_fderiv_bump_apply (v : E) :
    Integrable (fun z ↦ fderiv ℝ (bump (E := E)) z v) :=
  (continuous_fderiv_bump.clm_apply continuous_const).integrable_of_hasCompactSupport
    (hasCompactSupport_bump.fderiv_apply (𝕜 := ℝ) v)

variable [MeasurableSpace E] [BorelSpace E]

/-- `K(v) = ∫_{⟪z, ν⟫ ≥ 0} Dφ₁(z) v`. -/
private noncomputable def fluxK (ν v : E) : ℝ := ∫ z in halfSpace ν, fderiv ℝ bump z v

private theorem fluxK_tangential {ν u : E} (hu : ⟪u, ν⟫ = 0) : fluxK ν u = 0 := by
  set R := reflect u
  have hRu : R u = -u := Submodule.reflection_orthogonalComplement_singleton_eq_neg u
  have hRν : R ν = ν := by
    refine Submodule.reflection_mem_subspace_eq_self ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; exact hu
  have hpre : R ⁻¹' halfSpace ν = halfSpace ν := by
    ext z
    simp only [mem_preimage, mem_halfSpace]
    rw [show ⟪R z, ν⟫ = ⟪z, ν⟫ by rw [inner_reflect_left, hRν]]
  have hodd : ∀ z, fderiv ℝ bump (R z) u = -fderiv ℝ bump z u := fun z ↦ by
    rw [fderiv_bump_apply, fderiv_bump_apply, LinearIsometryEquiv.norm_map,
      show ⟪R z, u⟫ = -⟪z, u⟫ by rw [inner_reflect_left, hRu, inner_neg_right]]
    ring
  have hmp : MeasurePreserving R volume volume := R.measurePreserving
  have hme : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hme (fun z ↦ fderiv ℝ bump z u) (halfSpace ν)
  rw [hpre] at h
  simp only [hodd, integral_neg] at h
  unfold fluxK
  linarith

private theorem deriv_smoothTransition_nonneg (t : ℝ) : 0 ≤ deriv Real.smoothTransition t :=
  Real.smoothTransition.monotone.deriv_nonneg

private theorem fluxK_normal_neg {ν : E} (hν : ‖ν‖ = 1) : fluxK ν ν < 0 := by
  -- a point where `S' > 0`
  obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope Real.smoothTransition zero_lt_one
    Real.smoothTransition.continuous.continuousOn
    fun t _ ↦ (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t
      |>.differentiableWithinAt
  rw [Real.smoothTransition.one, Real.smoothTransition.zero] at hξd
  norm_num at hξd
  set s := √((1 - ξ) / 4) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith [hξ.2])
  have hs2 : s ^ 2 = (1 - ξ) / 4 := Real.sq_sqrt (by linarith [hξ.2])
  set z₀ : E := s • ν with hz₀
  have hz₀n : ‖z₀‖ ^ 2 = s ^ 2 := by rw [hz₀, norm_smul, hν, mul_one, Real.norm_of_nonneg hs0.le]
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  set f : E → ℝ := fun z ↦ fderiv ℝ bump z ν with hf
  have hfc : Continuous f := continuous_fderiv_bump.clm_apply continuous_const
  have hfz₀ : f z₀ = -(8 * s) := by
    change fderiv ℝ bump z₀ ν = _
    rw [fderiv_bump_apply, hz₀n, hs2, show 1 - 4 * ((1 - ξ) / 4) = ξ by ring, hξd, hz₀,
      real_inner_smul_left, hν1]
    ring
  have hf0 : f z₀ < 0 := by rw [hfz₀]; linarith
  -- a ball around `z₀` inside the open half space where `f < f z₀ / 2`
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1
    ((isOpen_lt hfc continuous_const).inter (isOpen_openHalfSpace ν)) z₀
    ⟨by change f z₀ < f z₀ / 2; linarith, by
      change 0 < ⟪z₀, ν⟫; rw [hz₀, real_inner_smul_left, hν1]; linarith⟩
  -- `-f ≥ 0` on the half space
  have hfneg : ∀ z ∈ halfSpace ν, 0 ≤ -f z := fun z hz ↦ by
    change 0 ≤ -fderiv ℝ bump z ν
    rw [fderiv_bump_apply, neg_neg]
    exact mul_nonneg (mul_nonneg (by norm_num) (deriv_smoothTransition_nonneg _))
      (mem_halfSpace.1 hz)
  have hint : Integrable (fun z ↦ -f z) := (integrable_fderiv_bump_apply ν).neg
  have hsub : ball z₀ δ ⊆ halfSpace ν := fun z hz ↦
    openHalfSpace_subset_halfSpace ν (hball hz).2
  have h1 : ∫ z in ball z₀ δ, -f z ≤ ∫ z in halfSpace ν, -f z :=
    setIntegral_mono_set hint.integrableOn
      ((ae_restrict_iff' (measurableSet_halfSpace ν)).2 (Eventually.of_forall hfneg))
      hsub.eventuallyLE
  have h2 : (-(f z₀) / 2) * volume.real (ball z₀ δ) ≤ ∫ z in ball z₀ δ, -f z :=
    setIntegral_ge_of_const_le_real measurableSet_ball measure_ball_lt_top.ne
      (fun z hz ↦ by have := (hball hz).1; simp only [mem_ofPred_eq] at this; linarith)
      hint.integrableOn
  have hvol : 0 < volume.real (ball z₀ δ) := by
    have : Nontrivial E := ⟨⟨ν, 0, by rintro rfl; simp at hν⟩⟩
    rw [measureReal_ball_eq hδ]; exact mul_pos (pow_pos hδ _) unitBallVolume_pos
  have h3 : 0 < (-(f z₀) / 2) * volume.real (ball z₀ δ) := mul_pos (by linarith) hvol
  have : fluxK ν ν = -∫ z in halfSpace ν, -f z := by
    rw [integral_neg, neg_neg]; rfl
  linarith

private theorem fluxK_eq {ν : E} (hν : ‖ν‖ = 1) (v : E) : fluxK ν v = ⟪v, ν⟫ * fluxK ν ν := by
  have hν1 : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  set u := v - ⟪v, ν⟫ • ν
  have hu : ⟪u, ν⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, hν1, mul_one, sub_self]
  have hv : v = u + ⟪v, ν⟫ • ν := (sub_add_cancel _ _).symm
  have e : fluxK ν v = fluxK ν u + ⟪v, ν⟫ * fluxK ν ν := by
    unfold fluxK
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, smul_eq_mul]
    rw [integral_add (integrable_fderiv_bump_apply u).integrableOn
      ((integrable_fderiv_bump_apply ν).integrableOn.const_mul _), integral_const_mul]
  rw [e, fluxK_tangential hu, zero_add]

/-! ### The scaled bump -/

/-- The scaled bump `φ_r(y) = φ₁((y - x)/r)`. -/
private noncomputable def bumpAt (x : E) (r : ℝ) (y : E) : ℝ := bump (r⁻¹ • (y - x))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem hasFDerivAt_bumpAt (x : E) (r : ℝ) (y : E) :
    HasFDerivAt (bumpAt x r) ((fderiv ℝ bump (r⁻¹ • (y - x))).comp (r⁻¹ • (1 : E →L[ℝ] E))) y := by
  have hg : HasFDerivAt (fun y : E ↦ r⁻¹ • (y - x)) (r⁻¹ • (1 : E →L[ℝ] E)) y := by
    have := (r⁻¹ • (1 : E →L[ℝ] E)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
    convert this using 1
    · ext v; simp
    · ext v; simp
  exact ((contDiff_bump.differentiable (by simp)) _).hasFDerivAt.comp y hg

omit [MeasurableSpace E] [BorelSpace E] in
private theorem inner_gradient_bumpAt (x : E) (r : ℝ) (y v : E) :
    ⟪v, ∇ (bumpAt x r) y⟫ = r⁻¹ * fderiv ℝ bump (r⁻¹ • (y - x)) v := by
  rw [inner_gradient_right, (hasFDerivAt_bumpAt x r y).fderiv]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
private theorem isTestFn_bumpAt (x : E) {r : ℝ} (hr : 0 < r) :
    IsTestFn (ball x r) (bumpAt x r) := by
  have hzero : ∀ y, r / 2 ≤ dist y x → bumpAt x r y = 0 := fun y hy ↦ bump_eq_zero (by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← dist_eq_norm]
    calc (1 : ℝ) / 2 = r⁻¹ * (r / 2) := by field_simp
      _ ≤ r⁻¹ * dist y x := by gcongr)
  refine ⟨(contDiff_bump.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)).of_le
    (by simp), HasCompactSupport.intro (isCompact_closedBall x (r / 2)) fun y hy ↦ hzero y
    (by rw [mem_closedBall, not_le] at hy; exact hy.le), ?_⟩
  refine (closure_minimal (fun y hy ↦ ?_) isClosed_closedBall).trans
    (closedBall_subset_ball (half_lt_self hr))
  by_contra h
  rw [mem_closedBall, not_le] at h
  exact hy (hzero y h.le)

/-- `∫_{B_r⁺} ⟪v, ∇φ_r⟫ = r^d r⁻¹ ⟪v, ν⟫ K(ν)` at a centre on the flat part. -/
private theorem setIntegral_inner_gradient_bumpAt {ν x : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    {r : ℝ} (hr : 0 < r) (v : E) :
    ∫ y in halfBall ν x r, ⟪v, ∇ (bumpAt x r) y⟫ =
      r ^ finrank ℝ E * r⁻¹ * (⟪v, ν⟫ * fluxK ν ν) := by
  rw [← fluxK_eq hν v]
  -- pass to the half space
  have h0 : ∀ y ∉ ball x r, ⟪v, ∇ (bumpAt x r) y⟫ = 0 := fun y hy ↦ by
    rw [((isTestFn_bumpAt x hr).eq_zero_and_gradient_eq_zero hy).2, inner_zero_right]
  rw [← setIntegral_eq_of_inter_subset (measurableSet_halfSpace ν) (halfBall_subset_halfSpace ν x r)
    (fun y hy ↦ ⟨ball_subset_closedBall hy.2, hy.1⟩) h0]
  -- change variables `y = x + r z`
  let M : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E r hr.ne').toContinuousLinearEquiv
  have hM : ∀ z, M z = r • z := fun z ↦ rfl
  have hMν : ∀ z, ⟪M z, ν⟫ = r * ⟪z, ν⟫ := fun z ↦ by rw [hM, real_inner_smul_left]
  have hdet : LinearMap.det (M : E →ₗ[ℝ] E) = r ^ finrank ℝ E := by
    have : (M : E →ₗ[ℝ] E) = r • LinearMap.id := by ext z; rfl
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hcv := setIntegral_comp_affine M x (fun y ↦ ⟪v, ∇ (bumpAt x r) y⟫) (halfSpace ν)
  rw [preimage_affine_halfSpace hr hx hMν, hdet] at hcv
  have hpt : ∀ z, ⟪v, ∇ (bumpAt x r) (x + M z)⟫ = r⁻¹ * fderiv ℝ bump z v := fun z ↦ by
    rw [inner_gradient_bumpAt, hM, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne',
      one_smul]
  simp only [hpt] at hcv
  rw [integral_const_mul, smul_eq_mul, abs_of_pos (pow_pos hr _)] at hcv
  have hrd : (0 : ℝ) < r ^ finrank ℝ E := pow_pos hr _
  unfold fluxK
  field_simp at hcv ⊢
  linarith

/-! ### The flux bound -/

variable (E) in
/-- **The flux bound at a flat point** (see the module docstring). -/
theorem sq_inner_mul_pow_le_of_flux {ν : E} (hν : ‖ν‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : E) (r : ℝ) (Q : E → E) (v : E), ⟪x, ν⟫ = 0 → 0 < r →
      ContinuousOn Q (halfBall ν x r) →
      (∀ φ : E → ℝ, IsTestFn (ball x r) φ → ∫ y in halfBall ν x r, ⟪Q y, ∇ φ y⟫ = 0) →
      ⟪v, ν⟫ ^ 2 * r ^ finrank ℝ E ≤ C * ∫ y in halfBall ν x r, ‖Q y - v‖ ^ 2 := by
  have : Nontrivial E := ⟨⟨ν, 0, by rintro rfl; simp at hν⟩⟩
  set K₀ := fluxK ν ν with hK₀
  have hK₀ : K₀ < 0 := fluxK_normal_neg hν
  obtain ⟨K₁', hK₁'⟩ := (hasCompactSupport_bump (E := E)).fderiv (𝕜 := ℝ)
    |>.exists_bound_of_continuous continuous_fderiv_bump
  set K₁ := max K₁' 1
  have hK₁ : 0 < K₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set vB := unitBallVolume E
  have hvB : 0 < vB := unitBallVolume_pos
  refine ⟨K₁ ^ 2 * vB / K₀ ^ 2, by positivity, ?_⟩
  intro x r Q v hx hr hQ hflux
  set B := halfBall ν x r with hB
  set g := ⟪v, ν⟫ with hg
  set P := ∫ y in B, ‖Q y - v‖ ^ 2 with hP
  have hBc : IsCompact B := isCompact_halfBall ν x r
  have hBm : MeasurableSet B := measurableSet_halfBall ν x r
  have hP0 : 0 ≤ P := setIntegral_nonneg hBm fun _ _ ↦ sq_nonneg _
  rcases eq_or_ne g 0 with hg0 | hg0
  · rw [hg0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  set φ := bumpAt x r
  have hφ := isTestFn_bumpAt x hr
  have hφc : Continuous (∇ φ) :=
    (toDual ℝ E).symm.continuous.comp (hφ.1.continuous_fderiv one_ne_zero)
  have hQv : ContinuousOn (fun y ↦ Q y - v) B := hQ.sub continuousOn_const
  -- the identity `r^d r⁻¹ g K₀ = -∫ ⟪Q - v, ∇φ⟫`
  have hid : r ^ finrank ℝ E * r⁻¹ * (g * K₀) = -∫ y in B, ⟪Q y - v, ∇ φ y⟫ := by
    have i1 : IntegrableOn (fun y ↦ ⟪Q y, ∇ φ y⟫) B :=
      (hQ.inner hφc.continuousOn).integrableOn_compact hBc
    have i2 : IntegrableOn (fun y ↦ ⟪v, ∇ φ y⟫) B :=
      (continuousOn_const.inner hφc.continuousOn).integrableOn_compact hBc
    simp_rw [inner_sub_left]
    rw [integral_sub i1 i2, hflux φ hφ, setIntegral_inner_gradient_bumpAt hν hx hr v]
    ring
  -- the gradient bound `‖∇φ‖ ≤ K₁ / r`
  have hgrad : ∀ y, ‖∇ φ y‖ ≤ r⁻¹ * K₁ := fun y ↦ by
    rw [gradient, LinearIsometryEquiv.norm_map, (hasFDerivAt_bumpAt x r y).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖fderiv ℝ bump (r⁻¹ • (y - x))‖ ≤ K₁ := (hK₁' _).trans (le_max_left _ _)
    have h2 : ‖r⁻¹ • (1 : E →L[ℝ] E)‖ ≤ r⁻¹ := by
      refine (norm_smul_le _ _).trans ?_
      rw [Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
      exact mul_le_of_le_one_right (inv_nonneg.2 hr.le) ContinuousLinearMap.norm_id_le
    calc _ ≤ K₁ * r⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) hK₁.le
      _ = r⁻¹ * K₁ := mul_comm _ _
  -- the volume of the half ball
  have hvolB : volume.real B ≤ r ^ finrank ℝ E * vB := by
    rw [← measureReal_ball_eq hr, measureReal_def, measureReal_def,
      measure_congr (halfBall_ae_eq (by rintro rfl; simp at hν) x r)]
    exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono inter_subset_left)
  -- `∫ ‖Q - v‖ ≤ (P / s + s |B|) / 2`
  have hi1 : IntegrableOn (fun y ↦ ‖Q y - v‖) B := hQv.norm.integrableOn_compact hBc
  have hi2 : IntegrableOn (fun y ↦ ‖Q y - v‖ ^ 2) B :=
    (hQv.norm.pow 2).integrableOn_compact hBc
  have hA : ∀ s > 0, ∫ y in B, ‖Q y - v‖ ≤ (P / s + s * volume.real B) / 2 := by
    intro s hs
    have hi3 : IntegrableOn (fun y ↦ (‖Q y - v‖ ^ 2 / s + s) / 2) B :=
      ((hi2.div_const s).add (continuousOn_const.integrableOn_compact hBc)).div_const 2
    refine (setIntegral_mono_on hi1 hi3 hBm fun y _ ↦ ?_).trans_eq ?_
    · have := sq_nonneg (‖Q y - v‖ - s)
      rw [le_div_iff₀ two_pos, div_add' _ _ _ hs.ne', le_div_iff₀ hs]
      nlinarith
    · rw [integral_div,
        integral_add (hi2.div_const s) (continuousOn_const.integrableOn_compact hBc),
        integral_div, setIntegral_const, smul_eq_mul, mul_comm]
  -- `|∫ ⟪Q - v, ∇φ⟫| ≤ (K₁ / r) ∫ ‖Q - v‖`
  have hI : |∫ y in B, ⟪Q y - v, ∇ φ y⟫| ≤ r⁻¹ * K₁ * ∫ y in B, ‖Q y - v‖ := by
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((hQv.inner hφc.continuousOn).abs.integrableOn_compact hBc)
      (hi1.const_mul _) hBm fun y _ ↦ ?_
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hgrad y) (norm_nonneg _)
  -- the algebra
  set a := |g|
  set k := |K₀|
  have ha : 0 < a := abs_pos.2 hg0
  have hk : 0 < k := abs_pos.2 hK₀.ne
  set rd := r ^ finrank ℝ E
  have hrd : 0 < rd := pow_pos hr _
  have hkey : rd * a * k ≤ K₁ * (P / (a * k / (K₁ * vB)) + a * k / (K₁ * vB) * (rd * vB)) / 2 := by
    have hs : 0 < a * k / (K₁ * vB) := by positivity
    have h1 := hA _ hs
    have h2 : |rd * r⁻¹ * (g * K₀)| = rd * r⁻¹ * (a * k) := by
      rw [abs_mul (rd * r⁻¹), abs_of_pos (by positivity : 0 < rd * r⁻¹), abs_mul]
    have h3 : rd * r⁻¹ * (a * k) ≤ r⁻¹ * K₁ * ((P / (a * k / (K₁ * vB)) +
        a * k / (K₁ * vB) * volume.real B) / 2) := by
      rw [← h2, hid, abs_neg]
      exact hI.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    have h4 : a * k / (K₁ * vB) * volume.real B ≤ a * k / (K₁ * vB) * (rd * vB) :=
      mul_le_mul_of_nonneg_left hvolB hs.le
    have h5 : rd * r⁻¹ * (a * k) ≤ r⁻¹ * (K₁ * (P / (a * k / (K₁ * vB)) +
        a * k / (K₁ * vB) * (rd * vB)) / 2) := by
      refine h3.trans ?_
      have : r⁻¹ * K₁ * ((P / (a * k / (K₁ * vB)) + a * k / (K₁ * vB) * volume.real B) / 2) =
          r⁻¹ * (K₁ * (P / (a * k / (K₁ * vB)) + a * k / (K₁ * vB) * volume.real B) / 2) := by
        ring
      rw [this]
      gcongr
    have h6 := mul_le_mul_of_nonneg_left h5 hr.le
    rw [show r * (rd * r⁻¹ * (a * k)) = rd * a * k by field_simp,
      show r * (r⁻¹ * (K₁ * (P / (a * k / (K₁ * vB)) + a * k / (K₁ * vB) * (rd * vB)) / 2)) =
        K₁ * (P / (a * k / (K₁ * vB)) + a * k / (K₁ * vB) * (rd * vB)) / 2 by field_simp] at h6
    exact h6
  have hsimp : K₁ * (P / (a * k / (K₁ * vB)) + a * k / (K₁ * vB) * (rd * vB)) / 2 =
      K₁ ^ 2 * vB * P / (2 * a * k) + rd * a * k / 2 := by
    field_simp
  rw [hsimp] at hkey
  have hg2 : g ^ 2 = a ^ 2 := (sq_abs g).symm
  have hK2 : K₀ ^ 2 = k ^ 2 := (sq_abs K₀).symm
  rw [hg2, hK2, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h7 : rd * a * k ≤ K₁ ^ 2 * vB * P / (a * k) := by
    have : K₁ ^ 2 * vB * P / (2 * a * k) = (K₁ ^ 2 * vB * P / (a * k)) / 2 := by
      field_simp
    linarith
  rw [le_div_iff₀ (by positivity)] at h7
  nlinarith

end BasicElliptic.Div
