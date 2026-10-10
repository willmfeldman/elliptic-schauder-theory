/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Projection.HarmonicReplacement
public import BasicElliptic.Harmonic.Decay
public import BasicElliptic.Campanato.Iteration
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import BasicElliptic.Div.Projection.TestPoincare
import BasicElliptic.Campanato.Density
import BasicElliptic.Normalize.ChangeOfVariables

/-!
# One-point Campanato decay for weak solutions

`BasicElliptic.Div.campanato_decay_at_point`: let `F` be a bounded, measurable, weakly curl-free
field on `B_R(x₀)` satisfying the weak identity
`∫ ⟪ã F, ∇φ⟫ = (∫ ⟪G, ∇φ⟫) + ∫ f φ` (`Div.IsWeakEqOn ã G f F (B_R) (B_R)`), with coefficients
and data that are Hölder **at the single point `x₀`**:
`‖ã(y) - 1‖ ≤ K |y - x₀|^α`, `‖G(y) - G(x₀)‖ ≤ K_G |y - x₀|^α`, `|f| ≤ K_f`, `‖F‖ ≤ M`.
Then with `ψ(ρ) = ∫_{B_ρ(x₀)} ‖F - F_{x₀,ρ}‖²` and `d = dim E`, for `0 < ρ ≤ R`,

`ψ(ρ) ≤ C ((ρ/R)^{d+2α} ψ(R) + ρ^{d+2α} (K² M² + K_G² + K_f² R^{2-2α}))`,   `C = C(E, α)`.

Nothing is assumed of `ã`, `G`, `f`, `F` away from `x₀` beyond measurability and the displayed
bounds; no ellipticity or symmetry of `ã` is used. This is the form used by the boundary theory
(`Div/Boundary/Decay.lean`) at a flat boundary point after even reflection, where `ã`, `G` are
Hölder only at `x₀`.

## Proof

Fix `0 < ρ ≤ r ≤ R`. Let `V` be the harmonic replacement of `F` on `B_r`
(`Div/Projection/HarmonicReplacement.lean`, `exists_harmonic_replacement`,
with the constant `c = G(x₀)`), so that
`D := ∫_{B_r} ‖F - V‖² ≤ (‖(1 - ã)F‖ + ‖G - G(x₀)‖ + 2r |B_r|^{1/2} K_f)²`
`≤ 12 |B_1| r^{d+2α} (K² M² + K_G² + K_f² R^{2-2α})`
(norms in `L²(B_r)`; we use `r² ≤ r^{2α} R^{2-2α}`). The mean minimizes `c ↦ ∫ ‖F - c‖²`
(`setIntegral_norm_sub_setAverage_sq_le`), so with the harmonic decay (`Harmonic/`,
`harmonic_campanato_decay`, constant `C_h`)
`ψ(ρ) ≤ 2 ∫_{B_ρ} ‖V - V_ρ‖² + 2 D ≤ 2 C_h (ρ/r)^{d+2} ∫_{B_r} ‖V - V_r‖² + 2 D`
and `∫_{B_r} ‖V - V_r‖² ≤ ∫_{B_r} ‖V - F_r‖² ≤ 2 ψ(r) + 2 D`. Hence
`ψ(ρ) ≤ 4 C_h (ρ/r)^{d+2} ψ(r) + (4 C_h + 2) D`.
`ψ` is nondecreasing (again because the mean minimizes), so the iteration lemma (`Campanato/`,
`campanato_iteration`, with exponents `a = d + 2 > b = d + 2α`) concludes.

The replacement field must be square integrable on `B_r` (to compare integrals over `B_ρ ⊆ B_r`);
`exists_harmonic_replacement` exports this.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.

## Provenance

New (W. M. Feldman).
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient ContDiff Topology

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Integrals over `B_R(x₀)` of a function vanishing off `B_r(x₀)`, `r ≤ R`, are integrals over
`B_r(x₀)`. -/
private theorem setIntegral_ball_eq_of_le {x₀ : E} {r R : ℝ} (hrR : r ≤ R) {g : E → ℝ}
    (hg : ∀ y ∉ ball x₀ r, g y = 0) : ∫ y in ball x₀ R, g y = ∫ y in ball x₀ r, g y :=
  setIntegral_eq_of_inter_subset measurableSet_ball (ball_subset_ball hrR) inter_subset_right hg

/-- Weak curl-freeness passes to smaller concentric balls. -/
private theorem isWeakCurlFree_ball_of_le {F : E → E} {x₀ : E} {r R : ℝ} (hrR : r ≤ R)
    (h : IsWeakCurlFree F (ball x₀ R)) : IsWeakCurlFree F (ball x₀ r) := by
  intro ψ hψ u w
  have hψ' : IsSmoothTestFn (ball x₀ R) ψ :=
    ⟨hψ.1, hψ.2.1, hψ.2.2.trans (ball_subset_ball hrR)⟩
  have hz : ∀ v, ∀ y ∉ ball x₀ r, fderiv ℝ ψ y v = 0 := fun v y hy ↦ by
    rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψ.2.2 h)), zero_apply]
  rw [← setIntegral_ball_eq_of_le hrR (fun y hy ↦ by rw [hz w y hy, mul_zero]),
    ← setIntegral_ball_eq_of_le hrR (fun y hy ↦ by rw [hz u y hy, mul_zero])]
  exact h ψ hψ' u w

/-- The weak identity on `B` against smooth tests (the form used by
`exists_harmonic_replacement`). -/
private def IsSmoothWeakEq (ã : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (F : E → E)
    (B : Set E) : Prop :=
  ∀ φ : E → ℝ, IsSmoothTestFn B φ →
    ∫ y in B, ⟪ã y (F y), ∇ φ y⟫ = (∫ y in B, ⟪G y, ∇ φ y⟫) + ∫ y in B, f y * φ y

/-- The weak identity on `B_R(x₀)` against smooth tests gives the weak identity on `B_r(x₀)`,
`r ≤ R`, in the form taken by `exists_harmonic_replacement`. -/
private theorem weak_ball_of_le {ã : E → E →L[ℝ] E} {G F : E → E} {f : E → ℝ} {x₀ : E}
    {r R : ℝ} (hrR : r ≤ R) (hweak : IsSmoothWeakEq ã G f F (ball x₀ R)) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x₀ r →
      ∫ y in ball x₀ r, ⟪ã y (F y), ∇ φ y⟫ =
        (∫ y in ball x₀ r, ⟪G y, ∇ φ y⟫) + ∫ y in ball x₀ r, f y * φ y := by
  intro φ h1 h2 h3
  have hφr : IsTestFn (ball x₀ r) φ := ⟨h1.of_le (by simp), h2, h3⟩
  have e1 : ∫ y in ball x₀ R, ⟪ã y (F y), ∇ φ y⟫ = ∫ y in ball x₀ r, ⟪ã y (F y), ∇ φ y⟫ :=
    setIntegral_ball_eq_of_le hrR fun y hy ↦ by
      simp [(hφr.eq_zero_and_gradient_eq_zero hy).2]
  have e2 : ∫ y in ball x₀ R, ⟪G y, ∇ φ y⟫ = ∫ y in ball x₀ r, ⟪G y, ∇ φ y⟫ :=
    setIntegral_ball_eq_of_le hrR fun y hy ↦ by
      simp [(hφr.eq_zero_and_gradient_eq_zero hy).2]
  have e3 : ∫ y in ball x₀ R, f y * φ y = ∫ y in ball x₀ r, f y * φ y :=
    setIntegral_ball_eq_of_le hrR fun y hy ↦ by
      simp [(hφr.eq_zero_and_gradient_eq_zero hy).1]
  have := hweak φ ⟨h1, h2, h3.trans (ball_subset_ball hrR)⟩
  rwa [e1, e2, e3] at this

/-- **The constant skew part drops out**. If `F ∈ L²(U; E)` is weakly curl-free and
`K† = -K`, then `∫_U ⟪K F, ∇φ⟫ = 0` for every `φ ∈ C_c^∞(U)`.

With an orthonormal basis `(b_j)` and `B(u, v) = ∫_U ⟪F, u⟫ ∂_v φ` (symmetric by
curl-freeness): `∫ ⟪K F, ∇φ⟫ = Σ_j B(b_j, K b_j) = Σ_j B(K b_j, b_j)`, and
`Σ_j ⟪F, K b_j⟫ ∂_{b_j} φ = -Σ_j ⟪K F, b_j⟫ ∂_{b_j} φ = -⟪K F, ∇φ⟫` by skewness; so the integral
equals its negative. -/
theorem setIntegral_inner_skew_eq_zero {U : Set E} {F : E → E}
    (hF : MemLp F 2 (volume.restrict U)) (hcurl : IsWeakCurlFree F U) {K : E →L[ℝ] E}
    (hK : ContinuousLinearMap.adjoint K = -K) {φ : E → ℝ} (hφ : IsSmoothTestFn U φ) :
    ∫ y in U, ⟪K (F y), ∇ φ y⟫ = 0 := by
  set b := stdOrthonormalBasis ℝ E
  have hint : ∀ u v : E, Integrable (fun y ↦ ⟪F y, u⟫ * fderiv ℝ φ y v) (volume.restrict U) :=
    fun u v ↦ (integrable_inner_mul (hF.toLp F) u (hφ.fderiv_apply v)).congr
      (by filter_upwards [hF.coeFn_toLp] with y h; rw [h])
  have e1 : ∀ y, ⟪K (F y), ∇ φ y⟫ = ∑ j, ⟪F y, b j⟫ * fderiv ℝ φ y (K (b j)) := by
    intro y
    rw [inner_gradient_right]
    conv_lhs => rw [← b.sum_repr' (F y)]
    simp [map_sum, map_smul, real_inner_comm]
  have e2 : ∀ y, ⟪K (F y), ∇ φ y⟫ = -∑ j, ⟪F y, K (b j)⟫ * fderiv ℝ φ y (b j) := by
    intro y
    have hadj : ∀ j, ⟪F y, K (b j)⟫ = -⟪b j, K (F y)⟫ := fun j ↦ by
      rw [← ContinuousLinearMap.adjoint_inner_left, hK, neg_apply, inner_neg_left,
        real_inner_comm]
    simp_rw [hadj, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rw [inner_gradient_right]
    conv_lhs => rw [← b.sum_repr' (K (F y))]
    simp [map_sum, map_smul, mul_comm]
  have h1 : ∫ y in U, ⟪K (F y), ∇ φ y⟫ =
      ∑ j, ∫ y in U, ⟪F y, b j⟫ * fderiv ℝ φ y (K (b j)) := by
    simp_rw [e1]
    exact integral_finsetSum _ fun j _ ↦ hint _ _
  have h2 : ∫ y in U, ⟪K (F y), ∇ φ y⟫ =
      -∑ j, ∫ y in U, ⟪F y, K (b j)⟫ * fderiv ℝ φ y (b j) := by
    simp_rw [e2]
    rw [integral_neg, integral_finsetSum _ fun j _ ↦ hint _ _]
  have h3 : ∀ j, ∫ y in U, ⟪F y, b j⟫ * fderiv ℝ φ y (K (b j)) =
      ∫ y in U, ⟪F y, K (b j)⟫ * fderiv ℝ φ y (b j) := fun j ↦ hcurl φ hφ (b j) (K (b j))
  simp_rw [h3] at h1
  linarith

private instance isFiniteMeasure_restrict_ball (x : E) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (ball x r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

/-- `(x + y + z)² ≤ 3 (x² + y² + z²)`. -/
private theorem sq_add_add_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖u - w‖² ≤ 2 ‖v - w‖² + 2 ‖u - v‖²`. -/
private theorem norm_sub_sq_le (u v w : E) : ‖u - w‖ ^ 2 ≤ 2 * ‖v - w‖ ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub u v w
  have h0 := norm_nonneg (u - w)
  nlinarith [sq_nonneg (‖v - w‖ - ‖u - v‖), norm_nonneg (v - w), norm_nonneg (u - v)]

/-- A measurable field bounded on `B_R(x₀)` is in `L²(B_r(x₀))` for `r ≤ R`. -/
private theorem memLp_ball_of_bound {F : E → E} {x₀ : E} {r R M : ℝ} (hrR : r ≤ R)
    (hFm : AEStronglyMeasurable F (volume.restrict (ball x₀ R)))
    (hFM : ∀ y ∈ ball x₀ R, ‖F y‖ ≤ M) : MemLp F 2 (volume.restrict (ball x₀ r)) :=
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  MemLp.of_bound (hFm.mono_measure (Measure.restrict_mono (ball_subset_ball hrR) le_rfl)) M
    ((ae_restrict_iff' measurableSet_ball).2
      (Eventually.of_forall fun y hy ↦ hFM y (ball_subset_ball hrR hy)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem integrable_norm_sq {μ : Measure E} {g : E → E} (hg : MemLp g 2 μ) :
    Integrable (fun y ↦ ‖g y‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg

/-- **The comparison chain.** If `F, V ∈ L²(B_r)` and `V` has harmonic components on `B_r`, then
for `0 < ρ ≤ r`, with `D = ∫_{B_r} ‖F - V‖²` and `C_h` the harmonic decay constant,
`ψ(ρ) ≤ 4 C_h (ρ/r)^{d+2} ψ(r) + (4 C_h + 2) D`. -/
private theorem comparison {Ch : ℝ} (hCh : 0 ≤ Ch)
    (hdecay : ∀ (V : E → E) (x : E) (r ρ : ℝ), 0 < ρ → ρ ≤ r →
      (∀ e : E, HarmonicOnNhd (fun y ↦ ⟪V y, e⟫) (ball x r)) →
      IntegrableOn (fun y ↦ ‖V y‖ ^ 2) (ball x r) →
      ∫ y in ball x ρ, ‖V y - ⨍ z in ball x ρ, V z‖ ^ 2 ≤
        Ch * (ρ / r) ^ (finrank ℝ E + 2) * ∫ y in ball x r, ‖V y - ⨍ z in ball x r, V z‖ ^ 2)
    {x₀ : E} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) {F V : E → E}
    (hFL : MemLp F 2 (volume.restrict (ball x₀ r))) (hVL : MemLp V 2 (volume.restrict (ball x₀ r)))
    (hVh : ∀ e : E, HarmonicOnNhd (fun y ↦ ⟪V y, e⟫) (ball x₀ r)) :
    ∫ y in ball x₀ ρ, ‖F y - ⨍ z in ball x₀ ρ, F z‖ ^ 2 ≤
      4 * Ch * (ρ / r) ^ (finrank ℝ E + 2) * (∫ y in ball x₀ r, ‖F y - ⨍ z in ball x₀ r, F z‖ ^ 2)
        + (4 * Ch + 2) * ∫ y in ball x₀ r, ‖F y - V y‖ ^ 2 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hρsub : ball x₀ ρ ⊆ ball x₀ r := ball_subset_ball hρr
  have hFLρ : MemLp F 2 (volume.restrict (ball x₀ ρ)) :=
    hFL.mono_measure (Measure.restrict_mono hρsub le_rfl)
  have hVLρ : MemLp V 2 (volume.restrict (ball x₀ ρ)) :=
    hVL.mono_measure (Measure.restrict_mono hρsub le_rfl)
  have hFVL : MemLp (fun y ↦ F y - V y) 2 (volume.restrict (ball x₀ r)) := hFL.sub hVL
  set mV := ⨍ z in ball x₀ ρ, V z
  set mF := ⨍ z in ball x₀ r, F z
  set D := ∫ y in ball x₀ r, ‖F y - V y‖ ^ 2 with hDdef
  set ψr := ∫ y in ball x₀ r, ‖F y - mF‖ ^ 2 with hψr
  have hψr0 : 0 ≤ ψr := setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hD0 : 0 ≤ D := setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have sa : ∫ y in ball x₀ ρ, ‖F y - ⨍ z in ball x₀ ρ, F z‖ ^ 2 ≤
      2 * (∫ y in ball x₀ ρ, ‖V y - mV‖ ^ 2) + 2 * ∫ y in ball x₀ ρ, ‖F y - V y‖ ^ 2 := by
    have hi1 : IntegrableOn (fun y ↦ ‖V y - mV‖ ^ 2) (ball x₀ ρ) :=
      integrable_norm_sq (hVLρ.sub (memLp_const mV))
    have hi2 : IntegrableOn (fun y ↦ ‖F y - V y‖ ^ 2) (ball x₀ ρ) :=
      integrable_norm_sq (hFLρ.sub hVLρ)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi1.const_mul 2)
      (hi2.const_mul 2)]
    exact (setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hFLρ.integrable one_le_two) (integrable_norm_sq hFLρ) mV).trans
      (integral_mono (integrable_norm_sq (hFLρ.sub (memLp_const mV)))
        ((hi1.const_mul 2).add (hi2.const_mul 2)) fun y ↦ norm_sub_sq_le (F y) (V y) mV)
  have sc : ∫ y in ball x₀ ρ, ‖V y - mV‖ ^ 2 ≤
      Ch * (ρ / r) ^ (finrank ℝ E + 2) * ∫ y in ball x₀ r, ‖V y - ⨍ z in ball x₀ r, V z‖ ^ 2 :=
    hdecay V x₀ r ρ hρ hρr hVh (integrable_norm_sq hVL)
  have sd : ∫ y in ball x₀ r, ‖V y - ⨍ z in ball x₀ r, V z‖ ^ 2 ≤ 2 * D + 2 * ψr := by
    have hi1 : IntegrableOn (fun y ↦ ‖F y - V y‖ ^ 2) (ball x₀ r) := integrable_norm_sq hFVL
    have hi2 : IntegrableOn (fun y ↦ ‖F y - mF‖ ^ 2) (ball x₀ r) :=
      integrable_norm_sq (hFL.sub (memLp_const mF))
    refine (setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hVL.integrable one_le_two) (integrable_norm_sq hVL) mF).trans ?_
    rw [hDdef, hψr, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi1.const_mul 2) (hi2.const_mul 2)]
    refine integral_mono (integrable_norm_sq (hVL.sub (memLp_const mF)))
      ((hi1.const_mul 2).add (hi2.const_mul 2)) fun y ↦ ?_
    have := norm_sub_sq_le (V y) (F y) mF
    rw [norm_sub_rev (V y) (F y)] at this
    simpa only [add_comm] using this
  have sf : ∫ y in ball x₀ ρ, ‖F y - V y‖ ^ 2 ≤ D :=
    setIntegral_mono_set (integrable_norm_sq hFVL) (Eventually.of_forall fun _ ↦ sq_nonneg _)
      hρsub.eventuallyLE
  set q := (ρ / r) ^ (finrank ℝ E + 2)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr)
  have hsd := mul_le_mul_of_nonneg_left sd (mul_nonneg hCh hq0)
  have hqD : Ch * q * D ≤ Ch * 1 * D :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq1 hCh) hD0
  linarith

/-- **The energy bound.** Under the hypotheses of `campanato_decay_at_point`, for `0 < r ≤ R`
there is a field `V ∈ L²(B_r)` with harmonic components on `B_r` and
`∫_{B_r} ‖F - V‖² ≤ 12 |B_1| (K² M² + K_G² + K_f² R^{2-2α}) r^{d+2α}`. -/
private theorem exists_replacement_energy_le {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {x₀ : E}
    {R M K KG Kf : ℝ} {F G : E → E} {f : E → ℝ} {ã : E → E →L[ℝ] E}
    (hFm : AEStronglyMeasurable F (volume.restrict (ball x₀ R)))
    (hFM : ∀ y ∈ ball x₀ R, ‖F y‖ ≤ M) (hcurl : IsWeakCurlFree F (ball x₀ R))
    (hãm : AEStronglyMeasurable ã (volume.restrict (ball x₀ R)))
    (hã : ∀ y ∈ ball x₀ R, ‖ã y - 1‖ ≤ K * dist y x₀ ^ α)
    (hGm : AEStronglyMeasurable G (volume.restrict (ball x₀ R)))
    (hG : ∀ y ∈ ball x₀ R, ‖G y - G x₀‖ ≤ KG * dist y x₀ ^ α)
    (hf : ∀ y ∈ ball x₀ R, |f y| ≤ Kf) (hweak : IsSmoothWeakEq ã G f F (ball x₀ R))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ V : E → E, (∀ e, HarmonicOnNhd (fun y ↦ ⟪V y, e⟫) (ball x₀ r)) ∧
      MemLp V 2 (volume.restrict (ball x₀ r)) ∧
      ∫ y in ball x₀ r, ‖F y - V y‖ ^ 2 ≤
        12 * unitBallVolume E * (K ^ 2 * M ^ 2 + KG ^ 2 + Kf ^ 2 * R ^ (2 - 2 * α)) *
          r ^ ((finrank ℝ E : ℝ) + 2 * α) := by
  have hR : 0 < R := hr.trans_le hrR
  have hM : 0 ≤ M := (norm_nonneg _).trans (hFM x₀ (mem_ball_self hR))
  have hKf : 0 ≤ Kf := (abs_nonneg _).trans (hf x₀ (mem_ball_self hR))
  have hsubR : ball x₀ r ⊆ ball x₀ R := ball_subset_ball hrR
  have hdist : ∀ y ∈ ball x₀ r, dist y x₀ ^ α ≤ r ^ α := fun y hy ↦
    Real.rpow_le_rpow dist_nonneg (mem_ball.1 hy).le hα.le
  have habs : ∀ {k : ℝ} {y : E}, y ∈ ball x₀ r → k * dist y x₀ ^ α ≤ |k| * r ^ α :=
    fun {k} {y} hy ↦ (mul_le_mul_of_nonneg_right (le_abs_self k)
      (Real.rpow_nonneg dist_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hdist y hy) (abs_nonneg k))
  have hãr : ∀ y ∈ ball x₀ r, ‖ã y - 1‖ ≤ |K| * r ^ α := fun y hy ↦
    (hã y (hsubR hy)).trans (habs hy)
  have hGr : ∀ y ∈ ball x₀ r, ‖G y - G x₀‖ ≤ |KG| * r ^ α := fun y hy ↦
    (hG y (hsubR hy)).trans (habs hy)
  have hãb : ∀ y ∈ ball x₀ r, ‖ã y‖ ≤ 1 + |K| * r ^ α := fun y hy ↦ by
    have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖ã y‖ ≤ ‖(1 : E →L[ℝ] E)‖ + ‖ã y - 1‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ _ := add_le_add h1 (hãr y hy)
  have hGL : MemLp G 2 (volume.restrict (ball x₀ r)) :=
    have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    MemLp.of_bound (hGm.mono_measure (Measure.restrict_mono hsubR le_rfl))
      (‖G x₀‖ + |KG| * r ^ α)
      ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy ↦
        (norm_le_norm_add_norm_sub' (G y) (G x₀)).trans (add_le_add le_rfl (hGr y hy))))
  obtain ⟨V, hVh, hVL, hFV, -⟩ := exists_harmonic_replacement hr (G x₀)
    (memLp_ball_of_bound hrR hFm hFM) (isWeakCurlFree_ball_of_le hrR hcurl)
    (hãm.mono_measure (Measure.restrict_mono hsubR le_rfl)) hãb hGL
    (fun y hy ↦ hf y (hsubR hy)) (weak_ball_of_le hrR hweak)
  refine ⟨V, hVh, hVL, ?_⟩
  set vol := volume.real (ball x₀ r) with hvoldef
  have hvol : vol = r ^ finrank ℝ E * unitBallVolume E := measureReal_ball_eq hr
  have hvol0 : 0 ≤ vol := measureReal_nonneg
  have hsqrt : ∀ {g : E → ℝ} {c : ℝ}, 0 ≤ c → (∀ y ∈ ball x₀ r, |g y| ≤ c ^ 2) →
      √(∫ y in ball x₀ r, g y) ≤ c * √vol := fun {g c} hc h ↦ by
    have h1 : ∫ y in ball x₀ r, g y ≤ c ^ 2 * vol :=
      (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const measure_ball_lt_top
        fun y hy ↦ by rw [Real.norm_eq_abs]; exact h y hy)
    calc √(∫ y in ball x₀ r, g y) ≤ √(c ^ 2 * vol) := Real.sqrt_le_sqrt h1
      _ = c * √vol := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  set t := r ^ α with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hr.le _
  have h1 : √(∫ y in ball x₀ r, ‖F y - ã y (F y)‖ ^ 2) ≤ |K| * t * M * √vol := by
    refine hsqrt (by positivity) fun y hy ↦ ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have he : F y - ã y (F y) = -((ã y - 1) (F y)) := by simp
    rw [he, norm_neg]
    exact ((ã y - 1).le_opNorm _).trans (mul_le_mul (hãr y hy) (hFM y (hsubR hy))
      (norm_nonneg _) (by positivity))
  have h2 : √(∫ y in ball x₀ r, ‖G y - G x₀‖ ^ 2) ≤ |KG| * t * √vol := by
    refine hsqrt (by positivity) fun y hy ↦ ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGr y hy) 2
  set D := ∫ y in ball x₀ r, ‖F y - V y‖ ^ 2 with hDdef
  have hD0 : 0 ≤ D := setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  set X := |K| * t * M + |KG| * t + 2 * r * Kf with hX
  have hsqrtD : √D ≤ √vol * X := by
    have := hFV.trans (add_le_add (add_le_add h1 h2) le_rfl)
    rw [hX]
    linarith
  have hD2 : D ≤ vol * X ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrtD 2
    rwa [Real.sq_sqrt hD0, mul_pow, Real.sq_sqrt hvol0] at this
  have e1 : t ^ 2 = r ^ (2 * α) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  have hr2 : r ^ 2 ≤ t ^ 2 * R ^ (2 - 2 * α) := by
    have e2 : r ^ 2 = r ^ (2 * α) * r ^ (2 - 2 * α) := by
      rw [← Real.rpow_add hr, ← Real.rpow_natCast]; congr 1; push_cast; ring
    rw [e2, e1]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrR (by linarith))
      (Real.rpow_nonneg hr.le _)
  have hrb : r ^ ((finrank ℝ E : ℝ) + 2 * α) = r ^ finrank ℝ E * t ^ 2 := by
    rw [Real.rpow_add hr, Real.rpow_natCast, e1]
  set S := K ^ 2 * M ^ 2 + KG ^ 2 + Kf ^ 2 * R ^ (2 - 2 * α) with hS
  have hX2 : X ^ 2 ≤ 12 * t ^ 2 * S := by
    have e : X ^ 2 ≤ 3 * ((|K| * t * M) ^ 2 + (|KG| * t) ^ 2 + (2 * r * Kf) ^ 2) :=
      sq_add_add_le _ _ _
    have e3 : (|K| * t * M) ^ 2 = t ^ 2 * (K ^ 2 * M ^ 2) := by rw [mul_pow, mul_pow, sq_abs]; ring
    have e4 : (|KG| * t) ^ 2 = t ^ 2 * KG ^ 2 := by rw [mul_pow, sq_abs]; ring
    have e5 : (2 * r * Kf) ^ 2 ≤ 4 * (t ^ 2 * (Kf ^ 2 * R ^ (2 - 2 * α))) := by
      have := mul_le_mul_of_nonneg_left hr2 (by positivity : (0 : ℝ) ≤ 4 * Kf ^ 2)
      calc (2 * r * Kf) ^ 2 = 4 * Kf ^ 2 * r ^ 2 := by ring
        _ ≤ 4 * Kf ^ 2 * (t ^ 2 * R ^ (2 - 2 * α)) := this
        _ = _ := by ring
    have p1 : 0 ≤ t ^ 2 * (K ^ 2 * M ^ 2) := by positivity
    have p2 : 0 ≤ t ^ 2 * KG ^ 2 := by positivity
    rw [e3, e4] at e
    have : 12 * t ^ 2 * S = 12 * (t ^ 2 * (K ^ 2 * M ^ 2)) + 12 * (t ^ 2 * KG ^ 2) +
        12 * (t ^ 2 * (Kf ^ 2 * R ^ (2 - 2 * α))) := by rw [hS]; ring
    rw [this]
    linarith
  calc D ≤ vol * X ^ 2 := hD2
    _ ≤ vol * (12 * t ^ 2 * S) := mul_le_mul_of_nonneg_left hX2 hvol0
    _ = _ := by rw [hvol, hrb]; ring

variable (E) in
/-- **One-point Campanato decay with a constant skew part**. As
`campanato_decay_at_point`, but with `‖ã(y) - (1 + K_s)‖ ≤ K |y - x₀|^α` for a constant skew
`K_s` (`K_s† = -K_s`), which drops out of the weak identity because `F` is curl-free
(`setIntegral_inner_skew_eq_zero`). There is `C = C(E, α) ≥ 0`
such that: if `F` is measurable, bounded by `M` and weakly curl-free on `B_R(x₀)` and satisfies
`Div.IsWeakEqOn ã G f F (B_R(x₀)) (B_R(x₀))`, with `ã`, `G` measurable,
`‖ã(y) - 1‖ ≤ K |y - x₀|^α`, `‖G(y) - G(x₀)‖ ≤ K_G |y - x₀|^α` and `|f| ≤ K_f` on `B_R(x₀)`, then
for `0 < ρ ≤ R`
`∫_{B_ρ} ‖F - F_ρ‖² ≤ C ((ρ/R)^{d+2α} ∫_{B_R} ‖F - F_R‖² + ρ^{d+2α} (K² M² + K_G² + K_f² R^{2-2α}))`
(`F_s` the mean over `B_s(x₀)`, `d = dim E`). Only the Hölder bounds **at `x₀`** enter. See the
module docstring for the proof. -/
theorem campanato_decay_at_point_skew {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : E) (R M K KG Kf : ℝ) (F G : E → E) (f : E → ℝ)
      (ã : E → E →L[ℝ] E) (Ks : E →L[ℝ] E), ContinuousLinearMap.adjoint Ks = -Ks → 0 < R →
      AEStronglyMeasurable F (volume.restrict (ball x₀ R)) → (∀ y ∈ ball x₀ R, ‖F y‖ ≤ M) →
      IsWeakCurlFree F (ball x₀ R) →
      AEStronglyMeasurable ã (volume.restrict (ball x₀ R)) →
      (∀ y ∈ ball x₀ R, ‖ã y - (1 + Ks)‖ ≤ K * dist y x₀ ^ α) →
      AEStronglyMeasurable G (volume.restrict (ball x₀ R)) →
      (∀ y ∈ ball x₀ R, ‖G y - G x₀‖ ≤ KG * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R, |f y| ≤ Kf) →
      IsWeakEqOn ã G f F (ball x₀ R) (ball x₀ R) →
      ∀ ρ ∈ Ioc 0 R, ∫ y in ball x₀ ρ, ‖F y - ⨍ z in ball x₀ ρ, F z‖ ^ 2 ≤
        C * ((ρ / R) ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (∫ y in ball x₀ R, ‖F y - ⨍ z in ball x₀ R, F z‖ ^ 2) +
          ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (K ^ 2 * M ^ 2 + KG ^ 2 + Kf ^ 2 * R ^ (2 - 2 * α))) := by
  obtain ⟨Ch, hCh, hdecay⟩ := harmonic_campanato_decay E (volume : Measure E) E
  set d := finrank ℝ E
  set ωB := unitBallVolume E
  have hω : 0 < ωB := unitBallVolume_pos
  set A := 4 * Ch with hAdef
  set a : ℝ := (d : ℝ) + 2 with ha
  set b : ℝ := (d : ℝ) + 2 * α with hb
  set Bf := (4 * Ch + 2) * (12 * ωB) with hBf
  have hA : 0 ≤ A := by positivity
  have hb0 : 0 < b := by positivity
  have hab : b < a := by rw [ha, hb]; linarith
  have hBf0 : 0 ≤ Bf := by positivity
  have hIC := iterConst_nonneg hA hab
  refine ⟨iterConst A a b * max 1 Bf, by positivity, ?_⟩
  intro x₀ R M K KG Kf F G f ã Ks hKs hR hFm hFM hcurl hãm hã hGm hG hf hweak ρ hρ
  -- remove the constant skew part: `ã' = ã - Ks`
  have hFLR : MemLp F 2 (volume.restrict (ball x₀ R)) := memLp_ball_of_bound le_rfl hFm hFM
  have hã' : ∀ y ∈ ball x₀ R, ‖(ã y - Ks) - 1‖ ≤ K * dist y x₀ ^ α := fun y hy ↦ by
    rw [sub_sub, add_comm Ks 1]; exact hã y hy
  have hãm' : AEStronglyMeasurable (fun y ↦ ã y - Ks) (volume.restrict (ball x₀ R)) :=
    hãm.sub aestronglyMeasurable_const
  have hweak' : IsSmoothWeakEq (fun y ↦ ã y - Ks) G f F (ball x₀ R) := by
    intro φ hφ
    have hbd : ∀ y ∈ ball x₀ R, ‖ã y‖ ≤ ‖1 + Ks‖ + |K| * R ^ α := fun y hy ↦ by
      refine (norm_le_norm_add_norm_sub' (ã y) (1 + Ks)).trans (add_le_add le_rfl ?_)
      refine (hã y hy).trans ((mul_le_mul_of_nonneg_right (le_abs_self K)
        (Real.rpow_nonneg dist_nonneg _)).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg K)))
      exact Real.rpow_le_rpow dist_nonneg (mem_ball.1 hy).le hα.le
    have hint : ∀ {H : E → E}, MemLp H 2 (volume.restrict (ball x₀ R)) →
        Integrable (fun y ↦ ⟪H y, ∇ φ y⟫) (volume.restrict (ball x₀ R)) :=
      fun {H} hH ↦ (L2.integrable_inner (hH.toLp H) (hφ.memLp_gradient.toLp _)).congr
        (by filter_upwards [hH.coeFn_toLp, hφ.memLp_gradient.coeFn_toLp] with y h1 h2
            rw [h1, h2])
    have haF : MemLp (fun y ↦ ã y (F y)) 2 (volume.restrict (ball x₀ R)) := by
      refine hFLR.of_le_mul (c := ‖1 + Ks‖ + |K| * R ^ α)
        (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hãm.prodMk hFm)) ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact (ã y).le_opNorm (F y) |>.trans
        (mul_le_mul_of_nonneg_right (hbd y hy) (norm_nonneg _))
    have hKF : MemLp (fun y ↦ Ks (F y)) 2 (volume.restrict (ball x₀ R)) :=
      Ks.lipschitzWith.comp_memLp (by simp) hFLR
    simp only [sub_apply, inner_sub_left]
    rw [integral_sub (hint haF) (hint hKF),
      setIntegral_inner_skew_eq_zero hFLR hcurl hKs hφ, sub_zero]
    exact hweak φ hφ.isTestFn
  set ψ : ℝ → ℝ := fun r ↦ ∫ y in ball x₀ r, ‖F y - ⨍ z in ball x₀ r, F z‖ ^ 2 with hψdef
  set S := K ^ 2 * M ^ 2 + KG ^ 2 + Kf ^ 2 * R ^ (2 - 2 * α) with hSdef
  have hKf : 0 ≤ Kf := (abs_nonneg _).trans (hf x₀ (mem_ball_self hR))
  have hS : 0 ≤ S := by positivity
  have hψ0 : ∀ r ∈ Ioc 0 R, 0 ≤ ψ r := fun r _ ↦
    setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  -- `ψ` is nondecreasing: the mean minimizes
  have hmono : MonotoneOn ψ (Ioc 0 R) := by
    intro r₁ h₁ r₂ h₂ h12
    have hL := memLp_ball_of_bound h₂.2 hFm hFM
    have hL1 := memLp_ball_of_bound (h12.trans h₂.2) hFm hFM
    exact (setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hL1.integrable one_le_two) (integrable_norm_sq hL1) _).trans
      (setIntegral_mono_set (integrable_norm_sq (hL.sub (memLp_const _)))
        (Eventually.of_forall fun _ ↦ sq_nonneg _) (ball_subset_ball h12).eventuallyLE)
  -- the one-step inequality
  have hstep : ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R →
      ψ ρ ≤ A * (ρ / r) ^ a * ψ r + (Bf * S) * r ^ b := by
    intro ρ r hρ hρr hrR
    have hr : 0 < r := hρ.trans_le hρr
    obtain ⟨V, hVh, hVL, hD⟩ := exists_replacement_energy_le hα hα1 hFm hFM hcurl hãm' hã' hGm hG
      hf hweak' hr hrR
    have h := comparison hCh hdecay hρ hρr (memLp_ball_of_bound hrR hFm hFM) hVL hVh
    have hqa : (ρ / r) ^ a = (ρ / r) ^ (d + 2) := by
      rw [ha, ← Real.rpow_natCast]; push_cast; ring_nf
    rw [hqa]
    calc ψ ρ ≤ _ := h
      _ ≤ A * (ρ / r) ^ (d + 2) * ψ r + (4 * Ch + 2) * (12 * ωB * S * r ^ b) := by
          rw [hAdef]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hD (by positivity))
      _ = A * (ρ / r) ^ (d + 2) * ψ r + Bf * S * r ^ b := by rw [hBf]; ring
  have hit := campanato_iteration hb0 hab hA (mul_nonneg hBf0 hS) hmono hψ0 hstep ρ R hρ.1 hρ.2
    le_rfl
  have hX : 0 ≤ (ρ / R) ^ b * ψ R := mul_nonneg (Real.rpow_nonneg (by have := hρ.1; positivity) _)
    (hψ0 R ⟨hR, le_rfl⟩)
  have hρb : 0 ≤ ρ ^ b * S := mul_nonneg (Real.rpow_nonneg hρ.1.le _) hS
  calc ψ ρ ≤ iterConst A a b * ((ρ / R) ^ b * ψ R + Bf * S * ρ ^ b) := hit
    _ ≤ iterConst A a b * (max 1 Bf * ((ρ / R) ^ b * ψ R + ρ ^ b * S)) := by
        gcongr
        have h1 : (ρ / R) ^ b * ψ R ≤ max 1 Bf * ((ρ / R) ^ b * ψ R) :=
          le_mul_of_one_le_left hX (le_max_left _ _)
        have h2 : Bf * S * ρ ^ b ≤ max 1 Bf * (ρ ^ b * S) := by
          rw [mul_assoc, mul_comm S]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hρb
        linarith
    _ = _ := by ring

variable (E) in
/-- **One-point Campanato decay** (GM, proof). There is `C = C(E, α) ≥ 0`
such that: if `F` is measurable, bounded by `M` and weakly curl-free on `B_R(x₀)` and satisfies
`Div.IsWeakEqOn ã G f F (B_R(x₀)) (B_R(x₀))`, with `ã`, `G` measurable,
`‖ã(y) - 1‖ ≤ K |y - x₀|^α`, `‖G(y) - G(x₀)‖ ≤ K_G |y - x₀|^α` and `|f| ≤ K_f` on `B_R(x₀)`, then
for `0 < ρ ≤ R`
`∫_{B_ρ} ‖F - F_ρ‖² ≤ C ((ρ/R)^{d+2α} ∫_{B_R} ‖F - F_R‖² + ρ^{d+2α} (K² M² + K_G² + K_f² R^{2-2α}))`
(`F_s` the mean over `B_s(x₀)`, `d = dim E`). Only the Hölder bounds **at `x₀`** enter; no
ellipticity, symmetry or continuity of `ã` is used. This is the case `K_s = 0` of
`campanato_decay_at_point_skew`; see the module docstring for the proof. -/
theorem campanato_decay_at_point {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : E) (R M K KG Kf : ℝ) (F G : E → E) (f : E → ℝ)
      (ã : E → E →L[ℝ] E), 0 < R →
      AEStronglyMeasurable F (volume.restrict (ball x₀ R)) → (∀ y ∈ ball x₀ R, ‖F y‖ ≤ M) →
      IsWeakCurlFree F (ball x₀ R) →
      AEStronglyMeasurable ã (volume.restrict (ball x₀ R)) →
      (∀ y ∈ ball x₀ R, ‖ã y - 1‖ ≤ K * dist y x₀ ^ α) →
      AEStronglyMeasurable G (volume.restrict (ball x₀ R)) →
      (∀ y ∈ ball x₀ R, ‖G y - G x₀‖ ≤ KG * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R, |f y| ≤ Kf) →
      IsWeakEqOn ã G f F (ball x₀ R) (ball x₀ R) →
      ∀ ρ ∈ Ioc 0 R, ∫ y in ball x₀ ρ, ‖F y - ⨍ z in ball x₀ ρ, F z‖ ^ 2 ≤
        C * ((ρ / R) ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (∫ y in ball x₀ R, ‖F y - ⨍ z in ball x₀ R, F z‖ ^ 2) +
          ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (K ^ 2 * M ^ 2 + KG ^ 2 + Kf ^ 2 * R ^ (2 - 2 * α))) := by
  obtain ⟨C, hC, h⟩ := campanato_decay_at_point_skew E hα hα1
  refine ⟨C, hC, fun x₀ R M K KG Kf F G f ã hR hFm hFM hcurl hãm hã ↦
    h x₀ R M K KG Kf F G f ã 0 (by simp) hR hFm hFM hcurl hãm fun y hy ↦ ?_⟩
  rw [add_zero]; exact hã y hy

end BasicElliptic.Div
