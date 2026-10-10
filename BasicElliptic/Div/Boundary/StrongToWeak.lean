/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Div
public import BasicElliptic.Div.Boundary.HalfBall
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Strong conormal solutions are weak conormal solutions

`Div.isConormalSolOn_of_strong` and `Div.isQuasilinearConormalSolOn_of_strong` prove
`Div.ConormalStrongToWeakStatement` and `Div.QuasilinearStrongToWeakStatement`.

## Proof

Both reduce to one identity (`integral_inner_gradient_eq`): let `B⁺ = halfBall ν x r`,
`Ω = ball x r ∩ {⟪·, ν⟫ > 0}`, `V ∈ C¹(Ω)` a vector field agreeing on `Ω` with `Vb`, continuous on
`B⁺`, with `-div V = g ∈ L¹(B⁺)` in `Ω` and `⟪Vb, ν⟫ = 0` on `ball x r ∩ flatPart ν`. Then
`∫_{B⁺} ⟪Vb, ∇φ⟫ = ∫_{B⁺} g φ` for every `φ ∈ C¹_c(ball x r)`.

Only `div V` is controlled near the flat part (the individual derivatives of `V` need not be
integrable), so we do not integrate by parts on `B⁺` directly. Instead, with the smooth transition
`s` and `χ_ε(y) = s(⟪y, ν⟫ / ε - 1)` (zero for `⟪y, ν⟫ ≤ ε`, one for `⟪y, ν⟫ ≥ 2ε`), the field
`Ψ_ε = χ_ε φ V` is `C¹_c(E)`, so `∫ div Ψ_ε = 0` (`integral_divergence_eq_zero`, from
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` in an orthonormal frame). Expanding,
`0 = ∫_Ω χ_ε (⟪Vb, ∇φ⟫ - g φ) + ∫_Ω φ s'(⟪y, ν⟫/ε - 1) ε⁻¹ ⟪Vb, ν⟫`.
As `ε → 0⁺` the first term tends to `∫_Ω (⟪Vb, ∇φ⟫ - g φ)` by dominated convergence. The second is
supported in the slab `ε ≤ ⟪y, ν⟫ ≤ 2ε`, where `|⟪Vb, ν⟫|` is uniformly small (uniform continuity
on the compact `B⁺` and the boundary condition at the foot point `y - ⟪y, ν⟫ ν`), and the slab has
volume `O(ε)` (`volume_slab_le`, by disjoint translates), so it tends to `0`.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_sub_inner_smul_le {ν : E} (hν : ‖ν‖ = 1) (z : E) :
    ‖z - ⟪z, ν⟫ • ν‖ ≤ ‖z‖ := by
  have h2 : ‖z - ⟪z, ν⟫ • ν‖ ^ 2 = ‖z‖ ^ 2 - ⟪z, ν⟫ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hν, Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  nlinarith [norm_nonneg (z - ⟪z, ν⟫ • ν), norm_nonneg z, sq_nonneg ⟪z, ν⟫]

/-- A slab of a cylinder with axis `ν`: tangential part within `r` of `c`, `a ≤ ⟪y, ν⟫ < b`. -/
private def slab (ν c : E) (r a b : ℝ) : Set E :=
  {y | ‖y - ⟪y, ν⟫ • ν - c‖ < r ∧ a ≤ ⟪y, ν⟫ ∧ ⟪y, ν⟫ < b}

private theorem slab_preimage_add {ν : E} (hν : ‖ν‖ = 1) (c : E) (r a b t : ℝ) :
    (fun y ↦ t • ν + y) ⁻¹' slab ν c r (a + t) (b + t) = slab ν c r a b := by
  have h1 : ∀ y : E, ⟪t • ν + y, ν⟫ = t + ⟪y, ν⟫ := fun y ↦ by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν, mul_one]
  ext y
  simp only [slab, mem_preimage, mem_ofPred_eq, h1]
  have h2 : t • ν + y - (t + ⟪y, ν⟫) • ν - c = y - ⟪y, ν⟫ • ν - c := by
    rw [add_smul]; abel
  rw [h2]
  constructor
  · rintro ⟨h, h', h''⟩; exact ⟨h, by linarith, by linarith⟩
  · rintro ⟨h, h', h''⟩; exact ⟨h, by linarith, by linarith⟩

private theorem slab_subset_closedBall {ν : E} (hν : ‖ν‖ = 1) (c : E) (r : ℝ) :
    slab ν c r 0 1 ⊆ closedBall c (r + 1) := by
  rintro y ⟨h, h0, h1⟩
  rw [mem_closedBall, dist_eq_norm]
  have : y - c = (y - ⟪y, ν⟫ • ν - c) + ⟪y, ν⟫ • ν := by abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_nonneg h0]
  linarith

private theorem ball_inter_subset_slab {ν : E} (hν : ‖ν‖ = 1) (x : E) (r a b : ℝ) :
    ball x r ∩ {y | a ≤ ⟪y, ν⟫ ∧ ⟪y, ν⟫ < b} ⊆ slab ν (x - ⟪x, ν⟫ • ν) r a b := by
  rintro y ⟨hy, ha, hb⟩
  refine ⟨?_, ha, hb⟩
  have : y - ⟪y, ν⟫ • ν - (x - ⟪x, ν⟫ • ν) = (y - x) - ⟪y - x, ν⟫ • ν := by
    rw [inner_sub_left, sub_smul]; abel
  rw [this]
  exact (norm_sub_inner_smul_le hν _).trans_lt (mem_ball_iff_norm.1 hy)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
private theorem measurableSet_slab (ν c : E) (r a b : ℝ) : MeasurableSet (slab ν c r a b) := by
  have h1 : Continuous fun y : E ↦ ‖y - ⟪y, ν⟫ • ν - c‖ := by fun_prop
  have h2 : Continuous fun y : E ↦ ⟪y, ν⟫ := by fun_prop
  exact (measurableSet_lt h1.measurable measurable_const).inter
    ((measurableSet_le measurable_const h2.measurable).inter
      (measurableSet_lt h2.measurable measurable_const))

private theorem volume_slab_lt_top {ν : E} (hν : ‖ν‖ = 1) (c : E) (r : ℝ) :
    volume (slab ν c r 0 1) < ⊤ :=
  (measure_mono (slab_subset_closedBall hν c r)).trans_lt measure_closedBall_lt_top

/-- Thin slabs: `|S(0, ε)| ≤ 2ε |S(0, 1)|` for `0 < ε ≤ 1/2` (disjoint translates). -/
private theorem volume_slab_le {ν : E} (hν : ‖ν‖ = 1) (c : E) (r : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    volume.real (slab ν c r 0 ε) ≤ 2 * ε * volume.real (slab ν c r 0 1) := by
  set N : ℕ := ⌊1 / ε⌋₊ with hN
  have hNε : (N : ℝ) * ε ≤ 1 := by
    have := Nat.floor_le (a := 1 / ε) (by positivity)
    rw [← hN] at this
    calc (N : ℝ) * ε ≤ 1 / ε * ε := by gcongr
      _ = 1 := by field_simp
  have hN2 : 1 ≤ 2 * ε * N := by
    have := Nat.lt_floor_add_one (1 / ε)
    rw [← hN] at this
    have h1 : 1 / ε - 1 < N := by linarith
    have h2 : 1 / ε * ε = 1 := by field_simp
    nlinarith
  set f : ℕ → Set E := fun k ↦ slab ν c r (k * ε) ((k + 1) * ε) with hf
  have hfm : ∀ k, volume (f k) = volume (slab ν c r 0 ε) := fun k ↦ by
    have := slab_preimage_add hν c r 0 ε (k * ε)
    rw [zero_add, show ε + k * ε = (k + 1) * ε by ring] at this
    rw [hf, ← this, measure_preimage_add]
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint f := by
    intro k _ l _ hkl
    refine Set.disjoint_left.2 fun y hk hl ↦ hkl ?_
    obtain ⟨_, hk1, hk2⟩ := hk
    obtain ⟨_, hl1, hl2⟩ := hl
    have h1 : (k : ℝ) < l + 1 := lt_of_mul_lt_mul_right (hk1.trans_lt hl2) hε.le
    have h2 : (l : ℝ) < k + 1 := lt_of_mul_lt_mul_right (hl1.trans_lt hk2) hε.le
    have h1' : k < l + 1 := by exact_mod_cast h1
    have h2' : l < k + 1 := by exact_mod_cast h2
    omega
  have hsub : (⋃ k ∈ Finset.range N, f k) ⊆ slab ν c r 0 1 := by
    intro y hy'
    obtain ⟨k, hk, hy, hy1, hy2⟩ := mem_iUnion₂.1 hy'
    rw [Finset.mem_range] at hk
    refine ⟨hy, le_trans (by positivity) hy1, hy2.trans_le ?_⟩
    have : ((k : ℝ) + 1) ≤ N := by exact_mod_cast hk
    nlinarith
  have hsum := measure_biUnion_finset (μ := volume) hdisj fun k _ ↦ measurableSet_slab ν c r _ _
  simp only [hfm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hle : (N : ENNReal) * volume (slab ν c r 0 ε) ≤ volume (slab ν c r 0 1) :=
    hsum ▸ measure_mono hsub
  have hlt := volume_slab_lt_top hν c r
  have hle' : (N : ℝ) * volume.real (slab ν c r 0 ε) ≤ volume.real (slab ν c r 0 1) := by
    have := ENNReal.toReal_mono hlt.ne hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
  have h0 : 0 ≤ volume.real (slab ν c r 0 ε) := measureReal_nonneg
  nlinarith

/-! ### Integration by parts on the whole space -/

private theorem integral_fderiv_apply_eq_zero' {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    (hs : HasCompactSupport h) (v : E) : ∫ y, fderiv ℝ h y v = 0 := by
  have hc : Continuous fun y ↦ fderiv ℝ h y v :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : E ↦ (1 : ℝ)) (g := h) (v := v) (by simp) ?_ ?_
    (fun y _ ↦ differentiableAt_const _) (fun y _ ↦ hh.differentiable one_ne_zero y)
  · simpa using key
  · simpa using hc.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) v)
  · simpa using hh.continuous.integrable_of_hasCompactSupport hs

private theorem integral_divergence_eq_zero {Ψ : E → E} (hΨ : ContDiff ℝ 1 Ψ)
    (hs : HasCompactSupport Ψ) : ∫ y, divergence Ψ y = 0 := by
  let b := stdOrthonormalBasis ℝ E
  have hd : ∀ y, divergence Ψ y = ∑ i, fderiv ℝ (fun z ↦ ⟪b i, Ψ z⟫) y (b i) := by
    intro y
    rw [divergence, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := (innerSL ℝ (b i)).hasFDerivAt.comp y
      ((hΨ.differentiable one_ne_zero) y).hasFDerivAt
    rw [show (fun z ↦ ⟪b i, Ψ z⟫) = (innerSL ℝ (b i)) ∘ Ψ from rfl, h.fderiv]
    simp
  have hci : ∀ i, ContDiff ℝ 1 (fun z ↦ ⟪b i, Ψ z⟫) := fun i ↦ contDiff_const.inner ℝ hΨ
  have hsi : ∀ i, HasCompactSupport (fun z ↦ ⟪b i, Ψ z⟫) := fun i ↦
    hs.comp_left (g := fun u ↦ ⟪b i, u⟫) (inner_zero_right _)
  simp_rw [hd]
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun i _ ↦ integral_fderiv_apply_eq_zero' (hci i) (hsi i) _
  · intro i _
    exact (((hci i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport ((hsi i).fderiv_apply (𝕜 := ℝ) _)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem divergence_smul {c : E → ℝ} {V : E → E} {y : E} (hc : DifferentiableAt ℝ c y)
    (hV : DifferentiableAt ℝ V y) :
    divergence (fun z ↦ c z • V z) y = c y * divergence V y + fderiv ℝ c y (V y) := by
  rw [divergence, divergence, fderiv_fun_smul hc hV, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_smulRight, map_add, map_smul,
    LinearMap.trace_smulRight, smul_eq_mul]
  rfl

/-! ### The smooth transition -/

private theorem deriv_smoothTransition_eq_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 0 :=
      (eventually_lt_nhds ht).mono fun s hs ↦ Real.smoothTransition.zero_of_nonpos hs.le
    rw [heq.deriv_eq, deriv_const]
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 1 :=
      (eventually_gt_nhds ht).mono fun s hs ↦ Real.smoothTransition.one_of_one_le hs.le
    rw [heq.deriv_eq, deriv_const]

private theorem exists_bound_deriv_smoothTransition' :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, |deriv Real.smoothTransition t| ≤ L := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨L, hL0, fun t ↦ ?_⟩
  by_cases ht : t < 0 ∨ 1 < t
  · rw [deriv_smoothTransition_eq_zero ht, abs_zero]; exact hL0
  · push Not at ht
    rw [← Real.norm_eq_abs]; exact hL t ⟨ht.1, ht.2⟩

/-! ### The core identity -/

/-- **Core identity.** Let `V ∈ C¹(Ω)`, `Ω = ball x r ∩ {⟪·, ν⟫ > 0}`, agree on `Ω` with `Vb`,
continuous on the closed half ball `B⁺`, with `-div V = g ∈ L¹(B⁺)` in `Ω` and `⟪Vb, ν⟫ = 0` on
`ball x r ∩ flatPart ν`. Then `∫_{B⁺} ⟪Vb, ∇φ⟫ = ∫_{B⁺} g φ` for `φ ∈ C¹_c(ball x r)`. -/
private theorem integral_inner_gradient_eq {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1)
    {V Vb : E → E} {g : E → ℝ}
    (hV : ContDiffOn ℝ 1 V (ball x r ∩ openHalfSpace ν))
    (hVb : ContinuousOn Vb (halfBall ν x r))
    (hVV : ∀ y ∈ ball x r ∩ openHalfSpace ν, Vb y = V y)
    (hg : IntegrableOn g (halfBall ν x r))
    (hdiv : ∀ y ∈ ball x r ∩ openHalfSpace ν, -divergence V y = g y)
    (hflat : ∀ y ∈ ball x r ∩ flatPart ν, ⟪Vb y, ν⟫ = 0)
    {φ : E → ℝ} (hφ : IsTestFn (ball x r) φ) :
    ∫ y in halfBall ν x r, ⟪Vb y, ∇ φ y⟫ = ∫ y in halfBall ν x r, g y * φ y := by
  set Ω := ball x r ∩ openHalfSpace ν with hΩ
  set B := halfBall ν x r with hB
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have hΩo : IsOpen Ω := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  have hΩB : Ω ⊆ B := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, mem_halfSpace.2 (mem_openHalfSpace.1 hz.2).le⟩
  have hBc : IsCompact B := isCompact_halfBall ν x r
  set s := Real.smoothTransition with hs
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_deriv_smoothTransition'
  have hsd : ∀ t, HasDerivAt s (deriv s t) t := fun t ↦
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have hsc' : Continuous (deriv s) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hl : ∀ y, HasFDerivAt (fun y : E ↦ ⟪y, ν⟫) (innerSL ℝ ν) y := by
    have hfun : (fun y : E ↦ ⟪y, ν⟫) = ⇑(innerSL ℝ ν) :=
      funext fun y ↦ by rw [innerSL_apply_apply, real_inner_comm]
    intro y; rw [hfun]; exact (innerSL ℝ ν).hasFDerivAt
  have hDφ : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv one_ne_zero
  -- the bulk integrand
  set P : E → ℝ := fun y ↦ fderiv ℝ φ y (Vb y) - g y * φ y with hP
  have hP1 : IntegrableOn (fun y ↦ fderiv ℝ φ y (Vb y)) Ω :=
    (ContinuousOn.integrableOn_compact hBc (hDφ.continuousOn.clm_apply hVb)).mono_set hΩB
  have hP2 : IntegrableOn (fun y ↦ g y * φ y) Ω :=
    (hg.mul_continuousOn hφ.1.continuous.continuousOn hBc).mono_set hΩB
  have hPi : IntegrableOn P Ω := hP1.sub hP2
  -- the cut-off and the boundary-layer integrand
  set χ : ℝ → E → ℝ := fun ε y ↦ s (ε⁻¹ * ⟪y, ν⟫ - 1) with hχ
  have hχc : ∀ ε, ContDiff ℝ 1 (χ ε) := fun ε ↦ Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).sub contDiff_const)
  set Jf : ℝ → E → ℝ := fun ε y ↦ φ y * (deriv s (ε⁻¹ * ⟪y, ν⟫ - 1) * (ε⁻¹ * ⟪Vb y, ν⟫))
    with hJf
  have hχ1 : ∀ ε y, ‖χ ε y‖ ≤ 1 := fun ε y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  -- `∫ div Ψ_ε = 0`, expanded
  have key : ∀ ε > 0, (∫ y in Ω, χ ε y * P y) + ∫ y in Ω, Jf ε y = 0 := by
    intro ε hε
    have hχd : ∀ y, HasFDerivAt (χ ε) (deriv s (ε⁻¹ * ⟪y, ν⟫ - 1) • (ε⁻¹ • innerSL ℝ ν)) y :=
      fun y ↦ (hsd _).comp_hasFDerivAt y (((hl y).const_mul ε⁻¹).sub_const 1)
    set c : E → ℝ := fun y ↦ χ ε y * φ y with hc
    have hcc : ContDiff ℝ 1 c := (hχc ε).mul hφ.1
    have hcs : tsupport c ⊆ Ω := by
      have hcl : IsClosed {y : E | ε ≤ ⟪y, ν⟫} :=
        isClosed_le continuous_const (continuous_id.inner continuous_const)
      refine (closure_minimal (fun y hy ↦ ?_) (hcl.inter (isClosed_tsupport φ))).trans ?_
      · have hy' : χ ε y * φ y ≠ 0 := hy
        refine ⟨?_, subset_tsupport φ (right_ne_zero_of_mul hy')⟩
        by_contra hlt
        have hlt' : ⟪y, ν⟫ < ε := not_le.1 hlt
        apply left_ne_zero_of_mul hy'
        refine Real.smoothTransition.zero_of_nonpos ?_
        have : ε⁻¹ * ⟪y, ν⟫ ≤ ε⁻¹ * ε := by gcongr
        rw [inv_mul_cancel₀ hε.ne'] at this
        linarith
      · rintro y ⟨hy1, hy2⟩
        exact ⟨hφ.2.2 hy2, lt_of_lt_of_le hε hy1⟩
    set Ψ : E → E := fun y ↦ c y • V y with hΨ
    have hΨ0 : ∀ y ∉ Ω, Ψ =ᶠ[𝓝 y] fun _ ↦ 0 := fun y hy ↦
      (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hy (hcs h)).mono fun z hz ↦ by
        change c z • V z = 0
        rw [hz, Pi.zero_apply, zero_smul]
    have hΨc : ContDiff ℝ 1 Ψ := by
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy : y ∈ Ω
      · exact hcc.contDiffAt.smul (hV.contDiffAt (hΩo.mem_nhds hy))
      · exact contDiffAt_const.congr_of_eventuallyEq (hΨ0 y hy)
    have hΨs : HasCompactSupport Ψ :=
      HasCompactSupport.smul_right (f' := V) (HasCompactSupport.mul_left (f := χ ε) hφ.2.1)
    have hdivΨ : ∀ y ∈ Ω, divergence Ψ y = χ ε y * P y + Jf ε y := by
      intro y hy
      have hVd : DifferentiableAt ℝ V y :=
        (hV.contDiffAt (hΩo.mem_nhds hy)).differentiableAt one_ne_zero
      have hφd : DifferentiableAt ℝ φ y := hφ.1.differentiable one_ne_zero y
      rw [hΨ, divergence_smul (hcc.differentiable one_ne_zero y) hVd, hc,
        fderiv_fun_mul (hχd y).differentiableAt hφd, (hχd y).fderiv]
      have hdv : divergence V y = -g y := by linarith [hdiv y hy]
      rw [hdv]
      simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, hP, hJf]
      rw [hVV y hy, real_inner_comm ν (V y)]
      ring
    have h0 := integral_divergence_eq_zero hΨc hΨs
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω) (fun y hy ↦ by
      rw [divergence, (hΨ0 y hy).fderiv_eq, fderiv_const_apply]
      simp)] at h0
    have hI1 : IntegrableOn (fun y ↦ χ ε y * P y) Ω :=
      Integrable.bdd_mul (c := 1) hPi (hχc ε).continuous.aestronglyMeasurable
        (Eventually.of_forall (hχ1 ε))
    have hJ1 : IntegrableOn (Jf ε) Ω := by
      refine (ContinuousOn.integrableOn_compact hBc ?_).mono_set hΩB
      exact hφ.1.continuous.continuousOn.mul
        ((hsc'.comp (by fun_prop : Continuous fun y : E ↦ ε⁻¹ * ⟪y, ν⟫ - 1)).continuousOn.mul
          (continuousOn_const.mul (hVb.inner continuousOn_const)))
    rw [setIntegral_congr_fun hΩm hdivΨ, integral_add hI1 hJ1] at h0
    exact h0
  have hI : Tendsto (fun ε ↦ ∫ y in Ω, χ ε y * P y) (𝓝[>] 0) (𝓝 (∫ y in Ω, P y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖P y‖) ?_ ?_ hPi.norm ?_
    · exact Eventually.of_forall fun ε ↦
        (hχc ε).continuous.aestronglyMeasurable.mul hPi.aestronglyMeasurable
    · exact Eventually.of_forall fun ε ↦ Eventually.of_forall fun y ↦ by
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 ε y)
    · filter_upwards [ae_restrict_mem hΩm] with y hy
      have hpos : 0 < ⟪y, ν⟫ := hy.2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ⟪y, ν⟫ / 2 by positivity)] with ε hε
      have h2 : 2 ≤ ⟪y, ν⟫ / ε := (le_div_iff₀ hε.1).2 (by linarith [hε.2])
      have h1 : 1 ≤ ε⁻¹ * ⟪y, ν⟫ - 1 := by rw [inv_mul_eq_div]; linarith
      change P y = s (ε⁻¹ * ⟪y, ν⟫ - 1) * P y
      rw [hs, Real.smoothTransition.one_of_one_le h1, one_mul]
  -- `⟪Vb, ν⟫` is uniformly small near the flat part on the support of `φ`
  have huc : ∀ η > 0, ∃ ε₁ > 0, ∀ y ∈ tsupport φ, 0 ≤ ⟪y, ν⟫ → ⟪y, ν⟫ < ε₁ →
      |⟪Vb y, ν⟫| ≤ η := by
    intro η hη
    obtain ⟨r', hr', hr'φ⟩ := exists_lt_subset_ball (isClosed_tsupport φ) hφ.2.2
    have hVbν : ContinuousOn (fun y ↦ ⟪Vb y, ν⟫) B := hVb.inner continuousOn_const
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.uniformContinuousOn_iff.1
      (hBc.uniformContinuousOn_of_continuous hVbν) η hη
    refine ⟨min δ₁ (r - r'), lt_min hδ₁ (by linarith), fun y hy hy0 hyε ↦ ?_⟩
    set y' := y - ⟪y, ν⟫ • ν with hy'
    have hyy' : dist y y' = ⟪y, ν⟫ := by
      rw [hy', dist_eq_norm, sub_sub_cancel, norm_smul, hν, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hy0]
    have hyx : dist y x < r' := hr'φ hy
    have hy'x : dist y' x < r := by
      have := dist_triangle y' y x
      rw [dist_comm] at hyy'
      linarith [min_le_right δ₁ (r - r')]
    have hy'f : ⟪y', ν⟫ = 0 := by
      rw [hy', inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν]
      ring
    have hyB : y ∈ B := ⟨mem_closedBall.2 (hyx.le.trans hr'.le), hy0⟩
    have hy'B : y' ∈ B := ⟨mem_closedBall.2 hy'x.le, hy'f.ge⟩
    have h := hδ₁' y hyB y' hy'B (by rw [hyy']; linarith [min_le_left δ₁ (r - r')])
    rw [hflat y' ⟨hy'x, hy'f⟩, Real.dist_eq, sub_zero] at h
    exact h.le
  have hJ : Tendsto (fun ε ↦ ∫ y in Ω, Jf ε y) (𝓝[>] 0) (𝓝 0) := by
    obtain ⟨Mφ, hMφ⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
    have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
    set c₀ := x - ⟪x, ν⟫ • ν
    set A := volume.real (slab ν c₀ r 0 1) with hA
    have hA0 : 0 ≤ A := measureReal_nonneg
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set K := 6 * Mφ * C₁ * A + 1 with hK
    have hK0 : 0 < K := by positivity
    set η := δ / (2 * K) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨ε₁, hε₁, hε₁'⟩ := huc η hη0
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (ε₁ / 2) (1 / 6) by positivity)]
      with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    have hε2 : 2 * ε < ε₁ := by linarith [min_le_left (ε₁ / 2) (1 / 6)]
    have hε3 : 3 * ε ≤ 1 / 2 := by linarith [min_le_right (ε₁ / 2) (1 / 6)]
    set Sε : Set E := {y | ε ≤ ⟪y, ν⟫ ∧ ⟪y, ν⟫ ≤ 2 * ε} with hSε
    have hSm : MeasurableSet Sε := by
      have h2 : Continuous fun y : E ↦ ⟪y, ν⟫ := by fun_prop
      exact (measurableSet_le measurable_const h2.measurable).inter
        (measurableSet_le h2.measurable measurable_const)
    set bnd := Mφ * (C₁ * (ε⁻¹ * η)) with hbnd
    have hbnd0 : 0 ≤ bnd := by positivity
    have hpt : ∀ y ∈ Ω, ‖Jf ε y‖ ≤ Sε.indicator (fun _ ↦ bnd) y := by
      intro y hy
      by_cases hyS : y ∈ Sε
      · rw [indicator_of_mem hyS]
        by_cases hφy : φ y = 0
        · simp only [hJf, hφy, zero_mul, norm_zero]; exact hbnd0
        · have hyt : y ∈ tsupport φ := subset_tsupport _ hφy
          have hη' := hε₁' y hyt (mem_openHalfSpace.1 hy.2).le (by linarith [hyS.2])
          simp only [hJf, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hε0]
          refine mul_le_mul ?_ (mul_le_mul (hC₁ _) (mul_le_mul_of_nonneg_left hη'
            (by positivity)) (by positivity) hC₁0) (by positivity) hMφ0
          rw [← Real.norm_eq_abs]; exact hMφ y
      · rw [indicator_of_notMem hyS]
        have hz : deriv s (ε⁻¹ * ⟪y, ν⟫ - 1) = 0 := by
          refine deriv_smoothTransition_eq_zero ?_
          rw [inv_mul_eq_div]
          rcases not_and_or.1 hyS with h | h
          · left
            have : ⟪y, ν⟫ / ε < 1 := (div_lt_one hε0).2 (not_le.1 h)
            linarith
          · right
            have : 2 < ⟪y, ν⟫ / ε := (lt_div_iff₀ hε0).2 (by linarith [not_le.1 h])
            linarith
        simp [hJf, hz]
    have hΩfin : volume Ω < ⊤ := (measure_mono (hΩB.trans
      (halfBall_subset_closedBall ν x r))).trans_lt measure_closedBall_lt_top
    have hSfin : volume.restrict Ω Sε ≠ ⊤ :=
      ((measure_mono (subset_univ Sε)).trans_lt (by rwa [Measure.restrict_apply_univ])).ne
    have hint : ‖∫ y in Ω, Jf ε y‖ ≤ ∫ y in Ω, Sε.indicator (fun _ ↦ bnd) y :=
      norm_integral_le_of_norm_le ((integrable_indicator_iff hSm).2 (integrableOn_const hSfin))
        ((ae_restrict_iff' hΩm).2 (Eventually.of_forall hpt))
    rw [integral_indicator_const _ hSm, measureReal_restrict_apply hSm, smul_eq_mul] at hint
    have hsub : Sε ∩ Ω ⊆ slab ν c₀ r 0 (3 * ε) := fun y hy ↦
      ball_inter_subset_slab hν x r 0 (3 * ε) ⟨hy.2.1, (mem_openHalfSpace.1 hy.2.2).le,
        by linarith [hy.1.2]⟩
    have hsub' : slab ν c₀ r 0 (3 * ε) ⊆ slab ν c₀ r 0 1 := fun y hy ↦
      ⟨hy.1, hy.2.1, by linarith [hy.2.2]⟩
    have hfin : volume (slab ν c₀ r 0 (3 * ε)) ≠ ⊤ :=
      ((measure_mono hsub').trans_lt (volume_slab_lt_top hν c₀ r)).ne
    have hvol : volume.real (Sε ∩ Ω) ≤ 2 * (3 * ε) * A :=
      (measureReal_mono hsub hfin).trans (volume_slab_le hν c₀ r (by positivity) hε3)
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
    calc ‖∫ y in Ω, Jf ε y‖ ≤ volume.real (Sε ∩ Ω) * bnd := hint
      _ ≤ 2 * (3 * ε) * A * bnd := mul_le_mul_of_nonneg_right hvol hbnd0
      _ = (6 * Mφ * C₁ * A) * η := by rw [hbnd]; field_simp; ring
      _ ≤ K * η := by gcongr; linarith
      _ = δ / 2 := by rw [hη]; field_simp
      _ < δ := by linarith
  have hI0 : Tendsto (fun ε ↦ ∫ y in Ω, χ ε y * P y) (𝓝[>] 0) (𝓝 0) := by
    have := hJ.neg
    rw [neg_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    linarith [key ε hε]
  have hP0 : ∫ y in Ω, P y = 0 := tendsto_nhds_unique hI hI0
  rw [hP, integral_sub hP1 hP2, sub_eq_zero] at hP0
  have hset := halfBall_ae_eq hν0 x r
  rw [setIntegral_congr_set hset, setIntegral_congr_set hset, ← hP0]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only
  rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]


/-! ### The two bridges -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If the ball misses the open half space, the closed half ball lies in the flat part. -/
private theorem halfBall_subset_flatPart {ν x : E} {r : ℝ} (hν : ‖ν‖ = 1)
    (hx : ⟪x, ν⟫ ≤ -r) : halfBall ν x r ⊆ flatPart ν := by
  rintro y ⟨hy, hy0⟩
  have h1 : ⟪y - x, ν⟫ ≤ ‖y - x‖ := by
    simpa [hν] using real_inner_le_norm (y - x) ν
  rw [inner_sub_left] at h1
  have h2 : ‖y - x‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
  exact le_antisymm (by linarith) (mem_halfSpace.1 hy0)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem contDiffOn_gradient_of_contDiffOn_two {w : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hw : ContDiffOn ℝ 2 w s) : ContDiffOn ℝ 1 (∇ w) s :=
  (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn
    (hw.fderiv_of_isOpen hs (by norm_num))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_gradient_of_isTestFn {U : Set E} {φ : E → ℝ} (hφ : IsTestFn U φ) :
    Continuous (∇ φ) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ.1.continuous_fderiv one_ne_zero)

variable (E) in
/-- **Strong ⇒ weak**, linear conormal problem (`Div.ConormalStrongToWeakStatement`). -/
theorem Div.isConormalSolOn_of_strong : Div.ConormalStrongToWeakStatement E := by
  intro ν x r a G f w hν hr hw hw2 ha ha1 hG hG1 hf hdiv hflat
  refine ⟨hw, fun φ hφ ↦ ?_⟩
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  rcases le_or_gt ⟪x, ν⟫ (-r) with hx | hx
  · have h0 : volume (halfBall ν x r) = 0 :=
      measure_mono_null (halfBall_subset_flatPart hν hx) (volume_flatPart hν0)
    simp [Measure.restrict_eq_zero.2 h0]
  set B := halfBall ν x r with hB
  set gW := gradientWithin w B with hgW
  have hΩo : IsOpen (ball x r ∩ openHalfSpace ν) := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hgc : ContinuousOn gW B := continuousOn_gradientWithin_halfBall hν hr hx hw
  have hgrad := contDiffOn_gradient_of_contDiffOn_two hΩo hw2
  have key := integral_inner_gradient_eq hν (V := fun z ↦ a z (∇ w z) - G z)
    (Vb := fun y ↦ a y (gW y) - G y) (g := f) ((ha1.clm_apply hgrad).sub hG1)
    ((ha.clm_apply hgc).sub hG) (fun y hy ↦ by
      rw [hgW, hB, gradientWithin_halfBall_eq hy])
    hf hdiv hflat hφ
  have hφc := continuous_gradient_of_isTestFn hφ
  have hi1 : IntegrableOn (fun y ↦ ⟪a y (gW y), ∇ φ y⟫) B :=
    ContinuousOn.integrableOn_compact (isCompact_halfBall ν x r)
      ((ha.clm_apply hgc).inner hφc.continuousOn)
  have hi2 : IntegrableOn (fun y ↦ ⟪G y, ∇ φ y⟫) B :=
    ContinuousOn.integrableOn_compact (isCompact_halfBall ν x r) (hG.inner hφc.continuousOn)
  simp only [inner_sub_left] at key
  rw [integral_sub hi1 hi2] at key
  linarith

variable (E) in
/-- **Strong ⇒ weak**, quasilinear conormal problem (`Div.QuasilinearStrongToWeakStatement`). -/
theorem Div.isQuasilinearConormalSolOn_of_strong : Div.QuasilinearStrongToWeakStatement E := by
  intro ν x r Φ U w hν hr hU hw hw2 hΦ hgU hdiv hflat
  refine ⟨hw, fun φ hφ ↦ ?_⟩
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  rcases le_or_gt ⟪x, ν⟫ (-r) with hx | hx
  · have h0 : volume (halfBall ν x r) = 0 :=
      measure_mono_null (halfBall_subset_flatPart hν hx) (volume_flatPart hν0)
    simp [Measure.restrict_eq_zero.2 h0]
  set B := halfBall ν x r with hB
  set gW := gradientWithin w B with hgW
  have hΩo : IsOpen (ball x r ∩ openHalfSpace ν) := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hΩB : ball x r ∩ openHalfSpace ν ⊆ B := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, mem_halfSpace.2 (mem_openHalfSpace.1 hz.2).le⟩
  have hgc : ContinuousOn gW B := continuousOn_gradientWithin_halfBall hν hr hx hw
  have hgrad := contDiffOn_gradient_of_contDiffOn_two hΩo hw2
  have hmaps : MapsTo (∇ w) (ball x r ∩ openHalfSpace ν) U := fun z hz ↦ by
    rw [← gradientWithin_halfBall_eq hz]; exact hgU z (hΩB hz)
  have key := integral_inner_gradient_eq hν (V := fun z ↦ Φ (∇ w z))
    (Vb := fun y ↦ Φ (gW y)) (g := 0) (hΦ.comp hgrad hmaps)
    (hΦ.continuousOn.comp hgc fun y hy ↦ hgU y hy)
    (fun y hy ↦ by
      rw [hgW, hB, gradientWithin_halfBall_eq hy]) integrableOn_zero
    (fun y hy ↦ by rw [hdiv y hy, neg_zero, Pi.zero_apply]) hflat hφ
  simpa using key

end BasicElliptic
