/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Harmonic.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Weyl's lemma for locally integrable functions

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`
(`volume` in applications), and `U ⊆ E` open.

* `BasicElliptic.exists_harmonic_ae_eq_of_weaklyHarmonic`: if `u ∈ L¹_loc(U)` satisfies
  `∫ u Δψ = 0` for every `ψ ∈ C_c^∞(U)`, then `u` agrees a.e. on `U` with a function harmonic
  on `U` (Mathlib's `InnerProductSpace.HarmonicOnNhd`).
* `BasicElliptic.exists_harmonic_ae_eq_of_weaklyHarmonic_field`: the same for a vector field
  `V : E → F` whose components `⟪V, e⟫` are weakly harmonic; the harmonic representative is
  harmonic as an `F`-valued map and componentwise.

## Proof

Fix `x₀ ∈ U` and `r > 0` with `B := closedBall x₀ (3 r) ⊆ U`, and let `f := 1_B u ∈ L¹`.

1. For any smooth kernel `κ` supported in `closedBall 0 r`, `f ⋆ κ` is smooth and
   `Δ (f ⋆ κ)(x) = ∫ u(t) Δ[κ(x - ·)](t) dt = 0` for `x ∈ ball x₀ (2 r)`, by weak harmonicity
   with the test function `κ(x - ·)`. So `f ⋆ κ` is harmonic on `ball x₀ (2 r)`.
2. Let `ρ` be a radial kernel of radius `r` (`ViscositySolns.Analysis.exists_radial_kernel`) and
   `h := f ⋆ ρ`. For a normed bump `φₙ` of radius `r/(n+1)` and `x ∈ ball x₀ r`, the mean value
   property of the harmonic `f ⋆ φₙ` and associativity and commutativity of convolution give
   `(f ⋆ φₙ)(x) = ((f ⋆ φₙ) ⋆ ρ)(x) = ((f ⋆ ρ) ⋆ φₙ)(x) = (h ⋆ φₙ)(x)`.
3. As `n → ∞`, the left side tends to `f(x)` for a.e. `x` (Lebesgue differentiation,
   `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`) and the right side to `h(x)`
   (`h` is continuous). Hence `u = h` a.e. on `ball x₀ r`.
4. The local harmonic representatives agree on overlaps (continuous functions equal a.e. on an
   open set are equal there), so they glue to a harmonic function on `U`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.2.3 (mollification).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001.

## Provenance

New (W. M. Feldman). The mollifier pattern follows
`ViscositySolns.Analysis.exists_contDiff_eventuallyEq_laplacian_eq_zero` (viscosity_solns v0.4.0)
and `EllipticBernoulli.eqOn_indicator_convolution_of_weaklyHarmonic` (elliptic-bernoulli-
foundations, `EllipticBernoulli/Harmonic/GradientEstimate.lean`).
-/

open InnerProductSpace MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped ContDiff Laplacian Convolution RealInnerProductSpace
open ViscositySolns.Analysis (exists_radial_kernel laplacian_convolution
  integral_radial_smul_eq_of_weaklyHarmonic tsupport_laplacian_subset)

public section

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Step 1: the Laplacian of a mollification of a weakly harmonic function vanishes wherever the
translated kernel stays inside `B ⊆ U`. -/
private theorem laplacian_indicator_convolution_eq_zero {U B : Set E} {u : E → ℝ}
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, u x * Δ ψ x ∂μ = 0)
    (hBU : B ⊆ U) (hf : LocallyIntegrable (B.indicator u) μ) {κ : E → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hκc : HasCompactSupport κ) {x : E}
    (hx : ∀ t, x - t ∈ tsupport κ → t ∈ B) :
    Δ (B.indicator u ⋆[lsmul ℝ ℝ, μ] κ) x = 0 := by
  set ψ : E → ℝ := fun t ↦ κ (x - t) with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hκc.comp_homeomorph (Homeomorph.subLeft x)
  have hψs : tsupport ψ ⊆ B := by
    intro t ht
    have : tsupport ψ = (Homeomorph.subLeft x) ⁻¹' tsupport κ :=
      tsupport_comp_eq_preimage κ (Homeomorph.subLeft x)
    rw [this] at ht
    exact hx t ht
  have hweakψ := hweak ψ hψ hψc (hψs.trans hBU)
  rw [laplacian_convolution hf hκ hκc, convolution_def, ← hweakψ]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp only [lsmul_apply, smul_eq_mul]
  by_cases ht : t ∈ B
  · rw [indicator_of_mem ht, hψ_def, laplacian_comp_sub_left]
  · have h0 : Δ ψ t = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
      ht (hψs (tsupport_laplacian_subset _ h))
    rw [indicator_of_notMem ht, h0, zero_mul, mul_zero]

/-- Step 1, packaged: the mollification by a kernel supported in `closedBall 0 r` of
`1_B u`, `B = closedBall x₀ (3 r) ⊆ U`, is harmonic on `ball x₀ (2 r)`. -/
private theorem harmonicOnNhd_indicator_convolution {U : Set E} {u : E → ℝ}
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, u x * Δ ψ x ∂μ = 0)
    {x₀ : E} {r : ℝ} (hBU : closedBall x₀ (3 * r) ⊆ U)
    (hf : LocallyIntegrable ((closedBall x₀ (3 * r)).indicator u) μ) {κ : E → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hκc : HasCompactSupport κ) (hκs : tsupport κ ⊆ closedBall 0 r) :
    HarmonicOnNhd ((closedBall x₀ (3 * r)).indicator u ⋆[lsmul ℝ ℝ, μ] κ)
      (ball x₀ (2 * r)) := by
  have hconv : ContDiff ℝ ∞ ((closedBall x₀ (3 * r)).indicator u ⋆[lsmul ℝ ℝ, μ] κ) :=
    hκc.contDiff_convolution_right (n := ⊤) (lsmul ℝ ℝ) hf hκ
  refine (harmonicOnNhd_iff_contDiffOn_laplacian_eq_zero isOpen_ball).2
    ⟨(hconv.of_le (by norm_cast)).contDiffOn, fun x hx ↦ ?_⟩
  refine laplacian_indicator_convolution_eq_zero hweak hBU hf hκ hκc fun t ht ↦ ?_
  have h1 := hκs ht
  rw [mem_closedBall_zero_iff] at h1
  rw [mem_ball] at hx
  rw [mem_closedBall]
  calc dist t x₀ ≤ dist t x + dist x x₀ := dist_triangle _ _ _
    _ = ‖x - t‖ + dist x x₀ := by rw [dist_comm, dist_eq_norm]
    _ ≤ 3 * r := by linarith

/-- Step 2a: mean value property against a radial kernel, for a function harmonic near
`closedBall x r`. -/
private theorem convolution_radial_eq_of_harmonic [Nontrivial E] {V : Set E} (hV : IsOpen V)
    {w : E → ℝ} (hw : HarmonicOnNhd w V) {x : E} {r : ℝ} (hr : 0 < r) (hxV : closedBall x r ⊆ V)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hg0 : ∀ t, r ^ 2 ≤ t → g t = 0)
    (hg1 : ∫ y, g (‖y‖ ^ 2) ∂μ = 1) :
    (w ⋆[lsmul ℝ ℝ, μ] fun y ↦ g (‖y‖ ^ 2)) x = w x := by
  have hk : Continuous fun s : ℝ ↦ g (s ^ 2) := hg.continuous.comp (continuous_pow 2)
  have hmvp := integral_radial_smul_eq_of_weaklyHarmonic hV hw.contDiffOn.continuousOn
    (HarmonicOnNhd.weaklyHarmonicOn (μ := μ) hV hw) hxV hk
    (fun s hs ↦ hg0 _ (pow_le_pow_left₀ hr.le hs.le 2))
  rw [hg1, one_smul] at hmvp
  rw [← hmvp, convolution_def, ← integral_add_left_eq_self _ x]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [lsmul_apply, smul_eq_mul, sub_add_cancel_left, norm_neg]
  ring

/-- Convolution with `lsmul ℝ ℝ` is commutative. -/
private theorem convolution_lsmul_comm (f g : E → ℝ) :
    f ⋆[lsmul ℝ ℝ, μ] g = g ⋆[lsmul ℝ ℝ, μ] f :=
  convolution_symm (lsmul ℝ ℝ) (by ext; simp)

/-- Step 2b: `((f ⋆ φ) ⋆ ρ)(x) = ((f ⋆ ρ) ⋆ φ)(x)` for `f ∈ L¹_loc` and continuous compactly
supported kernels `φ`, `ρ`. -/
private theorem convolution_convolution_swap {f φ ρ : E → ℝ} (hf : LocallyIntegrable f μ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (x : E) :
    ((f ⋆[lsmul ℝ ℝ, μ] φ) ⋆[lsmul ℝ ℝ, μ] ρ) x = ((f ⋆[lsmul ℝ ℝ, μ] ρ) ⋆[lsmul ℝ ℝ, μ] φ) x := by
  have hL : ∀ a b c : ℝ, lsmul ℝ ℝ (lsmul ℝ ℝ a b) c = lsmul ℝ ℝ a (lsmul ℝ ℝ b c) := by
    intro a b c; simp [mul_assoc]
  have hassoc : ∀ {g k : E → ℝ}, Continuous g → HasCompactSupport g → Continuous k →
      HasCompactSupport k →
      ((f ⋆[lsmul ℝ ℝ, μ] g) ⋆[lsmul ℝ ℝ, μ] k) x =
        (f ⋆[lsmul ℝ ℝ, μ] (g ⋆[lsmul ℝ ℝ, μ] k)) x := by
    intro g k hg hgc hk hkc
    refine convolution_assoc (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ) hL
      hf.aestronglyMeasurable hg.aestronglyMeasurable hk.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ hgc.convolutionExists_right (lsmul ℝ ℝ) hf hg y)
      (Eventually.of_forall fun y ↦
        hkc.norm.convolutionExists_right (mul ℝ ℝ) hg.norm.locallyIntegrable hk.norm y) ?_
    have hc : HasCompactSupport ((fun x ↦ ‖g x‖) ⋆[mul ℝ ℝ, μ] fun x ↦ ‖k x‖) :=
      hgc.norm.convolution (mul ℝ ℝ) hkc.norm
    exact hc.convolutionExists_right (mul ℝ ℝ) (fun y ↦ (hf y).norm)
      (hkc.norm.continuous_convolution_right (mul ℝ ℝ) hg.norm.locallyIntegrable hk.norm) x
  rw [hassoc hφ hφc hρ hρc, hassoc hρ hρc hφ hφc, convolution_lsmul_comm φ ρ]

/-- Steps 1–3: the local statement on a small ball around each point of `U`. -/
private theorem exists_local_harmonic_ae_eq [Nontrivial E] {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : LocallyIntegrableOn u U μ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, u x * Δ ψ x ∂μ = 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ r > 0, ∃ h : E → ℝ, HarmonicOnNhd h (ball x₀ r) ∧
      ∀ᵐ x ∂(μ.restrict (ball x₀ r)), u x = h x := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set r := ε / 4 with hr_def
  have hr : 0 < r := by positivity
  set B := closedBall x₀ (3 * r) with hB_def
  have hBU : B ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  set f := B.indicator u with hf_def
  have hfi : Integrable f μ :=
    (hu.integrableOn_compact_subset hBU (isCompact_closedBall _ _)).integrable_indicator
      measurableSet_closedBall
  have hf : LocallyIntegrable f μ := hfi.locallyIntegrable
  -- the radial kernel `ρ` and `h = f ⋆ ρ`
  obtain ⟨g, hg, hg0, hg1⟩ := exists_radial_kernel μ hr
  set ρ : E → ℝ := fun y ↦ g (‖y‖ ^ 2) with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := hg.comp (contDiff_norm_sq ℝ)
  have hρ0 : ∀ y, r < ‖y‖ → ρ y = 0 := fun y hy ↦ hg0 _ (pow_le_pow_left₀ hr.le hy.le 2)
  have hρs : tsupport ρ ⊆ closedBall 0 r := by
    refine closure_minimal (fun y hy ↦ ?_) isClosed_closedBall
    by_contra h
    rw [mem_closedBall_zero_iff, not_le] at h
    exact hy (hρ0 y h)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) r)
      ((subset_tsupport ρ).trans hρs)
  set h := f ⋆[lsmul ℝ ℝ, μ] ρ with hh_def
  have hharm : HarmonicOnNhd h (ball x₀ (2 * r)) :=
    harmonicOnNhd_indicator_convolution hweak hBU hf hρ hρc hρs
  have hhc : Continuous h := hρc.continuous_convolution_right (lsmul ℝ ℝ) hf hρ.continuous
  -- the bumps `φ n` of radius `r / (n + 1)`
  set R : ℕ → ℝ := fun n ↦ r * (1 / ((n : ℝ) + 1)) with hR_def
  have hRpos : ∀ n, 0 < R n := fun n ↦ by positivity
  set φ : ℕ → ContDiffBump (0 : E) := fun n ↦
    ⟨R n / 2, R n, by linarith [hRpos n], by linarith [hRpos n]⟩ with hφ_def
  have hRlim : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
    simpa [hφ_def, hR_def] using this
  have hRle : ∀ n, R n ≤ r := fun n ↦ by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simpa [hR_def] using mul_le_mul_of_nonneg_left this hr.le
  -- Step 2: `φ n ⋆ f = φ n ⋆ h` on `ball x₀ r`
  have hkey : ∀ n, ∀ x ∈ ball x₀ r,
      ((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] f) x = ((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] h) x := by
    intro n x hx
    set κ := (φ n).normed μ
    have hκ : ContDiff ℝ ∞ κ := (φ n).contDiff_normed
    have hκc : HasCompactSupport κ := (φ n).hasCompactSupport_normed
    have hκs : tsupport κ ⊆ closedBall 0 r := by
      rw [(φ n).tsupport_normed_eq]
      exact closedBall_subset_closedBall (hRle n)
    have hw : HarmonicOnNhd (f ⋆[lsmul ℝ ℝ, μ] κ) (ball x₀ (2 * r)) :=
      harmonicOnNhd_indicator_convolution hweak hBU hf hκ hκc hκs
    have hxB : closedBall x r ⊆ ball x₀ (2 * r) := by
      intro y hy
      rw [mem_ball] at hx ⊢
      rw [mem_closedBall] at hy
      linarith [dist_triangle y x x₀]
    rw [convolution_lsmul_comm, convolution_lsmul_comm _ h,
      ← convolution_radial_eq_of_harmonic isOpen_ball hw hr hxB hg hg0 hg1]
    exact convolution_convolution_swap hf hκ.continuous hκc hρ.continuous hρc x
  -- Step 3: pass to the limit
  refine ⟨r, hr, h, hharm.mono (ball_subset_ball (by linarith)), ?_⟩
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := μ) (K := 2)
    hRlim (Eventually.of_forall fun n ↦ by simp [hφ_def]; linarith) hf
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hae] with x hx hxb
  have hlim : Tendsto (fun n ↦ ((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] h) x) atTop (𝓝 (h x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous hRlim hhc x
  have hfx : f x = h x := tendsto_nhds_unique (hx.congr fun n ↦ hkey n x hxb) hlim
  have hxB : x ∈ B := ball_subset_closedBall (ball_subset_ball (by linarith) hxb)
  rwa [hf_def, indicator_of_mem hxB] at hfx

/-- **Weyl's lemma for `L¹_loc` functions.** A locally integrable function on an open set `U`
that is weakly harmonic there (`∫ u Δψ = 0` for every `ψ ∈ C_c^∞(U)`) agrees almost everywhere
on `U` with a function harmonic on `U`. -/
theorem exists_harmonic_ae_eq_of_weaklyHarmonic {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : LocallyIntegrableOn u U μ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, u x * Δ ψ x ∂μ = 0) :
    ∃ h : E → ℝ, HarmonicOnNhd h U ∧ ∀ᵐ x ∂(μ.restrict U), u x = h x := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- in dimension zero every function is constant, hence harmonic
    have hconst : u = fun _ ↦ u 0 := funext fun x ↦ congrArg u (Subsingleton.elim x 0)
    refine ⟨u, fun x _ ↦ ?_, Eventually.of_forall fun _ ↦ rfl⟩
    rw [hconst]
    exact harmonicAt_const _
  choose! r hr h hh hae using fun x (hx : x ∈ U) ↦ exists_local_harmonic_ae_eq hU hu hweak hx
  -- the local representatives agree on overlaps
  have hagree : ∀ x ∈ U, ∀ y ∈ U, EqOn (h x) (h y) (ball x (r x) ∩ ball y (r y)) := by
    intro x hx y hy
    have hW : IsOpen (ball x (r x) ∩ ball y (r y)) := isOpen_ball.inter isOpen_ball
    refine Measure.eqOn_open_of_ae_eq (μ := μ) ?_ hW
      ((hh x hx).contDiffOn.continuousOn.mono inter_subset_left)
      ((hh y hy).contDiffOn.continuousOn.mono inter_subset_right)
    have h1 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left (t := ball y (r y)))
      (hae x hx)
    have h2 := ae_restrict_of_ae_restrict_of_subset (inter_subset_right (s := ball x (r x)))
      (hae y hy)
    filter_upwards [h1, h2] with z hz1 hz2
    rw [← hz1, ← hz2]
  set H : E → ℝ := fun y ↦ h y y with hH_def
  have hHloc : ∀ x ∈ U, ∀ y ∈ U ∩ ball x (r x), H y = h x y := fun x hx y hy ↦
    hagree y hy.1 x hx ⟨mem_ball_self (hr y hy.1), hy.2⟩
  have hHnhds : ∀ x ∈ U, H =ᶠ[𝓝 x] h x := fun x hx ↦
    Filter.eventually_of_mem (inter_mem (hU.mem_nhds hx) (ball_mem_nhds x (hr x hx)))
      (hHloc x hx)
  refine ⟨H, fun x hx ↦ (harmonicAt_congr_nhds (hHnhds x hx)).2
    (hh x hx x (mem_ball_self (hr x hx))), ?_⟩
  -- the exceptional set is locally null
  have hnull : μ {x | x ∈ U ∧ u x ≠ H x} = 0 := by
    refine measure_null_of_locally_null _ fun x hx ↦ ⟨{x | x ∈ U ∧ u x ≠ H x} ∩ ball x (r x),
      inter_mem_nhdsWithin _ (ball_mem_nhds x (hr x hx.1)), ?_⟩
    have := hae x hx.1
    rw [ae_restrict_iff' measurableSet_ball, ae_iff] at this
    refine measure_mono_null (fun y hy ↦ ?_) this
    simp only [mem_ofPred_eq, not_imp]
    exact ⟨hy.2, by rw [← hHloc x hx.1 y ⟨hy.1.1, hy.2⟩]; exact hy.1.2⟩
  rw [ae_restrict_iff' hU.measurableSet, ae_iff]
  refine measure_mono_null (fun y hy ↦ ?_) hnull
  simp only [mem_ofPred_eq, not_imp] at hy
  exact hy

/-- **Weyl's lemma for `L¹_loc` vector fields.** A locally integrable field `V : E → F` on an open
set `U` whose components `⟪V, e⟫` are weakly harmonic agrees almost everywhere on `U` with a field
`H` harmonic on `U` (as an `F`-valued map, hence componentwise). -/
theorem exists_harmonic_ae_eq_of_weaklyHarmonic_field {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {U : Set E} (hU : IsOpen U) {V : E → F}
    (hV : LocallyIntegrableOn V U μ)
    (hweak : ∀ e : F, ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ⟪V x, e⟫ * Δ ψ x ∂μ = 0) :
    ∃ H : E → F, HarmonicOnNhd H U ∧ (∀ e : F, HarmonicOnNhd (fun y ↦ ⟪H y, e⟫) U) ∧
      ∀ᵐ x ∂(μ.restrict U), V x = H x := by
  set b := stdOrthonormalBasis ℝ F
  have hcomp : ∀ i, LocallyIntegrableOn (fun x ↦ ⟪V x, b i⟫) U μ := fun i ↦ by
    have := (innerSL ℝ (b i)).locallyIntegrableOn_comp hV
    convert this using 1
    ext x
    simp [real_inner_comm]
  choose h hh hae using fun i ↦
    exists_harmonic_ae_eq_of_weaklyHarmonic hU (hcomp i) (hweak (b i))
  set H : E → F := fun y ↦ ∑ i, h i y • b i with hH_def
  have hH : HarmonicOnNhd H U := harmonicOnNhd_sum_smul hh b
  refine ⟨H, hH, harmonicOnNhd_inner_left hH, ?_⟩
  filter_upwards [ae_all_iff.2 hae] with x hx
  rw [← b.sum_repr' (V x)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, hx i]

end BasicElliptic
