/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Harmonic.Basic
public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# The classical weak maximum principle

Let `E` be a finite-dimensional real inner product space and `Ω ⊆ E` a bounded open set.

* `BasicElliptic.exists_isMaxOn_add_sq_of_frontier_nonpos`: the compactness step. If `f` is
  continuous on `closure Ω`, `f ≤ 0` on `frontier Ω` and `f > 0` somewhere, then
  `f + ε ‖· - c‖²` attains its maximum over `closure Ω` at a point of `Ω`, for some `c` and some
  `ε > 0`.
* `BasicElliptic.laplacian_norm_sub_sq`: `Δ ‖· - c‖² = 2 dim E`.
* `BasicElliptic.laplacian_nonneg_of_isLocalMin_of_contDiffAt`: at an interior local minimum of
  a `C²` function the Laplacian is nonnegative (second-derivative test).
* `BasicElliptic.le_of_frontier_le_of_contDiffOn_two`: if `u, v ∈ C²(Ω) ∩ C(closure Ω)`,
  `Δ v ≤ Δ u` in `Ω` and `u ≤ v` on `frontier Ω`, then `u ≤ v` on `closure Ω`. Special cases:
  `BasicElliptic.le_of_harmonic_boundary` (comparison of harmonic functions) and
  `BasicElliptic.eqOn_of_harmonic_of_eqOn_frontier` (uniqueness for the Dirichlet problem).

The comparison statements assume `Nontrivial E`.

## Proof

At an interior maximum `x₀` of `u - v + ε ‖· - c‖²`, the function `v - u - ε ‖· - c‖²` has a
local minimum, so its Laplacian is nonnegative: `Δ v - Δ u ≥ 2 d ε > 0` at `x₀`, a
contradiction. No test functions are needed, so `C²` suffices.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001.

## Provenance

Ported from elliptic-bernoulli-foundations (W. M. Feldman),
`EllipticBernoulli/Harmonic/MaxPrinciple.lean`, commit
ea02c735ae1af1b0eab48928ff959c41ed49e9a8. Changes: namespace `BasicElliptic`; the annulus
section (`closure_annulus_subset`, `frontier_annulus_subset`,
`le_of_sphere_le_of_contDiffOn_two_annulus`) is not ported.
-/

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian

public section

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The compactness step -/

/-- **Interior maximum of a quadratic perturbation.** If `Ω` is bounded and open, `f` is
continuous on `closure Ω`, `f ≤ 0` on `frontier Ω`, and `f x₁ > 0` for some `x₁ ∈ closure Ω`,
then there are `c`, `ε > 0` and `x₀ ∈ Ω` such that `f + ε ‖· - c‖²` attains its maximum over
`closure Ω` at `x₀`. -/
theorem exists_isMaxOn_add_sq_of_frontier_nonpos {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {f : E → ℝ} (hf : ContinuousOn f (closure Ω))
    (hfr : ∀ x ∈ frontier Ω, f x ≤ 0) {x₁ : E} (hx₁ : x₁ ∈ closure Ω) (hpos : 0 < f x₁) :
    ∃ c : E, ∃ ε > 0, ∃ x₀ ∈ Ω, ∀ y ∈ closure Ω,
      f y + ε * ‖y - c‖ ^ 2 ≤ f x₀ + ε * ‖x₀ - c‖ ^ 2 := by
  obtain ⟨R, hR⟩ := hΩb.subset_closedBall x₁
  have hcl : closure Ω ⊆ closedBall x₁ R := closure_minimal hR isClosed_closedBall
  set ε : ℝ := f x₁ / (2 * (R ^ 2 + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hεR : ε * R ^ 2 < f x₁ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set g : E → ℝ := fun y ↦ f y + ε * ‖y - x₁‖ ^ 2 with hg
  have hgc : ContinuousOn g (closure Ω) := hf.add (by fun_prop)
  obtain ⟨x₀, hx₀, hmax⟩ := (hΩb.isCompact_closure).exists_isMaxOn ⟨x₁, hx₁⟩ hgc
  refine ⟨x₁, ε, hε0, x₀, ?_, fun y hy ↦ hmax hy⟩
  by_contra hx₀Ω
  have hfr₀ : x₀ ∈ frontier Ω := ⟨hx₀, by rwa [hΩ.interior_eq]⟩
  have h1 : g x₁ ≤ g x₀ := hmax hx₁
  have h2 : ‖x₀ - x₁‖ ≤ R := by
    have := hcl hx₀
    rwa [mem_closedBall, dist_eq_norm] at this
  have h3 : ‖x₀ - x₁‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  simp only [hg, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero] at h1
  nlinarith [hfr x₀ hfr₀]

/-! ### Two Laplacians -/

/-- `Δ ‖· - c‖² = 2 dim E`. -/
theorem laplacian_norm_sub_sq (c x : E) :
    Δ (fun y ↦ ‖y - c‖ ^ 2) x = 2 * finrank ℝ E := by
  have h1 := congrFun (ViscositySolns.Analysis.laplacian_comp_add_right
    (fun w : E ↦ ‖w‖ ^ 2) (-c)) x
  have h3 := ContDiff.laplacian_comp_norm_sq (E := E) contDiff_id (x - c)
  have hid : deriv (id : ℝ → ℝ) = fun _ ↦ 1 := funext fun _ ↦ deriv_id _
  simp only [id_eq, hid, deriv_const, mul_zero, zero_add, mul_one] at h3
  simp only [← sub_eq_add_neg] at h1
  rw [h1, h3]

omit [FiniteDimensional ℝ E] in
/-- `‖· - c‖²` is smooth. -/
theorem contDiff_norm_sub_sq (c : E) : ContDiff ℝ ∞ (fun y : E ↦ ‖y - c‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)

/-! ### The second-derivative test -/

omit [FiniteDimensional ℝ E] in
/-- At a local minimum of a function which is `C²` there, the second derivative is nonnegative
on the diagonal. -/
private theorem fderiv_fderiv_nonneg_of_isLocalMin' {f : E → ℝ} {x : E} (hmin : IsLocalMin f x)
    (hf : ContDiffAt ℝ 2 f x) (v : E) : 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  set L : ℝ → E := fun t ↦ x + t • v with hLdef
  have hL0 : L 0 = x := by simp [hLdef]
  have hLc : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  have hLt : Tendsto L (𝓝 0) (𝓝 x) := by simpa [hL0] using hLc.tendsto 0
  have hLd : ∀ t : ℝ, HasDerivAt L v t := fun t ↦ by
    have h := ((hasDerivAt_id t).smul_const v).const_add x
    rwa [one_smul] at h
  have hψmin : IsLocalMin (f ∘ L) 0 := by
    have h2 : IsMinFilter f (𝓝 x) (L 0) := by rwa [hL0]
    exact h2.comp_of_tendsto hLt
  have hf'1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hB : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (L 0) := by
    rw [hL0]; exact (hf'1.differentiableAt one_ne_zero).hasFDerivAt
  have hwq : HasDerivAt (fun t ↦ fderiv ℝ f (L t) v) (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have h1 := hB.comp_hasDerivAt 0 (hLd 0)
    simpa using h1.clm_apply (hasDerivAt_const 0 v)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (f ∘ L) (fderiv ℝ f (L t) v) t := by
    have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
      filter_upwards [hf.eventually (by simp)] with y hy
      exact hy.differentiableAt two_ne_zero
    filter_upwards [hLt.eventually hdiff] with t ht
    exact ht.hasFDerivAt.comp_hasDerivAt t (hLd t)
  -- the one-dimensional second-derivative test
  have hderiv : deriv (f ∘ L) =ᶠ[𝓝 0] fun t ↦ fderiv ℝ f (L t) v := by
    filter_upwards [hev] with t ht
    exact ht.deriv
  have hdd : deriv (deriv (f ∘ L)) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [hderiv.deriv_eq]; exact hwq.deriv
  rw [← hdd]
  by_contra hneg
  have hmax : IsLocalMax (f ∘ L) 0 :=
    isLocalMax_of_deriv_deriv_neg (not_le.1 hneg) hψmin.deriv_eq_zero
      (hev.self_of_nhds.continuousAt)
  have hconst : (f ∘ L) =ᶠ[𝓝 0] fun _ ↦ (f ∘ L) 0 := by
    filter_upwards [hmax, hψmin] with t h1 h2
    exact le_antisymm h1 h2
  have h0 : deriv (f ∘ L) =ᶠ[𝓝 0] fun _ ↦ 0 := by
    filter_upwards [hconst.eventuallyEq_nhds] with t ht
    rw [ht.deriv_eq, deriv_const]
  have : deriv (deriv (f ∘ L)) 0 = 0 := by rw [h0.deriv_eq, deriv_const]
  exact hneg (le_of_eq this.symm)

/-- **Second-derivative test.** At a local minimum of a function which is `C²` at that point,
the Laplacian is nonnegative. -/
theorem laplacian_nonneg_of_isLocalMin_of_contDiffAt {f : E → ℝ} {x : E}
    (hmin : IsLocalMin f x) (hf : ContDiffAt ℝ 2 f x) : 0 ≤ Δ f x := by
  set b := stdOrthonormalBasis ℝ E
  have hf'1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply]
  exact fderiv_fderiv_nonneg_of_isLocalMin' hmin hf (b i)

/-! ### The weak maximum principle -/

variable [Nontrivial E]

/-- **Weak maximum principle for `C²` functions** (Gilbarg–Trudinger, in
the `C²` setting). On a bounded open set `Ω`, if `u, v ∈ C²(Ω) ∩ C(closure Ω)`, `Δ v ≤ Δ u` in
`Ω`, and `u ≤ v` on `frontier Ω`, then `u ≤ v` on `closure Ω`. -/
theorem le_of_frontier_le_of_contDiffOn_two {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hv : ContDiffOn ℝ 2 v Ω) (hΔ : ∀ x ∈ Ω, Δ v x ≤ Δ u x)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hfr : ∀ x ∈ frontier Ω, u x ≤ v x) : ∀ x ∈ closure Ω, u x ≤ v x := by
  intro x₁ hx₁
  by_contra hlt
  obtain ⟨c, ε, hε, x₀, hx₀, hmax⟩ := exists_isMaxOn_add_sq_of_frontier_nonpos hΩ hΩb
    (f := u - v) (huc.sub hvc) (fun x hx ↦ by simpa using hfr x hx) hx₁
    (by simpa using not_le.1 hlt)
  -- `F = v - u - ε ‖· - c‖²` has a local minimum at `x₀`
  set F : E → ℝ := fun y ↦ v y - u y - ε * ‖y - c‖ ^ 2 with hF
  have hmin : IsLocalMin F x₀ := by
    filter_upwards [hΩ.mem_nhds hx₀] with y hy
    have := hmax y (subset_closure hy)
    simp only [Pi.sub_apply] at this
    simp only [hF]
    linarith
  have hu₀ : ContDiffAt ℝ 2 u x₀ := hu.contDiffAt (hΩ.mem_nhds hx₀)
  have hv₀ : ContDiffAt ℝ 2 v x₀ := hv.contDiffAt (hΩ.mem_nhds hx₀)
  have hq₀ : ContDiffAt ℝ 2 (fun y ↦ ε * ‖y - c‖ ^ 2) x₀ :=
    (contDiffAt_const.mul ((contDiff_norm_sub_sq c).contDiffAt)).of_le (by norm_cast)
  have hF₀ : ContDiffAt ℝ 2 F x₀ := (hv₀.sub hu₀).sub hq₀
  have hΔF := laplacian_nonneg_of_isLocalMin_of_contDiffAt hmin hF₀
  have hsplit : Δ F x₀ = Δ v x₀ - Δ u x₀ - ε * (2 * finrank ℝ E) := by
    have e1 : F = (v - u) - fun y ↦ ε * ‖y - c‖ ^ 2 := rfl
    have hvu : ContDiffAt ℝ 2 (v - u) x₀ := hv₀.sub hu₀
    rw [e1, hvu.laplacian_sub hq₀, hv₀.laplacian_sub hu₀]
    have e2 : (fun y ↦ ε * ‖y - c‖ ^ 2) = ε • fun y : E ↦ ‖y - c‖ ^ 2 := rfl
    rw [e2, laplacian_smul ε ((contDiff_norm_sub_sq c).contDiffAt.of_le (by norm_cast)),
      laplacian_norm_sub_sq, smul_eq_mul]
  have hdim : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
  have := hΔ x₀ hx₀
  nlinarith

/-- **Comparison of harmonic functions** (weak maximum principle). On a bounded open set, if
`h, k` are harmonic in `Ω`, continuous on `closure Ω`, and `h ≤ k` on `frontier Ω`, then `h ≤ k`
on `closure Ω`. -/
theorem le_of_harmonic_boundary {Ω : Set E} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {h k : E → ℝ} (hh : HarmonicOnNhd h Ω) (hk : HarmonicOnNhd k Ω)
    (hhc : ContinuousOn h (closure Ω)) (hkc : ContinuousOn k (closure Ω))
    (hfr : ∀ x ∈ frontier Ω, h x ≤ k x) : ∀ x ∈ closure Ω, h x ≤ k x :=
  le_of_frontier_le_of_contDiffOn_two hΩ hΩb hh.contDiffOn hk.contDiffOn
    (fun x hx ↦ by rw [(hh x hx).2.eq_of_nhds, (hk x hx).2.eq_of_nhds]) hhc hkc hfr

/-- **Uniqueness for the Dirichlet problem.** Two functions harmonic in a bounded open set,
continuous on its closure and equal on its frontier, are equal on its closure. -/
theorem eqOn_of_harmonic_of_eqOn_frontier {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {h k : E → ℝ} (hh : HarmonicOnNhd h Ω)
    (hk : HarmonicOnNhd k Ω) (hhc : ContinuousOn h (closure Ω))
    (hkc : ContinuousOn k (closure Ω)) (hfr : EqOn h k (frontier Ω)) : EqOn h k (closure Ω) :=
  fun x hx ↦ le_antisymm
    (le_of_harmonic_boundary hΩ hΩb hh hk hhc hkc (fun _ hy ↦ (hfr hy).le) x hx)
    (le_of_harmonic_boundary hΩ hΩb hk hh hkc hhc (fun _ hy ↦ (hfr hy).ge) x hx)

end BasicElliptic
