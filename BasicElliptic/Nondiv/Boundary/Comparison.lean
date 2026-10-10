/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Harmonic.DirichletBall
public import BasicElliptic.Harmonic.MaxPrinciple
public import BasicElliptic.Nondiv.Interior.PolyOps

/-!
# Comparison principles on the half ball (Neumann and Dirichlet barriers)

Let `E` be a finite-dimensional real inner product space, `ν` a unit vector, `x ∈ flatPart ν` and
`B⁺ = ball x r ∩ openHalfSpace ν`. Normal derivatives at flat points are one-sided: the derivative
at `t = 0` of
`t ↦ F (y + t • ν)` within `Ici 0`.

* `Nondiv.nonpos_of_halfBall_of_laplacian_nonneg` (**half-ball maximum principle**,
  Hopf-free): if `F` is continuous on `halfBall ν x r`, `C²` and subharmonic in `B⁺`,
  `F ≤ 0` on the spherical part, and at each flat point of `ball x r` either `F ≤ 0` or the
  inward normal derivative is `≥ 0`, then `F ≤ 0`.
* `Nondiv.abs_le_of_halfBall_neumann`: on the unit half ball, `|Δv| ≤ δ₁` in `B₁⁺`, `v = 0` on
  the spherical part and `|∂_ν v| ≤ δ₂` on the flat part give `|v| ≤ δ₁ + δ₂`. The barrier is
  `ψ = (B + δ₂) − B ‖z‖² − δ₂ ⟪z, ν⟫` with `B = δ₁ / (2d)`: `Δψ = −δ₁` and `∂_ν ψ = −δ₂` on the
  flat part.
* `Nondiv.abs_le_of_halfBall_dirichlet`: the same with `v = 0` on the whole boundary gives
  `|v| ≤ δ₁` (barrier `B (1 − ‖z‖²)`).

## Proof of the maximum principle

For `δ > 0` the function
`G = F + δ ‖· − (x − ν)‖²` is strictly subharmonic in `B⁺`, so it has no interior maximum; at a
flat point its inward derivative is `∂_ν F + 2δ > 0`, so it has no maximum there either (the
one-sided first-derivative test `IsLocalMaxOn.hasFDerivWithinAt_nonpos` along `ν`). Hence
`max G` is attained on the spherical part, where `G ≤ δ (r + 1)²`; let `δ → 0`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001.
-/

public section

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian RealInnerProductSpace

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- One-sided first-derivative test: if `g` has a maximum on `[0, s)` at `0` and a
right-derivative `e` at `0`, then `e ≤ 0`. -/
theorem le_zero_of_hasDerivWithinAt_Ici_of_isMax {g : ℝ → ℝ} {e s : ℝ} (hs : 0 < s)
    (hg : HasDerivWithinAt g e (Ici 0) 0) (hmax : ∀ t ∈ Ico 0 s, g t ≤ g 0) : e ≤ 0 := by
  have hloc : IsLocalMaxOn g (Ici 0) 0 := by
    filter_upwards [inter_mem_nhdsWithin (Ici 0) (Iio_mem_nhds hs), self_mem_nhdsWithin]
      with t ht _
    exact hmax t ⟨ht.1, ht.2⟩
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 :=
    mem_posTangentConeAt_of_segment_subset (by
      rw [zero_add, segment_eq_Icc zero_le_one]; exact Icc_subset_Ici_self)
  have := hloc.hasFDerivWithinAt_nonpos hg.hasFDerivWithinAt hcone
  simpa using this

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem nontrivial_of_norm_eq_one' {ν : E} (hν : ‖ν‖ = 1) : Nontrivial E :=
  ⟨⟨ν, 0, fun h ↦ by simp [h] at hν⟩⟩

/-- **Weak maximum principle on a half ball, mixed boundary condition** (Hopf-free). Let the
centre `x` lie on `flatPart ν`. Let `F` be continuous on `halfBall ν x r`, `C²` with `ΔF ≥ 0` in
`ball x r ∩ openHalfSpace ν`, `F ≤ 0` on `sphere x r ∩ halfSpace ν`, and at each point
`y ∈ ball x r ∩ flatPart ν` either `F y ≤ 0` or `t ↦ F (y + t • ν)` has a right-derivative
`d ≥ 0` at `0`. Then `F ≤ 0` on `halfBall ν x r`. -/
theorem nonpos_of_halfBall_of_laplacian_nonneg {ν x : E} (hν : ‖ν‖ = 1) (hx : x ∈ flatPart ν)
    {r : ℝ} {F : E → ℝ} (hFc : ContinuousOn F (halfBall ν x r))
    (hF2 : ContDiffOn ℝ 2 F (ball x r ∩ openHalfSpace ν))
    (hΔ : ∀ y ∈ ball x r ∩ openHalfSpace ν, 0 ≤ Δ F y)
    (hs : ∀ y ∈ sphere x r, y ∈ halfSpace ν → F y ≤ 0)
    (hf : ∀ y ∈ ball x r, y ∈ flatPart ν →
      F y ≤ 0 ∨ ∃ d : ℝ, HasDerivWithinAt (fun t : ℝ ↦ F (y + t • ν)) d (Ici 0) 0 ∧ 0 ≤ d) :
    ∀ y ∈ halfBall ν x r, F y ≤ 0 := by
  have := nontrivial_of_norm_eq_one' hν
  have hx0 : ⟪x, ν⟫ = 0 := hx
  have hνν : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  have hU : IsOpen (ball x r ∩ openHalfSpace ν) := isOpen_ball.inter (isOpen_openHalfSpace ν)
  intro y hy
  have hr : 0 ≤ r := dist_nonneg.trans hy.1
  suffices key : ∀ δ > 0, F y ≤ δ * (r + 1) ^ 2 by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have := key (ε / (r + 1) ^ 2) (by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    linarith
  intro δ hδ
  set c : E := x - ν
  set q : E → ℝ := fun z ↦ ‖z - c‖ ^ 2 with hq_def
  set G : E → ℝ := F + fun z ↦ δ * q z with hG_def
  have hqc : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hcpt : IsCompact (halfBall ν x r) := (isCompact_closedBall x r).inter_right
    (isClosed_halfSpace ν)
  have hxmem : x ∈ halfBall ν x r := ⟨mem_closedBall_self hr, hx0.ge⟩
  have hqcont : Continuous fun z ↦ δ * q z :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)
  obtain ⟨p, hp, hmax⟩ := hcpt.exists_isMaxOn (f := G) ⟨x, hxmem⟩
    (hFc.add hqcont.continuousOn)
  have hqb : ∀ z ∈ halfBall ν x r, q z ≤ (r + 1) ^ 2 := fun z hz ↦ by
    have : ‖z - c‖ ≤ r + 1 := by
      calc ‖z - c‖ = ‖(z - x) + ν‖ := by simp only [c]; congr 1; abel
        _ ≤ ‖z - x‖ + ‖ν‖ := norm_add_le _ _
        _ ≤ r + 1 := by rw [hν, ← dist_eq_norm]; linarith [mem_closedBall.1 hz.1]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hGp : G p ≤ δ * (r + 1) ^ 2 := by
    rcases eq_or_lt_of_le (mem_closedBall.1 hp.1) with hps | hpb
    · have h1 := hs p hps hp.2
      have h2 := hqb p hp
      simp only [hG_def, Pi.add_apply]
      nlinarith
    rcases eq_or_lt_of_le (mem_halfSpace.1 hp.2) with hpf | hpo
    · -- `p` on the flat part
      rcases hf p hpb hpf.symm with hF0 | ⟨d, hd, hd0⟩
      · have h2 := hqb p hp
        simp only [hG_def, Pi.add_apply]
        nlinarith
      exfalso
      set s : ℝ := r - dist p x
      have hs0 : 0 < s := by simp only [s]; linarith
      have hseg : ∀ t ∈ Ico (0 : ℝ) s, p + t • ν ∈ halfBall ν x r := by
        intro t ht
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall]
          calc dist (p + t • ν) x ≤ dist (p + t • ν) p + dist p x := dist_triangle _ _ _
            _ = t + dist p x := by
                rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hν, mul_one, Real.norm_eq_abs,
                  abs_of_nonneg ht.1]
            _ ≤ r := by simp only [s] at ht; linarith [ht.2]
        · rw [mem_halfSpace, inner_add_left, real_inner_smul_left, hνν, ← hpf]
          linarith [ht.1]
      -- the derivative of the penalization along `ν`
      have hqd : HasFDerivAt q (2 • (innerSL ℝ (p - c)).comp (ContinuousLinearMap.id ℝ E)) p :=
        ((hasFDerivAt_id p).sub_const c).norm_sq
      have hline : HasDerivAt (fun t : ℝ ↦ p + t • ν) ν 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add p
      have hqline : HasDerivAt (fun t : ℝ ↦ δ * q (p + t • ν))
          (δ * (2 * ⟪p - c, ν⟫)) 0 := by
        have hqd' : HasFDerivAt q (2 • (innerSL ℝ (p - c)).comp (ContinuousLinearMap.id ℝ E))
            (p + (0 : ℝ) • ν) := by rw [zero_smul, add_zero]; exact hqd
        have h1 := hqd'.comp_hasDerivAt (0 : ℝ) hline
        have h2 := h1.const_mul δ
        refine h2.congr_deriv ?_
        congr 1
        rw [ContinuousLinearMap.comp_id]
        simp [two_smul, two_mul, inner_sub_left]
      have hval : ⟪p - c, ν⟫ = 1 := by
        simp only [c, inner_sub_left, hx0, hνν, ← hpf]; ring
      rw [hval] at hqline
      have hGd : HasDerivWithinAt (fun t : ℝ ↦ G (p + t • ν)) (d + δ * (2 * 1)) (Ici 0) 0 :=
        hd.add hqline.hasDerivWithinAt
      have hle := le_zero_of_hasDerivWithinAt_Ici_of_isMax hs0 hGd fun t ht ↦ by
        have := hmax (hseg t ht)
        simpa using this
      linarith
    · -- `p` in the open half ball: `G` would have an interior maximum
      exfalso
      have hpU : p ∈ ball x r ∩ openHalfSpace ν := ⟨hpb, hpo⟩
      have hmin : IsLocalMin (-G) p := by
        filter_upwards [hU.mem_nhds hpU] with z hz
        have := hmax ⟨ball_subset_closedBall hz.1, mem_halfSpace.2 (le_of_lt hz.2)⟩
        simp only [Pi.neg_apply, neg_le_neg_iff]
        exact this
      have hFp : ContDiffAt ℝ 2 F p := hF2.contDiffAt (hU.mem_nhds hpU)
      have hq2 : ContDiffAt ℝ 2 (fun z ↦ δ * q z) p :=
        (contDiffAt_const.mul hqc.contDiffAt).of_le (by norm_cast)
      have hG2 : ContDiffAt ℝ 2 G p := hFp.add hq2
      have hΔG := laplacian_nonneg_of_isLocalMin_of_contDiffAt hmin hG2.neg
      have hΔq : Δ (fun z ↦ δ * q z) p = δ * (2 * finrank ℝ E) := by
        have e2 : (fun z ↦ δ * q z) = δ • q := rfl
        rw [e2, laplacian_smul δ (hqc.contDiffAt.of_le (by norm_cast)), laplacian_norm_sub_sq,
          smul_eq_mul]
      rw [laplacian_neg, Pi.neg_apply, hG_def, hFp.laplacian_add hq2, hΔq] at hΔG
      have hdim : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
      have := hΔ p hpU
      nlinarith
  have hqy : 0 ≤ q y := by positivity
  have h1 : F y + δ * q y ≤ F p + δ * q p := hmax hy
  have h2 : F p + δ * q p ≤ δ * (r + 1) ^ 2 := hGp
  nlinarith

/-! ### Barriers -/

/-- The Neumann barrier `ψ(z) = (δ₁/(2d) + δ₂) − δ₁/(2d) ‖z‖² − δ₂ ⟪ν, z⟫` as a quadratic
polynomial: `Δψ = −δ₁` and `∂_ν ψ = −δ₂` on the flat part. -/
private noncomputable def barrier (ν : E) (δ₁ δ₂ : ℝ) : QuadPoly E :=
  ⟨δ₁ / (2 * finrank ℝ E) + δ₂, -(δ₂ • innerSL ℝ ν), 0⟩ + QuadPoly.isotropic (-δ₁)

omit [FiniteDimensional ℝ E] in
private theorem barrier_eval (ν : E) (δ₁ δ₂ : ℝ) (z : E) :
    (barrier ν δ₁ δ₂).eval z =
      δ₁ / (2 * finrank ℝ E) + δ₂ - δ₂ * ⟪ν, z⟫ - δ₁ / (2 * finrank ℝ E) * ‖z‖ ^ 2 := by
  have hi : (innerSL ℝ z) z = ‖z‖ ^ 2 := by rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  simp [barrier, QuadPoly.eval, QuadPoly.isotropic, hi]
  ring

omit [FiniteDimensional ℝ E] in
private theorem barrier_deriv {ν : E} (hν : ‖ν‖ = 1) (δ₁ δ₂ : ℝ) {z : E}
    (hz : z ∈ flatPart ν) :
    HasDerivAt (fun t : ℝ ↦ (barrier ν δ₁ δ₂).eval (z + t • ν)) (-δ₂) 0 := by
  have hline : HasDerivAt (fun t : ℝ ↦ z + t • ν) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add z
  have hP := (barrier ν δ₁ δ₂).hasFDerivAt_eval z
  have hP' : HasFDerivAt (barrier ν δ₁ δ₂).eval
      ((barrier ν δ₁ δ₂).lin + (barrier ν δ₁ δ₂).hess z) (z + (0 : ℝ) • ν) := by
    rw [zero_smul, add_zero]; exact hP
  refine (hP'.comp_hasDerivAt (0 : ℝ) hline).congr_deriv ?_
  have hz0 : ⟪z, ν⟫ = 0 := hz
  have hνν : ⟪ν, ν⟫ = 1 := real_inner_self_of_norm_eq_one hν
  have h1 : (innerSL ℝ z) ν = 0 := by rw [innerSL_apply_apply]; exact hz0
  have h2 : (innerSL ℝ ν) z = 0 := by rw [innerSL_apply_apply, real_inner_comm]; exact hz0
  rw [add_apply, QuadPoly.hess_apply]
  simp [barrier, QuadPoly.isotropic, h1, h2, hν]

/-- One-sided barrier comparison on the unit half ball (common to the Neumann and Dirichlet
cases): if `Δv ≥ −δ₁` in `B₁⁺`, `v ≤ 0` on the spherical part, and at each flat point either
`v ≤ 0` or `∂_ν v ≥ −δ₂`, then `v ≤ δ₁ + δ₂`. -/
theorem le_of_halfBall_barrier {ν : E} (hν : ‖ν‖ = 1) {v : E → ℝ} {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hvc : ContinuousOn v (halfBall ν 0 1))
    (hv2 : ContDiffOn ℝ 2 v (ball 0 1 ∩ openHalfSpace ν))
    (hΔ : ∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, -δ₁ ≤ Δ v z)
    (hs : ∀ z ∈ sphere (0 : E) 1, z ∈ halfSpace ν → v z ≤ 0)
    (hf : ∀ z ∈ ball (0 : E) 1, z ∈ flatPart ν → v z ≤ 0 ∨ ∃ d : ℝ,
      HasDerivWithinAt (fun t : ℝ ↦ v (z + t • ν)) d (Ici 0) 0 ∧ -δ₂ ≤ d) :
    ∀ z ∈ halfBall ν 0 1, v z ≤ δ₁ + δ₂ := by
  have := nontrivial_of_norm_eq_one' hν
  have hd : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
  have hd1 : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast finrank_pos
  set ψ := barrier ν δ₁ δ₂ with hψ
  set B : ℝ := δ₁ / (2 * finrank ℝ E) with hB
  have hB0 : 0 ≤ B := by positivity
  have hBδ : B ≤ δ₁ := by
    rw [hB, div_le_iff₀ (by positivity)]; nlinarith
  have hinν : ∀ z : E, ‖z‖ ≤ 1 → ⟪ν, z⟫ ≤ 1 := fun z hz ↦ by
    have := real_inner_le_norm ν z
    rw [hν, one_mul] at this; linarith
  have hψ0 : ∀ z : E, ‖z‖ ≤ 1 → 0 ≤ ψ.eval z := fun z hz ↦ by
    rw [hψ, barrier_eval, ← hB]
    have h1 := hinν z hz
    have h2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    nlinarith
  have hψle : ∀ z ∈ halfBall ν (0 : E) 1, ψ.eval z ≤ δ₁ + δ₂ := fun z hz ↦ by
    rw [hψ, barrier_eval, ← hB]
    have h1 : 0 ≤ ⟪ν, z⟫ := by rw [real_inner_comm]; exact hz.2
    have h2 : 0 ≤ B * ‖z‖ ^ 2 := by positivity
    nlinarith
  have hΔψ : ∀ z, Δ ψ.eval z = -δ₁ := fun z ↦ by
    rw [QuadPoly.laplacian_eval, hψ, barrier, QuadPoly.trace_add, QuadPoly.trace_isotropic]
    simp [QuadPoly.trace]
  have hx0 : (0 : E) ∈ flatPart ν := by simp
  have key := nonpos_of_halfBall_of_laplacian_nonneg hν hx0 (F := v - ψ.eval)
    (hvc.sub ψ.continuous_eval.continuousOn) (hv2.sub ψ.contDiff_eval.contDiffOn)
    (fun z hz ↦ by
      have hv := hv2.contDiffAt
        ((isOpen_ball.inter (isOpen_openHalfSpace ν)).mem_nhds hz)
      rw [hv.laplacian_sub ψ.contDiff_eval.contDiffAt, hΔψ]
      linarith [hΔ z hz])
    (fun z hz hzh ↦ by
      have := hψ0 z (by rw [mem_sphere_zero_iff_norm.1 hz])
      simp only [Pi.sub_apply]; linarith [hs z hz hzh])
    (fun z hz hzf ↦ by
      rcases hf z hz hzf with h0 | ⟨d, hd, hdδ⟩
      · left
        have := hψ0 z (mem_ball_zero_iff.1 hz).le
        simp only [Pi.sub_apply]; linarith
      · right
        refine ⟨d + δ₂, ?_, by linarith⟩
        have := hd.sub (barrier_deriv hν δ₁ δ₂ hzf).hasDerivWithinAt
        rw [sub_neg_eq_add] at this
        exact this)
  intro z hz
  have h1 := key z hz
  have h2 := hψle z hz
  simp only [Pi.sub_apply] at h1
  linarith

/-- **Neumann comparison on the unit half ball.** If `v` is continuous on `halfBall ν 0 1`,
`C²` in `B₁⁺ = ball 0 1 ∩ openHalfSpace ν` with `|Δv| ≤ δ₁` there, `v = 0` on the spherical
part, and at each flat point of `ball 0 1` the inward normal derivative (right-derivative of
`t ↦ v (z + t • ν)` at `0`) has absolute value `≤ δ₂`, then `|v| ≤ δ₁ + δ₂`. -/
theorem abs_le_of_halfBall_neumann {ν : E} (hν : ‖ν‖ = 1) {v : E → ℝ} {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hvc : ContinuousOn v (halfBall ν 0 1))
    (hv2 : ContDiffOn ℝ 2 v (ball 0 1 ∩ openHalfSpace ν))
    (hΔ : ∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ v z| ≤ δ₁)
    (hs : ∀ z ∈ sphere (0 : E) 1, z ∈ halfSpace ν → v z = 0)
    (hN : ∀ z ∈ ball (0 : E) 1, z ∈ flatPart ν → ∃ d : ℝ,
      HasDerivWithinAt (fun t : ℝ ↦ v (z + t • ν)) d (Ici 0) 0 ∧ |d| ≤ δ₂) :
    ∀ z ∈ halfBall ν 0 1, |v z| ≤ δ₁ + δ₂ := by
  have hU : IsOpen (ball (0 : E) 1 ∩ openHalfSpace ν) :=
    isOpen_ball.inter (isOpen_openHalfSpace ν)
  have h1 := le_of_halfBall_barrier hν hδ₁ hδ₂ hvc hv2
    (fun z hz ↦ neg_le_of_abs_le (hΔ z hz)) (fun z hz hzh ↦ (hs z hz hzh).le)
    (fun z hz hzf ↦ by
      obtain ⟨d, hd, hdδ⟩ := hN z hz hzf
      exact Or.inr ⟨d, hd, neg_le_of_abs_le hdδ⟩)
  have h2 := le_of_halfBall_barrier hν hδ₁ hδ₂ (v := -v) hvc.neg hv2.neg
    (fun z hz ↦ by
      rw [laplacian_neg, Pi.neg_apply]
      have := hΔ z hz
      have := le_abs_self (Δ v z)
      linarith)
    (fun z hz hzh ↦ by simp [hs z hz hzh])
    (fun z hz hzf ↦ by
      obtain ⟨d, hd, hdδ⟩ := hN z hz hzf
      exact Or.inr ⟨-d, hd.neg, by have := le_abs_self d; linarith⟩)
  intro z hz
  have a := h1 z hz
  have b := h2 z hz
  simp only [Pi.neg_apply] at b
  rw [abs_le]; constructor <;> linarith

/-- **Dirichlet comparison on the unit half ball.** If `v` is continuous on `halfBall ν 0 1`,
`C²` in `B₁⁺` with `|Δv| ≤ δ` there, and `v = 0` on the spherical and on the flat part, then
`|v| ≤ δ`. -/
theorem abs_le_of_halfBall_dirichlet {ν : E} (hν : ‖ν‖ = 1) {v : E → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hvc : ContinuousOn v (halfBall ν 0 1))
    (hv2 : ContDiffOn ℝ 2 v (ball 0 1 ∩ openHalfSpace ν))
    (hΔ : ∀ z ∈ ball (0 : E) 1 ∩ openHalfSpace ν, |Δ v z| ≤ δ)
    (hs : ∀ z ∈ sphere (0 : E) 1, z ∈ halfSpace ν → v z = 0)
    (hD : ∀ z ∈ ball (0 : E) 1, z ∈ flatPart ν → v z = 0) :
    ∀ z ∈ halfBall ν 0 1, |v z| ≤ δ := by
  have h1 := le_of_halfBall_barrier hν hδ le_rfl hvc hv2
    (fun z hz ↦ neg_le_of_abs_le (hΔ z hz)) (fun z hz hzh ↦ (hs z hz hzh).le)
    (fun z hz hzf ↦ Or.inl (hD z hz hzf).le)
  have h2 := le_of_halfBall_barrier hν hδ le_rfl (v := -v) hvc.neg hv2.neg
    (fun z hz ↦ by
      rw [laplacian_neg, Pi.neg_apply]
      have := hΔ z hz
      have := le_abs_self (Δ v z)
      linarith)
    (fun z hz hzh ↦ by simp [hs z hz hzh])
    (fun z hz hzf ↦ Or.inl (by simp [hD z hz hzf]))
  intro z hz
  have a := h1 z hz
  have b := h2 z hz
  simp only [Pi.neg_apply, add_zero] at a b
  rw [abs_le]; constructor <;> linarith

end Nondiv

end BasicElliptic
