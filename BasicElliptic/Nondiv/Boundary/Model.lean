/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Harmonic.DirichletBall
public import BasicElliptic.Nondiv.Interior.PolyOps

/-!
# Model problems on the unit half ball: Neumann (even) and Dirichlet (odd)

`ν` is a unit vector, `R = reflect ν` the reflection across `flatPart ν`, and `B₁⁺ = halfBall ν 0
1`.

* `Nondiv.exists_harmonic_even_halfBall` (**Neumann model**): for `u` continuous on `B₁⁺` there
  is `h` harmonic in `ball 0 1`, continuous on `closedBall 0 1`, **even** (`h ∘ R = h`) and equal
  to `u` on the spherical part. Data: the even extension `u ∘ fold ν` on the whole sphere;
  evenness by uniqueness (`apply_reflect_eq_of_harmonic_ball`). By
  `Nondiv.hasDerivAt_line_eq_zero_of_reflect` its normal derivative vanishes on the flat part.
* `Nondiv.exists_harmonic_odd_halfBall` (**Dirichlet model**): if moreover `u = 0` on the flat
  part, there is such an `h` which is **odd** (`h ∘ R = -h`); in particular `h = 0` on the flat
  part.
* Polynomial symmetrization: `QuadPoly.evenPart ν P = ½ (P + P ∘ R)` and
  `QuadPoly.oddPart ν P = ½ (P − P ∘ R)`. Both are traceless if `P` is (`R` is an isometry), have
  coefficient size `≤ sumNorm P`, and approximate an even (odd) function as well as `P` does.
  The polynomial classes of the two boundary iterations are `Nondiv.IsEvenPoly ν`
  (`P ∘ R = P`, hence `∂_ν P = 0` on the flat part) and `Nondiv.VanishesOnFlat ν`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001.
-/

public section

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian RealInnerProductSpace

namespace BasicElliptic

/-! ### Reflection and folding -/

section Fold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `fold ν y = y − 2 min(⟪y, ν⟫, 0) ν`. -/
theorem Nondiv.fold_eq {ν : E} (hν : ‖ν‖ = 1) (y : E) :
    fold ν y = y - (2 * min ⟪y, ν⟫ 0) • ν := by
  unfold fold
  split_ifs with h
  · rw [min_eq_right h]; simp
  · rw [min_eq_left (not_le.1 h).le, reflect_apply hν]

theorem Nondiv.continuous_fold {ν : E} (hν : ‖ν‖ = 1) : Continuous (fold ν) := by
  rw [funext (Nondiv.fold_eq hν)]
  fun_prop

theorem Nondiv.fold_reflect {ν : E} (hν : ‖ν‖ = 1) (y : E) : fold ν (reflect ν y) = fold ν y := by
  rw [Nondiv.fold_eq hν, Nondiv.fold_eq hν, inner_reflect hν, reflect_apply hν]
  have : 2 * ⟪y, ν⟫ + 2 * min (-⟪y, ν⟫) 0 = 2 * min ⟪y, ν⟫ 0 := by
    rcases le_total 0 ⟪y, ν⟫ with h | h
    · rw [min_eq_left (by linarith), min_eq_right h]; ring
    · rw [min_eq_right (by linarith), min_eq_left h]; ring
  rw [sub_sub, ← add_smul, this]

theorem Nondiv.norm_fold (ν : E) (y : E) : ‖fold ν y‖ = ‖y‖ := by
  unfold fold
  split_ifs
  · rfl
  · exact (reflect ν).norm_map y

theorem Nondiv.reflect_add_smul {ν : E} (hν : ‖ν‖ = 1) {z : E} (hz : z ∈ flatPart ν) (t : ℝ) :
    reflect ν (z + t • ν) = z + (-t) • ν := by
  have hz0 : ⟪z, ν⟫ = 0 := hz
  rw [reflect_apply hν, inner_add_left, hz0, real_inner_smul_left,
    real_inner_self_of_norm_eq_one hν]
  module

end Fold

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Even functions have vanishing normal derivative -/

omit [FiniteDimensional ℝ E] in
/-- If `f` is differentiable at a flat point `z` and `f ∘ R = f` near `z`, then
`t ↦ f (z + t • ν)` has derivative `0` at `0`. -/
theorem hasDerivAt_line_eq_zero_of_reflect {ν : E} (hν : ‖ν‖ = 1) {f : E → ℝ} {z : E}
    (hz : z ∈ flatPart ν) (hf : DifferentiableAt ℝ f z)
    (hR : ∀ᶠ y in 𝓝 z, f (reflect ν y) = f y) :
    HasDerivAt (fun t : ℝ ↦ f (z + t • ν)) 0 0 := by
  set D := fderiv ℝ f z ν
  have hline : HasDerivAt (fun t : ℝ ↦ z + t • ν) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add z
  have hf' : HasFDerivAt f (fderiv ℝ f z) (z + (0 : ℝ) • ν) := by
    rw [zero_smul, add_zero]; exact hf.hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ ↦ f (z + t • ν)) D 0 := hf'.comp_hasDerivAt (0 : ℝ) hline
  have hcont : Tendsto (fun t : ℝ ↦ z + t • ν) (𝓝 0) (𝓝 z) := by
    have := hline.continuousAt.tendsto
    simpa using this
  have heq : (fun t : ℝ ↦ f (z + (-t) • ν)) =ᶠ[𝓝 0] fun t ↦ f (z + t • ν) := by
    filter_upwards [hcont.eventually hR] with t ht
    rw [← reflect_add_smul hν hz]; exact ht
  have hneg : HasDerivAt (fun t : ℝ ↦ f (z + (-t) • ν)) (-D) 0 := by
    have hg0 : HasDerivAt (fun t : ℝ ↦ f (z + t • ν)) D (-(0 : ℝ)) := by
      rw [neg_zero]; exact hg
    have := hg0.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun t : ℝ ↦ f (z + t • ν)) (-D) 0 := hneg.congr_of_eventuallyEq heq.symm
  have hD : D = -D := hg.unique h2
  have : D = 0 := by linarith
  rwa [this] at hg

/-! ### The model problems -/

/-- **Neumann model on the unit half ball.** For `u` continuous on `halfBall ν 0 1` there is `h`,
continuous on `closedBall 0 1` and harmonic in `ball 0 1`, with `h ∘ reflect ν = h` and `h = u`
on the spherical part `sphere 0 1 ∩ halfSpace ν`. -/
theorem exists_harmonic_even_halfBall {ν : E} (hν : ‖ν‖ = 1) {u : E → ℝ}
    (hu : ContinuousOn u (halfBall ν 0 1)) :
    ∃ h : E → ℝ, ContinuousOn h (closedBall 0 1) ∧ HarmonicOnNhd h (ball 0 1) ∧
      (∀ z ∈ closedBall (0 : E) 1, h (reflect ν z) = h z) ∧
      ∀ z ∈ sphere (0 : E) 1, z ∈ halfSpace ν → h z = u z := by
  have : Nontrivial E := ⟨⟨ν, 0, fun h ↦ by simp [h] at hν⟩⟩
  have hmaps : MapsTo (fold ν) (sphere (0 : E) 1) (halfBall ν 0 1) := fun y hy ↦
    ⟨by rw [mem_closedBall_zero_iff, norm_fold ν, mem_sphere_zero_iff_norm.1 hy],
      fold_mem_halfSpace hν y⟩
  obtain ⟨h, hc, hh, hbd⟩ := exists_harmonic_ball_boundary (0 : E) one_pos
    (g := fun y ↦ u (fold ν y)) (hu.comp (continuous_fold hν).continuousOn hmaps)
  have hx : (0 : E) ∈ flatPart ν := by simp
  refine ⟨h, hc, hh, apply_reflect_eq_of_harmonic_ball hx one_pos hh hc fun y hy ↦ ?_,
    fun z hz hzh ↦ ?_⟩
  · have hRy : reflect ν y ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, (reflect ν).norm_map, mem_sphere_zero_iff_norm.1 hy]
    rw [hbd hRy, hbd hy]
    simp only [fold_reflect hν]
  · rw [hbd hz]; simp only [fold_of_mem hzh]

omit [FiniteDimensional ℝ E] in
private theorem continuousOn_oddExt {ν : E} (hν : ‖ν‖ = 1) {u : E → ℝ}
    (hu : ContinuousOn u (halfBall ν 0 1))
    (h0 : ∀ z ∈ halfBall ν (0 : E) 1, z ∈ flatPart ν → u z = 0) :
    ContinuousOn (oddExt ν u) (closedBall 0 1) := by
  have hcont : Continuous fun y : E ↦ ⟪y, ν⟫ := continuous_id.inner continuous_const
  have hR : ∀ y ∈ closedBall (0 : E) 1, reflect ν y ∈ closedBall (0 : E) 1 := fun y hy ↦ by
    rw [mem_closedBall_zero_iff, (reflect ν).norm_map]; exact mem_closedBall_zero_iff.1 hy
  refine ContinuousOn.if (fun y hy ↦ ?_) (hu.mono fun y hy ↦ ⟨hy.1, ?_⟩)
    (((hu.comp (reflect ν).continuous.continuousOn fun y hy ↦ ⟨hR y hy.1, ?_⟩).neg).mono
      subset_rfl)
  · have hy0 : ⟪y, ν⟫ = 0 := (frontier_le_subset_eq continuous_const hcont hy.2).symm
    have hmem : y ∈ halfBall ν (0 : E) 1 := ⟨hy.1, hy0.ge⟩
    rw [reflect_eq_self_of_mem_flatPart hν hy0, h0 y hmem hy0, neg_zero]
  · exact (isClosed_le continuous_const hcont).closure_subset hy.2
  · have : ⟪y, ν⟫ ≤ 0 := closure_lt_subset_le hcont continuous_const
      (by simpa only [not_le] using hy.2)
    rw [mem_halfSpace, inner_reflect hν]; linarith

/-- **Dirichlet model on the unit half ball.** For `u` continuous on `halfBall ν 0 1` with `u = 0`
on the flat part there is `h`, continuous on `closedBall 0 1` and harmonic in `ball 0 1`, with
`h ∘ reflect ν = -h` (so `h = 0` on the flat part) and `h = u` on the spherical part. -/
theorem exists_harmonic_odd_halfBall {ν : E} (hν : ‖ν‖ = 1) {u : E → ℝ}
    (hu : ContinuousOn u (halfBall ν 0 1))
    (h0 : ∀ z ∈ halfBall ν (0 : E) 1, z ∈ flatPart ν → u z = 0) :
    ∃ h : E → ℝ, ContinuousOn h (closedBall 0 1) ∧ HarmonicOnNhd h (ball 0 1) ∧
      (∀ z ∈ closedBall (0 : E) 1, h (reflect ν z) = -h z) ∧
      ∀ z ∈ sphere (0 : E) 1, z ∈ halfSpace ν → h z = u z := by
  have : Nontrivial E := ⟨⟨ν, 0, fun h ↦ by simp [h] at hν⟩⟩
  obtain ⟨h, hc, hh, hbd⟩ := exists_harmonic_ball_boundary (0 : E) one_pos
    (g := oddExt ν u) ((continuousOn_oddExt hν hu h0).mono sphere_subset_closedBall)
  have hx : (0 : E) ∈ flatPart ν := by simp
  refine ⟨h, hc, hh, apply_reflect_eq_neg_of_harmonic_ball hx one_pos hh hc fun y hy ↦ ?_,
    fun z hz hzh ↦ ?_⟩
  · have hRy : reflect ν y ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, (reflect ν).norm_map, mem_sphere_zero_iff_norm.1 hy]
    rw [hbd hRy, hbd hy]
    simp only [oddExt, inner_reflect hν, reflect_reflect]
    rcases lt_trichotomy ⟪y, ν⟫ 0 with h1 | h1 | h1
    · have a : 0 ≤ -⟪y, ν⟫ := by linarith
      have b : ¬ 0 ≤ ⟪y, ν⟫ := by linarith
      simp only [a, b, ↓reduceIte, neg_neg]
    · have hy' : y ∈ halfBall ν (0 : E) 1 := ⟨sphere_subset_closedBall hy, h1.ge⟩
      have a : 0 ≤ -⟪y, ν⟫ := by linarith
      simp only [a, h1.ge, ↓reduceIte, reflect_eq_self_of_mem_flatPart hν h1, h0 y hy' h1,
        neg_zero]
    · have a : ¬ 0 ≤ -⟪y, ν⟫ := by linarith
      simp only [a, h1.le, ↓reduceIte]
  · rw [hbd hz]; simp only [oddExt, mem_halfSpace.1 hzh, ↓reduceIte]

/-! ### Polynomial classes -/

/-- Quadratic polynomials even under the reflection across `flatPart ν`. -/
@[expose] def IsEvenPoly (ν : E) (P : QuadPoly E) : Prop := ∀ z, P.eval (reflect ν z) = P.eval z

/-- Quadratic polynomials vanishing on `flatPart ν`. -/
@[expose] def VanishesOnFlat (ν : E) (P : QuadPoly E) : Prop := ∀ z ∈ flatPart ν, P.eval z = 0

omit [FiniteDimensional ℝ E] in
theorem IsEvenPoly.add {ν : E} {P Q : QuadPoly E} (hP : IsEvenPoly ν P) (hQ : IsEvenPoly ν Q) :
    IsEvenPoly ν (P + Q) := fun z ↦ by simp [QuadPoly.eval_add, hP z, hQ z]

omit [FiniteDimensional ℝ E] in
theorem IsEvenPoly.smul {ν : E} {P : QuadPoly E} (hP : IsEvenPoly ν P) (c : ℝ) :
    IsEvenPoly ν (c • P) := fun z ↦ by simp [QuadPoly.eval_smul, hP z]

omit [FiniteDimensional ℝ E] in
theorem IsEvenPoly.rescale {ν : E} {P : QuadPoly E} (hP : IsEvenPoly ν P) (c : ℝ) :
    IsEvenPoly ν (P.rescale c) := fun z ↦ by
  simp only [QuadPoly.eval_rescale, ← map_smul]
  exact hP _

omit [FiniteDimensional ℝ E] in
theorem VanishesOnFlat.add {ν : E} {P Q : QuadPoly E} (hP : VanishesOnFlat ν P)
    (hQ : VanishesOnFlat ν Q) : VanishesOnFlat ν (P + Q) := fun z hz ↦ by
  simp [QuadPoly.eval_add, hP z hz, hQ z hz]

omit [FiniteDimensional ℝ E] in
theorem VanishesOnFlat.smul {ν : E} {P : QuadPoly E} (hP : VanishesOnFlat ν P) (c : ℝ) :
    VanishesOnFlat ν (c • P) := fun z hz ↦ by simp [QuadPoly.eval_smul, hP z hz]

omit [FiniteDimensional ℝ E] in
theorem VanishesOnFlat.rescale {ν : E} {P : QuadPoly E} (hP : VanishesOnFlat ν P) (c : ℝ) :
    VanishesOnFlat ν (P.rescale c) := fun z hz ↦ by
  rw [QuadPoly.eval_rescale]
  exact hP _ (by simp only [mem_flatPart, real_inner_smul_left, mem_flatPart.1 hz, mul_zero])

omit [FiniteDimensional ℝ E] in
/-- An even polynomial has vanishing normal derivative on the flat part. -/
theorem IsEvenPoly.hasDerivAt_line {ν : E} (hν : ‖ν‖ = 1) {P : QuadPoly E}
    (hP : IsEvenPoly ν P) {z : E} (hz : z ∈ flatPart ν) :
    HasDerivAt (fun t : ℝ ↦ P.eval (z + t • ν)) 0 0 :=
  hasDerivAt_line_eq_zero_of_reflect hν hz (P.contDiff_eval (n := 1).differentiable
    one_ne_zero z) (Eventually.of_forall hP)

omit [FiniteDimensional ℝ E] in
/-- The isotropic quadratic `σ ‖z‖² / (2d)` is even. -/
theorem isEvenPoly_isotropic (ν : E) (σ : ℝ) : IsEvenPoly ν (QuadPoly.isotropic σ) := fun z ↦ by
  have e : (innerSL ℝ (reflect ν z)) (reflect ν z) = (innerSL ℝ z) z := by
    rw [innerSL_apply_apply, innerSL_apply_apply, LinearIsometryEquiv.inner_map_map]
  have e2 : (innerSL ℝ z) z = ‖z‖ ^ 2 := by
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  rw [e2] at e
  simp [QuadPoly.eval, QuadPoly.isotropic, e, e2]

end Nondiv

/-! ### Symmetrization of quadratic polynomials -/

namespace QuadPoly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `P ∘ reflect ν`. -/
noncomputable def reflectComp (ν : E) (P : QuadPoly E) : QuadPoly E :=
  P.compCLM (reflect ν : E →L[ℝ] E)

/-- The even part `½ (P + P ∘ reflect ν)`. -/
noncomputable def evenPart (ν : E) (P : QuadPoly E) : QuadPoly E :=
  (1 / 2 : ℝ) • (P + P.reflectComp ν)

/-- The odd part `½ (P − P ∘ reflect ν)`. -/
noncomputable def oddPart (ν : E) (P : QuadPoly E) : QuadPoly E :=
  (1 / 2 : ℝ) • (P + (-1 : ℝ) • P.reflectComp ν)

omit [FiniteDimensional ℝ E] in
@[simp] theorem eval_reflectComp (ν : E) (P : QuadPoly E) (z : E) :
    (P.reflectComp ν).eval z = P.eval (reflect ν z) := by
  simp [reflectComp]

omit [FiniteDimensional ℝ E] in
theorem eval_evenPart (ν : E) (P : QuadPoly E) (z : E) :
    (P.evenPart ν).eval z = (P.eval z + P.eval (reflect ν z)) / 2 := by
  simp [evenPart]; ring

omit [FiniteDimensional ℝ E] in
theorem eval_oddPart (ν : E) (P : QuadPoly E) (z : E) :
    (P.oddPart ν).eval z = (P.eval z - P.eval (reflect ν z)) / 2 := by
  simp [oddPart]; ring

theorem trace_reflectComp (ν : E) (P : QuadPoly E) : (P.reflectComp ν).trace = P.trace := by
  rw [← QuadPoly.laplacian_eval _ 0, ← QuadPoly.laplacian_eval P (reflect ν 0)]
  have e : (P.reflectComp ν).eval = P.eval ∘ (reflect ν) := funext fun z ↦ eval_reflectComp ν P z
  rw [e, ViscositySolns.Analysis.laplacian_comp_linearIsometryEquiv_right]
  rfl

theorem trace_evenPart (ν : E) (P : QuadPoly E) : (P.evenPart ν).trace = P.trace := by
  simp only [evenPart, trace_smul, trace_add, trace_reflectComp]; ring

theorem trace_oddPart (ν : E) (P : QuadPoly E) : (P.oddPart ν).trace = 0 := by
  simp only [oddPart, trace_smul, trace_add, trace_reflectComp]; ring

omit [FiniteDimensional ℝ E] in
theorem sumNorm_reflectComp_le (ν : E) (P : QuadPoly E) :
    (P.reflectComp ν).sumNorm ≤ P.sumNorm := by
  have hR : ‖(reflect ν : E →L[ℝ] E)‖ ≤ 1 :=
    (reflect ν).toLinearIsometry.norm_toContinuousLinearMap_le
  have h1 := P.norm_lin_compCLM_le (reflect ν : E →L[ℝ] E)
  have h2 := P.norm_quad_compCLM_le (reflect ν : E →L[ℝ] E)
  have hl : ‖(P.reflectComp ν).lin‖ ≤ ‖P.lin‖ :=
    h1.trans (mul_le_of_le_one_right (norm_nonneg _) hR)
  have hq : ‖(P.reflectComp ν).quad‖ ≤ ‖P.quad‖ := h2.trans (by
    calc ‖P.quad‖ * ‖(reflect ν : E →L[ℝ] E)‖ * ‖(reflect ν : E →L[ℝ] E)‖ ≤ ‖P.quad‖ * 1 * 1 := by
          gcongr
      _ = ‖P.quad‖ := by ring)
  simp only [sumNorm] at hl hq ⊢
  have : (P.reflectComp ν).const = P.const := rfl
  rw [this]; linarith

omit [FiniteDimensional ℝ E] in
private theorem sumNorm_half_smul_add_le (P Q : QuadPoly E) (hQ : Q.sumNorm ≤ P.sumNorm) :
    ((1 / 2 : ℝ) • (P + Q)).sumNorm ≤ P.sumNorm := by
  have h := sumNorm_add_le P Q
  have e : ((1 / 2 : ℝ) • (P + Q)).sumNorm = (1 / 2) * (P + Q).sumNorm := by
    simp only [sumNorm, smul_const, smul_lin, smul_quad, norm_smul, abs_mul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  rw [e]; linarith

omit [FiniteDimensional ℝ E] in
theorem sumNorm_evenPart_le (ν : E) (P : QuadPoly E) : (P.evenPart ν).sumNorm ≤ P.sumNorm :=
  sumNorm_half_smul_add_le _ _ (sumNorm_reflectComp_le ν P)

omit [FiniteDimensional ℝ E] in
theorem sumNorm_oddPart_le (ν : E) (P : QuadPoly E) : (P.oddPart ν).sumNorm ≤ P.sumNorm := by
  refine sumNorm_half_smul_add_le _ _ ?_
  have e : ((-1 : ℝ) • P.reflectComp ν).sumNorm = (P.reflectComp ν).sumNorm := by
    simp [sumNorm]
  rw [e]; exact sumNorm_reflectComp_le ν P

omit [FiniteDimensional ℝ E] in
theorem isEvenPoly_evenPart {ν : E} (P : QuadPoly E) : Nondiv.IsEvenPoly ν (P.evenPart ν) :=
  fun z ↦ by rw [eval_evenPart, eval_evenPart, reflect_reflect, add_comm]

omit [FiniteDimensional ℝ E] in
theorem vanishesOnFlat_oddPart {ν : E} (hν : ‖ν‖ = 1) (P : QuadPoly E) :
    Nondiv.VanishesOnFlat ν (P.oddPart ν) := fun z hz ↦ by
  rw [eval_oddPart, reflect_eq_self_of_mem_flatPart hν hz, sub_self, zero_div]

omit [FiniteDimensional ℝ E] in
/-- If `|h − P| ≤ ε` on a reflection-invariant set `S` and `h` is even, then
`|h − evenPart P| ≤ ε` on `S`. -/
theorem abs_sub_evenPart_le {ν : E} {P : QuadPoly E} {h : E → ℝ} {S : Set E} {ε : ℝ}
    (hS : ∀ z ∈ S, reflect ν z ∈ S) (hh : ∀ z ∈ S, h (reflect ν z) = h z)
    (hP : ∀ z ∈ S, |h z - P.eval z| ≤ ε) : ∀ z ∈ S, |h z - (P.evenPart ν).eval z| ≤ ε := by
  intro z hz
  have a := hP z hz
  have b := hP _ (hS z hz)
  rw [hh z hz] at b
  rw [eval_evenPart]
  calc |h z - (P.eval z + P.eval (reflect ν z)) / 2|
      = |(h z - P.eval z) + (h z - P.eval (reflect ν z))| / 2 := by
        rw [← abs_two, ← abs_div]; ring_nf
    _ ≤ (|h z - P.eval z| + |h z - P.eval (reflect ν z)|) / 2 := by
        gcongr; exact abs_add_le _ _
    _ ≤ ε := by linarith

omit [FiniteDimensional ℝ E] in
/-- If `|h − P| ≤ ε` on a reflection-invariant set `S` and `h` is odd, then
`|h − oddPart P| ≤ ε` on `S`. -/
theorem abs_sub_oddPart_le {ν : E} {P : QuadPoly E} {h : E → ℝ} {S : Set E} {ε : ℝ}
    (hS : ∀ z ∈ S, reflect ν z ∈ S) (hh : ∀ z ∈ S, h (reflect ν z) = -h z)
    (hP : ∀ z ∈ S, |h z - P.eval z| ≤ ε) : ∀ z ∈ S, |h z - (P.oddPart ν).eval z| ≤ ε := by
  intro z hz
  have a := hP z hz
  have b := hP _ (hS z hz)
  rw [hh z hz] at b
  rw [eval_oddPart]
  have b' : |h z + P.eval (reflect ν z)| ≤ ε := by
    rw [← abs_neg]; convert b using 2; ring
  calc |h z - (P.eval z - P.eval (reflect ν z)) / 2|
      = |(h z - P.eval z) + (h z + P.eval (reflect ν z))| / 2 := by
        rw [← abs_two, ← abs_div]; ring_nf
    _ ≤ (|h z - P.eval z| + |h z + P.eval (reflect ν z)|) / 2 := by
        gcongr; exact abs_add_le _ _
    _ ≤ ε := by linarith

end QuadPoly

end BasicElliptic
