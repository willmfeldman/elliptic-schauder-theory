/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Nondiv.Boundary.Assemble

/-!
# The conormal boundary data at a flat point

Let `s = halfBall ν x r`, let `w ∈ C²(s)` satisfy the conormal condition `⟪a ν, ∇w⟫ = γ` on the flat
part, with `β = a ν` there and `β, γ ∈ C^{1,α}(s)`. Fix a flat point `p` and `a₀ = a(p)`. At flat
points `y`,
```
⟪a₀ ν, ∇w(y)⟫ = γ̂(y) := γ(y) − ⟪β(y) − β(p), ∇w(y)⟫,
```
and `γ̂(y) = γ(p) + ℓ(y − p) + O(|y − p|^{1+α})` with `ℓ = Dγ(p) − ⟪Dβ(p) ·, ∇w(p)⟫`; the
constant involves `[Dγ]_α`, `[Dβ]_α`, `sup ‖Dβ‖`, `sup ‖Dw‖` and `sup ‖D²w‖`
(`Nondiv.abs_conormalData_sub_le`).

* `Nondiv.norm_fderivWithin_sub_le_of_holder`: `C^{1,α}` in the sense of `ContDiffHolderOn 1 α`
  gives a Hölder within-derivative.
* `Nondiv.norm_sub_sub_fderivWithin_le`: first-order Taylor bound with Hölder derivative on a
  convex set.
* `Nondiv.hasDerivWithinAt_line_of_inward`: the right-derivative along an inward direction at a
  point of the half ball is the within-derivative.
* `QuadPoly.conormalPoly`: the quadratic `⟪h, ν⟫ (c + ℓ h) / μ`, whose derivative along `a₀ ν`
  (with `⟪a₀ ν, ν⟫ = μ`) at flat `h` is `c + ℓ h`.
-/

public section

open Metric Set Filter Topology Module InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `C^{1,α}` gives a Hölder within-derivative. -/
theorem norm_fderivWithin_sub_le_of_holder [NormedSpace ℝ E] {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {φ : E → G} {s : Set E} (hs : UniqueDiffOn ℝ s) {C α : ℝ≥0}
    (h : HolderOnWith C α (iteratedFDerivWithin ℝ 1 φ s) s) {y y' : E} (hy : y ∈ s)
    (hy' : y' ∈ s) :
    ‖fderivWithin ℝ φ s y - fderivWithin ℝ φ s y'‖ ≤ C * dist y y' ^ (α : ℝ) := by
  have h1 := h.dist_le hy hy'
  rw [dist_eq_norm] at h1
  refine le_trans ?_ h1
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  have e : (fderivWithin ℝ φ s y - fderivWithin ℝ φ s y') v =
      (iteratedFDerivWithin ℝ 1 φ s y - iteratedFDerivWithin ℝ 1 φ s y') (fun _ ↦ v) := by
    rw [sub_apply, sub_apply, iteratedFDerivWithin_one_apply (hs y hy),
      iteratedFDerivWithin_one_apply (hs y' hy')]
  rw [e]
  refine ((iteratedFDerivWithin ℝ 1 φ s y -
    iteratedFDerivWithin ℝ 1 φ s y').le_opNorm _).trans ?_
  simp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **First-order Taylor bound with Hölder derivative.** On a convex set, if
`‖Dφ(z) − Dφ(p)‖ ≤ K |z − p|^α`, then `‖φ(y) − φ(p) − Dφ(p)(y − p)‖ ≤ K |y − p|^{1+α}`. -/
theorem norm_sub_sub_fderivWithin_le [NormedSpace ℝ E] {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {φ : E → G} {s : Set E} (hcv : Convex ℝ s)
    (hφ : DifferentiableOn ℝ φ s) {K α : ℝ} (hK0 : 0 ≤ K) (hα : 0 < α) {p y : E} (hp : p ∈ s)
    (hy : y ∈ s)
    (hK : ∀ z ∈ s, ‖fderivWithin ℝ φ s z - fderivWithin ℝ φ s p‖ ≤ K * dist z p ^ α) :
    ‖φ y - φ p - fderivWithin ℝ φ s p (y - p)‖ ≤ K * dist y p ^ (1 + α) := by
  set T := segment ℝ p y
  have hTs : T ⊆ s := hcv.segment_subset hp hy
  have hT : Convex ℝ T := convex_segment p y
  have hbound : ∀ z ∈ T, ‖fderivWithin ℝ φ s z - fderivWithin ℝ φ s p‖ ≤
      K * dist y p ^ α := fun z hz ↦ by
    refine (hK z (hTs hz)).trans ?_
    gcongr
    rw [dist_comm z p, dist_comm y p]
    obtain ⟨t₁, t₂, ht₁, ht₂, ht, rfl⟩ := hz
    rw [dist_eq_norm, dist_eq_norm]
    have : p - (t₁ • p + t₂ • y) = t₂ • (p - y) := by
      rw [show t₁ = 1 - t₂ by linarith]; module
    rw [this, norm_smul, Real.norm_of_nonneg ht₂]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz ↦ ((hφ z (hTs hz)).hasFDerivWithinAt).mono hTs) hbound hT
    (left_mem_segment ℝ p y) (right_mem_segment ℝ p y)
  calc _ ≤ K * dist y p ^ α * ‖y - p‖ := h
    _ = K * dist y p ^ (1 + α) := by
        rw [← dist_eq_norm, Real.rpow_add' dist_nonneg (by linarith), Real.rpow_one]; ring

omit [FiniteDimensional ℝ E] in
/-- The right-derivative along an inward direction at a point of `halfBall ν x r` strictly
inside `ball x r` is the within-derivative. -/
theorem hasDerivWithinAt_line_of_inward {ν x : E} {r : ℝ} {w : E → ℝ} {y v : E}
    (hy : y ∈ ball x r) (hyh : y ∈ halfSpace ν) (hv : 0 ≤ ⟪v, ν⟫)
    (hw : DifferentiableWithinAt ℝ w (halfBall ν x r) y) :
    HasDerivWithinAt (fun t : ℝ ↦ w (y + t • v)) (fderivWithin ℝ w (halfBall ν x r) y v)
      (Ici 0) 0 := by
  set ε := (r - dist y x) / (‖v‖ + 1) with hε
  have hε0 : 0 < ε := div_pos (by linarith [mem_ball.1 hy]) (by positivity)
  have hline : HasDerivWithinAt (fun t : ℝ ↦ y + t • v) v (Ici 0 ∩ Iio ε) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
    simpa using this.hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ ↦ y + t • v) (Ici 0 ∩ Iio ε) (halfBall ν x r) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall]
      have h1 : dist (y + t • v) x ≤ dist y x + t * ‖v‖ := by
        calc dist (y + t • v) x ≤ dist (y + t • v) y + dist y x := dist_triangle _ _ _
          _ = dist y x + t * ‖v‖ := by
              rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]; ring
      have h2 : t * ‖v‖ ≤ r - dist y x := by
        have h3 : t * (‖v‖ + 1) ≤ r - dist y x := by
          have h4 : t < ε := ht.2
          rw [hε, lt_div_iff₀ (by positivity)] at h4
          linarith
        have ht0 : 0 ≤ t := ht.1
        have : t * ‖v‖ ≤ t * (‖v‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) ht0
        linarith
      linarith
    · rw [mem_halfSpace, inner_add_left, real_inner_smul_left]
      exact add_nonneg hyh (mul_nonneg ht.1 hv)
  have hw' : HasFDerivWithinAt w (fderivWithin ℝ w (halfBall ν x r) y) (halfBall ν x r)
      (y + (0 : ℝ) • v) := by rw [zero_smul, add_zero]; exact hw.hasFDerivWithinAt
  have hcomp := hw'.comp_hasDerivWithinAt (0 : ℝ) hline hmaps
  exact (hasDerivWithinAt_inter (Iio_mem_nhds hε0)).1 hcomp

end Nondiv

namespace QuadPoly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic `h ↦ ⟪h, ν⟫ (c + ℓ h) / μ`. -/
noncomputable def conormalPoly (ν : E) (μ c : ℝ) (ℓ : E →L[ℝ] ℝ) : QuadPoly E :=
  ⟨0, (c / μ) • innerSL ℝ ν, μ⁻¹ • ((innerSL ℝ ν).smulRight ℓ + ℓ.smulRight (innerSL ℝ ν))⟩

theorem conormalPoly_quad_apply (ν : E) (μ c : ℝ) (ℓ : E →L[ℝ] ℝ) (v w : E) :
    (conormalPoly ν μ c ℓ).quad v w = μ⁻¹ * (⟪ν, v⟫ * ℓ w + ℓ v * ⟪ν, w⟫) := by
  simp only [conormalPoly, smul_apply, add_apply, smulRight_apply, smul_eq_mul]
  rw [innerSL_apply_apply, innerSL_apply_apply]

theorem conormalPoly_lin_apply (ν : E) (μ c : ℝ) (ℓ : E →L[ℝ] ℝ) (v : E) :
    (conormalPoly ν μ c ℓ).lin v = c / μ * ⟪ν, v⟫ := by
  simp only [conormalPoly, smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply]

theorem norm_conormalPoly_lin_le {ν : E} (hν : ‖ν‖ = 1) {μ c : ℝ} (hμ : 0 < μ)
    (ℓ : E →L[ℝ] ℝ) : ‖(conormalPoly ν μ c ℓ).lin‖ ≤ |c| / μ := by
  simp only [conormalPoly]
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hμ, innerSL_apply_norm, hν, mul_one]

theorem norm_conormalPoly_quad_le {ν : E} (hν : ‖ν‖ = 1) {μ c : ℝ} (hμ : 0 < μ)
    (ℓ : E →L[ℝ] ℝ) : ‖(conormalPoly ν μ c ℓ).quad‖ ≤ 2 * ‖ℓ‖ / μ := by
  simp only [conormalPoly]
  refine (norm_smul_le _ _).trans ?_
  have h1 : ‖(innerSL ℝ ν).smulRight ℓ + ℓ.smulRight (innerSL ℝ ν)‖ ≤ 2 * ‖ℓ‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smulRight_apply, norm_smulRight_apply, innerSL_apply_norm, hν]; linarith
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hμ]
  calc μ⁻¹ * ‖(innerSL ℝ ν).smulRight ℓ + ℓ.smulRight (innerSL ℝ ν)‖ ≤ μ⁻¹ * (2 * ‖ℓ‖) := by
        gcongr
    _ = 2 * ‖ℓ‖ / μ := by ring

/-- The derivative of `conormalPoly` along `v` at a flat `h`, when `⟪ν, v⟫ = μ`, is `c + ℓ h`. -/
theorem conormalPoly_deriv {ν : E} {μ c : ℝ} (hμ : μ ≠ 0) (ℓ : E →L[ℝ] ℝ) {h v : E}
    (hh : ⟪ν, h⟫ = 0) (hv : ⟪ν, v⟫ = μ) :
    ((conormalPoly ν μ c ℓ).lin + (conormalPoly ν μ c ℓ).hess h) v = c + ℓ h := by
  rw [add_apply, hess_apply, conormalPoly_lin_apply, conormalPoly_quad_apply,
    conormalPoly_quad_apply, hh, hv]
  field_simp
  ring

end QuadPoly


namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem hess_add_poly (P Q : QuadPoly E) : (P + Q).hess = P.hess + Q.hess := by
  ext v w; simp only [QuadPoly.hess_apply, QuadPoly.add_quad, add_apply]; ring

omit [FiniteDimensional ℝ E] in
theorem hess_const_poly (c : ℝ) : (⟨c, 0, 0⟩ : QuadPoly E).hess = 0 := by
  ext v w; simp [QuadPoly.hess_apply]

/-- **The conormal data at a flat point**. With
`ℓ = Dγ(p) − ⟪Dβ(p) ·, ∇w(p)⟫`, the function `γ̂(y) = γ(y) − ⟪β(y) − β(p), ∇w(y)⟫` satisfies
`|γ̂(y) − γ(p) − ℓ(y − p)| ≤ (K_γ + K_β M₁ + M_{Dβ} M₂ D^{1−α}) |y − p|^{1+α}`. -/
theorem abs_conormalData_sub_le {s : Set E} (hcv : Convex ℝ s) (hU : UniqueDiffOn ℝ s)
    {α : ℝ} (hα : 0 < α ∧ α < 1) {β : E → E} {γ w : E → ℝ} (hβd : DifferentiableOn ℝ β s)
    (hγd : DifferentiableOn ℝ γ s) (hw : ContDiffOn ℝ 2 w s) {Kγ Kβ MDβ M₁ M₂ D : ℝ}
    (hKγ : 0 ≤ Kγ) (hKβ : 0 ≤ Kβ) (hM₂0 : 0 ≤ M₂) (hMDβ0 : 0 ≤ MDβ)
    (hγH : ∀ y ∈ s, ∀ y' ∈ s,
      ‖fderivWithin ℝ γ s y - fderivWithin ℝ γ s y'‖ ≤ Kγ * dist y y' ^ α)
    (hβH : ∀ y ∈ s, ∀ y' ∈ s,
      ‖fderivWithin ℝ β s y - fderivWithin ℝ β s y'‖ ≤ Kβ * dist y y' ^ α)
    (hMDβ : ∀ y ∈ s, ‖fderivWithin ℝ β s y‖ ≤ MDβ)
    (hM₁ : ∀ y ∈ s, ‖fderivWithin ℝ w s y‖ ≤ M₁)
    (hM₂ : ∀ y ∈ s, ‖fderivWithin ℝ (fderivWithin ℝ w s) s y‖ ≤ M₂)
    (hD : ∀ y ∈ s, ∀ y' ∈ s, dist y y' ≤ D) {p y : E} (hp : p ∈ s) (hy : y ∈ s) :
    |(γ y - ⟪β y - β p, gradientWithin w s y⟫) -
        (γ p + (fderivWithin ℝ γ s p -
          (innerSL ℝ (gradientWithin w s p)).comp (fderivWithin ℝ β s p)) (y - p))| ≤
      (Kγ + Kβ * M₁ + MDβ * M₂ * D ^ (1 - α)) * dist y p ^ (1 + α) := by
  set t := dist y p with ht
  have ht0 : 0 ≤ t := dist_nonneg
  have hTγ := norm_sub_sub_fderivWithin_le hcv hγd hKγ hα.1 hp hy (fun z hz ↦ hγH z hz p hp)
  have hTβ := norm_sub_sub_fderivWithin_le hcv hβd hKβ hα.1 hp hy (fun z hz ↦ hβH z hz p hp)
  set Tβ := β y - β p - fderivWithin ℝ β s p (y - p) with hTβdef
  set v := fderivWithin ℝ β s p (y - p) with hv
  have hgradn : ∀ z, ‖gradientWithin w s z‖ = ‖fderivWithin ℝ w s z‖ := fun z ↦ by
    rw [gradientWithin, LinearIsometryEquiv.norm_map]
  have hgrad_sub : ‖gradientWithin w s y - gradientWithin w s p‖ ≤ M₂ * t := by
    rw [gradientWithin, gradientWithin, ← map_sub, LinearIsometryEquiv.norm_map, ht,
      dist_eq_norm]
    exact norm_fderivWithin_sub_le hcv hU hw hM₂ hy hp
  have hvn : ‖v‖ ≤ MDβ * t := by
    rw [hv, ht, dist_eq_norm]
    exact ((fderivWithin ℝ β s p).le_opNorm _).trans (by gcongr; exact hMDβ p hp)
  -- the decomposition
  have e : (γ y - ⟪β y - β p, gradientWithin w s y⟫) -
      (γ p + (fderivWithin ℝ γ s p -
        (innerSL ℝ (gradientWithin w s p)).comp (fderivWithin ℝ β s p)) (y - p)) =
      (γ y - γ p - fderivWithin ℝ γ s p (y - p)) - ⟪Tβ, gradientWithin w s y⟫ -
        ⟪v, gradientWithin w s y - gradientWithin w s p⟫ := by
    simp only [hTβdef, hv, sub_apply, coe_comp, Function.comp_apply, innerSL_apply_apply,
      inner_sub_left, inner_sub_right]
    rw [real_inner_comm (gradientWithin w s p)]
    ring
  rw [e]
  have h1 : |γ y - γ p - fderivWithin ℝ γ s p (y - p)| ≤ Kγ * t ^ (1 + α) := by
    rw [← Real.norm_eq_abs]; exact hTγ
  have h2 : |⟪Tβ, gradientWithin w s y⟫| ≤ Kβ * M₁ * t ^ (1 + α) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hgradn]
    calc ‖Tβ‖ * ‖fderivWithin ℝ w s y‖ ≤ Kβ * t ^ (1 + α) * M₁ :=
          mul_le_mul hTβ (hM₁ y hy) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 : |⟪v, gradientWithin w s y - gradientWithin w s p⟫| ≤
      MDβ * M₂ * D ^ (1 - α) * t ^ (1 + α) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hsq : t * t ≤ D ^ (1 - α) * t ^ (1 + α) := by
      rcases ht0.eq_or_lt with h0 | hpos
      · rw [← h0]; simp [Real.zero_rpow (by linarith : (1 : ℝ) + α ≠ 0)]
      · have hD' : t ≤ D := hD y hy p hp
        calc t * t = t ^ (1 - α) * t ^ (1 + α) := by
              rw [← Real.rpow_add hpos]; norm_num; ring
          _ ≤ D ^ (1 - α) * t ^ (1 + α) := by gcongr; linarith [hα.2]
    calc ‖v‖ * ‖gradientWithin w s y - gradientWithin w s p‖ ≤ (MDβ * t) * (M₂ * t) := by
          gcongr
      _ = MDβ * M₂ * (t * t) := by ring
      _ ≤ MDβ * M₂ * (D ^ (1 - α) * t ^ (1 + α)) := by gcongr
      _ = _ := by ring
  calc _ ≤ |γ y - γ p - fderivWithin ℝ γ s p (y - p) - ⟪Tβ, gradientWithin w s y⟫| +
        |⟪v, gradientWithin w s y - gradientWithin w s p⟫| := abs_sub _ _
    _ ≤ |γ y - γ p - fderivWithin ℝ γ s p (y - p)| + |⟪Tβ, gradientWithin w s y⟫| +
        |⟪v, gradientWithin w s y - gradientWithin w s p⟫| := by gcongr; exact abs_sub _ _
    _ ≤ _ := by
        have := add_le_add (add_le_add h1 h2) h3
        linarith

end Nondiv


namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- **Pointwise expansion at a flat point, conormal case with affine data.** As
`Nondiv.expansion_at_flat_point_conormal`, but the derivative `d` of `w` along `a(x₀) ν` at a flat
point `y` is only required to satisfy `|d − c − ℓ(y − x₀)| ≤ G |y − x₀|^{1+α}`. The affine part
is removed by subtracting the quadratic `⟪h, ν⟫ (c + ℓ h) / μ`, `μ = ⟪a(x₀) ν, ν⟫`
(`QuadPoly.conormalPoly`). The resulting `P` satisfies `tr (a(x₀) D²P) = F(x₀)`,
`R² ‖quad P‖ ≤ C N + 2 R² ‖ℓ‖ / lam` and `|w(y) − P(y − x₀)| ≤ C N (|y − x₀|/R)^{2+α}`, where `N`
is given by `hN`. -/
theorem expansion_at_flat_point_conormal_affine {α : ℝ} (hα : 0 < α ∧ α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ {ν : E}, ‖ν‖ = 1 → ∀ (a : E → E →L[ℝ] E) (F w : E → ℝ)
      (x₀ : E) (R M₀ M₂ MF Ka KF G c N : ℝ) (ℓ : E →L[ℝ] ℝ), x₀ ∈ flatPart ν → 0 < R →
      0 ≤ Ka → 0 ≤ KF → 0 ≤ M₂ → 0 ≤ G →
      ContinuousOn w (halfBall ν x₀ R) → ContDiffOn ℝ 2 w (ball x₀ R ∩ openHalfSpace ν) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ∑ i, fderiv ℝ (fderiv ℝ w) y
        (a y (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F y) →
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a x₀ ξ, ξ⟫) → ‖a x₀‖ ≤ Λ → (a x₀ : E →ₗ[ℝ] E).IsSymmetric →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖a y - a x₀‖ ≤ Ka * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, |F y - F x₀| ≤ KF * dist y x₀ ^ α) →
      |F x₀| ≤ MF → (∀ y ∈ halfBall ν x₀ R, |w y - w x₀| ≤ M₀) →
      (∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M₂) →
      (∀ y ∈ ball x₀ R, y ∈ flatPart ν → ∃ d : ℝ,
        HasDerivWithinAt (fun t : ℝ ↦ w (y + t • a x₀ ν)) d (Ici 0) 0 ∧
          |d - c - ℓ (y - x₀)| ≤ G * dist y x₀ ^ (1 + α)) →
      N = M₀ + |c| * R / lam + 2 * ‖ℓ‖ * R ^ 2 / lam +
        R ^ 2 * (MF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Λ) +
        R ^ (2 + α) * (KF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Ka +
          finrank ℝ E * Ka * (M₂ + 2 * ‖ℓ‖ / lam) + G) →
      ∃ P : QuadPoly E,
        ∑ i, P.hess (a x₀ (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F x₀ ∧
        R ^ 2 * ‖P.quad‖ ≤ C * N + R ^ 2 * (2 * ‖ℓ‖ / lam) ∧
        ∀ y ∈ halfSpace ν, dist y x₀ < κ * R →
          |w y - P.eval (y - x₀)| ≤ C * N * (dist y x₀ / R) ^ (2 + α) := by
  obtain ⟨C, κ, hC, hκ, hexp⟩ := expansion_at_flat_point_conormal (E := E) hα hlam hlamΛ
  refine ⟨C, κ, hC, hκ, ?_⟩
  intro ν hν a F w x₀ R M₀ M₂ MF Ka KF G c N ℓ hx₀ hR hKa hKF hM₂ hG hwc hw2 heq hell hbd
    hsymm ha hF hFx hM₀ hD2 hcon hN
  set e := stdOrthonormalBasis ℝ E
  have hx₀' : ⟪x₀, ν⟫ = 0 := hx₀
  set μ := ⟪a x₀ ν, ν⟫ with hμ
  have hμl : lam ≤ μ := by
    have := hell ν; rwa [hν, one_pow, mul_one] at this
  have hμ0 : 0 < μ := hlam.trans_le hμl
  have hνaν : ⟪ν, a x₀ ν⟫ = μ := real_inner_comm _ _
  set q := QuadPoly.conormalPoly ν μ c ℓ with hq
  set Q : QuadPoly E := q.shift (-x₀) + ⟨w x₀, 0, 0⟩ with hQ
  have hQe : ∀ y, Q.eval y = q.eval (y - x₀) + w x₀ := fun y ↦ by
    rw [hQ, QuadPoly.eval_add, QuadPoly.eval_shift, sub_eq_add_neg]; simp [QuadPoly.eval]
  have hQh : Q.hess = q.hess := by
    rw [hQ, hess_add_poly, hess_const_poly, add_zero]; rfl
  have hBℓ : ‖q.quad‖ ≤ 2 * ‖ℓ‖ / lam :=
    (QuadPoly.norm_conormalPoly_quad_le hν hμ0 ℓ).trans
      (div_le_div_of_nonneg_left (by positivity) hlam hμl)
  have hhess : ‖Q.hess‖ ≤ 2 * ‖ℓ‖ / lam := by
    rw [hQh]; exact (norm_hess_le_norm_quad q).trans hBℓ
  have hlin : ‖q.lin‖ ≤ |c| / lam :=
    (QuadPoly.norm_conormalPoly_lin_le hν hμ0 ℓ).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hlam hμl)
  have hU : IsOpen (ball x₀ R ∩ openHalfSpace ν) := isOpen_ball.inter (isOpen_openHalfSpace ν)
  set u : E → ℝ := fun y ↦ w y - Q.eval y with hu
  set Fu : E → ℝ := fun y ↦ F y - ∑ i, Q.hess (a y (e i)) (e i) with hFu
  have hdim : (0 : ℝ) ≤ finrank ℝ E := by positivity
  have hBq0 : 0 ≤ 2 * ‖ℓ‖ / lam := by positivity
  -- the hypotheses of the conormal expansion for `u`
  have hu2 : ContDiffOn ℝ 2 u (ball x₀ R ∩ openHalfSpace ν) := hw2.sub Q.contDiff_eval.contDiffOn
  have hequ : ∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ∑ i, fderiv ℝ (fderiv ℝ u) y (a y (e i)) (e i) =
      Fu y := fun y hy ↦ by
    simp only [hu, fderiv_fderiv_sub_eval hU hw2 hy Q, sub_apply, Finset.sum_sub_distrib, heq y hy,
      hFu]
  have hFuH : ∀ y ∈ ball x₀ R ∩ openHalfSpace ν, |Fu y - Fu x₀| ≤
      (KF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Ka) * dist y x₀ ^ α := fun y hy ↦ by
    have e1 : Fu y - Fu x₀ = (F y - F x₀) - ∑ i, Q.hess ((a y - a x₀) (e i)) (e i) := by
      simp only [hFu]; rw [← sum_apply_sub]; ring
    rw [e1]
    have h2 := abs_sum_apply_le Q.hess (a y - a x₀)
    have h3 : ‖Q.hess‖ * ‖a y - a x₀‖ ≤ 2 * ‖ℓ‖ / lam * (Ka * dist y x₀ ^ α) :=
      mul_le_mul hhess (ha y hy) (norm_nonneg _) hBq0
    have hda : 0 ≤ dist y x₀ ^ α := Real.rpow_nonneg dist_nonneg _
    calc _ ≤ |F y - F x₀| + |∑ i, Q.hess ((a y - a x₀) (e i)) (e i)| := abs_sub _ _
      _ ≤ KF * dist y x₀ ^ α + finrank ℝ E * (2 * ‖ℓ‖ / lam * (Ka * dist y x₀ ^ α)) := by
          gcongr
          · exact hF y hy
          · exact h2.trans (by gcongr)
      _ = _ := by ring
  have hFux : |Fu x₀| ≤ MF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Λ := by
    have h2 := abs_sum_apply_le Q.hess (a x₀)
    have h3 : ‖Q.hess‖ * ‖a x₀‖ ≤ 2 * ‖ℓ‖ / lam * Λ :=
      mul_le_mul hhess hbd (norm_nonneg _) hBq0
    calc |Fu x₀| ≤ |F x₀| + |∑ i, Q.hess (a x₀ (e i)) (e i)| := abs_sub _ _
      _ ≤ MF + finrank ℝ E * (2 * ‖ℓ‖ / lam * Λ) := by
          gcongr; exact h2.trans (by gcongr)
      _ = _ := by ring
  have hu0 : ∀ y ∈ halfBall ν x₀ R, |u y| ≤ M₀ + |c| * R / lam + 2 * ‖ℓ‖ * R ^ 2 / lam := by
    intro y hy
    have hyR : ‖y - x₀‖ ≤ R := by rw [← dist_eq_norm]; exact hy.1
    have hq0 : q.const = 0 := rfl
    have hev := q.abs_eval_le (y - x₀)
    rw [hq0, abs_zero, zero_add] at hev
    have h1 : ‖q.lin‖ * ‖y - x₀‖ ≤ |c| / lam * R :=
      mul_le_mul hlin hyR (norm_nonneg _) (by positivity)
    have h2 : ‖q.quad‖ * ‖y - x₀‖ ^ 2 ≤ 2 * ‖ℓ‖ / lam * R ^ 2 :=
      mul_le_mul hBℓ (pow_le_pow_left₀ (norm_nonneg _) hyR 2) (by positivity) hBq0
    have e1 : u y = (w y - w x₀) - q.eval (y - x₀) := by simp only [hu, hQe]; ring
    rw [e1]
    calc |(w y - w x₀) - q.eval (y - x₀)| ≤ |w y - w x₀| + |q.eval (y - x₀)| := abs_sub _ _
      _ ≤ M₀ + (|c| / lam * R + 2 * ‖ℓ‖ / lam * R ^ 2) := add_le_add (hM₀ y hy) (by linarith)
      _ = _ := by ring
  have hD2u : ∀ y ∈ ball x₀ R ∩ openHalfSpace ν, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤
      M₂ + 2 * ‖ℓ‖ / lam := fun y hy ↦ by
    simp only [hu]
    rw [fderiv_fderiv_sub_eval hU hw2 hy Q]
    exact (norm_sub_le _ _).trans (add_le_add (hD2 y hy) hhess)
  have hconu : ∀ y ∈ ball x₀ R, y ∈ flatPart ν → ∃ d : ℝ,
      HasDerivWithinAt (fun t : ℝ ↦ u (y + t • a x₀ ν)) d (Ici 0) 0 ∧
        |d| ≤ G * dist y x₀ ^ (1 + α) := by
    intro y hy hyf
    obtain ⟨d, hd, hdb⟩ := hcon y hy hyf
    have hline : HasDerivAt (fun t : ℝ ↦ y + t • a x₀ ν) (a x₀ ν) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (a x₀ ν)).const_add y
    have hQd : HasFDerivAt Q.eval (Q.lin + Q.hess y) (y + (0 : ℝ) • a x₀ ν) := by
      rw [zero_smul, add_zero]; exact Q.hasFDerivAt_eval y
    have hQline := hQd.comp_hasDerivAt (0 : ℝ) hline
    have hval : (Q.lin + Q.hess y) (a x₀ ν) = c + ℓ (y - x₀) := by
      have hflat : ⟪ν, y - x₀⟫ = 0 := by
        rw [inner_sub_right, real_inner_comm, mem_flatPart.1 hyf, real_inner_comm, hx₀', sub_self]
      have hQl : Q.lin + Q.hess y = q.lin + q.hess (y - x₀) := by
        rw [hQh]
        ext v
        simp only [hQ, QuadPoly.add_lin, QuadPoly.shift_lin, add_apply, map_sub, map_neg,
          neg_apply, sub_apply, add_zero]
        ring
      rw [hQl, QuadPoly.conormalPoly_deriv hμ0.ne' ℓ hflat hνaν]
    rw [hval] at hQline
    refine ⟨d - (c + ℓ (y - x₀)), hd.sub hQline.hasDerivWithinAt, ?_⟩
    rw [show d - (c + ℓ (y - x₀)) = d - c - ℓ (y - x₀) by ring]; exact hdb
  obtain ⟨P', hcons, hPc, hPe⟩ := hexp hν a Fu u x₀ R
    (M₀ + |c| * R / lam + 2 * ‖ℓ‖ * R ^ 2 / lam) (M₂ + 2 * ‖ℓ‖ / lam)
    (MF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Λ) Ka (KF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Ka) G hx₀
    hR hKa (by positivity) (by positivity) hG (hwc.sub Q.continuous_eval.continuousOn) hu2 hequ
    hell hbd hsymm ha hFuH hFux hu0 hD2u hconu
  rw [← hN] at hPc hPe
  refine ⟨P' + q + ⟨w x₀, 0, 0⟩, ?_, ?_, fun y hy hyd ↦ ?_⟩
  · rw [hess_add_poly, hess_add_poly, hess_const_poly, add_zero]
    simp only [add_apply, Finset.sum_add_distrib, hcons, hFu, hQh]
    ring
  · have h1 : R ^ 2 * ‖P'.quad‖ ≤ C * N := by
      have : 0 ≤ R * ‖P'.lin‖ := by positivity
      linarith [abs_nonneg P'.const]
    have h2 : ‖(P' + q + ⟨w x₀, 0, 0⟩ : QuadPoly E).quad‖ ≤ ‖P'.quad‖ + ‖q.quad‖ := by
      simp only [QuadPoly.add_quad, add_zero]; exact norm_add_le _ _
    calc R ^ 2 * ‖(P' + q + ⟨w x₀, 0, 0⟩ : QuadPoly E).quad‖ ≤
          R ^ 2 * (‖P'.quad‖ + ‖q.quad‖) := by gcongr
      _ ≤ C * N + R ^ 2 * (2 * ‖ℓ‖ / lam) := by nlinarith [sq_nonneg R]
  · have := hPe y hy hyd
    have e1 : w y - (P' + q + ⟨w x₀, 0, 0⟩ : QuadPoly E).eval (y - x₀) =
        u y - P'.eval (y - x₀) := by
      simp only [QuadPoly.eval_add, hu, hQe]; simp [QuadPoly.eval]; ring
    rw [e1]; exact this

end Nondiv


namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- **Boundary expansions for the conormal problem.** Under the hypotheses of the tier-1
conormal theorem, with the finite bounds obtained by compactness given as parameters, every flat
point `p` of `halfBall ν x (r/2)` carries a boundary expansion of `w` with
`tr (a(p) D²P) = F(p)` and constants independent of `p`. -/
theorem boundary_expansions_conormal {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    ∃ Cb κb : ℝ, 0 ≤ Cb ∧ 0 < κb ∧ ∀ {ν x : E} {r : ℝ} {a : E → E →L[ℝ] E} {F w γ : E → ℝ}
      {β : E → E} {Mw M₂ M₁ M₂w MDβ MDγ Mγ MF Ka KF Kγ Kβ G Bℓ Nb : ℝ},
      ‖ν‖ = 1 → ⟪x, ν⟫ = 0 → 0 < r → 0 ≤ Ka → 0 ≤ KF → 0 ≤ M₂ → 0 ≤ Kγ → 0 ≤ Kβ → 0 ≤ M₁ →
      0 ≤ M₂w → 0 ≤ MDβ → 0 ≤ Mw →
      IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
      (∀ y ∈ halfBall ν x r, ∀ y' ∈ halfBall ν x r, ‖a y - a y'‖ ≤ Ka * dist y y' ^ (α : ℝ)) →
      (∀ y ∈ halfBall ν x r, ∀ y' ∈ halfBall ν x r, |F y - F y'| ≤ KF * dist y y' ^ (α : ℝ)) →
      (∀ y ∈ halfBall ν x r, |F y| ≤ MF) →
      ContDiffOn ℝ 2 w (halfBall ν x r) → (∀ y ∈ halfBall ν x r, |w y| ≤ Mw) →
      (∀ y ∈ ball x r ∩ openHalfSpace ν, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M₂) →
      (∀ y ∈ halfBall ν x r, ‖fderivWithin ℝ w (halfBall ν x r) y‖ ≤ M₁) →
      (∀ y ∈ halfBall ν x r,
        ‖fderivWithin ℝ (fderivWithin ℝ w (halfBall ν x r)) (halfBall ν x r) y‖ ≤ M₂w) →
      (∀ y ∈ ball x r ∩ openHalfSpace ν, ∑ i, fderiv ℝ (fderiv ℝ w) y
        (a y (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F y) →
      DifferentiableOn ℝ β (halfBall ν x r) → DifferentiableOn ℝ γ (halfBall ν x r) →
      (∀ y ∈ halfBall ν x r, ∀ y' ∈ halfBall ν x r,
        ‖fderivWithin ℝ γ (halfBall ν x r) y - fderivWithin ℝ γ (halfBall ν x r) y'‖ ≤
          Kγ * dist y y' ^ (α : ℝ)) →
      (∀ y ∈ halfBall ν x r, ∀ y' ∈ halfBall ν x r,
        ‖fderivWithin ℝ β (halfBall ν x r) y - fderivWithin ℝ β (halfBall ν x r) y'‖ ≤
          Kβ * dist y y' ^ (α : ℝ)) →
      (∀ y ∈ halfBall ν x r, ‖fderivWithin ℝ β (halfBall ν x r) y‖ ≤ MDβ) →
      (∀ y ∈ halfBall ν x r, ‖fderivWithin ℝ γ (halfBall ν x r) y‖ ≤ MDγ) →
      (∀ y ∈ halfBall ν x r, |γ y| ≤ Mγ) →
      (∀ y ∈ halfBall ν x r ∩ flatPart ν, β y = a y ν) →
      HasConormalBC ν a γ (halfBall ν x r) w →
      G = Kγ + Kβ * M₁ + MDβ * M₂w * (2 * r) ^ (1 - (α : ℝ)) → Bℓ = MDγ + M₁ * MDβ →
      Nb = 2 * Mw + Mγ * (r / 2) / lam + 2 * Bℓ * (r / 2) ^ 2 / lam +
        (r / 2) ^ 2 * (MF + finrank ℝ E * (2 * Bℓ / lam) * Λ) +
        (r / 2) ^ (2 + (α : ℝ)) * (KF + finrank ℝ E * (2 * Bℓ / lam) * Ka +
          finrank ℝ E * Ka * (M₂ + 2 * Bℓ / lam) + G) →
      ∀ p ∈ halfBall ν x (r / 2), p ∈ flatPart ν → ∃ P : QuadPoly E,
        ∑ i, P.hess (a p (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = F p ∧
        ‖P.quad‖ ≤ (Cb * Nb + (r / 2) ^ 2 * (2 * Bℓ / lam)) / (r / 2) ^ 2 ∧
        ∀ y ∈ halfBall ν x r, dist y p < κb * (r / 2) →
          |w y - P.eval (y - p)| ≤
            Cb * Nb / (r / 2) ^ (2 + (α : ℝ)) * dist y p ^ (2 + (α : ℝ)) := by
  have hαr : 0 < (α : ℝ) ∧ (α : ℝ) < 1 := ⟨hα0, hα1⟩
  obtain ⟨Cb, κb, hCb, hκb, hexpb⟩ := expansion_at_flat_point_conormal_affine (E := E) hαr
    hlam hlamΛ
  refine ⟨Cb, κb, hCb, hκb, ?_⟩
  intro ν x r a F w γ β Mw M₂ M₁ M₂w MDβ MDγ Mγ MF Ka KF Kγ Kβ G Bℓ Nb hν hx hr hKa hKF hM₂0
    hKγ hKβ hM₁0 hM₂w0 hMDβ0 hMw0 hell hsym ha' hFH hFb hw hu0 hD2 hM₁ hM₂w heq hβd hγd hγH hβH
    hMDβ hMDγ hMγ hβa hbc hG hBℓ hNb p hp hpf
  obtain ⟨hcv, hcp, hsU, hdiam, hUs⟩ := halfBall_facts hν hx hr
  set s := halfBall ν x r with hs
  set U := ball x r ∩ openHalfSpace ν with hUdef
  have hxs : x ∈ s := ⟨mem_closedBall_self hr.le, hx.ge⟩
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hell x hxs).2
  have hMDγ0 : 0 ≤ MDγ := (norm_nonneg _).trans (hMDγ x hxs)
  have hMγ0 : 0 ≤ Mγ := (abs_nonneg _).trans (hMγ x hxs)
  have hMF0 : 0 ≤ MF := (abs_nonneg _).trans (hFb x hxs)
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hBℓ0 : 0 ≤ Bℓ := by rw [hBℓ]; positivity
  set R := r / 2 with hR_def
  have hR : 0 < R := by positivity
  have hps : p ∈ s := halfBall_mono ν x (by linarith) hp
  have hpR : halfBall ν p R ⊆ s := fun y hy ↦ ⟨by
    have h1 : dist y p ≤ R := hy.1
    have h2 : dist p x ≤ r / 2 := hp.1
    rw [mem_closedBall]
    linarith [dist_triangle y p x], hy.2⟩
  have hpB : ball p R ⊆ ball x r := fun y hy ↦ by
    have h1 : dist y p < R := hy
    have h2 : dist p x ≤ r / 2 := hp.1
    rw [mem_ball]
    linarith [dist_triangle y p x]
  have hpU : ball p R ∩ openHalfSpace ν ⊆ U := fun y hy ↦ ⟨hpB hy.1, hy.2⟩
  set c := γ p with hc
  set ℓ := fderivWithin ℝ γ s p -
    (innerSL ℝ (gradientWithin w s p)).comp (fderivWithin ℝ β s p) with hℓ
  have hℓn : ‖ℓ‖ ≤ Bℓ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(innerSL ℝ (gradientWithin w s p)).comp (fderivWithin ℝ β s p)‖ ≤
        M₁ * MDβ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [innerSL_apply_norm, gradientWithin, LinearIsometryEquiv.norm_map]
      exact mul_le_mul (hM₁ p hps) (hMDβ p hps) (norm_nonneg _) hM₁0
    rw [hBℓ]; linarith [hMDγ p hps]
  have hcn : |c| ≤ Mγ := hMγ p hps
  have hcon : ∀ y ∈ ball p R, y ∈ flatPart ν → ∃ d : ℝ,
      HasDerivWithinAt (fun t : ℝ ↦ w (y + t • a p ν)) d (Ici 0) 0 ∧
        |d - c - ℓ (y - p)| ≤ G * dist y p ^ (1 + (α : ℝ)) := by
    intro y hy hyf
    have hyx : y ∈ ball x r := hpB hy
    have hys : y ∈ s := ⟨ball_subset_closedBall hyx, flatPart_subset_halfSpace ν hyf⟩
    have hνin : 0 ≤ ⟪a p ν, ν⟫ := by
      have := (hell p hps).1 ν
      nlinarith [norm_nonneg ν, sq_nonneg ‖ν‖]
    refine ⟨_, hasDerivWithinAt_line_of_inward hyx hys.2 hνin
      ((hw.differentiableOn (by norm_num)) y hys), ?_⟩
    have hd : fderivWithin ℝ w s y (a p ν) =
        γ y - ⟪β y - β p, gradientWithin w s y⟫ := by
      rw [← inner_gradientWithin_eq, ← hβa p ⟨hps, hpf⟩, inner_sub_left,
        hβa y ⟨hys, hyf⟩, hbc y ⟨hys, hyf⟩]
      ring
    rw [hd, show γ y - ⟪β y - β p, gradientWithin w s y⟫ - c - ℓ (y - p) =
      (γ y - ⟪β y - β p, gradientWithin w s y⟫) - (γ p + ℓ (y - p)) by rw [hc]; ring, hG]
    exact abs_conormalData_sub_le hcv hsU hαr hβd hγd hw hKγ hKβ hM₂w0 hMDβ0 hγH hβH hMDβ
      hM₁ hM₂w hdiam hps hys
  obtain ⟨P, hcons, hPq, hPe⟩ := hexpb hν a F w p R (2 * Mw) M₂ MF Ka KF G c
    (2 * Mw + |c| * R / lam + 2 * ‖ℓ‖ * R ^ 2 / lam +
      R ^ 2 * (MF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Λ) +
      R ^ (2 + (α : ℝ)) * (KF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Ka +
        finrank ℝ E * Ka * (M₂ + 2 * ‖ℓ‖ / lam) + G)) ℓ hpf hR hKa hKF hM₂0 hG0
    (hw.continuousOn.mono hpR) ((hw.mono hUs).mono hpU) (fun y hy ↦ heq y (hpU hy))
    (hell p hps).1 (hell p hps).2 (hsym p hps) (fun y hy ↦ ha' y (hUs (hpU hy)) p hps)
    (fun y hy ↦ hFH y (hUs (hpU hy)) p hps) (hFb p hps)
    (fun y hy ↦ by
      have h1 := hu0 y (hpR hy)
      have h2 := hu0 p hps
      calc |w y - w p| ≤ |w y| + |w p| := abs_sub _ _
        _ ≤ 2 * Mw := by linarith)
    (fun y hy ↦ hD2 y (hpU hy)) hcon rfl
  have hNle : 2 * Mw + |c| * R / lam + 2 * ‖ℓ‖ * R ^ 2 / lam +
      R ^ 2 * (MF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Λ) +
      R ^ (2 + (α : ℝ)) * (KF + finrank ℝ E * (2 * ‖ℓ‖ / lam) * Ka +
        finrank ℝ E * Ka * (M₂ + 2 * ‖ℓ‖ / lam) + G) ≤ Nb := by
    rw [hNb]
    gcongr
  refine ⟨P, hcons, ?_, fun y hy hyd ↦ ?_⟩
  · rw [le_div_iff₀ (by positivity), mul_comm]
    refine hPq.trans ?_
    gcongr
  · have hdγ : 0 ≤ (dist y p / R) ^ (2 + (α : ℝ)) := by positivity
    calc _ ≤ _ := hPe y hy.2 hyd
      _ ≤ Cb * Nb * (dist y p / R) ^ (2 + (α : ℝ)) := by gcongr
      _ = _ := by rw [Real.div_rpow dist_nonneg hR.le]; ring

end Nondiv

end BasicElliptic
