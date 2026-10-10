/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Quasilinear.HigherOrder
public import BasicElliptic.Holder.DirHolder
import BasicElliptic.Div.Higher.SecondOrder
import BasicElliptic.Holder.Closure
import BasicElliptic.Holder.Algebra
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The `k`-induction: `C^{k+1}` up to the flat part for quasilinear conormal solutions

`Div.contDiffOn_halfBall_of_quasilinear_conormal_add_two`: a `C¹` quasilinear conormal solution
with `Φ ∈ C^{k+2}(U)` (`DΦ` symmetric, uniformly elliptic on the open convex `U ⊇ ∇w(B⁺)`) is
`C^{k+2}` on `halfBall ν x (r/2)`. This is the case `k + 1` of
`Div.QuasilinearConormalStatement`.

## Proof

Hölder regularity is carried through the induction in the scalar directional classes
`Div.DirHolderOn α m` (`Holder/DirHolder.lean`); vector and operator fields enter through
their components `⟪p, G y⟫`, `⟪p, a y q⟫`. All statements are local, at the centre `z` of a half
ball with `⟪z, ν⟫ ≥ 0`.

* **Linear induction** (`Div.linear_dirHolderOn`): for a conormal problem
  `∫ ⟪a ∇u, ∇φ⟫ = ∫ ⟪G, ∇φ⟫` on `halfBall ν z s` with symmetric uniformly elliptic `a` and
  `a, G ∈ C^{m+1,α}`, `u` is `C^{m+2,α}` on a smaller half ball. `m = 0` is the linear `C^{2,α}`
  theorem (`Div.exists_hessian_halfBall_of_linear`). For `m + 1`: by induction `u ∈ C^{m+2,α}`, so
  the tangential derivatives `∂_e u` solve the problem with coefficient `a` and flux
  `∂_e G - (∂_e a) ∇u ∈ C^{m+1,α}` (`IsConormalSolOn.isConormalSolOn_fderivWithin_apply`), hence are
  `C^{m+2,α}`; the equation `Σ_j D²u(b_j, a b_j) = R` (`Div.sum_hessianWithin_eq_of_linear`)
  then gives `u ∈ C^{m+3,α}` (`Div.dirHolderOn_add_two_of_rows`).
* **Quasilinear induction** (`Div.quasilinear_dirHolderOn`): with `Φ ∈ C^{k+2}`, `w` is
  `C^{k+2,α}` near every point of `ball x r ∩ halfSpace ν`. `k = 0` is
  `Div.exists_hessian_holder_halfBall`. For `k + 1`: `a = DΦ(∇w) ∈ C^{k+1,α}`
  (`Div.DirHolderOn.comp`), the tangential derivatives solve the linear problem with coefficient
  `a` and no data (`IsQuasilinearConormalSolOn.isConormalSolOn_fderivWithin_apply`), so the linear
  induction gives them in `C^{k+2,α}`, and the equation `tr (a D²w) = 0` gives `w ∈ C^{k+3,α}`.
-/

public section

open MeasureTheory Metric Set Filter RealInnerProductSpace
open scoped Gradient Topology NNReal ContDiff

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Components -/

section Components

omit [MeasurableSpace E] [BorelSpace E]

variable {S : Set E} {α : ℝ≥0}

/-- A vector field whose components are `DirHolderOn α 1` is `C¹` with an `α`-Hölder
within-derivative. -/
theorem contDiffOn_one_holder_of_components (hS : UniqueDiffOn ℝ S) (hα : 0 < α) {G : E → E}
    (hG : ∀ p, DirHolderOn α 1 (fun y ↦ ⟪p, G y⟫) S) :
    ContDiffOn ℝ 1 G S ∧ ∃ C, HolderOnWith C α (fderivWithin ℝ G S) S := by
  set b := stdOrthonormalBasis ℝ E
  have hexp : G = fun y ↦ ∑ i, ⟪b i, G y⟫ • b i := by
    funext y; exact (b.sum_repr' (G y)).symm
  rw [hexp]
  exact DirHolderOn.contDiffOn_one_and_holder_of_sum hS hα (fun i ↦ hG (b i)) b

/-- An operator field whose matrix entries are `DirHolderOn α 1` is `C¹` with an `α`-Hölder
within-derivative. -/
theorem contDiffOn_one_holder_of_components_clm (hS : UniqueDiffOn ℝ S) (hα : 0 < α)
    {a : E → E →L[ℝ] E} (ha : ∀ p q, DirHolderOn α 1 (fun y ↦ ⟪p, a y q⟫) S) :
    ContDiffOn ℝ 1 a S ∧ ∃ C, HolderOnWith C α (fderivWithin ℝ a S) S := by
  set b := stdOrthonormalBasis ℝ E
  have hexp : a = fun y ↦ ∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      ⟪b p.1, a y (b p.2)⟫ • (innerSL ℝ (b p.2)).smulRight (b p.1) := by
    funext y; exact clm_eq_sum_inner b (a y)
  rw [hexp]
  exact DirHolderOn.contDiffOn_one_and_holder_of_sum hS hα
    (fun p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ↦ ha (b p.1) (b p.2)) _

omit [FiniteDimensional ℝ E] in
/-- Components of the within-derivative of a vector field. -/
theorem inner_fderivWithin_apply {G : E → E} {y : E} (hS : UniqueDiffWithinAt ℝ S y)
    (hG : DifferentiableWithinAt ℝ G S y) (p v : E) :
    ⟪p, fderivWithin ℝ G S y v⟫ = fderivWithin ℝ (fun y ↦ ⟪p, G y⟫) S y v := by
  have h : HasFDerivWithinAt (fun y ↦ ⟪p, G y⟫) ((innerSL ℝ p).comp (fderivWithin ℝ G S y))
      S y := (innerSL ℝ p).hasFDerivAt.comp_hasFDerivWithinAt y hG.hasFDerivWithinAt
  rw [h.fderivWithin hS]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Entries of the within-derivative of an operator field. -/
theorem inner_fderivWithin_apply_clm {a : E → E →L[ℝ] E} {y : E}
    (hS : UniqueDiffWithinAt ℝ S y) (ha : DifferentiableWithinAt ℝ a S y) (p v q : E) :
    ⟪p, fderivWithin ℝ a S y v q⟫ = fderivWithin ℝ (fun y ↦ ⟪p, a y q⟫) S y v := by
  have h : HasFDerivWithinAt (fun y ↦ ⟪p, a y q⟫)
      ((innerSL ℝ p).comp ((ContinuousLinearMap.apply ℝ E q).comp (fderivWithin ℝ a S y)))
      S y :=
    (innerSL ℝ p).hasFDerivAt.comp_hasFDerivWithinAt y
      ((ContinuousLinearMap.apply ℝ E q).hasFDerivAt.comp_hasFDerivWithinAt y
        ha.hasFDerivWithinAt)
  rw [h.fderivWithin hS]
  rfl

omit [FiniteDimensional ℝ E] in
/-- `⟪p, A ξ⟫ = Σ_l ⟪b_l, ξ⟫ ⟪p, A b_l⟫`. -/
theorem inner_apply_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) (p ξ : E) : ⟪p, A ξ⟫ = ∑ l, ⟪b l, ξ⟫ * ⟪p, A (b l)⟫ := by
  conv_lhs => rw [← b.sum_repr' ξ]
  simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]

omit [FiniteDimensional ℝ E] in
/-- `v = Σ_i ⟪b_i, v⟫ (b_i - ⟪b_i, ν⟫ ν) + ⟪v, ν⟫ ν`. -/
theorem eq_sum_tangential_add {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (ν v : E) :
    v = ∑ i, ⟪b i, v⟫ • (b i - ⟪b i, ν⟫ • ν) + ⟪v, ν⟫ • ν := by
  simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul]
  rw [b.sum_repr' v]
  have : ∑ i, ⟪b i, v⟫ * ⟪b i, ν⟫ = ⟪v, ν⟫ := by
    rw [← b.sum_inner_mul_inner v ν]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm (b i) v]
  rw [this]
  abel

end Components

/-! ### The linear equation up to the flat part -/

/-- **The linear equation `Σ_j D²u(b_j, a b_j) = R` at every point of a half ball** on which `u` is
`C²` (`f = 0`; by continuity from the interior, `Div.sum_hessian_coeff_eq`). -/
theorem sum_hessianWithin_eq_of_linear {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν x : E} {r : ℝ}
    (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) {lam Λ : ℝ} (hlam : 0 < lam)
    {a : E → E →L[ℝ] E} {G : E → E} {u : E → ℝ}
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν x r)) (hsym : IsSymmetricOn a (halfBall ν x r))
    (ha : ContDiffOn ℝ 1 a (halfBall ν x r)) {Kda : ℝ≥0}
    (hDa : HolderOnWith Kda α (fderivWithin ℝ a (halfBall ν x r)) (halfBall ν x r))
    (hG : ContDiffOn ℝ 1 G (halfBall ν x r)) {Kdg : ℝ≥0}
    (hDG : HolderOnWith Kdg α (fderivWithin ℝ G (halfBall ν x r)) (halfBall ν x r))
    (h : IsConormalSolOn ν a G 0 x r u) {z : E} (hz : 0 ≤ ⟪z, ν⟫) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall z ρ ⊆ ball x r) (hC2 : ContDiffOn ℝ 2 u (halfBall ν z ρ))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {y : E} (hy : y ∈ halfBall ν z ρ) :
    ∑ j, fderivWithin ℝ (fderivWithin ℝ u (halfBall ν z ρ)) (halfBall ν z ρ) y (b j)
        (a y (b j)) =
      -∑ j, ⟪b j, fderivWithin ℝ a (halfBall ν x r) y (b j)
          (gradientWithin u (halfBall ν x r) y)⟫ +
        ∑ j, ⟪b j, fderivWithin ℝ G (halfBall ν x r) y (b j)⟫ := by
  set S := halfBall ν z ρ with hS
  set B := halfBall ν x r with hB
  have huS := uniqueDiffOn_halfBall hν hρ (by linarith : -ρ < ⟪z, ν⟫)
  have hBu := uniqueDiffOn_halfBall hν hr hx
  have hSB : S ⊆ B := fun y hy ↦ ⟨ball_subset_closedBall (hball hy.1), hy.2⟩
  have hgc : ContinuousOn (gradientWithin u B) B :=
    continuousOn_gradientWithin_halfBall hν hr hx h.1
  have hHc : ContinuousOn (fderivWithin ℝ (fderivWithin ℝ u S) S) S :=
    (hC2.fderivWithin huS (by norm_num : ((1 : ℕ) : ℕ∞ω) + 1 ≤ 2)).continuousOn_fderivWithin huS
      le_rfl
  have hDac : ContinuousOn (fderivWithin ℝ a B) B := ha.continuousOn_fderivWithin hBu le_rfl
  have hDGc : ContinuousOn (fderivWithin ℝ G B) B := hG.continuousOn_fderivWithin hBu le_rfl
  set F : E → ℝ := fun y ↦ ∑ j, fderivWithin ℝ (fderivWithin ℝ u S) S y (b j) (a y (b j)) -
    (-∑ j, ⟪b j, fderivWithin ℝ a B y (b j) (gradientWithin u B y)⟫ +
      ∑ j, ⟪b j, fderivWithin ℝ G B y (b j)⟫) with hF
  have hFc : ContinuousOn F S := by
    refine (continuousOn_finsetSum _ fun j _ ↦ (hHc.clm_apply continuousOn_const).clm_apply
      ((ha.continuousOn.mono hSB).clm_apply continuousOn_const)).sub
      ((continuousOn_finsetSum _ fun j _ ↦ continuousOn_const.inner
        (((hDac.mono hSB).clm_apply continuousOn_const).clm_apply (hgc.mono hSB))).neg.add
      (continuousOn_finsetSum _ fun j _ ↦ continuousOn_const.inner
        ((hDGc.mono hSB).clm_apply continuousOn_const)))
  set Ω' := interior S with hΩ'
  have hΩ'o : IsOpen Ω' := isOpen_interior
  have hΩ'S : Ω' ⊆ S := interior_subset
  have hΩ'Ω : Ω' ⊆ ball x r ∩ openHalfSpace ν := fun y hy ↦
    ⟨hball (hΩ'S hy).1, subset_openHalfSpace_of_isOpen hν hΩ'o (hΩ'S.trans fun _ h ↦ h.2) hy⟩
  have hF0 : ∀ y ∈ Ω', F y = 0 := by
    intro y hy
    have hyx := hΩ'Ω hy
    have heq : fderivWithin ℝ u S =ᶠ[𝓝 y] fderiv ℝ u := by
      filter_upwards [hΩ'o.mem_nhds hy] with z hz
      exact fderivWithin_of_mem_nhds (mem_of_superset (hΩ'o.mem_nhds hz) hΩ'S)
    have h1 : fderivWithin ℝ (fderivWithin ℝ u S) S y = fderiv ℝ (fderiv ℝ u) y := by
      rw [fderivWithin_of_mem_nhds (mem_of_superset (hΩ'o.mem_nhds hy) hΩ'S), heq.fderiv_eq]
    have := sum_hessian_coeff_eq hα hα1 hν hr hx hlam hell hsym ha hDa hG hDG
      continuous_const (Kf := 0) (holderOnWith_const 0 0 α _) h b hyx
    simp only [hF, h1, this]
    ring
  have hcl : closure Ω' = S := by
    rw [hΩ', (convex_halfBall ν z ρ).closure_interior_eq_closure_of_nonempty_interior
      (interior_halfBall_nonempty hν hρ (by linarith)), (isClosed_halfBall ν z ρ).closure_eq]
  have hmem := ((hFc y hy).mono hΩ'S).mem_closure_image (by rw [hcl]; exact hy)
  have hsub : F '' Ω' ⊆ {0} := by rintro _ ⟨y, hy, rfl⟩; exact hF0 y hy
  have := closure_mono hsub hmem
  rw [closure_singleton, mem_singleton_iff] at this
  simp only [hF] at this
  linarith

/-! ### Assembly in the directional Hölder classes -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Higher Hölder regularity from the tangential rows and the equation.** On a compact convex
`S` with unique derivatives, let `w ∈ C²(S)` have a symmetric within Hessian `H` with
`Σ_j H(b_j, A b_j) = R`, `A` symmetric with `⟪A ν, ν⟫ ≥ c > 0`. If the tangential rows
`D_S w(·) (b_i - ⟪b_i, ν⟫ ν)` are `C^{m+1,α}` and the entries of `A` and `R` are `C^{m,α}`, then
`w` is `C^{m+2,α}` on `S`. -/
theorem dirHolderOn_add_two_of_rows {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {ν : E} {S : Set E} (hS : UniqueDiffOn ℝ S) (hSc : IsCompact S) (hScv : Convex ℝ S)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) {w : E → ℝ} (hw : ContDiffOn ℝ 2 w S)
    (hsymm : ∀ y ∈ S, ∀ u v, fderivWithin ℝ (fderivWithin ℝ w S) S y u v =
      fderivWithin ℝ (fderivWithin ℝ w S) S y v u)
    {A : E → E →L[ℝ] E} (hAs : ∀ y ∈ S, (A y : E →ₗ[ℝ] E).IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hApos : ∀ y ∈ S, c ≤ ⟪A y ν, ν⟫) {R : E → ℝ}
    (heq : ∀ y ∈ S, ∑ j, fderivWithin ℝ (fderivWithin ℝ w S) S y (b j) (A y (b j)) = R y)
    {m : ℕ} (hA : ∀ p q, DirHolderOn α m (fun y ↦ ⟪p, A y q⟫) S)
    (hR : DirHolderOn α m R S)
    (hrows : ∀ i, DirHolderOn α (m + 1) (fun y ↦ fderivWithin ℝ w S y (b i - ⟪b i, ν⟫ • ν)) S) :
    DirHolderOn α (m + 2) w S := by
  set D := fderivWithin ℝ w S with hD
  set H := fderivWithin ℝ D S with hH
  have hD1 : ContDiffOn ℝ 1 D S := hw.fderivWithin hS (by norm_num)
  have hDd : ∀ y ∈ S, HasFDerivWithinAt D (H y) S y := fun y hy ↦
    ((hD1.differentiableOn one_ne_zero) y hy).hasFDerivWithinAt
  set e : ι → E := fun i ↦ b i - ⟪b i, ν⟫ • ν with he
  set g : ι → E → E →L[ℝ] ℝ := fun i ↦ fderivWithin ℝ (fun y ↦ D y (e i)) S with hg
  have hrowd : ∀ i, ∀ y ∈ S, HasFDerivWithinAt (fun y ↦ D y (e i))
      ((ContinuousLinearMap.apply ℝ ℝ (e i)) ∘L H y) S y := fun i y hy ↦
    (ContinuousLinearMap.apply ℝ ℝ (e i)).hasFDerivAt.comp_hasFDerivWithinAt y (hDd y hy)
  have hgi : ∀ y ∈ S, ∀ i ξ, g i y ξ = H y ξ (e i) := fun y hy i ξ ↦ by
    simp only [hg]
    rw [(hrowd i y hy).fderivWithin (hS y hy)]
    rfl
  have hgP : ∀ i q, DirHolderOn α m (fun y ↦ g i y q) S := fun i q ↦ (hrows i).2 q
  have hAP' : ∀ p q, DirHolderOn α m (fun y ↦ ⟪A y q, p⟫) S := fun p q ↦
    (hA p q).congr fun y _ ↦ real_inner_comm _ _
  have hmul : ∀ {f g : E → ℝ}, DirHolderOn α m f S → DirHolderOn α m g S →
      DirHolderOn α m (fun y ↦ f y * g y) S := fun hf hg ↦ hf.mul hS hSc hScv hα hα1 hg
  have hcmul : ∀ (k : ℝ) {f : E → ℝ}, DirHolderOn α m f S →
      DirHolderOn α m (fun y ↦ k * f y) S := fun k f hf ↦ hf.const_mul hS hSc hScv hα hα1 k
  -- the normal–normal derivative
  set nH : E → ℝ := fun y ↦ (R y - ∑ j, (∑ i, ⟪b i, A y (b j)⟫ * g i y (b j) +
    ⟪A y (b j), ν⟫ * ∑ i, ⟪b i, b j⟫ * g i y ν)) / ⟪A y ν, ν⟫ with hnH
  have hnHP : DirHolderOn α m nH S := by
    have hT : DirHolderOn α m (fun y ↦ ∑ j, (∑ i, ⟪b i, A y (b j)⟫ * g i y (b j) +
        ⟪A y (b j), ν⟫ * ∑ i, ⟪b i, b j⟫ * g i y ν)) S :=
      DirHolderOn.sum hS Finset.univ fun j _ ↦ (DirHolderOn.sum hS Finset.univ fun i _ ↦
        hmul (hA (b i) (b j)) (hgP i (b j))).add hS
        (hmul (hAP' ν (b j)) (DirHolderOn.sum hS Finset.univ fun i _ ↦ hcmul _ (hgP i ν)))
    refine (hmul (hR.sub hS hT) ((hAP' ν ν).inv hS hSc hScv hα hα1 hc hApos)).congr
      fun y _ ↦ ?_
    simp only [hnH, div_eq_mul_inv]
  have hνP : DirHolderOn α (m + 1) (fun y ↦ D y ν) S := by
    have h1 : ∀ y ∈ S, HasFDerivWithinAt (fun y ↦ D y ν)
        ((ContinuousLinearMap.apply ℝ ℝ ν) ∘L H y) S y := fun y hy ↦
      (ContinuousLinearMap.apply ℝ ℝ ν).hasFDerivAt.comp_hasFDerivWithinAt y (hDd y hy)
    refine ⟨fun y hy ↦ (h1 y hy).differentiableWithinAt, fun ξ ↦ ?_⟩
    refine ((DirHolderOn.sum hS Finset.univ fun i _ ↦ hcmul ⟪b i, ξ⟫ (hgP i ν)).add hS
      (hcmul ⟪ν, ξ⟫ hnHP)).congr fun y hy ↦ ?_
    rw [(h1 y hy).fderivWithin (hS y hy)]
    exact hessian_apply_normal_of_sum_eq b (H y) (hsymm y hy) (hAs y hy)
      (hc.trans_le (hApos y hy)).ne' (heq y hy) (hgi y hy) ξ
  refine ⟨hw.differentiableOn (by norm_num), fun v ↦ ?_⟩
  refine ((DirHolderOn.sum hS Finset.univ fun i _ ↦
    (hrows i).const_mul hS hSc hScv hα hα1 ⟪b i, v⟫).add hS
      (hνP.const_mul hS hSc hScv hα hα1 ⟪v, ν⟫)).congr fun y _ ↦ ?_
  conv_lhs => rw [eq_sum_tangential_add b ν v]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A positive number below finitely many positive numbers and below `s > 0`. -/
theorem exists_pos_lt_forall {ι : Type*} [Finite ι] {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i) {s : ℝ}
    (hs : 0 < s) : ∃ ε, 0 < ε ∧ ε < s ∧ ∀ i, ε < ρ i := by
  obtain ⟨ε, ⟨hεi, hεs⟩, hε⟩ := (((eventually_all.2 fun i ↦ mem_of_superset
    (Ioo_mem_nhdsGT (hρ i)) fun t ht ↦ ht.2).and (Ioo_mem_nhdsGT hs)).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  exact ⟨ε, hε, hεs.2, hεi⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem closure_interior_halfBall {ν z : E} {ρ : ℝ} (hν : ‖ν‖ = 1) (hρ : 0 < ρ)
    (hz : 0 ≤ ⟪z, ν⟫) : closure (interior (halfBall ν z ρ)) = halfBall ν z ρ := by
  rw [(convex_halfBall ν z ρ).closure_interior_eq_closure_of_nonempty_interior
    (interior_halfBall_nonempty hν hρ (by linarith)), (isClosed_halfBall ν z ρ).closure_eq]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem tangential_inner_eq_zero {ι : Type*} (b : ι → E) {ν : E} (hν : ‖ν‖ = 1) (i : ι) :
    ⟪b i - ⟪b i, ν⟫ • ν, ν⟫ = 0 := by
  simp only [inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν]
  ring

/-! ### The linear induction -/

/-- **Linear conormal `C^{m+2,α}`** (see the module docstring): for a conormal problem on
`halfBall ν z s` (`⟪z, ν⟫ ≥ 0`) with symmetric uniformly elliptic `a`, no `f`, and the entries of
`a` and the components of `G` in `C^{m+1,α}`, `u` is `C^{m+2,α}` on a smaller half ball around
`z`. -/
theorem linear_dirHolderOn {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {ν : E} (hν : ‖ν‖ = 1)
    (m : ℕ) : ∀ {z : E} {s lam Λ : ℝ} {a : E → E →L[ℝ] E} {G : E → E} {u : E → ℝ},
      0 < s → 0 ≤ ⟪z, ν⟫ → 0 < lam →
      IsUniformlyElliptic lam Λ a (halfBall ν z s) → IsSymmetricOn a (halfBall ν z s) →
      (∀ p q, DirHolderOn α (m + 1) (fun y ↦ ⟪p, a y q⟫) (halfBall ν z s)) →
      (∀ p, DirHolderOn α (m + 1) (fun y ↦ ⟪p, G y⟫) (halfBall ν z s)) →
      IsConormalSolOn ν a G 0 z s u →
      ∃ ρ, 0 < ρ ∧ ρ < s ∧ DirHolderOn α (m + 2) u (halfBall ν z ρ) := by
  have hα1' : α ≤ 1 := hα1.le
  induction m with
  | zero =>
    intro z s lam Λ a G u hs hz hlam hell hsym ha hG h
    have hBu := uniqueDiffOn_halfBall hν hs (by linarith : -s < ⟪z, ν⟫)
    obtain ⟨ha1, Kda, hKda⟩ := contDiffOn_one_holder_of_components_clm hBu hα ha
    obtain ⟨hG1, Kdg, hKdg⟩ := contDiffOn_one_holder_of_components hBu hα hG
    obtain ⟨ρ, hρ, Hs, hHs, C, hC⟩ := exists_hessian_halfBall_of_linear hα hα1 hν hs
      (by linarith) hlam hell hsym ha1 hKda hG1 hKdg continuous_const (Kf := 0)
      (holderOnWith_const 0 0 α _) h ⟨mem_ball_self hs, hz⟩
    set ρ' := min ρ (s / 2) with hρ'def
    have hρ' : 0 < ρ' := lt_min hρ (by positivity)
    have hS'ρ : halfBall ν z ρ' ⊆ halfBall ν z ρ := halfBall_mono ν z (min_le_left _ _)
    have hS'B : halfBall ν z ρ' ⊆ halfBall ν z s :=
      halfBall_mono ν z ((min_le_right _ _).trans (by linarith))
    have huS' := uniqueDiffOn_halfBall hν hρ' (by linarith : -ρ' < ⟪z, ν⟫)
    refine ⟨ρ', hρ', (min_le_right _ _).trans_lt (by linarith), ?_⟩
    exact DirHolderOn.of_hessian huS' (D := fderivWithin ℝ u (halfBall ν z s))
      (fun y hy ↦ ((h.1.differentiableOn one_ne_zero y (hS'B hy)).hasFDerivWithinAt).mono hS'B)
      (fun y hy ↦ (hHs y (hS'ρ hy)).mono hS'ρ) ⟨C, hC.mono hS'ρ⟩
  | succ m ih =>
    intro z s lam Λ a G u hs hz hlam hell hsym ha hG h
    set B := halfBall ν z s with hB
    have hBu := uniqueDiffOn_halfBall hν hs (by linarith : -s < ⟪z, ν⟫)
    have hBc := isCompact_halfBall ν z s
    have hBcv := convex_halfBall ν z s
    -- step 1: the induction hypothesis for `u`
    obtain ⟨ρ₁, hρ₁, hρ₁s, hu₁⟩ := ih hs hz hlam hell hsym
      (fun p q ↦ (ha p q).of_succ hBc hBcv hα hα1') (fun p ↦ (hG p).of_succ hBc hBcv hα hα1') h
    set T := halfBall ν z ρ₁ with hT
    have huT := uniqueDiffOn_halfBall hν hρ₁ (by linarith : -ρ₁ < ⟪z, ν⟫)
    have hTc := isCompact_halfBall ν z ρ₁
    have hTcv := convex_halfBall ν z ρ₁
    have hTB : T ⊆ B := halfBall_mono ν z hρ₁s.le
    have hballT : closedBall z ρ₁ ⊆ ball z s := closedBall_subset_ball hρ₁s
    have hC2T : ContDiffOn ℝ 2 u T := by
      have := (hu₁.of_le hTc hTcv hα hα1' (n := 2) (by omega)).contDiffOn hα
      exact_mod_cast this
    have haT : ∀ p q, DirHolderOn α (m + 2) (fun y ↦ ⟪p, a y q⟫) T := fun p q ↦
      (ha p q).mono hTB huT
    have hGT : ∀ p, DirHolderOn α (m + 2) (fun y ↦ ⟪p, G y⟫) T := fun p ↦ (hG p).mono hTB huT
    obtain ⟨ha1T, -⟩ := contDiffOn_one_holder_of_components_clm huT hα fun p q ↦
      (haT p q).of_le hTc hTcv hα hα1' (by omega)
    obtain ⟨hG1T, -⟩ := contDiffOn_one_holder_of_components huT hα fun p ↦
      (hGT p).of_le hTc hTcv hα hα1' (by omega)
    have huB : DifferentiableOn ℝ u B := h.1.differentiableOn one_ne_zero
    set gu := gradientWithin u B with hgu
    have hguT : ∀ l, DirHolderOn α (m + 1) (fun y ↦ ⟪l, gu y⟫) T := fun l ↦
      (hu₁.2 l).congr fun y hy ↦ by
        rw [real_inner_comm, hgu, gradientWithin, InnerProductSpace.toDual_symm_apply,
          ← fderivWithin_subset hTB (huT y hy) (huB y (hTB hy))]
    -- step 2: the tangential derivatives solve linear problems
    set s₂ := ρ₁ / 2 with hs₂
    have hs₂0 : 0 < s₂ := by positivity
    set S₂ := halfBall ν z s₂ with hS₂
    have huS₂ := uniqueDiffOn_halfBall hν hs₂0 (by linarith : -s₂ < ⟪z, ν⟫)
    have hS₂T : S₂ ⊆ T := halfBall_mono ν z (by linarith)
    set b := stdOrthonormalBasis ℝ E with hb
    set e : Fin (Module.finrank ℝ E) → E := fun i ↦ b i - ⟪b i, ν⟫ • ν with he
    have hlin : ∀ i, IsConormalSolOn ν a (fun y ↦ fderivWithin ℝ G T y (e i) -
        fderivWithin ℝ a T y (e i) (gu y)) 0 z s₂ (fun y ↦ fderivWithin ℝ u B y (e i)) :=
      fun i ↦ h.isConormalSolOn_fderivWithin_apply hν hs (by linarith) hs₂0 (by linarith) hz
        hballT hC2T ha1T hG1T (tangential_inner_eq_zero b hν i)
    have hG'P : ∀ i p, DirHolderOn α (m + 1) (fun y ↦ ⟪p, fderivWithin ℝ G T y (e i) -
        fderivWithin ℝ a T y (e i) (gu y)⟫) S₂ := by
      intro i p
      have h1 : DirHolderOn α (m + 1) (fun y ↦ fderivWithin ℝ (fun y ↦ ⟪p, G y⟫) T y (e i) -
          ∑ l, ⟪b l, gu y⟫ * fderivWithin ℝ (fun y ↦ ⟪p, a y (b l)⟫) T y (e i)) T :=
        ((hGT p).2 (e i)).sub huT (DirHolderOn.sum huT Finset.univ fun l _ ↦
          (hguT (b l)).mul huT hTc hTcv hα hα1' ((haT p (b l)).2 (e i)))
      refine (h1.mono hS₂T huS₂).congr fun y hy ↦ ?_
      have hyT := hS₂T hy
      rw [inner_sub_right, inner_fderivWithin_apply (huT y hyT)
        ((hG1T.differentiableOn one_ne_zero) y hyT), inner_apply_eq_sum b]
      congr 1
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [inner_fderivWithin_apply_clm (huT y hyT) ((ha1T.differentiableOn one_ne_zero) y hyT)]
    -- step 3: the induction hypothesis for the tangential derivatives
    have hloc : ∀ i, ∃ ρ, 0 < ρ ∧ ρ < s₂ ∧
        DirHolderOn α (m + 2) (fun y ↦ fderivWithin ℝ u B y (e i)) (halfBall ν z ρ) :=
      fun i ↦ ih hs₂0 hz hlam (hell.mono (hS₂T.trans hTB)) (hsym.mono (hS₂T.trans hTB))
        (fun p q ↦ ((ha p q).of_succ hBc hBcv hα hα1').mono (hS₂T.trans hTB) huS₂)
        (hG'P i) (hlin i)
    choose ρi hρi hρis hρiP using hloc
    obtain ⟨ε, hε, hεs, hεi⟩ := exists_pos_lt_forall hρi hs₂0
    set S₄ := halfBall ν z ε with hS₄
    have hu₄ := uniqueDiffOn_halfBall hν hε (by linarith : -ε < ⟪z, ν⟫)
    have hS₄c := isCompact_halfBall ν z ε
    have hS₄cv := convex_halfBall ν z ε
    have hS₄i : ∀ i, S₄ ⊆ halfBall ν z (ρi i) := fun i ↦ halfBall_mono ν z (hεi i).le
    have hS₄T : S₄ ⊆ T := halfBall_mono ν z (by linarith)
    have hS₄B : S₄ ⊆ B := hS₄T.trans hTB
    have hball₄ : closedBall z ε ⊆ ball z s :=
      (closedBall_subset_closedBall (by linarith)).trans hballT
    have hC2₄ : ContDiffOn ℝ 2 u S₄ := hC2T.mono hS₄T
    have hD₄ : ∀ y ∈ S₄, fderivWithin ℝ u S₄ y = fderivWithin ℝ u B y := fun y hy ↦
      fderivWithin_subset hS₄B (hu₄ y hy) (huB y (hS₄B hy))
    -- step 4: the equation and the assembly
    obtain ⟨ha1B, Kda, hKda⟩ := contDiffOn_one_holder_of_components_clm hBu hα fun p q ↦
      (ha p q).of_le hBc hBcv hα hα1' (by omega)
    obtain ⟨hG1B, Kdg, hKdg⟩ := contDiffOn_one_holder_of_components hBu hα fun p ↦
      (hG p).of_le hBc hBcv hα hα1' (by omega)
    have hRP : DirHolderOn α (m + 1) (fun y ↦ -∑ j, ⟪b j, fderivWithin ℝ a B y (b j) (gu y)⟫ +
        ∑ j, ⟪b j, fderivWithin ℝ G B y (b j)⟫) S₄ := by
      have h1 : DirHolderOn α (m + 1) (fun y ↦ -∑ j, ∑ l, ⟪b l, gu y⟫ *
          fderivWithin ℝ (fun y ↦ ⟪b j, a y (b l)⟫) B y (b j) +
          ∑ j, fderivWithin ℝ (fun y ↦ ⟪b j, G y⟫) B y (b j)) S₄ :=
        ((DirHolderOn.sum hu₄ Finset.univ fun j _ ↦ DirHolderOn.sum hu₄ Finset.univ fun l _ ↦
          ((hguT (b l)).mono hS₄T hu₄).mul hu₄ hS₄c hS₄cv hα hα1'
            (((ha (b j) (b l)).2 (b j)).mono hS₄B hu₄)).neg hu₄).add hu₄
          (DirHolderOn.sum hu₄ Finset.univ fun j _ ↦ ((hG (b j)).2 (b j)).mono hS₄B hu₄)
      refine h1.congr fun y hy ↦ ?_
      have hyB := hS₄B hy
      have e1 : ∀ j, ⟪b j, fderivWithin ℝ a B y (b j) (gu y)⟫ = ∑ l, ⟪b l, gu y⟫ *
          fderivWithin ℝ (fun y ↦ ⟪b j, a y (b l)⟫) B y (b j) := fun j ↦ by
        rw [inner_apply_eq_sum b]
        exact Finset.sum_congr rfl fun l _ ↦ by
          rw [inner_fderivWithin_apply_clm (hBu y hyB) ((ha1B.differentiableOn one_ne_zero) y hyB)]
      have e2 : ∀ j, ⟪b j, fderivWithin ℝ G B y (b j)⟫ =
          fderivWithin ℝ (fun y ↦ ⟪b j, G y⟫) B y (b j) := fun j ↦
        inner_fderivWithin_apply (hBu y hyB) ((hG1B.differentiableOn one_ne_zero) y hyB) _ _
      simp only [e1, e2]
    have hrows : ∀ i, DirHolderOn α (m + 2)
        (fun y ↦ fderivWithin ℝ u S₄ y (b i - ⟪b i, ν⟫ • ν)) S₄ := fun i ↦
      ((hρiP i).mono (hS₄i i) hu₄).congr fun y hy ↦ by rw [hD₄ y hy]
    have hApos : ∀ y ∈ S₄, lam ≤ ⟪a y ν, ν⟫ := fun y hy ↦ by
      have := (hell y (hS₄B hy)).1 ν
      rwa [hν, one_pow, mul_one] at this
    refine ⟨ε, hε, by linarith, ?_⟩
    exact dirHolderOn_add_two_of_rows b hu₄ hS₄c hS₄cv hα hα1' hC2₄
      (fun y hy u v ↦ (hC2₄ y hy).isSymmSndFDerivWithinAt (by simp) hu₄
        (by rw [closure_interior_halfBall hν hε hz]; exact hy) hy u v)
      (fun y hy ↦ hsym y (hS₄B hy)) hlam hApos
      (fun y hy ↦ sum_hessianWithin_eq_of_linear hα hα1 hν hs (by linarith) hlam hell hsym
        ha1B hKda hG1B hKdg h hz hε hball₄ hC2₄ b hy)
      (fun p q ↦ ((ha p q).of_succ hBc hBcv hα hα1').mono hS₄B hu₄) hRP hrows

/-! ### The quasilinear induction -/

/-- **Quasilinear conormal `C^{k+2,α}`** near every point of `ball x r ∩ halfSpace ν`, for
`Φ ∈ C^{k+2}(U)` (see the module docstring). -/
theorem quasilinear_dirHolderOn {ν x : E} {r : ℝ} {Φ : E → E} {U : Set E} {lam : ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r) (hx : -r < ⟪x, ν⟫) (hU : IsOpen U)
    (hUc : Convex ℝ U) (hlam : 0 < lam)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) (k : ℕ) (hΦ : ContDiffOn ℝ (k + 2 : ℕ) Φ U)
    {y₀ : E} (hy₀ : y₀ ∈ ball x r ∩ halfSpace ν) :
    ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧ ∃ ρ, 0 < ρ ∧ closedBall y₀ ρ ⊆ ball x r ∧
      DirHolderOn α (k + 2) w (halfBall ν y₀ ρ) := by
  set B := halfBall ν x r with hB
  have hy₀ν : 0 ≤ ⟪y₀, ν⟫ := hy₀.2
  have hy₀B : y₀ ∈ B := ⟨ball_subset_closedBall hy₀.1, hy₀.2⟩
  have hwB : DifferentiableOn ℝ w B := h.1.differentiableOn one_ne_zero
  induction k with
  | zero =>
    obtain ⟨α, hα, hα1, ρ, hρ, hball, Hs, hHs, C, hC⟩ := exists_hessian_holder_halfBall hν hr hx
      hU hUc hlam (by exact_mod_cast hΦ) hell hsym hrange h hy₀
    have hSB : halfBall ν y₀ ρ ⊆ B := fun y hy ↦ ⟨ball_subset_closedBall (hball hy.1), hy.2⟩
    exact ⟨α, hα, hα1, ρ, hρ, hball, DirHolderOn.of_hessian
      (uniqueDiffOn_halfBall hν hρ (by linarith)) (D := fderivWithin ℝ w B)
      (fun y hy ↦ ((hwB y (hSB hy)).hasFDerivWithinAt).mono hSB) hHs ⟨C, hC⟩⟩
  | succ k ih =>
    have hΦk : ContDiffOn ℝ (k + 2 : ℕ) Φ U :=
      hΦ.of_le (by exact_mod_cast (by omega : k + 2 ≤ k + 1 + 2))
    obtain ⟨α, hα, hα1, ρ₁, hρ₁, hball₁, hw₁⟩ := ih hΦk
    have hα1' : α ≤ 1 := hα1.le
    have hΦ2 : ContDiffOn ℝ 2 Φ U := hΦ.of_le (by exact_mod_cast (by omega : 2 ≤ k + 1 + 2))
    have hΦ1 : ContDiffOn ℝ 1 Φ U := hΦ.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1 + 2))
    -- a compact convex neighbourhood of the values of `∇w`
    set gw := gradientWithin w B with hgw
    set p₀ := gw y₀ with hp₀
    obtain ⟨κ₂, hκ₂, hκU⟩ := Metric.isOpen_iff.1 hU p₀ (hrange y₀ hy₀B)
    set κ := κ₂ / 2 with hκ
    have hKU : closedBall p₀ κ ⊆ U := (closedBall_subset_ball (by linarith)).trans hκU
    obtain ⟨η, hη, hηc⟩ := Metric.continuousWithinAt_iff.1
      ((continuousOn_gradientWithin_halfBall hν hr hx h.1) y₀ hy₀B) κ (by positivity)
    set ρ₂ := min ρ₁ (η / 2) with hρ₂
    have hρ₂0 : 0 < ρ₂ := lt_min hρ₁ (by positivity)
    set S₂ := halfBall ν y₀ ρ₂ with hS₂
    have hu₂ := uniqueDiffOn_halfBall hν hρ₂0 (by linarith : -ρ₂ < ⟪y₀, ν⟫)
    have hS₂c := isCompact_halfBall ν y₀ ρ₂
    have hS₂cv := convex_halfBall ν y₀ ρ₂
    have hS₂₁ : S₂ ⊆ halfBall ν y₀ ρ₁ := halfBall_mono ν y₀ (min_le_left _ _)
    have hball₂ : closedBall y₀ ρ₂ ⊆ ball x r :=
      (closedBall_subset_closedBall (min_le_left _ _)).trans hball₁
    have hS₂B : S₂ ⊆ B := fun y hy ↦ ⟨ball_subset_closedBall (hball₂ hy.1), hy.2⟩
    have hgK : ∀ y ∈ S₂, gw y ∈ closedBall p₀ κ := fun y hy ↦ by
      rw [mem_closedBall]
      have h1 : dist y y₀ ≤ ρ₂ := mem_closedBall.1 hy.1
      have h2 : ρ₂ ≤ η / 2 := min_le_right _ _
      exact (hηc (hS₂B hy) (by linarith)).le
    have hw₂ : DirHolderOn α (k + 2) w S₂ := hw₁.mono hS₂₁ hu₂
    have hC2₂ : ContDiffOn ℝ 2 w S₂ := by
      have := (hw₂.of_le hS₂c hS₂cv hα hα1' (n := 2) (by omega)).contDiffOn hα
      exact_mod_cast this
    -- the coefficient `A = DΦ(∇w) ∈ C^{k+1,α}`
    have hgwP : ∀ p, DirHolderOn α (k + 1) (fun y ↦ ⟪p, gw y⟫) S₂ := fun p ↦
      (hw₂.2 p).congr fun y hy ↦ by
        rw [real_inner_comm, hgw, gradientWithin, InnerProductSpace.toDual_symm_apply,
          ← fderivWithin_subset hS₂B (hu₂ y hy) (hwB y (hS₂B hy))]
    set A : E → E →L[ℝ] E := fun y ↦ fderiv ℝ Φ (gw y) with hA
    have hAP : ∀ p q, DirHolderOn α (k + 1) (fun y ↦ ⟪p, A y q⟫) S₂ := fun p q ↦
      DirHolderOn.comp hu₂ hS₂c hS₂cv hα hα1' hU (isCompact_closedBall p₀ κ)
        (convex_closedBall p₀ κ) hKU hgK hgwP (ψ := fun p' ↦ ⟪p, fderiv ℝ Φ p' q⟫)
        (contDiffOn_const.inner ℝ ((hΦ.fderiv_of_isOpen hU
          (by exact_mod_cast (by omega : k + 1 + 1 + 1 ≤ k + 1 + 2))).clm_apply
            contDiffOn_const))
    obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall p₀ κ).exists_bound_of_continuousOn
      ((hΦ1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
    have hellA : IsUniformlyElliptic lam Λ A S₂ := fun y hy ↦
      ⟨hell _ (hrange y (hS₂B hy)), hΛ _ (hgK y hy)⟩
    have hsymA : IsSymmetricOn A S₂ := fun y hy ↦ hsym _ (hrange y (hS₂B hy))
    -- the tangential derivatives
    set s₃ := ρ₂ / 2 with hs₃
    have hs₃0 : 0 < s₃ := by positivity
    have hu₃ := uniqueDiffOn_halfBall hν hs₃0 (by linarith : -s₃ < ⟪y₀, ν⟫)
    have hS₃₂ : halfBall ν y₀ s₃ ⊆ S₂ := halfBall_mono ν y₀ (by linarith)
    set b := stdOrthonormalBasis ℝ E with hb
    have hlin : ∀ i, IsConormalSolOn ν A 0 0 y₀ s₃
        (fun y ↦ fderivWithin ℝ w B y (b i - ⟪b i, ν⟫ • ν)) := fun i ↦
      h.isConormalSolOn_fderivWithin_apply hν hU hΦ1 hrange hs₃0 (by linarith) hy₀ν hball₂
        hC2₂ (tangential_inner_eq_zero b hν i)
    have hloc : ∀ i, ∃ ρ, 0 < ρ ∧ ρ < s₃ ∧ DirHolderOn α (k + 2)
        (fun y ↦ fderivWithin ℝ w B y (b i - ⟪b i, ν⟫ • ν)) (halfBall ν y₀ ρ) := fun i ↦
      linear_dirHolderOn hα hα1 hν k hs₃0 hy₀ν hlam (hellA.mono hS₃₂) (hsymA.mono hS₃₂)
        (fun p q ↦ (hAP p q).mono hS₃₂ hu₃)
        (fun p ↦ (DirHolderOn.const 0 (k + 1)).congr fun y _ ↦ by simp) (hlin i)
    choose ρi hρi hρis hρiP using hloc
    obtain ⟨ε, hε, hεs, hεi⟩ := exists_pos_lt_forall hρi hs₃0
    set S₄ := halfBall ν y₀ ε with hS₄
    have hu₄ := uniqueDiffOn_halfBall hν hε (by linarith : -ε < ⟪y₀, ν⟫)
    have hS₄c := isCompact_halfBall ν y₀ ε
    have hS₄cv := convex_halfBall ν y₀ ε
    have hS₄i : ∀ i, S₄ ⊆ halfBall ν y₀ (ρi i) := fun i ↦ halfBall_mono ν y₀ (hεi i).le
    have hS₄₂ : S₄ ⊆ S₂ := halfBall_mono ν y₀ (by linarith)
    have hS₄B : S₄ ⊆ B := hS₄₂.trans hS₂B
    have hball₄ : closedBall y₀ ε ⊆ ball x r :=
      (closedBall_subset_closedBall (by linarith)).trans hball₂
    have hC2₄ : ContDiffOn ℝ 2 w S₄ := hC2₂.mono hS₄₂
    have hD₄ : ∀ y ∈ S₄, fderivWithin ℝ w S₄ y = fderivWithin ℝ w B y := fun y hy ↦
      fderivWithin_subset hS₄B (hu₄ y hy) (hwB y (hS₄B hy))
    have hrows : ∀ i, DirHolderOn α (k + 2)
        (fun y ↦ fderivWithin ℝ w S₄ y (b i - ⟪b i, ν⟫ • ν)) S₄ := fun i ↦
      ((hρiP i).mono (hS₄i i) hu₄).congr fun y hy ↦ by rw [hD₄ y hy]
    have hApos : ∀ y ∈ S₄, lam ≤ ⟪A y ν, ν⟫ := fun y hy ↦ by
      have := (hellA y (hS₄₂ hy)).1 ν
      rwa [hν, one_pow, mul_one] at this
    refine ⟨α, hα, hα1, ε, hε, hball₄, ?_⟩
    exact dirHolderOn_add_two_of_rows b hu₄ hS₄c hS₄cv hα hα1' hC2₄
      (fun y hy u v ↦ (hC2₄ y hy).isSymmSndFDerivWithinAt (by simp) hu₄
        (by rw [closure_interior_halfBall hν hε hy₀ν]; exact hy) hy u v)
      (fun y hy ↦ hsymA y (hS₄₂ hy)) hlam hApos (R := fun _ ↦ 0)
      (fun y hy ↦ sum_hessianWithin_eq_zero hν hr hx hU hUc hlam hΦ2 hell hsym hrange h hy₀ν
        hε hball₄ hC2₄ b hy)
      (fun p q ↦ (hAP p q).mono hS₄₂ hu₄) (DirHolderOn.const 0 _) hrows

/-- **`C^{k+2}` up to the flat part for quasilinear conormal solutions** (`Φ ∈ C^{k+2}`; the case
`k + 1` of `Div.QuasilinearConormalStatement`). -/
theorem contDiffOn_halfBall_of_quasilinear_conormal_add_two (k : ℕ) {ν x : E} {r : ℝ}
    {Φ : E → E} {U : Set E} {lam : ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (hr : 0 < r)
    (hx : -r < ⟪x, ν⟫) (hU : IsOpen U) (hUc : Convex ℝ U) (hlam : 0 < lam)
    (hΦ : ContDiffOn ℝ (k + 2 : ℕ) Φ U)
    (hell : ∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫)
    (hsym : ∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric)
    (hrange : ∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U)
    (h : IsQuasilinearConormalSolOn ν Φ x r w) :
    ContDiffOn ℝ (k + 2 : ℕ) w (halfBall ν x (r / 2)) := by
  intro y hy
  have hy' : y ∈ ball x r ∩ halfSpace ν :=
    ⟨mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (by linarith)), hy.2⟩
  obtain ⟨α, hα, -, ρ, hρ, -, hP⟩ := quasilinear_dirHolderOn hν hr hx hU hUc hlam hell hsym
    hrange h k hΦ hy'
  refine (hP.contDiffOn hα y ⟨mem_closedBall_self hρ.le, hy.2⟩).mono_of_mem_nhdsWithin ?_
  exact mem_of_superset (inter_mem_nhdsWithin _ (ball_mem_nhds y hρ))
    fun z hz ↦ ⟨ball_subset_closedBall hz.2, hz.1.2⟩

end BasicElliptic.Div
