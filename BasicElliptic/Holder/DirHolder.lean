/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Holder
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import BasicElliptic.Holder.Algebra
import BasicElliptic.Holder.Closure
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Directional Hölder classes `C^{m,α}` for the higher-order induction

`Div.DirHolderOn α m f S` (`f : E → ℝ`): for `m = 0`, `f` is `α`-Hölder on `S`; for `m + 1`, `f`
is differentiable within `S` and every directional within-derivative `y ↦ D_S f(y) v` is
`DirHolderOn α m` on `S`. On a compact convex set with unique derivatives this is the class
`C^{m,α}(S)`; it is stated for scalar functions only, so the recursion never changes the codomain
(vector and matrix fields are handled through their components `⟪u, G y⟫`, `⟪u, a y v⟫`).

Closure properties (on compact convex `S` with unique derivatives, `0 < α ≤ 1`): constants,
sums, products, inverses of functions bounded below by a positive constant, compositions
`ψ ∘ g` with `ψ ∈ C^{m+1}` near the compact convex range of `g`, and `C^{m+1,α} ⊆ C^{m,α}`.
Bridges: `DirHolderOn α m f S → ContDiffOn ℝ m f S`, and from/to Hölder within-derivatives.

The declarations live in the namespace `BasicElliptic.Div`.
-/

public section

open Metric Set Filter RealInnerProductSpace
open scoped NNReal Topology ContDiff

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Directional `C^{m,α}` on `S` (see the module docstring). -/
@[expose] def DirHolderOn (α : ℝ≥0) : ℕ → (E → ℝ) → Set E → Prop
  | 0, f, S => ∃ C, HolderOnWith C α f S
  | m + 1, f, S => DifferentiableOn ℝ f S ∧
      ∀ v : E, DirHolderOn α m (fun y ↦ fderivWithin ℝ f S y v) S

namespace DirHolderOn

variable {α : ℝ≥0} {S T : Set E} {m : ℕ} {f g : E → ℝ}

theorem congr (h : DirHolderOn α m f S) (hfg : EqOn g f S) : DirHolderOn α m g S := by
  induction m generalizing f g with
  | zero =>
    obtain ⟨C, hC⟩ := h
    exact ⟨C, holderOnWith_iff_dist_le.2 fun x hx y hy ↦ by
      rw [hfg hx, hfg hy]; exact hC.dist_le hx hy⟩
  | succ m ih =>
    refine ⟨h.1.congr hfg, fun v ↦ ih (h.2 v) fun y hy ↦ ?_⟩
    rw [fderivWithin_congr hfg (hfg hy)]

theorem mono (h : DirHolderOn α m f S) (hTS : T ⊆ S) (hT : UniqueDiffOn ℝ T) :
    DirHolderOn α m f T := by
  induction m generalizing f with
  | zero => obtain ⟨C, hC⟩ := h; exact ⟨C, hC.mono hTS⟩
  | succ m ih =>
    refine ⟨h.1.mono hTS, fun v ↦ (ih (h.2 v)).congr fun y hy ↦ ?_⟩
    rw [fderivWithin_subset hTS (hT y hy) (h.1 y (hTS hy))]

theorem const (c : ℝ) (m : ℕ) : DirHolderOn α m (fun _ ↦ c) S := by
  induction m generalizing c with
  | zero => exact ⟨0, holderOnWith_const c 0 α S⟩
  | succ m ih =>
    refine ⟨differentiableOn_const c, fun v ↦ ?_⟩
    simpa only [fderivWithin_const_apply, zero_apply] using ih 0

theorem add (hS : UniqueDiffOn ℝ S) (hf : DirHolderOn α m f S) (hg : DirHolderOn α m g S) :
    DirHolderOn α m (fun y ↦ f y + g y) S := by
  induction m generalizing f g with
  | zero =>
    obtain ⟨C, hC⟩ := hf
    obtain ⟨C', hC'⟩ := hg
    exact ⟨_, holderOnWith_add hC hC'⟩
  | succ m ih =>
    refine ⟨hf.1.add hg.1, fun v ↦ (ih (hf.2 v) (hg.2 v)).congr fun y hy ↦ ?_⟩
    rw [fderivWithin_fun_add (hS y hy) (hf.1 y hy) (hg.1 y hy)]
    rfl

theorem neg (hS : UniqueDiffOn ℝ S) (hf : DirHolderOn α m f S) :
    DirHolderOn α m (fun y ↦ -f y) S := by
  induction m generalizing f with
  | zero => obtain ⟨C, hC⟩ := hf; exact ⟨_, holderOnWith_neg hC⟩
  | succ m ih =>
    refine ⟨hf.1.neg, fun v ↦ (ih (hf.2 v)).congr fun y hy ↦ ?_⟩
    rw [fderivWithin_fun_neg (hS y hy)]
    rfl

theorem sub (hS : UniqueDiffOn ℝ S) (hf : DirHolderOn α m f S) (hg : DirHolderOn α m g S) :
    DirHolderOn α m (fun y ↦ f y - g y) S := by
  simpa only [sub_eq_add_neg] using hf.add hS (hg.neg hS)

theorem sum (hS : UniqueDiffOn ℝ S) {ι : Type*} (t : Finset ι) {F : ι → E → ℝ}
    (h : ∀ i ∈ t, DirHolderOn α m (F i) S) : DirHolderOn α m (fun y ↦ ∑ i ∈ t, F i y) S := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using const (α := α) (S := S) 0 m
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i t)).add hS
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-! ### Bounds and the inclusion `C^{m+1,α} ⊆ C^{m,α}` -/

variable [FiniteDimensional ℝ E]

/-- A field of functionals whose values on every vector are Hölder is Hölder. -/
theorem _root_.BasicElliptic.Div.exists_holderOnWith_of_apply {L : E → E →L[ℝ] ℝ}
    (h : ∀ v : E, ∃ C, HolderOnWith C α (fun y ↦ L y v) S) : ∃ C, HolderOnWith C α L S := by
  set b := stdOrthonormalBasis ℝ E
  have hL : L = fun y ↦ ∑ i, L y (b i) • innerSL ℝ (b i) := by
    funext y
    ext ξ
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr' ξ]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  rw [hL]
  refine exists_holderOnWith_sum _ fun i _ ↦ ?_
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] using
    exists_holderOnWith_clm ((ContinuousLinearMap.lsmul ℝ ℝ).flip (innerSL ℝ (b i))) (h (b i))

theorem exists_holderOnWith_fderivWithin (h : DirHolderOn α 1 f S) :
    ∃ C, HolderOnWith C α (fderivWithin ℝ f S) S :=
  exists_holderOnWith_of_apply fun v ↦ h.2 v

theorem of_succ (hSc : IsCompact S) (hScv : Convex ℝ S) (hα : 0 < α)
    (hα1 : α ≤ 1) (h : DirHolderOn α (m + 1) f S) : DirHolderOn α m f S := by
  induction m generalizing f with
  | zero =>
    obtain ⟨C, hC⟩ := exists_holderOnWith_fderivWithin h
    obtain ⟨A, hA⟩ := exists_bound_of_holderOnWith hSc hα hC
    have hlip : LipschitzOnWith A f S :=
      hScv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun y hy ↦ (h.1 y hy).hasFDerivWithinAt)
        fun y hy ↦ by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hA y hy
    obtain ⟨Dm, hDm⟩ := Metric.isBounded_iff.1 hSc.isBounded
    exact ⟨_, holderOnWith_of_lipschitzOnWith hlip hα1 (le_max_right Dm 0)
      fun x hx y hy ↦ (hDm hx hy).trans (le_max_left _ _)⟩
  | succ m ih => exact ⟨h.1, fun v ↦ ih (h.2 v)⟩

theorem of_le (hSc : IsCompact S) (hScv : Convex ℝ S) (hα : 0 < α)
    (hα1 : α ≤ 1) {n : ℕ} (hnm : n ≤ m) (h : DirHolderOn α m f S) : DirHolderOn α n f S := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih (h.of_succ hSc hScv hα hα1)

/-! ### Products and inverses -/

theorem mul (hS : UniqueDiffOn ℝ S) (hSc : IsCompact S) (hScv : Convex ℝ S) (hα : 0 < α)
    (hα1 : α ≤ 1) (hf : DirHolderOn α m f S) (hg : DirHolderOn α m g S) :
    DirHolderOn α m (fun y ↦ f y * g y) S := by
  induction m generalizing f g with
  | zero =>
    change ∃ C, HolderOnWith C α (fun y ↦ f y * g y) S
    simpa only [ContinuousLinearMap.mul_apply'] using
      exists_holderOnWith_bilinear hSc hα (ContinuousLinearMap.mul ℝ ℝ) hf hg
  | succ m ih =>
    refine ⟨hf.1.mul hg.1, fun v ↦ ?_⟩
    refine ((ih (hf.2 v) (hg.of_succ hSc hScv hα hα1)).add hS
      (ih (hf.of_succ hSc hScv hα hα1) (hg.2 v))).congr fun y hy ↦ ?_
    rw [fderivWithin_fun_mul (hS y hy) (hf.1 y hy) (hg.1 y hy)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring

theorem const_mul (hS : UniqueDiffOn ℝ S) (hSc : IsCompact S) (hScv : Convex ℝ S) (hα : 0 < α)
    (hα1 : α ≤ 1) (c : ℝ) (hf : DirHolderOn α m f S) : DirHolderOn α m (fun y ↦ c * f y) S :=
  (const c m).mul hS hSc hScv hα hα1 hf

theorem inv (hS : UniqueDiffOn ℝ S) (hSc : IsCompact S) (hScv : Convex ℝ S) (hα : 0 < α)
    (hα1 : α ≤ 1) {c : ℝ} (hc : 0 < c) (hf : DirHolderOn α m f S) (hfc : ∀ y ∈ S, c ≤ f y) :
    DirHolderOn α m (fun y ↦ (f y)⁻¹) S := by
  induction m generalizing f with
  | zero => exact exists_holderOnWith_inv hc hf hfc
  | succ m ih =>
    have hne : ∀ y ∈ S, f y ≠ 0 := fun y hy ↦ (hc.trans_le (hfc y hy)).ne'
    have hi := ih (hf.of_succ hSc hScv hα hα1) hfc
    refine ⟨hf.1.inv hne, fun v ↦ ?_⟩
    refine ((hf.2 v).neg hS |>.mul hS hSc hScv hα hα1 (hi.mul hS hSc hScv hα hα1 hi)).congr
      fun y hy ↦ ?_
    have hd := (hasDerivAt_inv (hne y hy)).hasFDerivAt.comp_hasFDerivWithinAt y
      (hf.1 y hy).hasFDerivWithinAt
    rw [show (fun y ↦ (f y)⁻¹) = (fun x ↦ x⁻¹) ∘ f from rfl, hd.fderivWithin (hS y hy)]
    simp
    field_simp
    simp

/-! ### Regularity and bridges -/

omit [FiniteDimensional ℝ E] in
theorem continuousOn (hα : 0 < α) (h : DirHolderOn α m f S) : ContinuousOn f S := by
  cases m with
  | zero => obtain ⟨C, hC⟩ := h; exact hC.continuousOn hα
  | succ m => exact h.1.continuousOn

theorem contDiffOn (hα : 0 < α) (h : DirHolderOn α m f S) :
    ContDiffOn ℝ m f S := by
  induction m generalizing f with
  | zero => exact contDiffOn_zero.2 (h.continuousOn hα)
  | succ m ih =>
    set b := stdOrthonormalBasis ℝ E
    have hD : EqOn (fderivWithin ℝ f S) (fun y ↦ ∑ i, fderivWithin ℝ f S y (b i) •
        innerSL ℝ (b i)) S := fun y _ ↦ by
      ext ξ
      simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
        innerSL_apply_apply, smul_eq_mul]
      conv_lhs => rw [← b.sum_repr' ξ]
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    rw [Nat.cast_succ]
    refine contDiffOn_succ_of_fderivWithin h.1 (by simp) ?_
    exact (ContDiffOn.sum fun i _ ↦ (ih (h.2 (b i))).smul contDiffOn_const).congr hD

omit [FiniteDimensional ℝ E] in
/-- A function with an `α`-Hölder within-derivative is `DirHolderOn α 1`. -/
theorem of_hasFDerivWithinAt (hS : UniqueDiffOn ℝ S) {D : E → E →L[ℝ] ℝ}
    (hD : ∀ y ∈ S, HasFDerivWithinAt f (D y) S y) (hDH : ∃ C, HolderOnWith C α D S) :
    DirHolderOn α 1 f S := by
  refine ⟨fun y hy ↦ (hD y hy).differentiableWithinAt, fun v ↦ ?_⟩
  obtain ⟨C, hC⟩ := exists_holderOnWith_clm (ContinuousLinearMap.apply ℝ ℝ v) hDH
  exact ⟨C, holderOnWith_iff_dist_le.2 fun p hp q hq ↦ by
    rw [(hD p hp).fderivWithin (hS p hp), (hD q hq).fderivWithin (hS q hq)]
    exact hC.dist_le hp hq⟩

omit [FiniteDimensional ℝ E] in
/-- A function with a within-derivative which has an `α`-Hölder within-derivative is
`DirHolderOn α 2`. -/
theorem of_hessian (hS : UniqueDiffOn ℝ S) {D : E → E →L[ℝ] ℝ}
    (hD : ∀ y ∈ S, HasFDerivWithinAt f (D y) S y) {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hH : ∀ y ∈ S, HasFDerivWithinAt D (H y) S y) (hHH : ∃ C, HolderOnWith C α H S) :
    DirHolderOn α 2 f S := by
  refine ⟨fun y hy ↦ (hD y hy).differentiableWithinAt, fun v ↦ ?_⟩
  have h1 : DirHolderOn α 1 (fun y ↦ D y v) S := by
    refine of_hasFDerivWithinAt hS (D := fun y ↦ (ContinuousLinearMap.apply ℝ ℝ v) ∘L H y)
      (fun y hy ↦ (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasFDerivWithinAt y
        (hH y hy)) ?_
    simpa only [ContinuousLinearMap.compL_apply] using exists_holderOnWith_clm
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) ℝ (ContinuousLinearMap.apply ℝ ℝ v)) hHH
  exact h1.congr fun y hy ↦ by rw [(hD y hy).fderivWithin (hS y hy)]

/-! ### Compositions -/

/-- **Composition.** If the components `⟪u, g⟫` are `C^{m,α}` on `S`, `g(S) ⊆ K` with `K` compact
convex inside the open `U`, and `ψ ∈ C^{m+1}(U)`, then `ψ ∘ g` is `C^{m,α}` on `S`. -/
theorem comp (hS : UniqueDiffOn ℝ S) (hSc : IsCompact S) (hScv : Convex ℝ S) (hα : 0 < α)
    (hα1 : α ≤ 1) {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKU : K ⊆ U) {g : E → E} (hgK : ∀ y ∈ S, g y ∈ K)
    (hg : ∀ u : E, DirHolderOn α m (fun y ↦ ⟪u, g y⟫) S) {ψ : E → ℝ}
    (hψ : ContDiffOn ℝ (m + 1 : ℕ) ψ U) : DirHolderOn α m (fun y ↦ ψ (g y)) S := by
  set b := stdOrthonormalBasis ℝ E with hb
  have hgexp : g = fun y ↦ ∑ l, ⟪b l, g y⟫ • b l := by
    funext y; exact (b.sum_repr' (g y)).symm
  induction m generalizing ψ with
  | zero =>
    have hψ1 : ContDiffOn ℝ 1 ψ U := by simpa using hψ
    obtain ⟨L₀, hL₀⟩ := hK.exists_bound_of_continuousOn
      ((hψ1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
    have hlip : LipschitzOnWith (Real.toNNReal L₀) ψ K := by
      refine hKc.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (f' := fun p ↦ fderiv ℝ ψ p) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
      · exact ((hψ1.differentiableOn one_ne_zero p (hKU hp)).differentiableAt
          (hU.mem_nhds (hKU hp))).hasFDerivAt.hasFDerivWithinAt
      · rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact (hL₀ p hp).trans (Real.le_coe_toNNReal L₀)
    have hgH : ∃ C, HolderOnWith C α g S := by
      rw [hgexp]
      refine exists_holderOnWith_sum _ fun l _ ↦ ?_
      simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] using
        exists_holderOnWith_clm ((ContinuousLinearMap.lsmul ℝ ℝ).flip (b l)) (hg (b l))
    obtain ⟨C, hC⟩ := hgH
    exact ⟨_, holderOnWith_comp_lipschitzOnWith hlip hC hgK⟩
  | succ m ih =>
    have hgd : DifferentiableOn ℝ g S := by
      rw [hgexp]
      intro y hy
      exact DifferentiableWithinAt.fun_sum fun l _ ↦ ((hg (b l)).1 y hy).smul_const (b l)
    have hψd : ∀ p ∈ U, DifferentiableAt ℝ ψ p := fun p hp ↦
      (hψ.differentiableOn (by simp) p hp).differentiableAt (hU.mem_nhds hp)
    refine ⟨fun y hy ↦ (hψd _ (hKU (hgK y hy))).comp_differentiableWithinAt y (hgd y hy),
      fun v ↦ ?_⟩
    have hform : EqOn (fun y ↦ fderivWithin ℝ (fun y ↦ ψ (g y)) S y v)
        (fun y ↦ ∑ l, fderivWithin ℝ (fun y ↦ ⟪b l, g y⟫) S y v * fderiv ℝ ψ (g y) (b l))
        S := by
      intro y hy
      have h1 := ((hψd _ (hKU (hgK y hy))).hasFDerivAt.comp_hasFDerivWithinAt y
        (hgd y hy).hasFDerivWithinAt).fderivWithin (hS y hy)
      have h2 : ∀ l, fderivWithin ℝ (fun y ↦ ⟪b l, g y⟫) S y v =
          ⟪b l, fderivWithin ℝ g S y v⟫ := fun l ↦ by
        have h3 : HasFDerivWithinAt (fun y ↦ ⟪b l, g y⟫)
            ((innerSL ℝ (b l)).comp (fderivWithin ℝ g S y)) S y :=
          (innerSL ℝ (b l)).hasFDerivAt.comp_hasFDerivWithinAt y (hgd y hy).hasFDerivWithinAt
        rw [h3.fderivWithin (hS y hy)]
        rfl
      simp only [h2]
      rw [show (fun y ↦ ψ (g y)) = ψ ∘ g from rfl, h1, ContinuousLinearMap.comp_apply]
      conv_lhs => rw [← b.sum_repr' (fderivWithin ℝ g S y v)]
      simp only [map_sum, map_smul, smul_eq_mul]
    refine (DirHolderOn.sum hS _ fun l _ ↦ ((hg (b l)).2 v).mul hS hSc hScv hα hα1
      (ih (fun u ↦ (hg u).of_succ hSc hScv hα hα1) (ψ := fun p ↦ fderiv ℝ ψ p (b l))
        ?_)).congr hform
    exact (hψ.fderiv_of_isOpen hU (by push_cast; exact le_rfl)).clm_apply contDiffOn_const

/-! ### Vector fields from components -/

/-- A finite combination `Σ_k c_k(y) • M_k` of `DirHolderOn α 1` functions is `C¹` with an
`α`-Hölder within-derivative. -/
theorem contDiffOn_one_and_holder_of_sum {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hS : UniqueDiffOn ℝ S) (hα : 0 < α) {ι : Type*} [Fintype ι]
    {c : ι → E → ℝ} (hc : ∀ k, DirHolderOn α 1 (c k) S) (M : ι → F) :
    ContDiffOn ℝ 1 (fun y ↦ ∑ k, c k y • M k) S ∧
      ∃ C, HolderOnWith C α (fderivWithin ℝ (fun y ↦ ∑ k, c k y • M k) S) S := by
  have hd : ∀ y ∈ S, HasFDerivWithinAt (fun y ↦ ∑ k, c k y • M k)
      (∑ k, (fderivWithin ℝ (c k) S y).smulRight (M k)) S y := fun y hy ↦
    HasFDerivWithinAt.fun_sum fun k _ ↦ ((hc k).1 y hy).hasFDerivWithinAt.smul_const (M k)
  refine ⟨ContDiffOn.sum fun k _ ↦
    ((by exact_mod_cast (hc k).contDiffOn hα : ContDiffOn ℝ 1 (c k) S)).smul
      contDiffOn_const, ?_⟩
  obtain ⟨C, hC⟩ : ∃ C, HolderOnWith C α
      (fun y ↦ ∑ k, (fderivWithin ℝ (c k) S y).smulRight (M k)) S :=
    exists_holderOnWith_sum _ fun k _ ↦
      exists_holderOnWith_clm ((ContinuousLinearMap.smulRightL ℝ E F).flip (M k))
        (exists_holderOnWith_fderivWithin (hc k))
  exact ⟨C, holderOnWith_iff_dist_le.2 fun p hp q hq ↦ by
    rw [(hd p hp).fderivWithin (hS p hp), (hd q hq).fderivWithin (hS q hq)]
    exact hC.dist_le hp hq⟩

end DirHolderOn

/-- Expansion of an operator in an orthonormal basis:
`A = Σ_{i,j} ⟪b_i, A b_j⟫ • (ξ ↦ ⟪b_j, ξ⟫ b_i)`. -/
theorem clm_eq_sum_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    A = ∑ p : ι × ι, ⟪b p.1, A (b p.2)⟫ • (innerSL ℝ (b p.2)).smulRight (b p.1) := by
  ext ξ
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [Fintype.sum_prod_type]
  simp only [smul_smul]
  have : ∀ i, ∑ j, (⟪b i, A (b j)⟫ * ⟪b j, ξ⟫) • b i = ⟪b i, A ξ⟫ • b i := fun i ↦ by
    rw [← Finset.sum_smul]
    congr 1
    conv_rhs => rw [← b.sum_repr' ξ]
    simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  simp only [this]
  exact (b.sum_repr' (A ξ)).symm

end BasicElliptic.Div
