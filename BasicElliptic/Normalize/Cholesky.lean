/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Basic.HalfSpace
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Normalizing a frozen coefficient

Let `a₀ : E →L[ℝ] E` be symmetric with `lam ‖ξ‖² ≤ ⟪a₀ ξ, ξ⟫` and
`‖a₀‖ ≤ Λ`. We produce `M : E ≃L[ℝ] E` with `M ∘ M† = a₀`, so that `S = M⁻¹` satisfies
`S a₀ S† = I`, with `‖M‖ ≤ √Λ` and `‖M⁻¹‖ ≤ 1 / √lam`.

* `BasicElliptic.exists_isSymmetric_comp_self_eq`: a symmetric square root of a positive symmetric
  operator, built from the eigenvector basis.
* `BasicElliptic.exists_sqrt`: the interior normalization (no half-space constraint).
* `BasicElliptic.exists_halfSpace_sqrt`: the boundary normalization. In addition
  `⟪M z, ν⟫ = m ⟪z, ν⟫` with `√lam ≤ m ≤ √Λ`, so `M` and `M⁻¹` preserve `halfSpace ν` and
  `flatPart ν`, and the conormal direction `a₀ ν = m M ν` is sent by `M⁻¹` to `m ν`.
* `BasicElliptic.symPart`, `BasicElliptic.skewPart`: for a nonsymmetric `a₀` one normalizes
  with the symmetric part; `exists_sqrt_symPart` records `M⁻¹ a₀ M⁻† = I + K` with `K` skew.
* `BasicElliptic.normalizeCoeff M a z = M⁻¹ ∘ a (x₀ + M z) ∘ M⁻†` and its ellipticity bounds
  `isUniformlyElliptic_normalizeCoeff`.

## Construction

A block Cholesky factorization through the Schur complement in `ν^⊥ ⊕ ℝν` would also work; we
use a shorter route: let `P = a₀^{1/2}` (symmetric, from the
spectral theorem) and let `Q` be the Householder reflection exchanging the unit vectors `ν` and
`P ν / ‖P ν‖`. Then `M := P ∘ Q` satisfies `M M† = P Q Q† P = a₀` and `M† ν = Q P ν = ‖P ν‖ ν`,
i.e. `⟪M z, ν⟫ = m ⟪z, ν⟫` with `m = ‖P ν‖ = √⟪a₀ ν, ν⟫`. The resulting `M` is the block
upper-triangular Cholesky factor up to an orthogonal change of the `ν^⊥` block, which is
immaterial.
-/

public section

open RealInnerProductSpace ContinuousLinearMap

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Symmetric square root -/

/-- A positive symmetric operator has a symmetric square root. -/
theorem exists_isSymmetric_comp_self_eq {a₀ : E →L[ℝ] E}
    (hsymm : (a₀ : E →ₗ[ℝ] E).IsSymmetric) (hpos : ∀ ξ, 0 ≤ ⟪a₀ ξ, ξ⟫) :
    ∃ P : E →L[ℝ] E, (P : E →ₗ[ℝ] E).IsSymmetric ∧ P ∘L P = a₀ := by
  classical
  let e := hsymm.eigenvectorBasis (rfl : Module.finrank ℝ E = _)
  let μ := hsymm.eigenvalues (rfl : Module.finrank ℝ E = _)
  have he : ∀ i, a₀ (e i) = μ i • e i := fun i ↦ hsymm.apply_eigenvectorBasis rfl i
  have hμ : ∀ i, 0 ≤ μ i := fun i ↦ by
    have := hpos (e i)
    rwa [he, real_inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.1 i, one_pow,
      mul_one] at this
  let P : E →L[ℝ] E := ∑ i, √(μ i) • InnerProductSpace.rankOne ℝ (e i) (e i)
  have hP : ∀ x, P x = ∑ i, (√(μ i) * ⟪e i, x⟫) • e i := fun x ↦ by
    simp [P, sum_apply, InnerProductSpace.rankOne_apply, smul_smul]
  have hPe : ∀ j, P (e j) = √(μ j) • e j := fun j ↦ by
    rw [hP]; simp [e.inner_eq_ite]
  refine ⟨P, fun x y ↦ ?_, ?_⟩
  · simp only [coe_coe, hP, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm x (e i)]; ring
  · refine ContinuousLinearMap.coe_injective (e.toBasis.ext fun j ↦ ?_)
    simp only [coe_coe, OrthonormalBasis.coe_toBasis, coe_comp, Function.comp_apply, hPe,
      map_smul, smul_smul, he]
    rw [← sq, Real.sq_sqrt (hμ j)]

/-! ### Interior normalization -/

omit [FiniteDimensional ℝ E] in
private theorem norm_sq_apply_eq {P a₀ : E →L[ℝ] E} (hP : (P : E →ₗ[ℝ] E).IsSymmetric)
    (hPP : P ∘L P = a₀) (x : E) : ‖P x‖ ^ 2 = ⟪a₀ x, x⟫ := by
  rw [← real_inner_self_eq_norm_sq, ← hPP, coe_comp, Function.comp_apply]
  exact (hP (P x) x).symm

omit [FiniteDimensional ℝ E] in
private theorem inner_le_of_norm_le {a₀ : E →L[ℝ] E} {Λ : ℝ} (hbd : ‖a₀‖ ≤ Λ) (x : E) :
    ⟪a₀ x, x⟫ ≤ Λ * ‖x‖ ^ 2 :=
  calc ⟪a₀ x, x⟫ ≤ ‖a₀ x‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ ‖a₀‖ * ‖x‖ * ‖x‖ := by gcongr; exact le_opNorm _ _
    _ ≤ Λ * ‖x‖ * ‖x‖ := by gcongr
    _ = Λ * ‖x‖ ^ 2 := by ring

/-- The square root with two-sided bounds, as an equivalence. -/
private theorem exists_sqrt_aux {a₀ : E →L[ℝ] E} {lam Λ : ℝ} (hlam : 0 < lam)
    (hsymm : (a₀ : E →ₗ[ℝ] E).IsSymmetric) (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a₀ ξ, ξ⟫)
    (hbd : ‖a₀‖ ≤ Λ) :
    ∃ P : E ≃L[ℝ] E, ((P : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric ∧
      (P : E →L[ℝ] E) ∘L (P : E →L[ℝ] E) = a₀ ∧
      (∀ x, √lam * ‖x‖ ≤ ‖P x‖) ∧ (∀ x, ‖P x‖ ≤ √Λ * ‖x‖) := by
  obtain ⟨P, hP, hPP⟩ := exists_isSymmetric_comp_self_eq hsymm fun ξ ↦
    (mul_nonneg hlam.le (sq_nonneg _)).trans (hell ξ)
  have hlow : ∀ x, √lam * ‖x‖ ≤ ‖P x‖ := fun x ↦ by
    rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul hlam.le, ← Real.sqrt_sq (norm_nonneg (P x))]
    exact Real.sqrt_le_sqrt ((hell x).trans (norm_sq_apply_eq hP hPP x).ge)
  have hup : ∀ x, ‖P x‖ ≤ √Λ * ‖x‖ := fun x ↦ by
    have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hbd
    rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul hΛ, ← Real.sqrt_sq (norm_nonneg (P x))]
    exact Real.sqrt_le_sqrt ((norm_sq_apply_eq hP hPP x).le.trans (inner_le_of_norm_le hbd x))
  have hinj : Function.Injective (P : E →ₗ[ℝ] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := hlow x
    rw [coe_coe] at hx
    rw [hx, norm_zero] at this
    exact norm_le_zero_iff.1 (le_of_mul_le_mul_left (by simpa using this) (Real.sqrt_pos.2 hlam))
  let Pe : E ≃L[ℝ] E := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv
  have hPe : (Pe : E →L[ℝ] E) = P := by ext x; rfl
  exact ⟨Pe, hPe ▸ hP, hPe ▸ hPP, hlow, hup⟩

omit [FiniteDimensional ℝ E] in
/-- Operator norm bound from a lower bound `c ‖x‖ ≤ ‖M x‖`. -/
private theorem norm_symm_le {M : E ≃L[ℝ] E} {c : ℝ} (hc : 0 < c) (h : ∀ x, c * ‖x‖ ≤ ‖M x‖) :
    ‖(M.symm : E →L[ℝ] E)‖ ≤ 1 / c := by
  refine opNorm_le_bound _ (by positivity) fun y ↦ ?_
  have := h (M.symm y)
  rw [ContinuousLinearEquiv.apply_symm_apply] at this
  rw [ContinuousLinearEquiv.coe_coe, div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]
  exact this

omit [FiniteDimensional ℝ E] in
private theorem norm_le_of_forall {M : E ≃L[ℝ] E} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, ‖M x‖ ≤ c * ‖x‖) :
    ‖(M : E →L[ℝ] E)‖ ≤ c :=
  opNorm_le_bound _ hc h

/-- **Interior normalization.** For `a₀` symmetric with `lam ‖ξ‖² ≤ ⟪a₀ ξ, ξ⟫` and `‖a₀‖ ≤ Λ`, there
is a symmetric `M : E ≃L[ℝ] E` with `M M† = a₀` (so `M⁻¹ a₀ M⁻† = I`), `‖M‖ ≤ √Λ` and
`‖M⁻¹‖ ≤ 1 / √lam`. -/
theorem exists_sqrt {a₀ : E →L[ℝ] E} {lam Λ : ℝ} (hlam : 0 < lam)
    (hsymm : (a₀ : E →ₗ[ℝ] E).IsSymmetric) (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a₀ ξ, ξ⟫)
    (hbd : ‖a₀‖ ≤ Λ) :
    ∃ M : E ≃L[ℝ] E, (M : E →L[ℝ] E) ∘L adjoint (M : E →L[ℝ] E) = a₀ ∧
      ((M : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric ∧
      ‖(M : E →L[ℝ] E)‖ ≤ √Λ ∧ ‖(M.symm : E →L[ℝ] E)‖ ≤ 1 / √lam := by
  obtain ⟨P, hP, hPP, hlow, hup⟩ := exists_sqrt_aux hlam hsymm hell hbd
  have hadj : adjoint (P : E →L[ℝ] E) = P :=
    (isSelfAdjoint_iff_isSymmetric.2 hP)
  exact ⟨P, by rw [hadj, hPP], hP, norm_le_of_forall (Real.sqrt_nonneg _) hup,
    norm_symm_le (Real.sqrt_pos.2 hlam) hlow⟩

/-! ### Boundary normalization -/

/-- **Half-space-preserving normalization**. For `a₀` symmetric with
`lam ‖ξ‖² ≤ ⟪a₀ ξ, ξ⟫`, `‖a₀‖ ≤ Λ` and a unit vector `ν`, there is `M : E ≃L[ℝ] E` with
`M M† = a₀` and `⟪M z, ν⟫ = m ⟪z, ν⟫` for some `m ∈ [√lam, √Λ]` (so `M` and `M⁻¹` preserve
`halfSpace ν` and `flatPart ν`), `‖M‖ ≤ √Λ` and `‖M⁻¹‖ ≤ 1 / √lam`. -/
theorem exists_halfSpace_sqrt {a₀ : E →L[ℝ] E} {ν : E} (hν : ‖ν‖ = 1) {lam Λ : ℝ}
    (hlam : 0 < lam) (hsymm : (a₀ : E →ₗ[ℝ] E).IsSymmetric)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a₀ ξ, ξ⟫) (hbd : ‖a₀‖ ≤ Λ) :
    ∃ M : E ≃L[ℝ] E, (M : E →L[ℝ] E) ∘L adjoint (M : E →L[ℝ] E) = a₀ ∧
      (∃ m, √lam ≤ m ∧ m ≤ √Λ ∧ ∀ z, ⟪M z, ν⟫ = m * ⟪z, ν⟫) ∧
      ‖(M : E →L[ℝ] E)‖ ≤ √Λ ∧ ‖(M.symm : E →L[ℝ] E)‖ ≤ 1 / √lam := by
  obtain ⟨P, hP, hPP, hlow, hup⟩ := exists_sqrt_aux hlam hsymm hell hbd
  have hadjP : adjoint (P : E →L[ℝ] E) = P := isSelfAdjoint_iff_isSymmetric.2 hP
  set m := ‖P ν‖ with hm
  have hmν : ‖P ν‖ = ‖m • ν‖ := by rw [norm_smul, hν, mul_one, Real.norm_of_nonneg (norm_nonneg _)]
  let Q : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (P ν - m • ν))ᗮ.reflection
  have hQ : Q (P ν) = m • ν := Submodule.reflection_sub hmν
  have hQsymm : Q.symm = Q := Submodule.reflection_symm
  let M : E ≃L[ℝ] E := Q.toContinuousLinearEquiv.trans P
  have hMapp : ∀ z, M z = P (Q z) := fun _ ↦ rfl
  have hMc : (M : E →L[ℝ] E) = (P : E →L[ℝ] E) ∘L (Q : E →L[ℝ] E) := by ext; rfl
  refine ⟨M, ?_, ⟨m, ?_, ?_, fun z ↦ ?_⟩, ?_, ?_⟩
  · rw [hMc, adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm, hadjP, hQsymm, comp_assoc,
      ← comp_assoc (Q : E →L[ℝ] E)]
    have : (Q : E →L[ℝ] E) ∘L (Q : E →L[ℝ] E) = 1 := by
      ext x; simp [Q, Submodule.reflection_reflection]
    rw [this, ← hPP]; ext x; rfl
  · simpa [hν] using hlow ν
  · simpa [hν] using hup ν
  · have h1 : ⟪P (Q z), ν⟫ = ⟪Q z, P ν⟫ := hP (Q z) ν
    have h2 : Q (Q z) = z := by
      conv_lhs => rw [← hQsymm]
      exact LinearIsometryEquiv.symm_apply_apply Q z
    rw [hMapp, h1, ← Q.inner_map_map, h2, hQ, real_inner_smul_right]
  · exact norm_le_of_forall (Real.sqrt_nonneg _) fun z ↦ by
      rw [hMapp]; exact (hup _).trans_eq (by rw [Q.norm_map])
  · exact norm_symm_le (Real.sqrt_pos.2 hlam) fun z ↦ by
      rw [hMapp]; exact (hlow _).trans_eq' (by rw [Q.norm_map])

/-! ### Consequences: `M⁻¹ a₀ M⁻† = I` and conjugated coefficients -/

omit [FiniteDimensional ℝ E] in
theorem adjoint_symm_comp_adjoint (M : E ≃L[ℝ] E) [CompleteSpace E] :
    adjoint (M.symm : E →L[ℝ] E) ∘L adjoint (M : E →L[ℝ] E) = 1 := by
  rw [← adjoint_comp]
  have : (M : E →L[ℝ] E) ∘L (M.symm : E →L[ℝ] E) = 1 := by ext; simp
  rw [this, adjoint_one]

omit [FiniteDimensional ℝ E] in
theorem adjoint_comp_adjoint_symm (M : E ≃L[ℝ] E) [CompleteSpace E] :
    adjoint (M : E →L[ℝ] E) ∘L adjoint (M.symm : E →L[ℝ] E) = 1 := by
  rw [← adjoint_comp]
  have : (M.symm : E →L[ℝ] E) ∘L (M : E →L[ℝ] E) = 1 := by ext; simp
  rw [this, adjoint_one]

/-- If `M M† = a₀` then `M⁻¹ a₀ M⁻† = I`. -/
theorem symm_comp_comp_adjoint_symm_eq_one {M : E ≃L[ℝ] E} {a₀ : E →L[ℝ] E}
    (hM : (M : E →L[ℝ] E) ∘L adjoint (M : E →L[ℝ] E) = a₀) :
    (M.symm : E →L[ℝ] E) ∘L a₀ ∘L adjoint (M.symm : E →L[ℝ] E) = 1 := by
  rw [← hM, comp_assoc, adjoint_comp_adjoint_symm]
  ext; simp

/-! ### Symmetric and skew parts -/

/-- The symmetric part `(a + a†) / 2` of an operator. -/
@[expose] noncomputable def symPart (a : E →L[ℝ] E) : E →L[ℝ] E := (2⁻¹ : ℝ) • (a + adjoint a)

/-- The skew part `(a - a†) / 2` of an operator. -/
@[expose] noncomputable def skewPart (a : E →L[ℝ] E) : E →L[ℝ] E := (2⁻¹ : ℝ) • (a - adjoint a)

theorem symPart_apply (a : E →L[ℝ] E) (ξ : E) :
    symPart a ξ = (2⁻¹ : ℝ) • (a ξ + adjoint a ξ) := rfl

theorem skewPart_apply (a : E →L[ℝ] E) (ξ : E) :
    skewPart a ξ = (2⁻¹ : ℝ) • (a ξ - adjoint a ξ) := rfl

theorem symPart_add_skewPart (a : E →L[ℝ] E) : symPart a + skewPart a = a := by
  ext ξ; simp only [add_apply, symPart_apply, skewPart_apply]; module

theorem isSymmetric_symPart (a : E →L[ℝ] E) : (symPart a : E →ₗ[ℝ] E).IsSymmetric := by
  intro ξ η
  simp only [coe_coe, symPart_apply, real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_add_right, adjoint_inner_left, adjoint_inner_right]
  ring

theorem adjoint_skewPart (a : E →L[ℝ] E) : adjoint (skewPart a) = -skewPart a := by
  refine ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  simp only [adjoint_inner_left, neg_apply, inner_neg_left, skewPart_apply, real_inner_smul_left,
    real_inner_smul_right, inner_sub_left, inner_sub_right, adjoint_inner_right,
    adjoint_inner_left]
  ring

theorem inner_symPart_self (a : E →L[ℝ] E) (ξ : E) : ⟪symPart a ξ, ξ⟫ = ⟪a ξ, ξ⟫ := by
  simp only [symPart_apply, real_inner_smul_left, inner_add_left, adjoint_inner_left]
  rw [real_inner_comm ξ (a ξ)]; ring

theorem norm_symPart_le (a : E →L[ℝ] E) : ‖symPart a‖ ≤ ‖a‖ := by
  have h : ‖adjoint a‖ = ‖a‖ := LinearIsometryEquiv.norm_map _ a
  unfold symPart
  calc ‖(2⁻¹ : ℝ) • (a + adjoint a)‖ ≤ ‖(2⁻¹ : ℝ)‖ * ‖a + adjoint a‖ :=
        opNorm_smul_le _ _
    _ ≤ 2⁻¹ * (‖a‖ + ‖adjoint a‖) := by
        rw [Real.norm_of_nonneg (by norm_num)]; gcongr; exact norm_add_le _ _
    _ = ‖a‖ := by rw [h]; ring

/-- **Interior normalization of a nonsymmetric coefficient**. If
`lam ‖ξ‖² ≤ ⟪a₀ ξ, ξ⟫` and `‖a₀‖ ≤ Λ` (no symmetry), there is `M` with `M M† = symPart a₀`,
`‖M‖ ≤ √Λ`, `‖M⁻¹‖ ≤ 1 / √lam`, and `M⁻¹ a₀ M⁻† = I + K` with `K = M⁻¹ (skewPart a₀) M⁻†` skew
(`K† = -K`). -/
theorem exists_sqrt_symPart {a₀ : E →L[ℝ] E} {lam Λ : ℝ} (hlam : 0 < lam)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪a₀ ξ, ξ⟫) (hbd : ‖a₀‖ ≤ Λ) :
    ∃ M : E ≃L[ℝ] E, (M : E →L[ℝ] E) ∘L adjoint (M : E →L[ℝ] E) = symPart a₀ ∧
      ‖(M : E →L[ℝ] E)‖ ≤ √Λ ∧ ‖(M.symm : E →L[ℝ] E)‖ ≤ 1 / √lam ∧
      (M.symm : E →L[ℝ] E) ∘L a₀ ∘L adjoint (M.symm : E →L[ℝ] E) =
        1 + (M.symm : E →L[ℝ] E) ∘L skewPart a₀ ∘L adjoint (M.symm : E →L[ℝ] E) ∧
      adjoint ((M.symm : E →L[ℝ] E) ∘L skewPart a₀ ∘L adjoint (M.symm : E →L[ℝ] E)) =
        -((M.symm : E →L[ℝ] E) ∘L skewPart a₀ ∘L adjoint (M.symm : E →L[ℝ] E)) := by
  obtain ⟨M, hM, -, hMn, hMn'⟩ := exists_sqrt hlam (isSymmetric_symPart a₀)
    (fun ξ ↦ (inner_symPart_self a₀ ξ).symm ▸ hell ξ) ((norm_symPart_le a₀).trans hbd)
  refine ⟨M, hM, hMn, hMn', ?_, ?_⟩
  · rw [← symm_comp_comp_adjoint_symm_eq_one hM]
    conv_lhs => rw [← symPart_add_skewPart a₀]
    rw [add_comp, comp_add]
  · rw [adjoint_comp, adjoint_comp, adjoint_adjoint, adjoint_skewPart]
    ext; simp

end BasicElliptic
