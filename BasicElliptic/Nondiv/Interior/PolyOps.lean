/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Poly.Quadratic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Operations on quadratic polynomials for the nondivergence iteration

Complements `BasicElliptic/Poly/Quadratic.lean` with what the sup-norm Campanato iteration of
`Nondiv/Interior/Iterate.lean` needs:

* `QuadPoly` addition and real scalar multiplication (`eval_add`, `eval_smul`);
* `QuadPoly.sumNorm P = |const| + ‖lin‖ + ‖quad‖`, the coefficient size used by the iteration
  (it controls `quad`, which is not assumed symmetric), with the evaluation bound
  `abs_eval_le_sumNorm_mul`;
* `QuadPoly.trace P = ∑ᵢ quad eᵢ eᵢ` over `stdOrthonormalBasis ℝ E`, and
  `QuadPoly.laplacian_eval`: `Δ P.eval = P.trace`;
* `QuadPoly.compCLM P L`: `(P.compCLM L).eval z = P.eval (L z)`;
* `QuadPoly.toTriple`: the coefficients as an element of a complete space, for limits.

## Provenance

Elliptic analogue of the coefficient lemmas of `CaloricPoly` in parabolic-basic-theory,
`ParabolicBasic/Schauder/Iteration/Iterate.lean` (own repository, commit
`2507d9a800377e91c591862286b2ba2d6464d918`).
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Laplacian
open InnerProductSpace ContinuousLinearMap

namespace BasicElliptic

namespace QuadPoly

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : Add (QuadPoly E) := ⟨fun P Q ↦ ⟨P.const + Q.const, P.lin + Q.lin, P.quad + Q.quad⟩⟩

instance : SMul ℝ (QuadPoly E) := ⟨fun c P ↦ ⟨c * P.const, c • P.lin, c • P.quad⟩⟩

instance : Zero (QuadPoly E) := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem add_const (P Q : QuadPoly E) : (P + Q).const = P.const + Q.const := rfl
@[simp] theorem add_lin (P Q : QuadPoly E) : (P + Q).lin = P.lin + Q.lin := rfl
@[simp] theorem add_quad (P Q : QuadPoly E) : (P + Q).quad = P.quad + Q.quad := rfl
@[simp] theorem smul_const (c : ℝ) (P : QuadPoly E) : (c • P).const = c * P.const := rfl
@[simp] theorem smul_lin (c : ℝ) (P : QuadPoly E) : (c • P).lin = c • P.lin := rfl
@[simp] theorem smul_quad (c : ℝ) (P : QuadPoly E) : (c • P).quad = c • P.quad := rfl
@[simp] theorem zero_const : (0 : QuadPoly E).const = 0 := rfl
@[simp] theorem zero_lin : (0 : QuadPoly E).lin = 0 := rfl
@[simp] theorem zero_quad : (0 : QuadPoly E).quad = 0 := rfl
@[simp] theorem rescale_const (P : QuadPoly E) (r : ℝ) : (P.rescale r).const = P.const := rfl
@[simp] theorem rescale_lin (P : QuadPoly E) (r : ℝ) : (P.rescale r).lin = r • P.lin := rfl
@[simp] theorem rescale_quad (P : QuadPoly E) (r : ℝ) : (P.rescale r).quad = r ^ 2 • P.quad :=
  rfl

@[simp] theorem eval_add (P Q : QuadPoly E) (z : E) : (P + Q).eval z = P.eval z + Q.eval z := by
  simp only [eval, add_const, add_lin, add_quad, add_apply]; ring

@[simp] theorem eval_smul (c : ℝ) (P : QuadPoly E) (z : E) : (c • P).eval z = c * P.eval z := by
  simp only [eval, smul_const, smul_lin, smul_quad, smul_apply, smul_eq_mul]
  ring

@[simp] theorem eval_zero_poly (z : E) : (0 : QuadPoly E).eval z = 0 := by simp [eval]

/-- The coefficient size `|const| + ‖lin‖ + ‖quad‖`. -/
def sumNorm (P : QuadPoly E) : ℝ := |P.const| + ‖P.lin‖ + ‖P.quad‖

theorem sumNorm_nonneg (P : QuadPoly E) : 0 ≤ P.sumNorm := by unfold sumNorm; positivity

theorem abs_const_le_sumNorm (P : QuadPoly E) : |P.const| ≤ P.sumNorm := by
  unfold sumNorm; linarith [norm_nonneg P.lin, norm_nonneg P.quad]

theorem norm_lin_le_sumNorm (P : QuadPoly E) : ‖P.lin‖ ≤ P.sumNorm := by
  unfold sumNorm; linarith [abs_nonneg P.const, norm_nonneg P.quad]

theorem norm_quad_le_sumNorm (P : QuadPoly E) : ‖P.quad‖ ≤ P.sumNorm := by
  unfold sumNorm; linarith [abs_nonneg P.const, norm_nonneg P.lin]

theorem sumNorm_add_le (P Q : QuadPoly E) : (P + Q).sumNorm ≤ P.sumNorm + Q.sumNorm := by
  simp only [sumNorm, add_const, add_lin, add_quad]
  linarith [abs_add_le P.const Q.const, norm_add_le P.lin Q.lin, norm_add_le P.quad Q.quad]

/-- The crude evaluation bound `|P z| ≤ |c| + ‖ℓ‖ ‖z‖ + ‖B‖ ‖z‖²`. -/
theorem abs_eval_le (P : QuadPoly E) (z : E) :
    |P.eval z| ≤ |P.const| + ‖P.lin‖ * ‖z‖ + ‖P.quad‖ * ‖z‖ ^ 2 := by
  have h1 : |P.lin z| ≤ ‖P.lin‖ * ‖z‖ := by
    rw [← Real.norm_eq_abs]; exact P.lin.le_opNorm z
  have h2 : |P.quad z z| ≤ ‖P.quad‖ * ‖z‖ ^ 2 := by
    rw [← Real.norm_eq_abs, sq, ← mul_assoc]; exact P.quad.le_opNorm₂ z z
  have h3 : |(1 / 2 : ℝ) * P.quad z z| ≤ |P.quad z z| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by norm_num [abs_of_pos])
  unfold eval
  linarith [abs_add_le (P.const + P.lin z) ((1 / 2 : ℝ) * P.quad z z),
    abs_add_le P.const (P.lin z)]

/-- For `‖z‖ ≤ s` with `1 ≤ s`: `|P z| ≤ sumNorm P · s²`. -/
theorem abs_eval_le_sumNorm_mul (P : QuadPoly E) {z : E} {s : ℝ} (hs : 1 ≤ s) (hz : ‖z‖ ≤ s) :
    |P.eval z| ≤ P.sumNorm * s ^ 2 := by
  have h := P.abs_eval_le z
  have e1 : ‖P.lin‖ * ‖z‖ ≤ ‖P.lin‖ * s ^ 2 :=
    mul_le_mul_of_nonneg_left (hz.trans (by nlinarith)) (norm_nonneg _)
  have e2 : ‖P.quad‖ * ‖z‖ ^ 2 ≤ ‖P.quad‖ * s ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) (norm_nonneg _)
  have e3 : |P.const| ≤ |P.const| * s ^ 2 := le_mul_of_one_le_right (abs_nonneg _) (by nlinarith)
  unfold sumNorm
  nlinarith

/-- The coefficient size of the increment `c • P.rescale t`. -/
theorem sumNorm_smul_rescale (P : QuadPoly E) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    (c • P.rescale t).sumNorm = c * (|P.const| + t * ‖P.lin‖ + t ^ 2 * ‖P.quad‖) := by
  simp only [sumNorm, smul_const, smul_lin, smul_quad, rescale_const, rescale_lin, rescale_quad,
    abs_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg ht,
    abs_of_nonneg (sq_nonneg t)]
  ring

/-- The coefficients as an element of the complete space `ℝ × E* × (E →L E →L ℝ)`. -/
def toTriple (P : QuadPoly E) : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) :=
  (P.const, P.lin, P.quad)

/-- The polynomial with given coefficients. -/
def ofTriple (p : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ)) : QuadPoly E := ⟨p.1, p.2.1, p.2.2⟩

@[simp] theorem ofTriple_toTriple (P : QuadPoly E) : ofTriple P.toTriple = P := rfl

theorem dist_toTriple_add_le (P Q : QuadPoly E) :
    dist P.toTriple (P + Q).toTriple ≤ Q.sumNorm := by
  rw [toTriple, toTriple, Prod.dist_eq, Prod.dist_eq]
  simp only [add_const, add_lin, add_quad, dist_eq_norm, sub_add_cancel_left,
    norm_neg, Real.norm_eq_abs]
  have := Q.abs_const_le_sumNorm
  have := Q.norm_lin_le_sumNorm
  have := Q.norm_quad_le_sumNorm
  exact max_le (by linarith) (max_le (by linarith) (by linarith))

theorem continuous_eval_ofTriple (z : E) :
    Continuous fun p : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ (ofTriple p).eval z := by
  simp only [eval, ofTriple]
  fun_prop

theorem continuous_sumNorm_ofTriple :
    Continuous fun p : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ (ofTriple p).sumNorm := by
  simp only [sumNorm, ofTriple]
  fun_prop

/-- Composition with a continuous linear map: `(P.compCLM L).eval z = P.eval (L z)`. -/
def compCLM (P : QuadPoly E) (L : E →L[ℝ] E) : QuadPoly E :=
  ⟨P.const, P.lin.comp L, P.quad.bilinearComp L L⟩

@[simp] theorem eval_compCLM (P : QuadPoly E) (L : E →L[ℝ] E) (z : E) :
    (P.compCLM L).eval z = P.eval (L z) := by
  simp [compCLM, eval, ContinuousLinearMap.bilinearComp_apply]

theorem norm_lin_compCLM_le (P : QuadPoly E) (L : E →L[ℝ] E) :
    ‖(P.compCLM L).lin‖ ≤ ‖P.lin‖ * ‖L‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

theorem norm_quad_compCLM_le (P : QuadPoly E) (L : E →L[ℝ] E) :
    ‖(P.compCLM L).quad‖ ≤ ‖P.quad‖ * ‖L‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun x y ↦ ?_
  simp only [compCLM, ContinuousLinearMap.bilinearComp_apply]
  calc ‖P.quad (L x) (L y)‖ ≤ ‖P.quad‖ * ‖L x‖ * ‖L y‖ := P.quad.le_opNorm₂ _ _
    _ ≤ ‖P.quad‖ * (‖L‖ * ‖x‖) * (‖L‖ * ‖y‖) := by
        gcongr <;> exact L.le_opNorm _
    _ = ‖P.quad‖ * ‖L‖ * ‖L‖ * ‖x‖ * ‖y‖ := by ring

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The trace `∑ᵢ quad eᵢ eᵢ` over `stdOrthonormalBasis ℝ E`: the Laplacian of `eval`. -/
def trace (P : QuadPoly E) : ℝ :=
  ∑ i, P.quad (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)

@[simp] theorem trace_add (P Q : QuadPoly E) : (P + Q).trace = P.trace + Q.trace := by
  simp [trace, Finset.sum_add_distrib]

@[simp] theorem trace_smul (c : ℝ) (P : QuadPoly E) : (c • P).trace = c * P.trace := by
  simp [trace, Finset.mul_sum]

@[simp] theorem trace_rescale (P : QuadPoly E) (r : ℝ) : (P.rescale r).trace = r ^ 2 * P.trace :=
  by simp [trace, Finset.mul_sum]

theorem continuous_trace_ofTriple :
    Continuous fun p : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ (ofTriple p).trace := by
  simp only [trace, ofTriple]
  fun_prop

omit [FiniteDimensional ℝ E] in
theorem fderiv_fderiv_eval (P : QuadPoly E) (z : E) :
    fderiv ℝ (fderiv ℝ P.eval) z = P.hess := by
  have : fderiv ℝ P.eval = fun z ↦ P.lin + P.hess z := funext P.fderiv_eval
  rw [this, fderiv_const_add]
  exact P.hess.fderiv

/-- `Δ P = tr P`. -/
theorem laplacian_eval (P : QuadPoly E) (z : E) : Δ P.eval z = P.trace := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, fderiv_fderiv_eval, trace]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [hess_self]

/-- The isotropic quadratic `z ↦ (σ / (2 dim E)) ‖z‖²`, with trace `σ`. -/
def isotropic (σ : ℝ) : QuadPoly E :=
  ⟨0, 0, (σ / Module.finrank ℝ E) • innerSL ℝ⟩

theorem trace_isotropic [Nontrivial E] (σ : ℝ) : (isotropic σ : QuadPoly E).trace = σ := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  have hterm : ∀ i, (isotropic σ : QuadPoly E).quad (stdOrthonormalBasis ℝ E i)
      (stdOrthonormalBasis ℝ E i) = σ / Module.finrank ℝ E := fun i ↦ by
    simp only [isotropic, smul_apply, smul_eq_mul]
    change σ / _ * ⟪stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i⟫_ℝ = _
    rw [real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ E).orthonormal.1 i, one_pow, mul_one]
  simp only [trace, hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  field_simp

theorem norm_quad_isotropic_le [Nontrivial E] (σ : ℝ) :
    ‖(isotropic σ : QuadPoly E).quad‖ ≤ |σ| := by
  have hd : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  simp only [isotropic]
  calc ‖(σ / Module.finrank ℝ E) • innerSL ℝ (E := E)‖
      ≤ ‖σ / Module.finrank ℝ E‖ * ‖innerSL ℝ (E := E)‖ := norm_smul_le _ _
    _ ≤ |σ| / Module.finrank ℝ E * 1 := by
        rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
        gcongr
        exact norm_innerSL_le ℝ
    _ ≤ |σ| := by rw [mul_one]; exact div_le_self (abs_nonneg _) hd

theorem sumNorm_isotropic_le [Nontrivial E] (σ : ℝ) :
    (isotropic σ : QuadPoly E).sumNorm ≤ |σ| := by
  have := norm_quad_isotropic_le (E := E) σ
  simp only [sumNorm] at this ⊢
  simpa [isotropic] using this

theorem abs_eval_isotropic_le [Nontrivial E] (σ : ℝ) (z : E) :
    |(isotropic σ : QuadPoly E).eval z| ≤ |σ| * ‖z‖ ^ 2 := by
  have h := (isotropic σ : QuadPoly E).abs_eval_le z
  have hq := norm_quad_isotropic_le (E := E) σ
  simp only [isotropic, abs_zero, norm_zero, zero_mul, zero_add] at h hq
  exact h.trans (mul_le_mul_of_nonneg_right hq (by positivity))

end Inner

end QuadPoly

end BasicElliptic
