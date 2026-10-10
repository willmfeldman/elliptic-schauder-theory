/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Quadratic polynomials on a normed space

`BasicElliptic.QuadPoly E` is a quadratic polynomial `z ↦ c + ℓ z + ½ B z z` on a real normed
space `E`, stored coordinate-free by its constant term `const : ℝ`, linear part
`lin : E →L[ℝ] ℝ` and bilinear part `quad : E →L[ℝ] E →L[ℝ] ℝ`. This is the shape of the frozen
`PolyApproxBridgeStatement` (`P0 p + P1 p z + ½ P2 p z z`), so `quad` is **not** assumed
symmetric; only its symmetrization `hess = ½ (quad + quad.flip)` is seen by `eval`
(`eval_eq_hess`).

* `QuadPoly.eval`, `QuadPoly.hess` (symmetric: `hess_comm`);
* `QuadPoly.IsDegLE k`: degree filters (`k = 0`: constant, `k = 1`: affine);
* `QuadPoly.shift P h`: the recentred polynomial, `(P.shift h).eval z = P.eval (z + h)`;
* `QuadPoly.rescale P r`: `(P.rescale r).eval z = P.eval (r • z)`;
* calculus: `hasFDerivAt_eval` (`D P (z) = ℓ + hess z`), `contDiff_eval`.

## Provenance

Elliptic, coordinate-free analogue of `CaloricPoly` (`a, b, c, M`) in parabolic-basic-theory,
`ParabolicBasic/Schauder/Poly.lean` (own repository, commit
`2507d9a800377e91c591862286b2ba2d6464d918`): the time coefficient is dropped, and the symmetric
matrix `M` is replaced by a (not necessarily symmetric) continuous bilinear form, as in the frozen
statement.
-/

@[expose] public noncomputable section

open scoped Topology

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (E) in
/-- A quadratic polynomial `z ↦ const + lin z + ½ quad z z` on `E`. -/
@[ext] structure QuadPoly where
  /-- The constant term (value at the origin). -/
  const : ℝ
  /-- The linear part (derivative at the origin). -/
  lin : E →L[ℝ] ℝ
  /-- The bilinear part; only its symmetrization `hess` matters. -/
  quad : E →L[ℝ] E →L[ℝ] ℝ

namespace QuadPoly

/-- Evaluation `const + lin z + ½ quad z z` (the expression of `PolyApproxBridgeStatement`). -/
noncomputable def eval (P : QuadPoly E) (z : E) : ℝ :=
  P.const + P.lin z + (1 / 2 : ℝ) * P.quad z z

/-- The symmetric part `½ (quad + quad.flip)` of the bilinear term: the Hessian of `eval`. -/
noncomputable def hess (P : QuadPoly E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (P.quad + P.quad.flip)

theorem hess_apply (P : QuadPoly E) (v w : E) :
    P.hess v w = (1 / 2 : ℝ) * (P.quad v w + P.quad w v) := by
  simp [hess]; ring

theorem hess_comm (P : QuadPoly E) (v w : E) : P.hess v w = P.hess w v := by
  rw [hess_apply, hess_apply, add_comm]

theorem hess_self (P : QuadPoly E) (v : E) : P.hess v v = P.quad v v := by
  rw [hess_apply]; ring

theorem eval_eq_hess (P : QuadPoly E) (z : E) :
    P.eval z = P.const + P.lin z + (1 / 2 : ℝ) * P.hess z z := by
  rw [eval, hess_self]

@[simp] theorem eval_zero (P : QuadPoly E) : P.eval 0 = P.const := by simp [eval]

/-- Degree filters: `IsDegLE 0` is constant, `IsDegLE 1` affine, `IsDegLE (k + 2)` arbitrary. -/
def IsDegLE (P : QuadPoly E) : ℕ → Prop
  | 0 => P.lin = 0 ∧ P.quad = 0
  | 1 => P.quad = 0
  | _ + 2 => True

instance : Sub (QuadPoly E) := ⟨fun P Q ↦ ⟨P.const - Q.const, P.lin - Q.lin, P.quad - Q.quad⟩⟩

@[simp] theorem sub_const (P Q : QuadPoly E) : (P - Q).const = P.const - Q.const := rfl
@[simp] theorem sub_lin (P Q : QuadPoly E) : (P - Q).lin = P.lin - Q.lin := rfl
@[simp] theorem sub_quad (P Q : QuadPoly E) : (P - Q).quad = P.quad - Q.quad := rfl

@[simp] theorem eval_sub (P Q : QuadPoly E) (z : E) : (P - Q).eval z = P.eval z - Q.eval z := by
  simp only [eval, sub_const, sub_lin, sub_quad, sub_apply]; ring

theorem hess_sub (P Q : QuadPoly E) : (P - Q).hess = P.hess - Q.hess := by
  ext v w; simp only [hess_apply, sub_quad, sub_apply]; ring

/-- The polynomial recentred at `h`: `(P.shift h).eval z = P.eval (z + h)`. -/
noncomputable def shift (P : QuadPoly E) (h : E) : QuadPoly E :=
  ⟨P.eval h, P.lin + P.hess h, P.quad⟩

@[simp] theorem shift_const (P : QuadPoly E) (h : E) : (P.shift h).const = P.eval h := rfl
@[simp] theorem shift_lin (P : QuadPoly E) (h : E) : (P.shift h).lin = P.lin + P.hess h := rfl
@[simp] theorem shift_quad (P : QuadPoly E) (h : E) : (P.shift h).quad = P.quad := rfl

@[simp] theorem hess_shift (P : QuadPoly E) (h : E) : (P.shift h).hess = P.hess := rfl

@[simp] theorem eval_shift (P : QuadPoly E) (h z : E) : (P.shift h).eval z = P.eval (z + h) := by
  simp only [eval, shift_const, shift_lin, shift_quad, add_apply, map_add,
    hess_apply]
  ring

/-- The polynomial rescaled by `r`: `(P.rescale r).eval z = P.eval (r • z)`. -/
noncomputable def rescale (P : QuadPoly E) (r : ℝ) : QuadPoly E :=
  ⟨P.const, r • P.lin, (r ^ 2) • P.quad⟩

@[simp] theorem eval_rescale (P : QuadPoly E) (r : ℝ) (z : E) :
    (P.rescale r).eval z = P.eval (r • z) := by
  simp only [eval, rescale, smul_apply, map_smul, smul_eq_mul]; ring

/-! ### Calculus -/

theorem hasFDerivAt_eval (P : QuadPoly E) (z : E) :
    HasFDerivAt P.eval (P.lin + P.hess z) z := by
  have hq : HasFDerivAt (fun y ↦ P.quad y y) (P.quad z + P.quad.flip z) z := by
    exact (P.quad.hasFDerivAt.clm_apply (hasFDerivAt_id z)).congr_fderiv (by ext v; simp)
  have := ((hasFDerivAt_const P.const z).add P.lin.hasFDerivAt).add (hq.const_mul (1 / 2 : ℝ))
  exact this.congr_fderiv (by ext v; simp [hess])

theorem fderiv_eval (P : QuadPoly E) (z : E) : fderiv ℝ P.eval z = P.lin + P.hess z :=
  (P.hasFDerivAt_eval z).fderiv

theorem contDiff_eval (P : QuadPoly E) {n : WithTop ℕ∞} : ContDiff ℝ n P.eval :=
  (contDiff_const.add P.lin.contDiff).add
    (contDiff_const.mul (P.quad.contDiff.clm_apply contDiff_id))

theorem continuous_eval (P : QuadPoly E) : Continuous P.eval :=
  (P.contDiff_eval (n := 0)).continuous

end QuadPoly

end BasicElliptic
