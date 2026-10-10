/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Uniform ellipticity of coefficient fields

Coefficients are fields of continuous linear maps `a : E → E →L[ℝ] E` (not matrices).
`Matrix`-based coefficients on `EuclideanSpace ℝ (Fin d)` are transported with Mathlib's
`Matrix.toEuclideanCLM`.

* `BasicElliptic.IsUniformlyElliptic lam Λ a s`: `lam ‖ξ‖² ≤ ⟪a y ξ, ξ⟫` and `‖a y‖ ≤ Λ` for
  `y ∈ s`. No symmetry is assumed: the interior divergence-form theory allows nonsymmetric
  `a`.
* `BasicElliptic.IsSymmetricOn a s`: `a y` is symmetric for `y ∈ s`. The conormal (flat-boundary)
  divergence-form statements assume it.
-/

@[expose] public noncomputable section

open RealInnerProductSpace

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniform ellipticity with constants `lam` (lower) and `Λ` (upper) on `s`:
`lam ‖ξ‖² ≤ ⟪a y ξ, ξ⟫` and `‖a y‖ ≤ Λ` for all `y ∈ s` and `ξ`. No symmetry is assumed. -/
def IsUniformlyElliptic (lam Λ : ℝ) (a : E → E →L[ℝ] E) (s : Set E) : Prop :=
  ∀ y ∈ s, (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪a y ξ, ξ⟫) ∧ ‖a y‖ ≤ Λ

/-- The coefficient field `a` is symmetric on `s`: `⟪a y ξ, η⟫ = ⟪ξ, a y η⟫` for `y ∈ s`. -/
def IsSymmetricOn (a : E → E →L[ℝ] E) (s : Set E) : Prop :=
  ∀ y ∈ s, (a y : E →ₗ[ℝ] E).IsSymmetric

theorem IsUniformlyElliptic.mono {lam Λ : ℝ} {a : E → E →L[ℝ] E} {s t : Set E}
    (h : IsUniformlyElliptic lam Λ a t) (hst : s ⊆ t) : IsUniformlyElliptic lam Λ a s :=
  fun y hy ↦ h y (hst hy)

theorem IsSymmetricOn.mono {a : E → E →L[ℝ] E} {s t : Set E} (h : IsSymmetricOn a t)
    (hst : s ⊆ t) : IsSymmetricOn a s :=
  fun y hy ↦ h y (hst hy)

end BasicElliptic
