/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Vocabulary.Holder

/-!
# Vocabulary: `BasicElliptic/Defs/Elliptic.lean`

Part of the challenge vocabulary, split along the library's module boundaries (see
`../Vocabulary.lean`).
-/

@[expose] public section

/-!
## `BasicElliptic/Defs/Elliptic.lean`

uniform ellipticity and symmetry of coefficient fields.
-/

section

noncomputable section

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

end BasicElliptic

end
