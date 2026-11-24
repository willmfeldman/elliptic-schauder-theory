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
public import Vocabulary.Div

/-!
# Vocabulary: `BasicElliptic/Defs/Nondiv.lean`

Part of the challenge vocabulary, split along the library's module boundaries (see
`../Vocabulary.lean`).
-/

@[expose] public section

/-!
## `BasicElliptic/Defs/Nondiv.lean`

the nondivergence operator `tr (a D²w) + ⟪b, ∇w⟫`, classical solutions and flat boundary conditions. The trace `tr (a(y) D²w(y))` is written `∑ i, D²w(y) (a(y) eᵢ, eᵢ)` over the orthonormal basis `e = stdOrthonormalBasis ℝ E`; it is `tr (H ∘ a(y))` for the Hessian operator `H`, hence independent of the orthonormal basis.
-/

section

noncomputable section

open RealInnerProductSpace

namespace BasicElliptic

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The nondivergence operator `tr (a(y) D²w(y)) + ⟪b(y), ∇w(y)⟫` with derivatives within `s`. The
trace is `∑ i, D²w(y) (a(y) eᵢ, eᵢ)` over `e = stdOrthonormalBasis ℝ E` (basis independent; see the
module docstring). -/
def op (a : E → E →L[ℝ] E) (b : E → E) (s : Set E) (w : E → ℝ) (y : E) : ℝ :=
  (∑ i, iteratedFDerivWithin ℝ 2 w s y
      ![a y (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E i]) +
    ⟪b y, gradientWithin w s y⟫

/-- Classical solution of `tr (a D²w) + ⟪b, ∇w⟫ = f` on `s`: `w ∈ C²(s)` with derivatives within
`s`, and the equation holds at every point of `s`. -/
def IsSolOn (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ) (s : Set E) (w : E → ℝ) : Prop :=
  ContDiffOn ℝ 2 w s ∧ ∀ y ∈ s, op a b s w y = f y

end Nondiv

namespace Nondiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Tier-1 conormal-compatible boundary condition `⟪a(y) ν, ∇w(y)⟫ = γ(y)` on `s ∩ flatPart ν`
(gradient within `s`). -/
def HasConormalBC (ν : E) (a : E → E →L[ℝ] E) (γ : E → ℝ) (s : Set E) (w : E → ℝ) : Prop :=
  ∀ y ∈ s ∩ flatPart ν, ⟪a y ν, gradientWithin w s y⟫ = γ y

/-- Dirichlet boundary condition `w = g` on `s ∩ flatPart ν`. -/
def HasDirichletBC (ν : E) (g : E → ℝ) (s : Set E) (w : E → ℝ) : Prop :=
  ∀ y ∈ s ∩ flatPart ν, w y = g y

end Nondiv

end BasicElliptic

end
