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

/-!
# Vocabulary: `BasicElliptic/Basic/HalfSpace.lean`

Part of the challenge vocabulary, split along the library's module boundaries (see
`../Vocabulary.lean`).
-/

@[expose] public section

/-!
## `BasicElliptic/Basic/HalfSpace.lean`

half spaces, the flat part, closed half balls, and the reflection across the flat part.
-/

section

noncomputable section

open Metric Set RealInnerProductSpace

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Definitions -/

/-- The closed half space `{x | 0 ≤ ⟪x, ν⟫}`. -/
def halfSpace (ν : E) : Set E := {x | 0 ≤ ⟪x, ν⟫}

/-- The open half space `{x | 0 < ⟪x, ν⟫}`. -/
def openHalfSpace (ν : E) : Set E := {x | 0 < ⟪x, ν⟫}

/-- The flat part `{x | ⟪x, ν⟫ = 0}`, the boundary hyperplane of `halfSpace ν`. -/
def flatPart (ν : E) : Set E := {x | ⟪x, ν⟫ = 0}

/-- The closed half ball `closedBall x r ∩ halfSpace ν`. -/
def halfBall (ν x : E) (r : ℝ) : Set E := closedBall x r ∩ halfSpace ν


/-! ### Reflection across the flat part -/

/-- The reflection across `flatPart ν`: Mathlib's reflection in the hyperplane `(ℝ ∙ ν)ᗮ`. For
`‖ν‖ = 1` it is `y ↦ y - 2 ⟪y, ν⟫ ν` (`reflect_apply`). -/
def reflect (ν : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ν)ᗮ.reflection

/-- The fold onto the half space: the identity on `halfSpace ν`, `reflect ν` off it. -/
def fold (ν : E) (y : E) : E := if 0 ≤ ⟪y, ν⟫ then y else reflect ν y

/-- The even extension `h ∘ fold ν` of a function given on `halfSpace ν`. -/
def evenExt {β : Type*} (ν : E) (h : E → β) (y : E) : β := h (fold ν y)

/-- The odd extension of a real function given on `halfSpace ν`: `h` on the half space and
`-h ∘ reflect ν` off it. -/
def oddExt (ν : E) (h : E → ℝ) (y : E) : ℝ :=
  if 0 ≤ ⟪y, ν⟫ then h y else -h (reflect ν y)

/-- Even reflection of a vector field: `G` on the half space, `R (G (R y))` off it
(`R = reflect ν`). Off the flat part, `∇(w ∘ fold ν) = reflectField ν (∇w)`. -/
def reflectField (ν : E) (G : E → E) (y : E) : E :=
  if 0 ≤ ⟪y, ν⟫ then G y else reflect ν (G (reflect ν y))

/-- Even reflection of a coefficient field: `a` on the half space, `R ∘ a (R y) ∘ R` off it
(`R = reflect ν`). -/
def reflectCoeff (ν : E) (a : E → E →L[ℝ] E) (y : E) : E →L[ℝ] E :=
  if 0 ≤ ⟪y, ν⟫ then a y
  else (reflect ν : E →L[ℝ] E) ∘L a (reflect ν y) ∘L (reflect ν : E →L[ℝ] E)

end BasicElliptic

end
