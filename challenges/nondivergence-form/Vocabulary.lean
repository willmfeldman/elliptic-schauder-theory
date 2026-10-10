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
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Vocabulary: headline theorems in nondivergence form, and the polynomial-approximation bridge

Challenge vocabulary: a Mathlib-only restatement, in this order and one part
per file, of the library files

* `BasicElliptic/Basic/HalfSpace.lean`
* `BasicElliptic/Defs/Holder.lean`
* `BasicElliptic/Defs/Elliptic.lean`
* `BasicElliptic/Defs/Nondiv.lean`

Each part keeps the library's names, definitions and order, with the theorems dropped, and
keeps its `open` commands inside its own section. `scripts/challenge-prep.py sync` copies this
file into the generated block of `Challenge.lean`; Comparator checks each copied declaration
against the library by name and value.
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

/-!
## `BasicElliptic/Defs/Holder.lean`

Hölder seminorms on sets, `C^{k,α}` on sets (`ContDiffHolderOn`), and the oscillation `regionOsc`.
-/

section

noncomputable section

open scoped NNReal ENNReal

namespace BasicElliptic

section Holder

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- The Hölder seminorm of exponent `α` of `f` on `s`, in `ℝ≥0∞`: the infimum of the constants `C`
with `HolderOnWith C α f s`. -/
def eHolderSeminormOn (α : ℝ≥0) (f : X → Y) (s : Set X) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : HolderOnWith C α f s), (C : ℝ≥0∞)

/-- The real Hölder seminorm `(eHolderSeminormOn α f s).toReal`. -/
def holderSeminormOn (α : ℝ≥0) (f : X → Y) (s : Set X) : ℝ :=
  (eHolderSeminormOn α f s).toReal

end Holder

section ContDiffHolder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `f` is `C^{k,α}` on `s`: `C^k` on `s` with derivatives taken within `s`, and the `k`-th
within-derivative is `α`-Hölder on `s` with some constant. -/
def ContDiffHolderOn (k : ℕ) (α : ℝ≥0) (f : E → F) (s : Set E) : Prop :=
  ContDiffOn ℝ k f s ∧ ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ k f s) s

end ContDiffHolder

/-- The oscillation `sup_s f - inf_s f` of a real function on a set, stated literally as
`sSup (f '' s) - sInf (f '' s)`. -/
def regionOsc {X : Type*} (f : X → ℝ) (s : Set X) : ℝ :=
  sSup (f '' s) - sInf (f '' s)

end BasicElliptic

end

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
