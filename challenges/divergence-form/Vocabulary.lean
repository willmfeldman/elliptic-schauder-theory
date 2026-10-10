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

/-!
# Vocabulary: headline theorems in divergence form, and Campanato's characterization

Challenge vocabulary: a Mathlib-only restatement, in this order and one part
per file, of the library files

* `BasicElliptic/Basic/HalfSpace.lean`
* `BasicElliptic/Defs/Holder.lean`
* `BasicElliptic/Defs/Elliptic.lean`
* `BasicElliptic/Defs/Div.lean`

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
## `BasicElliptic/Defs/Div.lean`

test functions, the divergence, and weak (and conormal) solutions in divergence form.
-/

section

noncomputable section

open MeasureTheory Metric RealInnerProductSpace
open scoped Gradient

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `φ ∈ C¹_c(U)`: `φ` is `C¹` on `E`, compactly supported, with `tsupport φ ⊆ U`. -/
def IsTestFn (U : Set E) (φ : E → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- The divergence `tr (DV(y))` of a vector field, coordinate-free (the trace of the Fréchet
derivative). -/
def divergence (V : E → E) (y : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ V y : E →ₗ[ℝ] E)

namespace Div

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The weak identity `∫_s ⟪a F, ∇φ⟫ = ∫_s ⟪G, ∇φ⟫ + ∫_s f φ` for all `φ ∈ C¹_c(U)`, for an
explicit field `F` (standing for `∇w`). -/
def IsWeakEqOn (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (F : E → E) (s U : Set E) : Prop :=
  ∀ φ : E → ℝ, IsTestFn U φ →
    ∫ y in s, ⟪a y (F y), ∇ φ y⟫ = (∫ y in s, ⟪G y, ∇ φ y⟫) + ∫ y in s, f y * φ y

/-- Region-general weak solution: `w ∈ C¹(s)` (derivatives within `s`) and the weak identity holds
over `s` with `∇w = gradientWithin w s`, against tests in `C¹_c(U)`. -/
def IsWeakSolWithin (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (s U : Set E) (w : E → ℝ) :
    Prop :=
  ContDiffOn ℝ 1 w s ∧ IsWeakEqOn a G f (gradientWithin w s) s U

/-- Interior weak solution of `-div (a ∇w - G) = f` on `U` (open in applications): `w ∈ C¹(U)`
and `∫_U ⟪a ∇w, ∇φ⟫ = ∫_U ⟪G, ∇φ⟫ + ∫_U f φ` for all `φ ∈ C¹_c(U)`. No symmetry of `a` is
assumed. -/
def IsWeakSolOn (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (U : Set E) (w : E → ℝ) : Prop :=
  ContDiffOn ℝ 1 w U ∧ IsWeakEqOn a G f (∇ w) U U

/-- Conormal weak solution on the closed half ball `B_r⁺ = halfBall ν x r`: `w ∈ C¹(B_r⁺)` and
`∫_{B_r⁺} ⟪a ∇w, ∇φ⟫ = ∫_{B_r⁺} ⟪G, ∇φ⟫ + ∫_{B_r⁺} f φ` for every `φ ∈ C¹_c(ball x r)`. The tests
need not vanish on the flat part; for smooth data this encodes `-div (a ∇w - G) = f` in
`B_r ∩ {⟪·, ν⟫ > 0}` and `⟪a ∇w - G, ν⟫ = 0` on `B_r ∩ flatPart ν`. -/
def IsConormalSolOn (ν : E) (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (x : E) (r : ℝ)
    (w : E → ℝ) : Prop :=
  IsWeakSolWithin a G f (halfBall ν x r) (ball x r) w

/-- Interior weak solution with an explicit gradient field `F`: `w` has gradient
`F y` at almost every `y ∈ U`, and `F` satisfies the weak identity on `U` against `C¹_c(U)`. This
is the notion satisfied by the even reflection of a conormal solution, which is only Lipschitz and
piecewise `C¹`. -/
def IsWeakSolOnField (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (U : Set E) (w : E → ℝ)
    (F : E → E) : Prop :=
  (∀ᵐ y ∂(volume.restrict U), HasGradientAt w (F y) y) ∧ IsWeakEqOn a G f F U U

/-- Quasilinear conormal weak solution on `B_r⁺ = halfBall ν x r`: `w ∈ C¹(B_r⁺)` and
`∫_{B_r⁺} ⟪Φ(∇w), ∇φ⟫ = 0` for every `φ ∈ C¹_c(ball x r)` (encoding `div Φ(∇w) = 0` with the
conormal condition `⟪Φ(∇w), ν⟫ = 0` on the flat part). -/
def IsQuasilinearConormalSolOn (ν : E) (Φ : E → E) (x : E) (r : ℝ) (w : E → ℝ) : Prop :=
  ContDiffOn ℝ 1 w (halfBall ν x r) ∧
    ∀ φ : E → ℝ, IsTestFn (ball x r) φ →
      ∫ y in halfBall ν x r, ⟪Φ (gradientWithin w (halfBall ν x r) y), ∇ φ y⟫ = 0

end Div

end BasicElliptic

end
