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
public import Vocabulary.Elliptic

/-!
# Vocabulary: `BasicElliptic/Defs/Div.lean`

Part of the challenge vocabulary, split along the library's module boundaries (see
`../Vocabulary.lean`).
-/

@[expose] public section

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
