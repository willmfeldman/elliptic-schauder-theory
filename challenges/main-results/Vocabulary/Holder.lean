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
public import Vocabulary.HalfSpace

/-!
# Vocabulary: `BasicElliptic/Defs/Holder.lean`

Part of the challenge vocabulary, split along the library's module boundaries (see
`../Vocabulary.lean`).
-/

@[expose] public section

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
