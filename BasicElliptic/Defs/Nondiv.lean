/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Basic.HalfSpace
public import BasicElliptic.Defs.Holder
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Classical solutions in nondivergence form

* `BasicElliptic.Nondiv.op a b s w y = tr (a(y) D²w(y)) + ⟪b(y), ∇w(y)⟫`, all derivatives within
  `s`.

  **Trace convention.** `tr (a D²w)` is written as `∑ i, D²w(y) (a(y) eᵢ, eᵢ)` over the orthonormal
  basis `e = stdOrthonormalBasis ℝ E`. This is `tr (H ∘ a(y))` with `H` the Hessian operator, hence
  equals `tr (a(y) ∘ H)` and is independent of the orthonormal basis. Only the symmetric part of
  `a` contributes when `D²w(y)` is symmetric (e.g. `w` is `C²` near `y`). We use the basis form
  rather than `LinearMap.trace` to avoid the Riesz identification `(E →L[ℝ] ℝ) ≃ E`, which is
  semilinear and awkward to compose with.
* `BasicElliptic.Nondiv.IsSolOn a b f s w`: `w ∈ C²(s)` (within `s`) and `op a b s w = f` on `s`.
* Tier-1 flat boundary conditions, on `s ∩ flatPart ν`:
  `BasicElliptic.Nondiv.HasConormalBC ν a γ s w` (`⟪a(y) ν, ∇w(y)⟫ = γ(y)`) and
  `BasicElliptic.Nondiv.HasDirichletBC ν g s w` (`w = g`).
-/

@[expose] public noncomputable section

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
