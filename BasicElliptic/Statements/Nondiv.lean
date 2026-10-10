/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Nondiv
public import BasicElliptic.Defs.Elliptic
public import BasicElliptic.Defs.Holder

/-!
# Headline statements: nondivergence form

One `def …Statement : Prop` per headline result; proofs live in the files named in their
docstrings. Conventions as in `BasicElliptic/Statements/Div.lean`. Specific to nondivergence form:

* only qualitative `C²` regularity of the solution is assumed: `C²` on the open ball for the
  interior results, `C²` on the closed half ball for the tier-1 boundary results;
* tier-1 boundary conditions: the conormal-compatible condition `⟪a ν, ∇w⟫ = γ` with
  `a ν` and `γ` of class `C^{1,α}` along the flat part (expressed by a `C^{1,α}` field `β` on the
  half ball agreeing with `a ν` on the flat part, and `γ ∈ C^{1,α}` on the half ball), and `a`
  symmetric so that the condition is conormal rather than oblique; or the Dirichlet condition
  `w = g` with `g ∈ C^{2,α}`. Centres lie on the flat part. The tier-1 statements are qualitative;
  a scaled estimate can be added later.

## References

* [GT] D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  reprint of the 1998 edition, Classics in Mathematics, Springer, 2001.
* L. A. Caffarelli, *Interior a priori estimates for solutions of fully non-linear equations*,
  Ann. of Math. (2) 130 (1989), no. 1, 189–213.
-/

@[expose] public noncomputable section

open Metric Set RealInnerProductSpace
open scoped NNReal

namespace BasicElliptic

namespace Nondiv

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Interior Schauder regularity, nondivergence form** (GT; Caffarelli's
polynomial-approximation proof). A `C²` solution of `tr (a D²w) + ⟪b, ∇w⟫ = f` on an open `U`,
with `a` uniformly elliptic and `a, b, f ∈ C^α`, is `C^{2,α}` on every closed ball in `U`. Proved
by `Nondiv.contDiffHolderOn_two_of_isSolution` (`Nondiv/Interior/Main.lean`). -/
def SchauderInteriorStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ (U : Set E) (lam Λ : ℝ) (Ka Kb Kf : ℝ≥0) (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ)
    (w : E → ℝ),
    IsOpen U → 0 < lam → IsUniformlyElliptic lam Λ a U →
    HolderOnWith Ka α a U → HolderOnWith Kb α b U → HolderOnWith Kf α f U →
    IsSolOn a b f U w →
    ∀ (z : E) (ρ : ℝ), closedBall z ρ ⊆ U → ContDiffHolderOn 2 α w (closedBall z ρ)

/-- **Scaled interior Schauder estimate, nondivergence form** (GT, scaled):
`r² |D²w(x)| + r^{2+α} [D²w]_{α, B_{r/2}} ≤ C (osc_{B_r} w + r² ‖f‖_∞ + r^{2+α} [f]_α)`, with
`C = C(E, α, lam, Λ, K)` whenever the scale-invariant coefficient bounds
`[a]_α r^α ≤ K` and `r ‖b‖_∞ + r^{1+α} [b]_α ≤ K` hold. Proved by
`Nondiv.schauder_ball_estimate` (`Nondiv/Interior/Main.lean`). -/
def SchauderBallEstimateStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 → ∀ (lam Λ K : ℝ), 0 < lam →
  ∃ C : ℝ, ∀ (x : E) (r : ℝ) (Ka Kb Kf : ℝ≥0) (Mb Mf : ℝ) (a : E → E →L[ℝ] E) (b : E → E)
    (f : E → ℝ) (w : E → ℝ),
    0 < r → IsUniformlyElliptic lam Λ a (ball x r) →
    HolderOnWith Ka α a (ball x r) → (Ka : ℝ) * r ^ (α : ℝ) ≤ K →
    HolderOnWith Kb α b (ball x r) → (∀ y ∈ ball x r, ‖b y‖ ≤ Mb) →
    r * Mb + r ^ (1 + (α : ℝ)) * Kb ≤ K →
    HolderOnWith Kf α f (ball x r) → (∀ y ∈ ball x r, |f y| ≤ Mf) →
    ContinuousOn w (closedBall x r) → IsSolOn a b f (ball x r) w →
    r ^ 2 * ‖iteratedFDeriv ℝ 2 w x‖ +
        r ^ (2 + (α : ℝ)) * holderSeminormOn α (iteratedFDeriv ℝ 2 w) (closedBall x (r / 2)) ≤
      C * (regionOsc w (closedBall x r) + r ^ 2 * Mf + r ^ (2 + (α : ℝ)) * Kf)

/-- **Tier-1 boundary Schauder regularity, conormal-compatible condition** (GT).
Let the centre lie on the flat part, `a` be symmetric, uniformly elliptic and `C^α`,
`b, f ∈ C^α` on the closed half ball, and let `w ∈ C²(halfBall ν x r)` solve
`tr (a D²w) + ⟪b, ∇w⟫ = f` with `⟪a ν, ∇w⟫ = γ` on the flat part, where `a ν` (through a
`C^{1,α}` field `β`) and `γ` are `C^{1,α}`. Then `w ∈ C^{2,α}(halfBall ν x (r/2))`. Proved by
`Nondiv.schauder_halfBall_conormal` (`Nondiv/Boundary/Main.lean`). -/
def SchauderHalfBallConormalStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ (ν x : E) (r lam Λ : ℝ) (Ka Kb Kf : ℝ≥0) (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ)
    (β : E → E) (γ : E → ℝ) (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r → ⟪x, ν⟫ = 0 → 0 < lam →
    IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
    HolderOnWith Ka α a (halfBall ν x r) → HolderOnWith Kb α b (halfBall ν x r) →
    HolderOnWith Kf α f (halfBall ν x r) →
    ContDiffHolderOn 1 α β (halfBall ν x r) → (∀ y ∈ halfBall ν x r ∩ flatPart ν, β y = a y ν) →
    ContDiffHolderOn 1 α γ (halfBall ν x r) →
    IsSolOn a b f (halfBall ν x r) w → HasConormalBC ν a γ (halfBall ν x r) w →
    ContDiffHolderOn 2 α w (halfBall ν x (r / 2))

/-- **Tier-1 boundary Schauder regularity, Dirichlet condition** (GT, in the
flat case). Let the centre lie on the flat part, `a` be uniformly elliptic and `C^α`,
`b, f ∈ C^α` on the closed half ball, `g ∈ C^{2,α}(halfBall ν x r)`, and let
`w ∈ C²(halfBall ν x r)` solve `tr (a D²w) + ⟪b, ∇w⟫ = f` with `w = g` on the flat part. Then
`w ∈ C^{2,α}(halfBall ν x (r/2))`. Proved by `Nondiv.schauder_halfBall_dirichlet`
(`Nondiv/Boundary/Main.lean`). -/
def SchauderHalfBallDirichletStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ (ν x : E) (r lam Λ : ℝ) (Ka Kb Kf : ℝ≥0) (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ)
    (g : E → ℝ) (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r → ⟪x, ν⟫ = 0 → 0 < lam →
    IsUniformlyElliptic lam Λ a (halfBall ν x r) →
    HolderOnWith Ka α a (halfBall ν x r) → HolderOnWith Kb α b (halfBall ν x r) →
    HolderOnWith Kf α f (halfBall ν x r) →
    ContDiffHolderOn 2 α g (halfBall ν x r) →
    IsSolOn a b f (halfBall ν x r) w → HasDirichletBC ν g (halfBall ν x r) w →
    ContDiffHolderOn 2 α w (halfBall ν x (r / 2))

end Nondiv

end BasicElliptic
