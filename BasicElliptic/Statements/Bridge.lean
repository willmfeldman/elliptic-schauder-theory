/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Basic.HalfSpace
public import BasicElliptic.Defs.Holder
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Headline statements: bridges (D)

* `BasicElliptic.CampanatoHolderStatement`: Campanato's characterization of Hölder continuity on
  closed half balls (`Campanato/`).
* `BasicElliptic.PolyApproxBridgeStatement`: uniform pointwise second-order polynomial expansions
  on a convex body give `C^{2,α}` with derivatives within the set (`Poly/`).

Conventions as in `BasicElliptic/Statements/Div.lean`.

## References

* [GM] M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
* [GT] D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  reprint of the 1998 edition, Classics in Mathematics, Springer, 2001.
* L. A. Caffarelli, *Interior a priori estimates for solutions of fully non-linear equations*,
  Ann. of Math. (2) 130 (1989), no. 1, 189–213.
* S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup.
  Pisa (3) 17 (1963), 175–188.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set RealInnerProductSpace
open scoped NNReal

namespace BasicElliptic

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Campanato's characterization** (GM; Campanato 1963), on closed half balls
`S = halfBall ν x R` with `⟪x, ν⟫ ≥ 0` (this includes closed balls: take `⟪x, ν⟫ ≥ R`). If `F` is
continuous on `S` and its mean square oscillation over `ball p ρ ∩ S` is at most `M² ρ^{2α}` for
all `p ∈ S` and `ρ ∈ (0, R]`, then `F` is `α`-Hölder on `S` with constant `C M`, `C = C(E, α)`.
Proved by `holderOnWith_of_campanato` (`Campanato/Holder.lean`). -/
def CampanatoHolderStatement [MeasurableSpace E] [BorelSpace E] (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] : Prop :=
  ∀ α : ℝ, 0 < α → α ≤ 1 → ∃ C : ℝ, ∀ (ν x : E) (R M : ℝ) (F : E → V),
    ‖ν‖ = 1 → 0 < R → 0 ≤ ⟪x, ν⟫ → 0 ≤ M → ContinuousOn F (halfBall ν x R) →
    (∀ p ∈ halfBall ν x R, ∀ ρ ∈ Ioc 0 R,
      ⨍ y in ball p ρ ∩ halfBall ν x R, ‖F y - ⨍ z in ball p ρ ∩ halfBall ν x R, F z‖ ^ 2 ≤
        M ^ 2 * ρ ^ (2 * α)) →
    ∀ p ∈ halfBall ν x R, ∀ q ∈ halfBall ν x R, ‖F p - F q‖ ≤ C * M * dist p q ^ α

/-- **Polynomial approximation ⇒ `C^{2,α}` on a convex body** (Caffarelli; GT, in the
pointwise form). Let `S` be convex and bounded with nonempty interior. If at every
`p ∈ S` there is a quadratic polynomial `P0 p + P1 p (q - p) + ½ P2 p (q - p) (q - p)` with
`|u q - (…)| ≤ A |q - p|^{2+α}` for `q ∈ S`, `|q - p| < ρ₀`, then `u ∈ C^{2,α}(S)` (derivatives
within `S`) and `Du = P1` on `S`. Proved by `contDiffHolderOn_two_of_polyApprox`
(`Poly/Bridge.lean`). -/
def PolyApproxBridgeStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ (S : Set E) (u : E → ℝ) (P0 : E → ℝ) (P1 : E → E →L[ℝ] ℝ) (P2 : E → E →L[ℝ] E →L[ℝ] ℝ)
    (A ρ₀ : ℝ),
    Convex ℝ S → Bornology.IsBounded S → (interior S).Nonempty → 0 < ρ₀ →
    (∀ p ∈ S, ∀ q ∈ S, dist q p < ρ₀ →
      |u q - (P0 p + P1 p (q - p) + (1 / 2 : ℝ) * P2 p (q - p) (q - p))| ≤
        A * dist q p ^ (2 + (α : ℝ))) →
    ContDiffHolderOn 2 α u S ∧ ∀ p ∈ S, fderivWithin ℝ u S p = P1 p

end BasicElliptic
