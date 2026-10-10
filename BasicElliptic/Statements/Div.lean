/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Defs.Div
public import BasicElliptic.Defs.Elliptic
public import BasicElliptic.Defs.Holder
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Headline statements: divergence form

One `def …Statement : Prop` per headline result. Each is proved by the theorem
named in its docstring.

Conventions:
* `E` is a finite-dimensional real inner product space with its Haar `volume`
  (`measureSpaceOfInnerProductSpace`); it is an explicit argument of every statement.
* Hölder exponents are `α : ℝ≥0` with `0 < α < 1`. Hölder hypotheses are `HolderOnWith K α _ s`
  with the constant named; estimates are scale invariant, with `C` depending only on the data
  listed before `∃ C` (dimension through `E`, `α`, `lam`, `Λ` and the bound `K` on the
  scale-invariant coefficient seminorm `[a]_α r^α`). `∃ C` comes before `∀ w`.
* Regularity hypotheses on solutions are qualitative only: `C¹` on the region (closed half ball;
  `C¹` on the open ball for interior results).
* Interior results allow nonsymmetric `a`; conormal results assume `a` (resp. `DΦ`) symmetric.
* Half balls `halfBall ν x r` have an arbitrary centre with `-r < ⟪x, ν⟫`;
  derivatives at the centre are `fderivWithin` on the closed half ball.
* Sign convention: the weak identity `∫ ⟪a ∇w, ∇φ⟫ = ∫ ⟪G, ∇φ⟫ + ∫ f φ` is the weak form of
  `-div (a ∇w - G) = f`.

## References

* [GM] M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
* [GT] D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  reprint of the 1998 edition, Classics in Mathematics, Springer, 2001.
* G. M. Lieberman, *Oblique Derivative Problems for Elliptic Equations*, World Scientific, 2013.
* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Scuola Norm. Sup.
  Pisa Cl. Sci. (4) 4 (1977), no. 2, 373–391.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set RealInnerProductSpace
open scoped NNReal Gradient

namespace BasicElliptic

namespace Div

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Interior `C^{1,α}` -/

/-- **Interior `C^{1,α}` regularity, divergence form** (GM; GT). A `C¹` weak
solution of `-div (a ∇w - G) = f` on an open `U`, with `a` uniformly elliptic (not necessarily
symmetric) and `C^α`, `G ∈ C^α`, `f` bounded and measurable, is `C^{1,α}` on every closed ball in
`U`. Proved by `Div.contDiffHolderOn_one_of_isWeakSolution` (`Div/Interior/Main.lean`). -/
def C1HolderBallStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ (U : Set E) (lam Λ : ℝ) (Ka KG : ℝ≥0) (Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
    (f : E → ℝ) (w : E → ℝ),
    IsOpen U → 0 < lam → IsUniformlyElliptic lam Λ a U →
    HolderOnWith Ka α a U → HolderOnWith KG α G U →
    AEStronglyMeasurable f (volume.restrict U) → (∀ y ∈ U, |f y| ≤ Mf) →
    IsWeakSolOn a G f U w →
    ∀ (z : E) (ρ : ℝ), closedBall z ρ ⊆ U → ContDiffHolderOn 1 α w (closedBall z ρ)

/-- **Scaled interior `C^{1,α}` estimate, divergence form** (GM, scaled):
`r |∇w(x)| + r^{1+α} [∇w]_{α, B_{r/2}} ≤ C (osc_{B_r} w + r^{1+α} [G]_α + r² ‖f‖_∞)`, with
`C = C(E, α, lam, Λ, K)` whenever `[a]_{α, B_r} r^α ≤ K`. Proved by `Div.c1Holder_ball_estimate`
(`Div/Interior/Main.lean`). -/
def C1HolderBallEstimateStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 → ∀ (lam Λ K : ℝ), 0 < lam →
  ∃ C : ℝ, ∀ (x : E) (r : ℝ) (Ka KG : ℝ≥0) (Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
    (f : E → ℝ) (w : E → ℝ),
    0 < r → IsUniformlyElliptic lam Λ a (ball x r) →
    HolderOnWith Ka α a (ball x r) → (Ka : ℝ) * r ^ (α : ℝ) ≤ K →
    HolderOnWith KG α G (ball x r) →
    AEStronglyMeasurable f (volume.restrict (ball x r)) → (∀ y ∈ ball x r, |f y| ≤ Mf) →
    ContinuousOn w (closedBall x r) → IsWeakSolOn a G f (ball x r) w →
    r * ‖fderiv ℝ w x‖ +
        r ^ (1 + (α : ℝ)) * holderSeminormOn α (fderiv ℝ w) (closedBall x (r / 2)) ≤
      C * (regionOsc w (closedBall x r) + r ^ (1 + (α : ℝ)) * KG + r ^ 2 * Mf)

/-! ### Conormal flat boundary `C^{1,α}` -/

/-- **Conormal flat-boundary `C^{1,α}` regularity** (GM; GT (Dirichlet analogue);
Lieberman, *Oblique derivative problems*, Ch. 4). A conormal weak solution `w ∈ C¹(B_r⁺)` with `a`
symmetric, uniformly elliptic and `C^α`, `G ∈ C^α`, `f` bounded and measurable, is `C^{1,α}` on
`B_{r/2}⁺`. Proved by `Div.contDiffHolderOn_one_halfBall_of_isConormalSolution`
(`Div/Boundary/Main.lean`). -/
def C1HolderHalfBallStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ (ν x : E) (r lam Λ : ℝ) (Ka KG : ℝ≥0) (Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
    (f : E → ℝ) (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r → -r < ⟪x, ν⟫ → 0 < lam →
    IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
    HolderOnWith Ka α a (halfBall ν x r) → HolderOnWith KG α G (halfBall ν x r) →
    AEStronglyMeasurable f (volume.restrict (halfBall ν x r)) →
    (∀ y ∈ halfBall ν x r, |f y| ≤ Mf) →
    IsConormalSolOn ν a G f x r w →
    ContDiffHolderOn 1 α w (halfBall ν x (r / 2))

/-- **Scaled conormal flat-boundary `C^{1,α}` estimate** (GM, scaled):
`r |∇w(x)| + r^{1+α} [∇w]_{α, B_{r/2}⁺} ≤ C (osc_{B_r⁺} w + r^{1+α} [G]_α + r ‖G‖_∞ + r² ‖f‖_∞)`,
with `C = C(E, α, lam, Λ, K)` whenever `[a]_{α, B_r⁺} r^α ≤ K`. The term `r ‖G‖_∞` accounts for the
inhomogeneous conormal datum `⟪G, ν⟫` (it is the scaled form of the full `C^α` norm of `G` in GM).
Proved by `Div.c1Holder_halfBall_estimate` (`Div/Boundary/Main.lean`). -/
def C1HolderHalfBallEstimateStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 → ∀ (lam Λ K : ℝ), 0 < lam →
  ∃ C : ℝ, ∀ (ν x : E) (r : ℝ) (Ka KG : ℝ≥0) (MG Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
    (f : E → ℝ) (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r → -r < ⟪x, ν⟫ →
    IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
    HolderOnWith Ka α a (halfBall ν x r) → (Ka : ℝ) * r ^ (α : ℝ) ≤ K →
    HolderOnWith KG α G (halfBall ν x r) → (∀ y ∈ halfBall ν x r, ‖G y‖ ≤ MG) →
    AEStronglyMeasurable f (volume.restrict (halfBall ν x r)) →
    (∀ y ∈ halfBall ν x r, |f y| ≤ Mf) →
    IsConormalSolOn ν a G f x r w →
    r * ‖fderivWithin ℝ w (halfBall ν x r) x‖ +
        r ^ (1 + (α : ℝ)) *
          holderSeminormOn α (fderivWithin ℝ w (halfBall ν x r)) (halfBall ν x (r / 2)) ≤
      C * (regionOsc w (halfBall ν x r) + r ^ (1 + (α : ℝ)) * KG + r * MG + r ^ 2 * Mf)

/-! ### Strong ⇒ weak bridges and measurable even reflection -/

/-- **Strong ⇒ weak, linear conormal problem**. Let `B_r^+ = ball x r ∩ {⟪·, ν⟫ > 0}`
(open). If `w ∈ C¹(halfBall ν x r) ∩ C²(B_r^+)`, `a, G` are continuous on the closed half ball and
`C¹` on `B_r^+`, `f` is integrable on the half ball, `-div (a ∇w - G) = f` pointwise in `B_r^+`,
and `⟪a ∇w - G, ν⟫ = 0` pointwise on `ball x r ∩ flatPart ν`, then `w` is a conormal weak
solution. Proved by `Div.isConormalSolOn_of_strong` (`Div/Boundary/StrongToWeak.lean`). -/
def ConormalStrongToWeakStatement : Prop :=
  ∀ (ν x : E) (r : ℝ) (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r →
    ContDiffOn ℝ 1 w (halfBall ν x r) → ContDiffOn ℝ 2 w (ball x r ∩ openHalfSpace ν) →
    ContinuousOn a (halfBall ν x r) → ContDiffOn ℝ 1 a (ball x r ∩ openHalfSpace ν) →
    ContinuousOn G (halfBall ν x r) → ContDiffOn ℝ 1 G (ball x r ∩ openHalfSpace ν) →
    IntegrableOn f (halfBall ν x r) →
    (∀ y ∈ ball x r ∩ openHalfSpace ν, -divergence (fun z ↦ a z (∇ w z) - G z) y = f y) →
    (∀ y ∈ ball x r ∩ flatPart ν,
      ⟪a y (gradientWithin w (halfBall ν x r) y) - G y, ν⟫ = 0) →
    IsConormalSolOn ν a G f x r w

/-- **Strong ⇒ weak, quasilinear conormal problem**. If
`w ∈ C¹(halfBall ν x r) ∩ C²(B_r^+)` (`B_r^+ = ball x r ∩ {⟪·, ν⟫ > 0}`), `Φ` is `C¹` on an open
`U` containing `∇w(halfBall ν x r)`, `div Φ(∇w) = 0` pointwise in `B_r^+` and `⟪Φ(∇w), ν⟫ = 0`
pointwise on `ball x r ∩ flatPart ν`, then `w` is a quasilinear conormal weak solution. Proved by
`Div.isQuasilinearConormalSolOn_of_strong` (`Div/Boundary/StrongToWeak.lean`). -/
def QuasilinearStrongToWeakStatement : Prop :=
  ∀ (ν x : E) (r : ℝ) (Φ : E → E) (U : Set E) (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r → IsOpen U →
    ContDiffOn ℝ 1 w (halfBall ν x r) → ContDiffOn ℝ 2 w (ball x r ∩ openHalfSpace ν) →
    ContDiffOn ℝ 1 Φ U → (∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U) →
    (∀ y ∈ ball x r ∩ openHalfSpace ν, divergence (fun z ↦ Φ (∇ w z)) y = 0) →
    (∀ y ∈ ball x r ∩ flatPart ν, ⟪Φ (gradientWithin w (halfBall ν x r) y), ν⟫ = 0) →
    IsQuasilinearConormalSolOn ν Φ x r w

/-- **Even reflection with measurable coefficients**. Let the centre `x`
lie on the flat part and let `w` be a conormal weak solution on `halfBall ν x r` with `a`, `G`, `f`
bounded and measurable (no continuity, no symmetry). Then the even reflection `w ∘ fold ν` is a weak
solution on the full ball `ball x r`, with explicit gradient field the reflected gradient, for the
reflected data `ã = reflectCoeff ν a` (`R a(R·) R` below the plane), `G̃ = reflectField ν G`,
`f̃ = f ∘ fold ν`. Proved by `Div.IsConormalSolOn.evenReflect` (`Div/Reflection.lean`). -/
def EvenReflectStatement : Prop :=
  ∀ (ν x : E) (r Λ MG Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r → ⟪x, ν⟫ = 0 →
    AEStronglyMeasurable a (volume.restrict (halfBall ν x r)) →
    (∀ y ∈ halfBall ν x r, ‖a y‖ ≤ Λ) →
    AEStronglyMeasurable G (volume.restrict (halfBall ν x r)) →
    (∀ y ∈ halfBall ν x r, ‖G y‖ ≤ MG) →
    AEStronglyMeasurable f (volume.restrict (halfBall ν x r)) →
    (∀ y ∈ halfBall ν x r, |f y| ≤ Mf) →
    IsConormalSolOn ν a G f x r w →
    IsWeakSolOnField (reflectCoeff ν a) (reflectField ν G) (evenExt ν f) (ball x r)
      (evenExt ν w) (reflectField ν (gradientWithin w (halfBall ν x r)))

/-! ### Higher order and the quasilinear conormal problem -/

/-- **Linear conormal `C^{2,α}`** from `C^{1,α}` coefficients (difference quotients; GM;
GT, by analogy). With `a` symmetric, uniformly elliptic and `C^{1,α}`, `G ∈ C^{1,α}`,
`f ∈ C^α` on the closed half ball, a conormal weak solution `w ∈ C¹(B_r⁺)` is `C^{2,α}` on
`B_{r/2}⁺`. Proved by `Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff`
(`Div/Higher/Main.lean`). -/
def C2HolderHalfBallStatement : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ (ν x : E) (r lam Λ : ℝ) (Kf : ℝ≥0) (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ)
    (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r → -r < ⟪x, ν⟫ → 0 < lam →
    IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
    ContDiffHolderOn 1 α a (halfBall ν x r) → ContDiffHolderOn 1 α G (halfBall ν x r) →
    HolderOnWith Kf α f (halfBall ν x r) →
    IsConormalSolOn ν a G f x r w →
    ContDiffHolderOn 2 α w (halfBall ν x (r / 2))

/-- **Quasilinear conormal regularity** (Kinderlehrer–Nirenberg 1977-type conclusion; GM).
Let `Φ` be `C^{k+1}` on an open convex `U`, with `DΦ` uniformly elliptic
(lower bound `lam > 0`) and symmetric on `U` (`Φ` is locally a gradient). If
`w ∈ C¹(halfBall ν x r)` is a quasilinear conormal weak solution with `∇w(halfBall ν x r) ⊆ U`,
then `w` is `C^{k+1}` on `halfBall ν x (r/2)`. Only qualitative `C¹` regularity of `w` is assumed.
Proved by `Div.contDiffOn_halfBall_of_quasilinear_conormal` (`Div/Quasilinear/Main.lean`). -/
def QuasilinearConormalStatement (k : ℕ) : Prop :=
  ∀ (ν x : E) (r : ℝ) (Φ : E → E) (U : Set E) (lam : ℝ) (w : E → ℝ),
    ‖ν‖ = 1 → 0 < r → -r < ⟪x, ν⟫ → IsOpen U → Convex ℝ U → 0 < lam →
    ContDiffOn ℝ (k + 1 : ℕ) Φ U →
    (∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫) →
    (∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric) →
    (∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U) →
    IsQuasilinearConormalSolOn ν Φ x r w →
    ContDiffOn ℝ (k + 1 : ℕ) w (halfBall ν x (r / 2))

/-- **Scaled quasilinear conormal estimate** (GM, applied to the derivative
equations). Fix a unit `ν` and `Φ ∈ C²(U)` with `U` open, `0 ∈ U`, and `DΦ` uniformly
elliptic and symmetric on `U`. There are `η > 0` and `C` such that every quasilinear conormal weak
solution `w ∈ C¹(halfBall ν x r)` with `|∇w| ≤ η` on the half ball satisfies, at the centre,
`r |∇w(x)| ≤ C osc w` and `r² |D²w(x)| ≤ C osc w` (derivatives within the closed half ball).
Proved by `Div.quasilinear_conormal_estimate` (`Div/Quasilinear/Main.lean`). -/
def QuasilinearConormalEstimateStatement : Prop :=
  ∀ (ν : E) (Φ : E → E) (U : Set E) (lam : ℝ),
    ‖ν‖ = 1 → IsOpen U → (0 : E) ∈ U → 0 < lam →
    ContDiffOn ℝ 2 Φ U →
    (∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫) →
    (∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric) →
    ∃ η > 0, ∃ C : ℝ, ∀ (x : E) (r : ℝ) (w : E → ℝ),
      0 < r → -r < ⟪x, ν⟫ →
      IsQuasilinearConormalSolOn ν Φ x r w →
      (∀ y ∈ halfBall ν x r, ‖gradientWithin w (halfBall ν x r) y‖ ≤ η) →
      r * ‖fderivWithin ℝ w (halfBall ν x r) x‖ ≤ C * regionOsc w (halfBall ν x r) ∧
        r ^ 2 * ‖fderivWithin ℝ (fderivWithin ℝ w (halfBall ν x r)) (halfBall ν x r) x‖ ≤
          C * regionOsc w (halfBall ν x r)

end Div

end BasicElliptic
