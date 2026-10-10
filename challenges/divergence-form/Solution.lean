module

public import BasicElliptic.Div.Interior.Main
public import BasicElliptic.Div.Boundary.Main
public import BasicElliptic.Div.Boundary.StrongToWeak
public import BasicElliptic.Div.Reflection
public import BasicElliptic.Div.Higher.Main
public import BasicElliptic.Div.Quasilinear.Main
public import BasicElliptic.Campanato.Holder

/-!
# Solution: headline theorems in divergence form, and Campanato's characterization

Discharges the challenge statements by the library theorems `Div.contDiffHolderOn_one_of_isWeakSolution E`, `Div.c1Holder_ball_estimate E`, `Div.contDiffHolderOn_one_halfBall_of_isConormalSolution E`, `Div.c1Holder_halfBall_estimate E`, `Div.isConormalSolOn_of_strong E`, `Div.isQuasilinearConormalSolOn_of_strong E`, `Div.IsConormalSolOn.evenReflect E`, `Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff E`, `fun k ↦ Div.contDiffOn_halfBall_of_quasilinear_conormal E k`, `Div.quasilinear_conormal_estimate E`, `holderOnWith_of_campanato (E := E) V`, whose types are the
library's `…Statement` definitions; the statements below are their unfolded forms.

## References

* S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup.
  Pisa (3) 17 (1963), 175–188.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001.
* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Scuola Norm. Sup.
  Pisa Cl. Sci. (4) 4 (1977), no. 2, 373–391.
* G. M. Lieberman, *Oblique Derivative Problems for Elliptic Equations*, World Scientific, 2013.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set RealInnerProductSpace
open scoped NNReal Gradient

namespace BasicElliptic

/-- Challenge: **interior `C^{1,α}` regularity, divergence form** (Giaquinta–Martinazzi;
Gilbarg–Trudinger). A `C¹` weak solution of `-div (a ∇w - G) = f` on
an open `U`, with `a` uniformly elliptic (not necessarily symmetric) and `C^α`, `G ∈ C^α`, and `f`
bounded and measurable, is `C^{1,α}` on every closed ball in `U`. -/
theorem challenge_contDiffHolderOn_one_of_isWeakSolution
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (U : Set E) (lam Λ : ℝ) (Ka KG : ℝ≥0) (Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
      (f : E → ℝ) (w : E → ℝ),
      IsOpen U → 0 < lam → IsUniformlyElliptic lam Λ a U →
      HolderOnWith Ka α a U → HolderOnWith KG α G U →
      AEStronglyMeasurable f (volume.restrict U) → (∀ y ∈ U, |f y| ≤ Mf) →
      Div.IsWeakSolOn a G f U w →
      ∀ (z : E) (ρ : ℝ), closedBall z ρ ⊆ U → ContDiffHolderOn 1 α w (closedBall z ρ) :=
  Div.contDiffHolderOn_one_of_isWeakSolution E

/-- Challenge: **scaled interior `C^{1,α}` estimate, divergence form** (Giaquinta–Martinazzi, in
scaled form):
`r |∇w(x)| + r^{1+α} [∇w]_{α, B_{r/2}} ≤ C (osc_{B_r} w + r^{1+α} [G]_α + r² ‖f‖_∞)`, with
`C = C(E, α, lam, Λ, K)` whenever `[a]_{α, B_r} r^α ≤ K`. -/
theorem challenge_c1Holder_ball_estimate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 → ∀ (lam Λ K : ℝ), 0 < lam →
    ∃ C : ℝ, ∀ (x : E) (r : ℝ) (Ka KG : ℝ≥0) (Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
      (f : E → ℝ) (w : E → ℝ),
      0 < r → IsUniformlyElliptic lam Λ a (ball x r) →
      HolderOnWith Ka α a (ball x r) → (Ka : ℝ) * r ^ (α : ℝ) ≤ K →
      HolderOnWith KG α G (ball x r) →
      AEStronglyMeasurable f (volume.restrict (ball x r)) → (∀ y ∈ ball x r, |f y| ≤ Mf) →
      ContinuousOn w (closedBall x r) → Div.IsWeakSolOn a G f (ball x r) w →
      r * ‖fderiv ℝ w x‖ +
          r ^ (1 + (α : ℝ)) * holderSeminormOn α (fderiv ℝ w) (closedBall x (r / 2)) ≤
        C * (regionOsc w (closedBall x r) + r ^ (1 + (α : ℝ)) * KG + r ^ 2 * Mf) :=
  Div.c1Holder_ball_estimate E

/-- Challenge: **conormal flat-boundary `C^{1,α}` regularity** (Giaquinta–Martinazzi;
Gilbarg–Trudinger (Dirichlet analogue); Lieberman, Chapter 4). A conormal weak
solution `w ∈ C¹(B_r⁺)` of `-div (a ∇w - G) = f` on the closed half ball `B_r⁺ = halfBall ν x r`
(the tests need not vanish on the flat part), with `a` symmetric, uniformly elliptic and `C^α`,
`G ∈ C^α`, and `f` bounded and measurable, is `C^{1,α}` on `B_{r/2}⁺`. The centre is arbitrary
with `-r < ⟪x, ν⟫`. -/
theorem challenge_contDiffHolderOn_one_halfBall_of_isConormalSolution
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (ν x : E) (r lam Λ : ℝ) (Ka KG : ℝ≥0) (Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
      (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r → -r < ⟪x, ν⟫ → 0 < lam →
      IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
      HolderOnWith Ka α a (halfBall ν x r) → HolderOnWith KG α G (halfBall ν x r) →
      AEStronglyMeasurable f (volume.restrict (halfBall ν x r)) →
      (∀ y ∈ halfBall ν x r, |f y| ≤ Mf) →
      Div.IsConormalSolOn ν a G f x r w →
      ContDiffHolderOn 1 α w (halfBall ν x (r / 2)) :=
  Div.contDiffHolderOn_one_halfBall_of_isConormalSolution E

/-- Challenge: **scaled conormal flat-boundary `C^{1,α}` estimate** (Giaquinta–Martinazzi, in scaled
form):
`r |∇w(x)| + r^{1+α} [∇w]_{α, B_{r/2}⁺} ≤ C (osc_{B_r⁺} w + r^{1+α} [G]_α + r ‖G‖_∞ + r² ‖f‖_∞)`,
with `C = C(E, α, lam, Λ, K)` whenever `[a]_{α, B_r⁺} r^α ≤ K`. The term `r ‖G‖_∞` accounts for the
inhomogeneous conormal datum `⟪G, ν⟫`. -/
theorem challenge_c1Holder_halfBall_estimate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 → ∀ (lam Λ K : ℝ), 0 < lam →
    ∃ C : ℝ, ∀ (ν x : E) (r : ℝ) (Ka KG : ℝ≥0) (MG Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E)
      (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r → -r < ⟪x, ν⟫ →
      IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
      HolderOnWith Ka α a (halfBall ν x r) → (Ka : ℝ) * r ^ (α : ℝ) ≤ K →
      HolderOnWith KG α G (halfBall ν x r) → (∀ y ∈ halfBall ν x r, ‖G y‖ ≤ MG) →
      AEStronglyMeasurable f (volume.restrict (halfBall ν x r)) →
      (∀ y ∈ halfBall ν x r, |f y| ≤ Mf) →
      Div.IsConormalSolOn ν a G f x r w →
      r * ‖fderivWithin ℝ w (halfBall ν x r) x‖ +
          r ^ (1 + (α : ℝ)) *
            holderSeminormOn α (fderivWithin ℝ w (halfBall ν x r)) (halfBall ν x (r / 2)) ≤
        C * (regionOsc w (halfBall ν x r) + r ^ (1 + (α : ℝ)) * KG + r * MG + r ^ 2 * Mf) :=
  Div.c1Holder_halfBall_estimate E

/-- Challenge: **strong solutions are weak solutions, linear conormal problem**. Let
`B_r^+ = ball x r ∩ {⟪·, ν⟫ > 0}` (open). If `w ∈ C¹(halfBall ν x r) ∩ C²(B_r^+)`, `a, G` are
continuous on the closed half ball and `C¹` on `B_r^+`, `f` is integrable on the half ball,
`-div (a ∇w - G) = f` pointwise in `B_r^+`, and `⟪a ∇w - G, ν⟫ = 0` pointwise on
`ball x r ∩ flatPart ν`, then `w` is a conormal weak solution. -/
theorem challenge_isConormalSolOn_of_strong
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (ν x : E) (r : ℝ) (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r →
      ContDiffOn ℝ 1 w (halfBall ν x r) → ContDiffOn ℝ 2 w (ball x r ∩ openHalfSpace ν) →
      ContinuousOn a (halfBall ν x r) → ContDiffOn ℝ 1 a (ball x r ∩ openHalfSpace ν) →
      ContinuousOn G (halfBall ν x r) → ContDiffOn ℝ 1 G (ball x r ∩ openHalfSpace ν) →
      IntegrableOn f (halfBall ν x r) →
      (∀ y ∈ ball x r ∩ openHalfSpace ν, -divergence (fun z ↦ a z (∇ w z) - G z) y = f y) →
      (∀ y ∈ ball x r ∩ flatPart ν,
        ⟪a y (gradientWithin w (halfBall ν x r) y) - G y, ν⟫ = 0) →
      Div.IsConormalSolOn ν a G f x r w :=
  Div.isConormalSolOn_of_strong E

/-- Challenge: **strong solutions are weak solutions, quasilinear conormal problem**. If
`w ∈ C¹(halfBall ν x r) ∩ C²(B_r^+)`, `Φ` is `C¹` on an open `U` containing
`∇w(halfBall ν x r)`, `div Φ(∇w) = 0` pointwise in `B_r^+` and `⟪Φ(∇w), ν⟫ = 0` pointwise on
`ball x r ∩ flatPart ν`, then `w` is a quasilinear conormal weak solution. -/
theorem challenge_isQuasilinearConormalSolOn_of_strong
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (ν x : E) (r : ℝ) (Φ : E → E) (U : Set E) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r → IsOpen U →
      ContDiffOn ℝ 1 w (halfBall ν x r) → ContDiffOn ℝ 2 w (ball x r ∩ openHalfSpace ν) →
      ContDiffOn ℝ 1 Φ U → (∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U) →
      (∀ y ∈ ball x r ∩ openHalfSpace ν, divergence (fun z ↦ Φ (∇ w z)) y = 0) →
      (∀ y ∈ ball x r ∩ flatPart ν, ⟪Φ (gradientWithin w (halfBall ν x r) y), ν⟫ = 0) →
      Div.IsQuasilinearConormalSolOn ν Φ x r w :=
  Div.isQuasilinearConormalSolOn_of_strong E

/-- Challenge: **even reflection with measurable coefficients**. Let the centre `x` lie on the flat
part and let `w` be a conormal weak solution on `halfBall ν x r` with `a`, `G`, `f` bounded and
measurable (no continuity, no symmetry). Then the even reflection `w ∘ fold ν` is a weak solution
on the full ball `ball x r`, with gradient field the reflected gradient, for the reflected data
`reflectCoeff ν a` (`R a(R·) R` below the plane, `R = reflect ν`), `reflectField ν G` and
`f ∘ fold ν`. -/
theorem challenge_isConormalSolOn_evenReflect
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (ν x : E) (r Λ MG Mf : ℝ) (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r → ⟪x, ν⟫ = 0 →
      AEStronglyMeasurable a (volume.restrict (halfBall ν x r)) →
      (∀ y ∈ halfBall ν x r, ‖a y‖ ≤ Λ) →
      AEStronglyMeasurable G (volume.restrict (halfBall ν x r)) →
      (∀ y ∈ halfBall ν x r, ‖G y‖ ≤ MG) →
      AEStronglyMeasurable f (volume.restrict (halfBall ν x r)) →
      (∀ y ∈ halfBall ν x r, |f y| ≤ Mf) →
      Div.IsConormalSolOn ν a G f x r w →
      Div.IsWeakSolOnField (reflectCoeff ν a) (reflectField ν G) (evenExt ν f) (ball x r)
        (evenExt ν w) (reflectField ν (gradientWithin w (halfBall ν x r))) :=
  Div.IsConormalSolOn.evenReflect E

/-- Challenge: **linear conormal `C^{2,α}` regularity** (Giaquinta–Martinazzi;
Gilbarg–Trudinger, by analogy). With `a` symmetric, uniformly elliptic and
`C^{1,α}`, `G ∈ C^{1,α}` and `f ∈ C^α` on the closed half ball, a conormal weak solution
`w ∈ C¹(B_r⁺)` is `C^{2,α}` on `B_{r/2}⁺`. -/
theorem challenge_contDiffHolderOn_two_halfBall_of_c1Holder_coeff
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (ν x : E) (r lam Λ : ℝ) (Kf : ℝ≥0) (a : E → E →L[ℝ] E) (G : E → E) (f : E → ℝ)
      (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r → -r < ⟪x, ν⟫ → 0 < lam →
      IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
      ContDiffHolderOn 1 α a (halfBall ν x r) → ContDiffHolderOn 1 α G (halfBall ν x r) →
      HolderOnWith Kf α f (halfBall ν x r) →
      Div.IsConormalSolOn ν a G f x r w →
      ContDiffHolderOn 2 α w (halfBall ν x (r / 2)) :=
  Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff E

/-- Challenge: **quasilinear conormal regularity** (the type of conclusion of
Kinderlehrer–Nirenberg 1977; Giaquinta–Martinazzi). Let `Φ` be `C^{k+1}` on an open convex
`U`, with `DΦ` uniformly elliptic (lower bound `lam > 0`) and symmetric on `U`. If
`w ∈ C¹(halfBall ν x r)` is a quasilinear conormal weak solution of `div Φ(∇w) = 0` with
`∇w(halfBall ν x r) ⊆ U`, then `w` is `C^{k+1}` on `halfBall ν x (r/2)`. -/
theorem challenge_contDiffOn_halfBall_of_quasilinear_conormal
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (k : ℕ) (ν x : E) (r : ℝ) (Φ : E → E) (U : Set E) (lam : ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r → -r < ⟪x, ν⟫ → IsOpen U → Convex ℝ U → 0 < lam →
      ContDiffOn ℝ (k + 1 : ℕ) Φ U →
      (∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫) →
      (∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric) →
      (∀ y ∈ halfBall ν x r, gradientWithin w (halfBall ν x r) y ∈ U) →
      Div.IsQuasilinearConormalSolOn ν Φ x r w →
      ContDiffOn ℝ (k + 1 : ℕ) w (halfBall ν x (r / 2)) :=
  fun k ↦ Div.contDiffOn_halfBall_of_quasilinear_conormal E k

/-- Challenge: **scaled quasilinear conormal estimate** (Giaquinta–Martinazzi,
applied to the derivative equations). Fix a unit `ν` and `Φ ∈ C²(U)` with `U` open, `0 ∈ U`, and
`DΦ` uniformly elliptic and symmetric on `U`. There are `η > 0` and `C` such that every
quasilinear conormal weak solution `w ∈ C¹(halfBall ν x r)` with `|∇w| ≤ η` on the half ball
satisfies, at the centre, `r |∇w(x)| ≤ C osc w` and `r² |D²w(x)| ≤ C osc w` (derivatives within
the closed half ball). -/
theorem challenge_quasilinear_conormal_estimate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ (ν : E) (Φ : E → E) (U : Set E) (lam : ℝ),
      ‖ν‖ = 1 → IsOpen U → (0 : E) ∈ U → 0 < lam →
      ContDiffOn ℝ 2 Φ U →
      (∀ p ∈ U, ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ Φ p ξ, ξ⟫) →
      (∀ p ∈ U, (fderiv ℝ Φ p : E →ₗ[ℝ] E).IsSymmetric) →
      ∃ η > 0, ∃ C : ℝ, ∀ (x : E) (r : ℝ) (w : E → ℝ),
        0 < r → -r < ⟪x, ν⟫ →
        Div.IsQuasilinearConormalSolOn ν Φ x r w →
        (∀ y ∈ halfBall ν x r, ‖gradientWithin w (halfBall ν x r) y‖ ≤ η) →
        r * ‖fderivWithin ℝ w (halfBall ν x r) x‖ ≤ C * regionOsc w (halfBall ν x r) ∧
          r ^ 2 * ‖fderivWithin ℝ (fderivWithin ℝ w (halfBall ν x r)) (halfBall ν x r) x‖ ≤
            C * regionOsc w (halfBall ν x r) :=
  Div.quasilinear_conormal_estimate E

/-- Challenge: **Campanato's characterization of Hölder continuity** (Campanato 1963;
Giaquinta–Martinazzi), on closed half balls `S = halfBall ν x R` with `⟪x, ν⟫ ≥ 0`
(this includes closed balls: take `⟪x, ν⟫ ≥ R`). If `F` is continuous on `S` and its mean square
oscillation over `ball p ρ ∩ S` is at most `M² ρ^{2α}` for all `p ∈ S` and `ρ ∈ (0, R]`, then `F`
is `α`-Hölder on `S` with constant `C M`, `C = C(E, α)`. -/
theorem challenge_holderOnWith_of_campanato
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] :
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∃ C : ℝ, ∀ (ν x : E) (R M : ℝ) (F : E → V),
      ‖ν‖ = 1 → 0 < R → 0 ≤ ⟪x, ν⟫ → 0 ≤ M → ContinuousOn F (halfBall ν x R) →
      (∀ p ∈ halfBall ν x R, ∀ ρ ∈ Ioc 0 R,
        ⨍ y in ball p ρ ∩ halfBall ν x R, ‖F y - ⨍ z in ball p ρ ∩ halfBall ν x R, F z‖ ^ 2 ≤
          M ^ 2 * ρ ^ (2 * α)) →
      ∀ p ∈ halfBall ν x R, ∀ q ∈ halfBall ν x R, ‖F p - F q‖ ≤ C * M * dist p q ^ α :=
  holderOnWith_of_campanato (E := E) V

end BasicElliptic
