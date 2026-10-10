module

public import BasicElliptic.Nondiv.Interior.Main
public import BasicElliptic.Nondiv.Boundary.Main
public import BasicElliptic.Poly.Bridge

/-!
# Solution: headline theorems in nondivergence form, and the polynomial-approximation bridge

Discharges the challenge statements by the library theorems `Nondiv.contDiffHolderOn_two_of_isSolution E`, `Nondiv.schauder_ball_estimate E`, `Nondiv.schauder_halfBall_conormal E`, `Nondiv.schauder_halfBall_dirichlet E`, `contDiffHolderOn_two_of_polyApprox E`, whose types are the
library's `…Statement` definitions; the statements below are their unfolded forms.

## References

* L. A. Caffarelli, *Interior a priori estimates for solutions of fully non-linear equations*,
  Ann. of Math. (2) 130 (1989), no. 1, 189–213.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set RealInnerProductSpace
open scoped NNReal Gradient

namespace BasicElliptic

/-- Challenge: **interior Schauder regularity, nondivergence form** (Gilbarg–Trudinger; Caffarelli
1989). A `C²` solution of `tr (a D²w) + ⟪b, ∇w⟫ = f` on an open
`U`, with `a` uniformly elliptic and `a, b, f ∈ C^α`, is `C^{2,α}` on every closed ball in `U`. -/
theorem challenge_contDiffHolderOn_two_of_isSolution
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (U : Set E) (lam Λ : ℝ) (Ka Kb Kf : ℝ≥0) (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ)
      (w : E → ℝ),
      IsOpen U → 0 < lam → IsUniformlyElliptic lam Λ a U →
      HolderOnWith Ka α a U → HolderOnWith Kb α b U → HolderOnWith Kf α f U →
      Nondiv.IsSolOn a b f U w →
      ∀ (z : E) (ρ : ℝ), closedBall z ρ ⊆ U → ContDiffHolderOn 2 α w (closedBall z ρ) :=
  Nondiv.contDiffHolderOn_two_of_isSolution E

/-- Challenge: **scaled interior Schauder estimate, nondivergence form** (Gilbarg–Trudinger, in
scaled form):
`r² |D²w(x)| + r^{2+α} [D²w]_{α, B_{r/2}} ≤ C (osc_{B_r} w + r² ‖f‖_∞ + r^{2+α} [f]_α)`, with
`C = C(E, α, lam, Λ, K)` whenever `[a]_α r^α ≤ K` and `r ‖b‖_∞ + r^{1+α} [b]_α ≤ K`. -/
theorem challenge_schauder_ball_estimate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 → ∀ (lam Λ K : ℝ), 0 < lam →
    ∃ C : ℝ, ∀ (x : E) (r : ℝ) (Ka Kb Kf : ℝ≥0) (Mb Mf : ℝ) (a : E → E →L[ℝ] E) (b : E → E)
      (f : E → ℝ) (w : E → ℝ),
      0 < r → IsUniformlyElliptic lam Λ a (ball x r) →
      HolderOnWith Ka α a (ball x r) → (Ka : ℝ) * r ^ (α : ℝ) ≤ K →
      HolderOnWith Kb α b (ball x r) → (∀ y ∈ ball x r, ‖b y‖ ≤ Mb) →
      r * Mb + r ^ (1 + (α : ℝ)) * Kb ≤ K →
      HolderOnWith Kf α f (ball x r) → (∀ y ∈ ball x r, |f y| ≤ Mf) →
      ContinuousOn w (closedBall x r) → Nondiv.IsSolOn a b f (ball x r) w →
      r ^ 2 * ‖iteratedFDeriv ℝ 2 w x‖ +
          r ^ (2 + (α : ℝ)) * holderSeminormOn α (iteratedFDeriv ℝ 2 w) (closedBall x (r / 2)) ≤
        C * (regionOsc w (closedBall x r) + r ^ 2 * Mf + r ^ (2 + (α : ℝ)) * Kf) :=
  Nondiv.schauder_ball_estimate E

/-- Challenge: **flat-boundary Schauder regularity, conormal-compatible condition**
(Gilbarg–Trudinger, flat case). Let the centre lie on the flat part, `a` be
symmetric, uniformly elliptic and `C^α`, `b, f ∈ C^α` on the closed half ball, and let
`w ∈ C²(halfBall ν x r)` solve `tr (a D²w) + ⟪b, ∇w⟫ = f` with `⟪a ν, ∇w⟫ = γ` on the flat part,
where `a ν` (through a `C^{1,α}` field `β` agreeing with it on the flat part) and `γ` are
`C^{1,α}`. Then `w ∈ C^{2,α}(halfBall ν x (r/2))`. -/
theorem challenge_schauder_halfBall_conormal
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (ν x : E) (r lam Λ : ℝ) (Ka Kb Kf : ℝ≥0) (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ)
      (β : E → E) (γ : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r → ⟪x, ν⟫ = 0 → 0 < lam →
      IsUniformlyElliptic lam Λ a (halfBall ν x r) → IsSymmetricOn a (halfBall ν x r) →
      HolderOnWith Ka α a (halfBall ν x r) → HolderOnWith Kb α b (halfBall ν x r) →
      HolderOnWith Kf α f (halfBall ν x r) →
      ContDiffHolderOn 1 α β (halfBall ν x r) →
      (∀ y ∈ halfBall ν x r ∩ flatPart ν, β y = a y ν) →
      ContDiffHolderOn 1 α γ (halfBall ν x r) →
      Nondiv.IsSolOn a b f (halfBall ν x r) w → Nondiv.HasConormalBC ν a γ (halfBall ν x r) w →
      ContDiffHolderOn 2 α w (halfBall ν x (r / 2)) :=
  Nondiv.schauder_halfBall_conormal E

/-- Challenge: **flat-boundary Schauder regularity, Dirichlet condition** (Gilbarg–Trudinger, flat
case). Let the centre lie on the flat part, `a` be uniformly
elliptic and `C^α`, `b, f ∈ C^α` on the closed half ball, `g ∈ C^{2,α}(halfBall ν x r)`, and let
`w ∈ C²(halfBall ν x r)` solve `tr (a D²w) + ⟪b, ∇w⟫ = f` with `w = g` on the flat part. Then
`w ∈ C^{2,α}(halfBall ν x (r/2))`. -/
theorem challenge_schauder_halfBall_dirichlet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (ν x : E) (r lam Λ : ℝ) (Ka Kb Kf : ℝ≥0) (a : E → E →L[ℝ] E) (b : E → E) (f : E → ℝ)
      (g : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < r → ⟪x, ν⟫ = 0 → 0 < lam →
      IsUniformlyElliptic lam Λ a (halfBall ν x r) →
      HolderOnWith Ka α a (halfBall ν x r) → HolderOnWith Kb α b (halfBall ν x r) →
      HolderOnWith Kf α f (halfBall ν x r) →
      ContDiffHolderOn 2 α g (halfBall ν x r) →
      Nondiv.IsSolOn a b f (halfBall ν x r) w → Nondiv.HasDirichletBC ν g (halfBall ν x r) w →
      ContDiffHolderOn 2 α w (halfBall ν x (r / 2)) :=
  Nondiv.schauder_halfBall_dirichlet E

/-- Challenge: **polynomial approximation implies `C^{2,α}` on a convex body** (Caffarelli 1989;
Gilbarg–Trudinger, in pointwise form). Let `S` be convex and bounded with nonempty interior.
If at every `p ∈ S` there is a quadratic polynomial `P0 p + P1 p (q - p) + ½ P2 p (q - p) (q - p)`
with `|u q - (…)| ≤ A |q - p|^{2+α}` for `q ∈ S`, `|q - p| < ρ₀`, then `u ∈ C^{2,α}(S)`
(derivatives within `S`) and `Du = P1` on `S`. -/
theorem challenge_contDiffHolderOn_two_of_polyApprox
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (S : Set E) (u : E → ℝ) (P0 : E → ℝ) (P1 : E → E →L[ℝ] ℝ) (P2 : E → E →L[ℝ] E →L[ℝ] ℝ)
      (A ρ₀ : ℝ),
      Convex ℝ S → Bornology.IsBounded S → (interior S).Nonempty → 0 < ρ₀ →
      (∀ p ∈ S, ∀ q ∈ S, dist q p < ρ₀ →
        |u q - (P0 p + P1 p (q - p) + (1 / 2 : ℝ) * P2 p (q - p) (q - p))| ≤
          A * dist q p ^ (2 + (α : ℝ))) →
      ContDiffHolderOn 2 α u S ∧ ∀ p ∈ S, fderivWithin ℝ u S p = P1 p :=
  contDiffHolderOn_two_of_polyApprox E

end BasicElliptic
