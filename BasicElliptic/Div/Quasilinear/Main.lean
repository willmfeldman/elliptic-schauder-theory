/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Div
import BasicElliptic.Div.Quasilinear.SecondOrder
import BasicElliptic.Div.Quasilinear.HigherOrder
import BasicElliptic.Div.Quasilinear.Induction
import BasicElliptic.Div.Quasilinear.Estimate

/-!
# The quasilinear conormal problem

`Div.contDiffOn_halfBall_of_quasilinear_conormal` and `Div.quasilinear_conormal_estimate` prove
`Div.QuasilinearConormalStatement` and `Div.QuasilinearConormalEstimateStatement`.

Status: sorry-free.
* `k = 0` is the hypothesis `w ∈ C¹`; `k = 1` (`C²` up to the flat part) is
  `Div.contDiffOn_two_halfBall_of_quasilinear_conormal` (`Div/Quasilinear/SecondOrder.lean`),
  using the local `C^{1,1/2}` lemma of `Div/Quasilinear/GradientHolder.lean`.
* `k = 2` (the `C³` case) is `Div.contDiffOn_three_halfBall_of_quasilinear_conormal`
  (`Div/Quasilinear/HigherOrder.lean`): differentiated weak identity for tangential derivatives,
  the linear `C^{2,α}` theorem (`Div/Higher/Main.lean`), and the normal–normal derivative from the
  equation.
* `k ≥ 3` is `Div.contDiffOn_halfBall_of_quasilinear_conormal_add_two`
  (`Div/Quasilinear/Induction.lean`): the same scheme as a `k`-induction, with Hölder regularity
  carried in the directional classes `Div.DirHolderOn` and a linear `C^{m+2,α}` induction.
* The scaled estimate is `Div.quasilinear_conormal_estimate_aux`
  (`Div/Quasilinear/Estimate.lean`).
-/

public section

namespace BasicElliptic

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Quasilinear conormal regularity** : a `C¹` quasilinear conormal weak
solution with `Φ ∈ C^{k+1}` is `C^{k+1}` on the half ball of half the radius
(`Div.QuasilinearConormalStatement`). -/
theorem Div.contDiffOn_halfBall_of_quasilinear_conormal (k : ℕ) :
    Div.QuasilinearConormalStatement E k := by
  intro ν x r Φ U lam w hν hr hx hU hUc hlam hΦ hell hsym hrange hsol
  match k with
  | 0 =>
    have := hsol.1.mono (halfBall_mono ν x (by linarith : r / 2 ≤ r))
    simpa using this
  | 1 =>
    have hΦ2 : ContDiffOn ℝ 2 Φ U := by simpa using hΦ
    simpa using Div.contDiffOn_two_halfBall_of_quasilinear_conormal hν hr hx hU hUc hlam hΦ2
      hell hsym hrange hsol
  | 2 =>
    have hΦ3 : ContDiffOn ℝ 3 Φ U := by simpa using hΦ
    simpa using Div.contDiffOn_three_halfBall_of_quasilinear_conormal hν hr hx hU hUc hlam hΦ3
      hell hsym hrange hsol
  | k + 3 =>
    have e : k + 3 + 1 = k + 2 + 2 := by omega
    rw [e] at hΦ ⊢
    exact Div.contDiffOn_halfBall_of_quasilinear_conormal_add_two (k + 2) hν hr hx hU hUc hlam
      hΦ hell hsym hrange hsol

/-- **Scaled quasilinear conormal estimate** :
`r |∇w(x)| + r² |D²w(x)| ≲ osc w` for solutions with small gradient
(`Div.QuasilinearConormalEstimateStatement`). -/
theorem Div.quasilinear_conormal_estimate : Div.QuasilinearConormalEstimateStatement E :=
  Div.quasilinear_conormal_estimate_aux E

end BasicElliptic
