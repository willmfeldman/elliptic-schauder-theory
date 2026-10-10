/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

import BasicElliptic

/-!
# Axiom check for the 16 headline theorems (release gate)

Checked with `lake env lean scripts/check_axioms.lean` (CI). Each `#guard_msgs` fails the
elaboration unless `#print axioms` reports exactly `propext`, `Classical.choice` and
`Quot.sound` (in particular no `sorryAx` and no extra axiom); whitespace is compared laxly
because the message is line-wrapped by the pretty printer. The list is the README headline
table; `formalization.yaml` lists the same names and `scripts/check-formalization-manifest.rb`
checks them independently.
-/

/--
info: 'BasicElliptic.Div.contDiffHolderOn_one_of_isWeakSolution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.contDiffHolderOn_one_of_isWeakSolution

/--
info: 'BasicElliptic.Div.c1Holder_ball_estimate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.c1Holder_ball_estimate

/--
info: 'BasicElliptic.Div.contDiffHolderOn_one_halfBall_of_isConormalSolution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.contDiffHolderOn_one_halfBall_of_isConormalSolution

/--
info: 'BasicElliptic.Div.c1Holder_halfBall_estimate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.c1Holder_halfBall_estimate

/--
info: 'BasicElliptic.Div.isConormalSolOn_of_strong'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.isConormalSolOn_of_strong

/--
info: 'BasicElliptic.Div.isQuasilinearConormalSolOn_of_strong'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.isQuasilinearConormalSolOn_of_strong

/--
info: 'BasicElliptic.Div.IsConormalSolOn.evenReflect'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.IsConormalSolOn.evenReflect

/--
info: 'BasicElliptic.Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff

/--
info: 'BasicElliptic.Div.contDiffOn_halfBall_of_quasilinear_conormal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.contDiffOn_halfBall_of_quasilinear_conormal

/--
info: 'BasicElliptic.Div.quasilinear_conormal_estimate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Div.quasilinear_conormal_estimate

/--
info: 'BasicElliptic.Nondiv.contDiffHolderOn_two_of_isSolution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Nondiv.contDiffHolderOn_two_of_isSolution

/--
info: 'BasicElliptic.Nondiv.schauder_ball_estimate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Nondiv.schauder_ball_estimate

/--
info: 'BasicElliptic.Nondiv.schauder_halfBall_conormal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Nondiv.schauder_halfBall_conormal

/--
info: 'BasicElliptic.Nondiv.schauder_halfBall_dirichlet'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.Nondiv.schauder_halfBall_dirichlet

/--
info: 'BasicElliptic.holderOnWith_of_campanato'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.holderOnWith_of_campanato

/--
info: 'BasicElliptic.contDiffHolderOn_two_of_polyApprox'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BasicElliptic.contDiffHolderOn_two_of_polyApprox
