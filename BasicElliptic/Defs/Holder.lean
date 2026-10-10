/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder seminorms on sets and `C^{k,α}` on sets

Mathlib's `HolderOnWith C α f s` is the predicate; here we add:

* `BasicElliptic.eHolderSeminormOn α f s : ℝ≥0∞`: the best constant `C` with
  `HolderOnWith C α f s` (`⊤` if there is none). This mirrors Mathlib's `eHolderNorm` (which is the
  global version, on the whole space).
* `BasicElliptic.holderSeminormOn α f s : ℝ`: its real part, the form used in estimates. It is only
  meaningful when `f` is Hölder on `s` (it is `0` when the seminorm is infinite); every headline
  estimate states or implies the finiteness separately.
* `BasicElliptic.ContDiffHolderOn k α f s`: `f` is `C^k` on `s` (derivatives within `s`) and its
  `k`-th within-derivative `iteratedFDerivWithin ℝ k f s` is `α`-Hölder on `s`. Typically `s` is a
  closed ball or a closed half ball.
* `BasicElliptic.regionOsc f s = sSup (f '' s) - sInf (f '' s)`: the oscillation of a real
  function on a set, stated literally (`regionOsc_def`). It is only meaningful for `f`
  bounded on `s`; the headline statements apply it to functions continuous on compact sets.
-/

@[expose] public noncomputable section

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

theorem eHolderSeminormOn_le_of_holderOnWith {C α : ℝ≥0} {f : X → Y} {s : Set X}
    (h : HolderOnWith C α f s) : eHolderSeminormOn α f s ≤ C :=
  iInf₂_le C h

theorem eHolderSeminormOn_lt_top_of_holderOnWith {C α : ℝ≥0} {f : X → Y} {s : Set X}
    (h : HolderOnWith C α f s) : eHolderSeminormOn α f s < ⊤ :=
  (eHolderSeminormOn_le_of_holderOnWith h).trans_lt ENNReal.coe_lt_top

theorem holderSeminormOn_le_of_holderOnWith {C α : ℝ≥0} {f : X → Y} {s : Set X}
    (h : HolderOnWith C α f s) : holderSeminormOn α f s ≤ C :=
  ENNReal.toReal_le_of_le_ofReal C.2 (by simpa using eHolderSeminormOn_le_of_holderOnWith h)

theorem holderSeminormOn_nonneg (α : ℝ≥0) (f : X → Y) (s : Set X) :
    0 ≤ holderSeminormOn α f s :=
  ENNReal.toReal_nonneg

end Holder

section ContDiffHolder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `f` is `C^{k,α}` on `s`: `C^k` on `s` with derivatives taken within `s`, and the `k`-th
within-derivative is `α`-Hölder on `s` with some constant. -/
def ContDiffHolderOn (k : ℕ) (α : ℝ≥0) (f : E → F) (s : Set E) : Prop :=
  ContDiffOn ℝ k f s ∧ ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ k f s) s

theorem ContDiffHolderOn.contDiffOn {k : ℕ} {α : ℝ≥0} {f : E → F} {s : Set E}
    (h : ContDiffHolderOn k α f s) : ContDiffOn ℝ k f s :=
  h.1

end ContDiffHolder

/-- The oscillation `sup_s f - inf_s f` of a real function on a set, stated literally as
`sSup (f '' s) - sInf (f '' s)`. -/
def regionOsc {X : Type*} (f : X → ℝ) (s : Set X) : ℝ :=
  sSup (f '' s) - sInf (f '' s)

@[simp] theorem regionOsc_def {X : Type*} (f : X → ℝ) (s : Set X) :
    regionOsc f s = sSup (f '' s) - sInf (f '' s) :=
  rfl

end BasicElliptic
