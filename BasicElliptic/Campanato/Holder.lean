/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco, William M. Feldman
-/
module

public import BasicElliptic.Statements.Bridge
public import BasicElliptic.Campanato.Density
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Segment

/-!
# Campanato's characterization of Hölder continuity

`BasicElliptic.holderOnWith_of_campanato` proves the frozen `CampanatoHolderStatement`
(Giaquinta–Martinazzi; Campanato 1963) on closed half balls.

The argument runs on any compact set `S` with interior measure density
(`BasicElliptic.HasDensity S c₀ ρ₀`, a "type A" region) and for a field `F : E → V`
**continuous** on `S` with values in a Banach space `V`. Continuity identifies `F p` with the limit
of the averages `A(p, ρ) = ⨍_{B_ρ(p) ∩ S} F`, so no Lebesgue points and no representatives are
needed. The hypothesis `IsCampanatoOn S F α M ρ₀` is

  `⨍_{B_ρ(p) ∩ S} ‖F - A(p, ρ)‖² ≤ M² ρ^{2α}` for `p ∈ S`, `0 < ρ ≤ ρ₀`.

* `norm_setAverage_sub_setAverage_le_of_campanato`: if `B_{ρ₂}(p₂) ⊆ B_{ρ₁}(p₁)` and
  `ρ₂ ≤ ρ₁ ≤ 2 ρ₂`, then `‖A(p₁, ρ₁) - A(p₂, ρ₂)‖ ≤ K M ρ₁^α`. Average
  `‖a - b‖² ≤ 2 ‖F - a‖² + 2 ‖F - b‖²` over `B_{ρ₂}(p₂) ∩ S` and use the density bound.
* `norm_sub_setAverage_le_of_campanato`: `‖F p - A(p, ρ)‖ ≤ L M ρ^α` (telescoping over
  `ρ 2^{-k}` and continuity of `F` at `p`).
* `norm_sub_le_of_campanato`: `‖F p - F q‖ ≤ C M |p - q|^α` for `|p - q| ≤ ρ₀ / 2`.
* `holderOnWith_of_campanato`: the half-ball statement. Half balls have density
  (`halfBall_density`) and are convex, so two midpoint steps extend the local bound to all pairs.

The constants depend only on `E` (through `d = finrank ℝ E` and `|B_1|`), `c₀` and `α`.

## References

* S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup.
  Pisa (3) 17 (1963), 175–188.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.

## Provenance

The comparison of two averages (`sq_ballAverage_sub_le`, `abs_ballAverage_sub_half_le`,
`abs_ballAverage_sub_of_dist_le`) and the dyadic telescoping (`abs_ballAverage_sub_dyadic`) are
adapted from LeanPool/lean-pool, <https://github.com/LeanPool/lean-pool>, files
`LeanPool/EllipticPDE/Campanato/{Basic,Compare,Telescope,Holder}.lean`, commit
`2d2ff0720fb4979f0265226ee62f1d573d0a9085` (Apache-2.0, © 2026 Alejandro Soto Franco).
Changes: real-valued `u` on `EuclideanSpace ℝ (Fin d)` with balls inside an open `Ω` becomes a
`V`-valued `F` on a finite-dimensional inner product space, with averages over `B_ρ(p) ∩ S` on a set
with density; the hypothesis is in average form; continuity of `F` replaces the a.e.
representative `campanatoLimit` and the Lebesgue differentiation theorem.
-/

public section

open MeasureTheory Metric Set Filter Module RealInnerProductSpace
open scoped Topology

namespace BasicElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Campanato decay hypothesis in average form on a set `S`: for `p ∈ S` and `0 < ρ ≤ ρ₀`,
`⨍_{B_ρ(p) ∩ S} ‖F - ⨍_{B_ρ(p) ∩ S} F‖² ≤ M² ρ^{2α}`. -/
@[expose] def IsCampanatoOn (S : Set E) (F : E → V) (α M ρ₀ : ℝ) : Prop :=
  ∀ p ∈ S, ∀ ρ ∈ Ioc 0 ρ₀,
    ⨍ y in ball p ρ ∩ S, ‖F y - ⨍ z in ball p ρ ∩ S, F z‖ ^ 2 ≤ M ^ 2 * ρ ^ (2 * α)

/-! ### Constants -/

/-- The comparison constant `K = √(2 (2^d + 1) |B_1| / c₀)`. -/
noncomputable def campanatoCompareConst (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c₀ : ℝ) : ℝ :=
  Real.sqrt (2 * (2 ^ finrank ℝ E + 1) * unitBallVolume E / c₀)

/-- The telescoped constant `L = K / (1 - 2^{-α})`. -/
noncomputable def campanatoLimitConst (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c₀ α : ℝ) : ℝ :=
  campanatoCompareConst E c₀ / (1 - (1 / 2 : ℝ) ^ α)

/-- The local Hölder constant `3 L + 2 K` of `norm_sub_le_of_campanato`. -/
noncomputable def campanatoHolderConst (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c₀ α : ℝ) : ℝ :=
  3 * campanatoLimitConst E c₀ α + 2 * campanatoCompareConst E c₀

theorem campanatoCompareConst_nonneg (c₀ : ℝ) : 0 ≤ campanatoCompareConst E c₀ :=
  Real.sqrt_nonneg _

theorem campanatoLimitConst_nonneg {c₀ α : ℝ} (hα : 0 < α) :
    0 ≤ campanatoLimitConst E c₀ α := by
  have : (1 / 2 : ℝ) ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  exact div_nonneg (campanatoCompareConst_nonneg c₀) (by linarith)

theorem campanatoHolderConst_nonneg {c₀ α : ℝ} (hα : 0 < α) :
    0 ≤ campanatoHolderConst E c₀ α := by
  have := campanatoLimitConst_nonneg (E := E) (c₀ := c₀) hα
  have := campanatoCompareConst_nonneg (E := E) c₀
  rw [campanatoHolderConst]; positivity

/-! ### Elementary facts about averages -/

/-- If `‖F y - v‖ ≤ ε` on `U`, then the average of `F` over `U` is within `ε` of `v`. -/
theorem norm_setAverage_sub_le_of_forall [CompleteSpace V] {U : Set E} {F : E → V} {v : V} {ε : ℝ}
    (hU0 : volume U ≠ 0) (hU : volume U ≠ ⊤) (hFi : IntegrableOn F U)
    (hε : ∀ y ∈ U, ‖F y - v‖ ≤ ε) :
    ‖(⨍ y in U, F y) - v‖ ≤ ε := by
  have hpos : 0 < volume.real U := ENNReal.toReal_pos hU0 hU
  have hsub : (⨍ y in U, F y) - v = (volume.real U)⁻¹ • ∫ y in U, (F y - v) := by
    rw [integral_sub hFi (integrableOn_const hU), setIntegral_const, setAverage_eq, smul_sub,
      smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  calc (volume.real U)⁻¹ * ‖∫ y in U, (F y - v)‖
      ≤ (volume.real U)⁻¹ * (ε * volume.real U) :=
        mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const hU.lt_top hε)
          (inv_pos.2 hpos).le
    _ = ε := by field_simp

omit [NormedSpace ℝ V] in
/-- **Comparison of two constants** (after LeanPool `sq_ballAverage_sub_le`): if `T ⊆ U₁ ∩ U₂`,
then `‖a - b‖² |T| ≤ 2 ∫_{U₁} ‖F - a‖² + 2 ∫_{U₂} ‖F - b‖²`. -/
theorem sq_norm_sub_mul_le {T U₁ U₂ : Set E} {F : E → V} {a b : V} (hT : MeasurableSet T)
    (hTfin : volume T ≠ ⊤) (hT₁ : T ⊆ U₁) (hT₂ : T ⊆ U₂)
    (hi₁ : IntegrableOn (fun y ↦ ‖F y - a‖ ^ 2) U₁)
    (hi₂ : IntegrableOn (fun y ↦ ‖F y - b‖ ^ 2) U₂) :
    ‖a - b‖ ^ 2 * volume.real T ≤
      2 * (∫ y in U₁, ‖F y - a‖ ^ 2) + 2 * ∫ y in U₂, ‖F y - b‖ ^ 2 := by
  have hpt : ∀ y ∈ T, ‖a - b‖ ^ 2 ≤ 2 * ‖F y - a‖ ^ 2 + 2 * ‖F y - b‖ ^ 2 := by
    intro y _
    have h : ‖a - b‖ ≤ ‖F y - a‖ + ‖F y - b‖ := by
      calc ‖a - b‖ = ‖(F y - b) - (F y - a)‖ := by congr 1; abel
        _ ≤ ‖F y - b‖ + ‖F y - a‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    nlinarith [norm_nonneg (a - b), sq_nonneg (‖F y - a‖ - ‖F y - b‖)]
  have hiT₁ := hi₁.mono_set hT₁
  have hiT₂ := hi₂.mono_set hT₂
  have hmono := setIntegral_mono_on (integrableOn_const hTfin)
    ((hiT₁.const_mul 2).add (hiT₂.const_mul 2)) hT hpt
  simp only [Pi.add_apply] at hmono
  rw [setIntegral_const, smul_eq_mul, integral_add (hiT₁.const_mul 2) (hiT₂.const_mul 2),
    integral_const_mul, integral_const_mul] at hmono
  have h₁ : ∫ y in T, ‖F y - a‖ ^ 2 ≤ ∫ y in U₁, ‖F y - a‖ ^ 2 :=
    setIntegral_mono_set hi₁ (ae_of_all _ fun _ ↦ by positivity) hT₁.eventuallyLE
  have h₂ : ∫ y in T, ‖F y - b‖ ^ 2 ≤ ∫ y in U₂, ‖F y - b‖ ^ 2 :=
    setIntegral_mono_set hi₂ (ae_of_all _ fun _ ↦ by positivity) hT₂.eventuallyLE
  calc ‖a - b‖ ^ 2 * volume.real T = volume.real T * ‖a - b‖ ^ 2 := mul_comm _ _
    _ ≤ _ := hmono
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h₁ two_pos.le)
        (mul_le_mul_of_nonneg_left h₂ two_pos.le)

/-! ### The Campanato estimates on a set with density -/

section General

variable {S : Set E} {F : E → V} {α M ρ₀ c₀ : ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurableSet_ball_inter (hSc : IsCompact S) (p : E) (ρ : ℝ) :
    MeasurableSet (ball p ρ ∩ S) :=
  measurableSet_ball.inter hSc.isClosed.measurableSet

private theorem volume_ball_inter_ne_top (p : E) (ρ : ℝ) : volume (ball p ρ ∩ S) ≠ ⊤ :=
  ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne

omit [NormedSpace ℝ V] in
private theorem integrableOn_of_subset (hSc : IsCompact S) (hF : ContinuousOn F S) {U : Set E}
    (hU : U ⊆ S) : IntegrableOn F U :=
  (hF.integrableOn_compact hSc).mono_set hU

omit [NormedSpace ℝ V] in
private theorem integrableOn_sq_of_subset (hSc : IsCompact S) (hF : ContinuousOn F S)
    {U : Set E} (hU : U ⊆ S) (c : V) : IntegrableOn (fun y ↦ ‖F y - c‖ ^ 2) U :=
  (((hF.sub continuousOn_const).norm.pow 2).integrableOn_compact hSc).mono_set hU

private theorem volumeReal_pos (hc₀ : 0 < c₀) (hS : HasDensity S c₀ ρ₀) {p : E} (hp : p ∈ S)
    {ρ : ℝ} (hρ : ρ ∈ Ioc 0 ρ₀) : 0 < volume.real (ball p ρ ∩ S) :=
  lt_of_lt_of_le (by have := hρ.1; positivity) (hS p hp ρ hρ)

/-- The Campanato hypothesis bounds the integral: `∫ ‖F - A(p, ρ)‖² ≤ |B_1| ρ^d M² ρ^{2α}`. -/
private theorem integral_sq_le (hc₀ : 0 < c₀) (hS : HasDensity S c₀ ρ₀)
    (hcamp : IsCampanatoOn S F α M ρ₀) {p : E} (hp : p ∈ S) {ρ : ℝ} (hρ : ρ ∈ Ioc 0 ρ₀) :
    ∫ y in ball p ρ ∩ S, ‖F y - ⨍ z in ball p ρ ∩ S, F z‖ ^ 2 ≤
      unitBallVolume E * ρ ^ finrank ℝ E * (M ^ 2 * ρ ^ (2 * α)) := by
  set U := ball p ρ ∩ S
  have hpos := volumeReal_pos hc₀ hS hp hρ
  have h := hcamp p hp ρ hρ
  rw [setAverage_eq, smul_eq_mul] at h
  have hvol : volume.real U ≤ unitBallVolume E * ρ ^ finrank ℝ E := by
    rw [mul_comm, ← measureReal_ball_eq hρ.1]
    exact measureReal_mono inter_subset_left measure_ball_lt_top.ne
  have hMρ : 0 ≤ M ^ 2 * ρ ^ (2 * α) := by
    have := Real.rpow_nonneg hρ.1.le (2 * α); positivity
  calc ∫ y in U, ‖F y - ⨍ z in U, F z‖ ^ 2
      = volume.real U * ((volume.real U)⁻¹ * ∫ y in U, ‖F y - ⨍ z in U, F z‖ ^ 2) := by
        rw [mul_inv_cancel_left₀ hpos.ne']
    _ ≤ volume.real U * (M ^ 2 * ρ ^ (2 * α)) := mul_le_mul_of_nonneg_left h hpos.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hvol hMρ

/-- **Comparison of two averages** (after LeanPool `abs_ballAverage_sub_le_of_le` and
`abs_ballAverage_sub_of_dist_le`). If `B_{ρ₂}(p₂) ⊆ B_{ρ₁}(p₁)` and `ρ₂ ≤ ρ₁ ≤ 2 ρ₂ ≤ 2 ρ₀`,
then `‖A(p₁, ρ₁) - A(p₂, ρ₂)‖ ≤ K M ρ₁^α`. -/
theorem norm_setAverage_sub_setAverage_le_of_campanato (hα : 0 < α) (hM : 0 ≤ M)
    (hc₀ : 0 < c₀) (hSc : IsCompact S) (hS : HasDensity S c₀ ρ₀) (hF : ContinuousOn F S)
    (hcamp : IsCampanatoOn S F α M ρ₀) {p₁ p₂ : E} (hp₁ : p₁ ∈ S) (hp₂ : p₂ ∈ S)
    {ρ₁ ρ₂ : ℝ} (hρ₂ : 0 < ρ₂) (h₂₁ : ρ₂ ≤ ρ₁) (h₁₂ : ρ₁ ≤ 2 * ρ₂) (hρ₁ : ρ₁ ≤ ρ₀)
    (hball : ball p₂ ρ₂ ⊆ ball p₁ ρ₁) :
    ‖(⨍ z in ball p₁ ρ₁ ∩ S, F z) - ⨍ z in ball p₂ ρ₂ ∩ S, F z‖ ≤
      campanatoCompareConst E c₀ * M * ρ₁ ^ α := by
  have hρ₁0 : 0 < ρ₁ := hρ₂.trans_le h₂₁
  have hmem₁ : ρ₁ ∈ Ioc 0 ρ₀ := ⟨hρ₁0, hρ₁⟩
  have hmem₂ : ρ₂ ∈ Ioc 0 ρ₀ := ⟨hρ₂, h₂₁.trans hρ₁⟩
  have hI₁ := integral_sq_le hc₀ hS hcamp hp₁ hmem₁
  have hI₂ := integral_sq_le hc₀ hS hcamp hp₂ hmem₂
  have hden := hS p₂ hp₂ ρ₂ hmem₂
  set d := finrank ℝ E
  set ω := unitBallVolume E
  have hω : 0 < ω := unitBallVolume_pos
  set a := ⨍ z in ball p₁ ρ₁ ∩ S, F z
  set b := ⨍ z in ball p₂ ρ₂ ∩ S, F z
  have hcmp := sq_norm_sub_mul_le (F := F) (a := a) (b := b)
    (measurableSet_ball_inter hSc p₂ ρ₂) (volume_ball_inter_ne_top p₂ ρ₂)
    (inter_subset_inter_left _ hball) subset_rfl
    (integrableOn_sq_of_subset hSc hF inter_subset_right a)
    (integrableOn_sq_of_subset hSc hF inter_subset_right b)
  -- powers
  set X : ℝ := ρ₁ ^ α with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hρ₁0.le _
  have h2α₁ : ρ₁ ^ (2 * α) = X ^ 2 := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hρ₁0.le]; congr 1; push_cast; ring
  have h2α₂ : ρ₂ ^ (2 * α) ≤ X ^ 2 := by
    rw [← h2α₁]; exact Real.rpow_le_rpow hρ₂.le h₂₁ (by linarith)
  have hd₁ : ρ₁ ^ d ≤ 2 ^ d * ρ₂ ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hρ₁0.le h₁₂ d
  have hρ₂d : 0 < ρ₂ ^ d := pow_pos hρ₂ d
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  -- the squared bound
  have hsq : ‖a - b‖ ^ 2 * (c₀ * ρ₂ ^ d) ≤
      (2 * (2 ^ d + 1) * ω) * (M ^ 2 * X ^ 2) * ρ₂ ^ d := by
    have h1 : ‖a - b‖ ^ 2 * (c₀ * ρ₂ ^ d) ≤ ‖a - b‖ ^ 2 * volume.real (ball p₂ ρ₂ ∩ S) :=
      mul_le_mul_of_nonneg_left hden (sq_nonneg _)
    have h2 : ω * ρ₁ ^ d * (M ^ 2 * ρ₁ ^ (2 * α)) ≤ ω * (2 ^ d * ρ₂ ^ d) * (M ^ 2 * X ^ 2) := by
      rw [h2α₁]; gcongr
    have h3 : ω * ρ₂ ^ d * (M ^ 2 * ρ₂ ^ (2 * α)) ≤ ω * ρ₂ ^ d * (M ^ 2 * X ^ 2) := by
      gcongr
    nlinarith
  have hK : campanatoCompareConst E c₀ ^ 2 * c₀ = 2 * (2 ^ d + 1) * ω := by
    rw [campanatoCompareConst, Real.sq_sqrt (by positivity), div_mul_cancel₀ _ hc₀.ne']
  have hsq' : ‖a - b‖ ^ 2 ≤ (campanatoCompareConst E c₀ * M * X) ^ 2 := by
    have hpos : 0 < c₀ * ρ₂ ^ d := mul_pos hc₀ hρ₂d
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖a - b‖ ^ 2 * (c₀ * ρ₂ ^ d) ≤ (2 * (2 ^ d + 1) * ω) * (M ^ 2 * X ^ 2) * ρ₂ ^ d := hsq
      _ = (campanatoCompareConst E c₀ * M * X) ^ 2 * (c₀ * ρ₂ ^ d) := by rw [← hK]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (campanatoCompareConst_nonneg c₀) hM) hX0) two_ne_zero).1 hsq'

private theorem half_pow_rpow {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) (α : ℝ) :
    (ρ * (1 / 2 : ℝ) ^ k) ^ α = ρ ^ α * ((1 / 2 : ℝ) ^ α) ^ k := by
  rw [Real.mul_rpow hρ (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ) α, mul_comm]

/-- **Dyadic telescoping** (after LeanPool `abs_ballAverage_sub_dyadic`):
`‖A(p, ρ) - A(p, ρ 2^{-k})‖ ≤ K M ρ^α (1 - q^k) / (1 - q)`, `q = 2^{-α}`. -/
private theorem norm_setAverage_sub_dyadic_le (hα : 0 < α) (hM : 0 ≤ M)
    (hc₀ : 0 < c₀) (hSc : IsCompact S) (hS : HasDensity S c₀ ρ₀) (hF : ContinuousOn F S)
    (hcamp : IsCampanatoOn S F α M ρ₀) {p : E} (hp : p ∈ S) {ρ : ℝ} (hρ : ρ ∈ Ioc 0 ρ₀)
    (k : ℕ) :
    ‖(⨍ z in ball p ρ ∩ S, F z) - ⨍ z in ball p (ρ * (1 / 2 : ℝ) ^ k) ∩ S, F z‖ ≤
      campanatoCompareConst E c₀ * M * ρ ^ α *
        ((1 - ((1 / 2 : ℝ) ^ α) ^ k) / (1 - (1 / 2 : ℝ) ^ α)) := by
  set q : ℝ := (1 / 2 : ℝ) ^ α with hq
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hden : 0 < 1 - q := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hk0 : 0 < ρ * (1 / 2 : ℝ) ^ k := by have := hρ.1; positivity
    have hkle : ρ * (1 / 2 : ℝ) ^ k ≤ ρ :=
      mul_le_of_le_one_right hρ.1.le (pow_le_one₀ (by norm_num) (by norm_num))
    have hstep := norm_setAverage_sub_setAverage_le_of_campanato hα hM hc₀ hSc hS hF hcamp
      hp hp (ρ₁ := ρ * (1 / 2 : ℝ) ^ k) (ρ₂ := ρ * (1 / 2 : ℝ) ^ (k + 1))
      (by have := hρ.1; positivity) (by rw [pow_succ]; linarith) (by rw [pow_succ]; linarith)
      (hkle.trans hρ.2) (ball_subset_ball (by rw [pow_succ]; linarith))
    rw [half_pow_rpow hρ.1.le, ← hq] at hstep
    calc _ ≤ ‖(⨍ z in ball p ρ ∩ S, F z) - ⨍ z in ball p (ρ * (1 / 2 : ℝ) ^ k) ∩ S, F z‖ +
          ‖(⨍ z in ball p (ρ * (1 / 2 : ℝ) ^ k) ∩ S, F z) -
            ⨍ z in ball p (ρ * (1 / 2 : ℝ) ^ (k + 1)) ∩ S, F z‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add ih hstep
      _ = _ := by field_simp; ring

/-- **The value is close to the averages:** `‖F p - A(p, ρ)‖ ≤ L M ρ^α` for `p ∈ S`,
`0 < ρ ≤ ρ₀`. Continuity of `F` replaces the Lebesgue differentiation theorem. -/
theorem norm_sub_setAverage_le_of_campanato [CompleteSpace V] (hα : 0 < α) (hM : 0 ≤ M)
    (hc₀ : 0 < c₀) (hSc : IsCompact S) (hS : HasDensity S c₀ ρ₀) (hF : ContinuousOn F S)
    (hcamp : IsCampanatoOn S F α M ρ₀) {p : E} (hp : p ∈ S) {ρ : ℝ} (hρ : ρ ∈ Ioc 0 ρ₀) :
    ‖F p - ⨍ z in ball p ρ ∩ S, F z‖ ≤ campanatoLimitConst E c₀ α * M * ρ ^ α := by
  set q : ℝ := (1 / 2 : ℝ) ^ α with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hden : 0 < 1 - q := by linarith
  have hK := campanatoCompareConst_nonneg (E := E) c₀
  have hρα : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ.1.le _
  have hbound : ∀ k : ℕ,
      ‖(⨍ z in ball p ρ ∩ S, F z) - ⨍ z in ball p (ρ * (1 / 2 : ℝ) ^ k) ∩ S, F z‖ ≤
        campanatoLimitConst E c₀ α * M * ρ ^ α := by
    intro k
    refine (norm_setAverage_sub_dyadic_le hα hM hc₀ hSc hS hF hcamp hp hρ k).trans ?_
    rw [campanatoLimitConst, ← hq, div_eq_mul_one_div (campanatoCompareConst E c₀)]
    have : (1 - q ^ k) / (1 - q) ≤ 1 / (1 - q) :=
      div_le_div_of_nonneg_right (by have := pow_nonneg hq0 k; linarith) hden.le
    have : 0 ≤ campanatoCompareConst E c₀ * M * ρ ^ α := by positivity
    nlinarith
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousWithinAt_iff.1 (hF p hp) (ε / 2) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hδ hρ.1) (by norm_num : (1 / 2 : ℝ) < 1)
  set r := ρ * (1 / 2 : ℝ) ^ k with hr
  have hr0 : 0 < r := by have := hρ.1; positivity
  have hrδ : r < δ := by rw [hr, mul_comm]; exact (lt_div_iff₀ hρ.1).1 hk
  have hrmem : r ∈ Ioc 0 ρ₀ :=
    ⟨hr0, (mul_le_of_le_one_right hρ.1.le (pow_le_one₀ (by norm_num) (by norm_num))).trans hρ.2⟩
  have hclose : ‖(⨍ z in ball p r ∩ S, F z) - F p‖ ≤ ε / 2 := by
    refine norm_setAverage_sub_le_of_forall ?_ (volume_ball_inter_ne_top p r)
      (integrableOn_of_subset hSc hF inter_subset_right) fun y hy ↦ ?_
    · have := volumeReal_pos hc₀ hS hp hrmem
      exact fun h ↦ by simp [measureReal_def, h] at this
    · rw [← dist_eq_norm]
      exact (hδF hy.2 ((mem_ball.1 hy.1).trans hrδ)).le
  calc ‖F p - ⨍ z in ball p ρ ∩ S, F z‖
      ≤ ‖(⨍ z in ball p r ∩ S, F z) - F p‖ +
          ‖(⨍ z in ball p ρ ∩ S, F z) - ⨍ z in ball p r ∩ S, F z‖ := by
        rw [norm_sub_rev (F p)]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _ |>.trans_eq (add_comm _ _)
    _ ≤ ε / 2 + campanatoLimitConst E c₀ α * M * ρ ^ α := add_le_add hclose (hbound k)
    _ < campanatoLimitConst E c₀ α * M * ρ ^ α + ε := by linarith

/-- **Campanato ⇒ Hölder, local form.** On a compact set with density `c₀` up to scale `ρ₀`,
`‖F p - F q‖ ≤ C M |p - q|^α` for `|p - q| ≤ ρ₀ / 2`, `C = campanatoHolderConst E c₀ α`. -/
theorem norm_sub_le_of_campanato [CompleteSpace V] (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M)
    (hc₀ : 0 < c₀) (hSc : IsCompact S) (hS : HasDensity S c₀ ρ₀) (hF : ContinuousOn F S)
    (hcamp : IsCampanatoOn S F α M ρ₀) {p q : E} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : dist p q ≤ ρ₀ / 2) :
    ‖F p - F q‖ ≤ campanatoHolderConst E c₀ α * M * dist p q ^ α := by
  rcases (dist_nonneg (x := p) (y := q)).eq_or_lt with h0 | hδ
  · rw [← h0, dist_eq_zero.1 h0.symm, sub_self, norm_zero]
    have := campanatoHolderConst_nonneg (E := E) (c₀ := c₀) hα
    rw [Real.zero_rpow hα.ne', mul_zero]
  set δ := dist p q with hδdef
  have hK := campanatoCompareConst_nonneg (E := E) c₀
  have hL := campanatoLimitConst_nonneg (E := E) (c₀ := c₀) hα
  have h2δ : 2 * δ ≤ ρ₀ := by linarith
  have hball : ball q δ ⊆ ball p (2 * δ) := fun y hy ↦ by
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y q p, dist_comm p q]
  have h1 := norm_sub_setAverage_le_of_campanato hα hM hc₀ hSc hS hF hcamp hp
    (ρ := 2 * δ) ⟨by linarith, h2δ⟩
  have h2 := norm_setAverage_sub_setAverage_le_of_campanato hα hM hc₀ hSc hS hF hcamp hp hq
    hδ (by linarith) le_rfl h2δ hball
  have h3 := norm_sub_setAverage_le_of_campanato hα hM hc₀ hSc hS hF hcamp hq
    (ρ := δ) ⟨hδ, by linarith⟩
  have h2α : (2 * δ) ^ α ≤ 2 * δ ^ α := by
    rw [Real.mul_rpow (by norm_num) hδ.le]
    have : (2 : ℝ) ^ α ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hδ.le _)
  have hLM : 0 ≤ campanatoLimitConst E c₀ α * M := mul_nonneg hL hM
  have hKM : 0 ≤ campanatoCompareConst E c₀ * M := mul_nonneg hK hM
  calc ‖F p - F q‖
      ≤ ‖F p - ⨍ z in ball p (2 * δ) ∩ S, F z‖ +
          ‖(⨍ z in ball p (2 * δ) ∩ S, F z) - ⨍ z in ball q δ ∩ S, F z‖ +
          ‖F q - ⨍ z in ball q δ ∩ S, F z‖ := by
        refine (norm_sub_le_norm_sub_add_norm_sub _ (⨍ z in ball q δ ∩ S, F z) _).trans ?_
        rw [norm_sub_rev (⨍ z in ball q δ ∩ S, F z) (F q)]
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ campanatoLimitConst E c₀ α * M * (2 * δ) ^ α +
          campanatoCompareConst E c₀ * M * (2 * δ) ^ α +
          campanatoLimitConst E c₀ α * M * δ ^ α := by gcongr
    _ ≤ campanatoLimitConst E c₀ α * M * (2 * δ ^ α) +
          campanatoCompareConst E c₀ * M * (2 * δ ^ α) +
          campanatoLimitConst E c₀ α * M * δ ^ α := by gcongr
    _ = campanatoHolderConst E c₀ α * M * δ ^ α := by rw [campanatoHolderConst]; ring

end General

/-! ### Half balls -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ V] in
/-- Doubling the range of a Hölder bound on a convex set via the midpoint (`α ≤ 1`). -/
private theorem norm_sub_le_of_midpoint {S : Set E} (hS : Convex ℝ S) {F : E → V}
    {C α r : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (h : ∀ p ∈ S, ∀ q ∈ S, dist p q ≤ r → ‖F p - F q‖ ≤ C * dist p q ^ α) :
    ∀ p ∈ S, ∀ q ∈ S, dist p q ≤ 2 * r → ‖F p - F q‖ ≤ (2 * C) * dist p q ^ α := by
  intro p hp q hq hpq
  set m := midpoint ℝ p q
  have hm : m ∈ S := hS.segment_subset hp hq (midpoint_mem_segment p q)
  have h2 : ‖(2 : ℝ)‖⁻¹ = 1 / 2 := by norm_num
  have hpm : dist p m = dist p q / 2 := by
    rw [dist_left_midpoint, h2]; ring
  have hmq : dist m q = dist p q / 2 := by
    rw [dist_midpoint_right, h2]; ring
  have hhalf : (dist p q / 2) ^ α ≤ dist p q ^ α :=
    Real.rpow_le_rpow (by positivity) (by linarith [dist_nonneg (x := p) (y := q)]) hα.le
  calc ‖F p - F q‖ ≤ ‖F p - F m‖ + ‖F m - F q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * dist p m ^ α + C * dist m q ^ α :=
        add_le_add (h p hp m hm (by rw [hpm]; linarith)) (h m hm q hq (by rw [hmq]; linarith))
    _ ≤ C * dist p q ^ α + C * dist p q ^ α := by
        rw [hpm, hmq]; gcongr
    _ = (2 * C) * dist p q ^ α := by ring

/-- **Campanato's characterization on half balls** (GM; Campanato 1963): proves the
frozen `CampanatoHolderStatement`, with `C = 4 · campanatoHolderConst E (|B_1| / 14^d) α`. -/
theorem holderOnWith_of_campanato (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] : CampanatoHolderStatement E V := by
  intro α hα hα1
  refine ⟨4 * campanatoHolderConst E (halfBallDensityConst E) α, ?_⟩
  intro ν x R M F hν hR hx hM hF hcamp p hp q hq
  set S := halfBall ν x R
  have hC := campanatoHolderConst_nonneg (E := E) (c₀ := halfBallDensityConst E) hα
  have hSc : IsCompact S := (isCompact_closedBall x R).inter_right (isClosed_halfSpace ν)
  have hloc' : ∀ p ∈ S, ∀ q ∈ S, dist p q ≤ R / 2 →
      ‖F p - F q‖ ≤ (campanatoHolderConst E (halfBallDensityConst E) α * M) * dist p q ^ α :=
    fun p hp q hq h ↦ norm_sub_le_of_campanato hα hα1 hM halfBallDensityConst_pos hSc
      (halfBall_density hν hR hx) hF hcamp hp hq h
  have h2 := norm_sub_le_of_midpoint (convex_halfBall ν x R) hα (mul_nonneg hC hM) hloc'
  have h4 := norm_sub_le_of_midpoint (convex_halfBall ν x R) hα (by positivity) h2
  have hdist : dist p q ≤ 2 * (2 * (R / 2)) := by
    have := dist_triangle p x q
    rw [dist_comm x q] at this
    linarith [(mem_halfBall.1 hp).1, (mem_halfBall.1 hq).1]
  calc ‖F p - F q‖ ≤ 2 * (2 * (campanatoHolderConst E (halfBallDensityConst E) α * M)) *
        dist p q ^ α := h4 p hp q hq hdist
    _ = _ := by ring

end BasicElliptic
