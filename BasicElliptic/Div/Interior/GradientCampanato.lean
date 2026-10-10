/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Interior.PointDecay
public import BasicElliptic.Defs.Elliptic
public import BasicElliptic.Defs.Holder
import BasicElliptic.Normalize.Cholesky
import BasicElliptic.Normalize.ChangeOfVariables
import BasicElliptic.Normalize.Ellipsoid
import BasicElliptic.Normalize.HolderMap
import BasicElliptic.Campanato.Density
import BasicElliptic.Common.BallMeasure
import BasicElliptic.Common.RealArith

/-!
# Campanato decay of `∇w` at an interior point

`BasicElliptic.Div.gradient_campanato_at_point`: let `w ∈ C¹(U)` be a weak solution of
`-div (a ∇w - G) = f` on an open `U` (`Div.IsWeakSolOn a G f U w`), with `a` uniformly elliptic
(`lam`, `Λ`; not necessarily symmetric), `a ∈ C^α` (constant `K_a`), `G ∈ C^α` (constant `K_G`),
`|f| ≤ M_f`. If `B_δ(x₀) ⊆ U` and `‖∇w‖ ≤ M₀` on `B_δ(x₀)`, then for every set `S` and
`0 < ρ ≤ √(lam/Λ) δ`

`∫_{B_ρ(x₀) ∩ S} ‖∇w - (∇w)_{B_ρ(x₀) ∩ S}‖²`
  `≤ C ρ^{d+2α} (M₀² δ^{-2α} + K_a² M₀² + K_G² + M_f² δ^{2-2α})`

with `C = C(E, α, lam, Λ)`.

## Proof

Write `a(x₀) = A_s + A_k` (symmetric and skew parts) and take `M` with `M M† = A_s`,
`‖M‖ ≤ √Λ`, `‖M⁻¹‖ ≤ 1/√lam` (`exists_sqrt_symPart`). Under `T z = x₀ + M z` the weak identity
transports (`IsWeakEqOn.comp_affine`) to coefficients `ã = M⁻¹ (a ∘ T) M⁻†` with
`ã(0) = 1 + K_s`, `K_s = M⁻¹ A_k M⁻†` skew, data `G̃ = M⁻¹ (G ∘ T)`, `f̃ = f ∘ T` and field
`F̃ = M† (∇w ∘ T) = ∇(w ∘ T)`, which is weakly curl-free. On `B_{R̃}(0)`, `R̃ = δ/√Λ`
(`T(B_{R̃}(0)) ⊆ B_δ(x₀)`): `‖ã(z) - ã(0)‖ ≤ K_a Λ^{α/2} lam⁻¹ |z|^α`,
`‖G̃(z) - G̃(0)‖ ≤ K_G Λ^{α/2} lam^{-1/2} |z|^α`, `‖F̃‖ ≤ √Λ M₀`. The one-point decay with skew part
(`campanato_decay_at_point_skew`), together with `ψ̃(R̃) ≤ ∫_{B_{R̃}} ‖F̃‖² ≤ Λ M₀² |B_{R̃}|`, gives
`ψ̃(ρ̃) ≤ C ρ̃^{d+2α} (…)` for `ρ̃ ≤ R̃`. Back in the original coordinates,
`B_ρ(x₀) ⊆ T(B_{ρ/√lam}(0))`, and with `c = M^{-†} F̃_{0,ρ/√lam}`,
`∫_{T(B_ρ̃)} ‖∇w - c‖² = |det M| ∫_{B_ρ̃} ‖M^{-†}(F̃ - F̃_{ρ̃})‖² ≤ Λ^{d/2} lam⁻¹ ψ̃(ρ̃)`
(`|det M| ≤ ‖M‖^d`, by comparing volumes). The mean over `B_ρ(x₀) ∩ S` minimizes.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012. (GM)
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient ContDiff Topology NNReal

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private instance isFiniteMeasure_restrict_ball' (x : E) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (ball x r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

/-- Restriction of the weak identity to a ball inside the region and the test domain. -/
private theorem IsWeakEqOn.restrict_ball {a : E → E →L[ℝ] E} {G F : E → E} {f : E → ℝ}
    {s U : Set E} (h : IsWeakEqOn a G f F s U) (hs : MeasurableSet s) {c : E} {r : ℝ}
    (hBs : ball c r ⊆ s) (hBU : ball c r ⊆ U) : IsWeakEqOn a G f F (ball c r) (ball c r) := by
  intro φ hφ
  have key := h φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hBU⟩
  have h0 := fun y hy ↦ hφ.eq_zero_and_gradient_eq_zero (y := y) hy
  rwa [setIntegral_eq_of_inter_subset hs hBs inter_subset_right fun y hy ↦ by simp [(h0 y hy).2],
    setIntegral_eq_of_inter_subset hs hBs inter_subset_right fun y hy ↦ by simp [(h0 y hy).2],
    setIntegral_eq_of_inter_subset hs hBs inter_subset_right fun y hy ↦ by
      simp [(h0 y hy).1]] at key

/-- Weak curl-freeness only depends on the values on `U`. -/
private theorem IsWeakCurlFree.congr {F F' : E → E} {U : Set E} (h : IsWeakCurlFree F U)
    (hU : MeasurableSet U) (heq : EqOn F F' U) : IsWeakCurlFree F' U := by
  intro ψ hψ u v
  have e : ∀ u v : E, ∫ y in U, ⟪F y, u⟫ * fderiv ℝ ψ y v =
      ∫ y in U, ⟪F' y, u⟫ * fderiv ℝ ψ y v := fun u v ↦
    setIntegral_congr_fun hU fun y hy ↦ by simp only [heq hy]
  rw [← e, ← e]
  exact h ψ hψ u v

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem integrable_norm_sq' {μ : Measure E} {g : E → E} (hg : MemLp g 2 μ) :
    Integrable (fun y ↦ ‖g y‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg

/-- `∫_s g ≤ C |s|` for `|g| ≤ C` on a ball. -/
private theorem setIntegral_le_of_abs_le {g : E → ℝ} {x₀ : E} {r C : ℝ}
    (h : ∀ y ∈ ball x₀ r, |g y| ≤ C) : ∫ y in ball x₀ r, g y ≤ C * volume.real (ball x₀ r) :=
  (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const measure_ball_lt_top
    fun y hy ↦ by rw [Real.norm_eq_abs]; exact h y hy)

/-- The conclusion of `campanato_decay_at_point_skew` with constant `Cd`, as a predicate. -/
private def DecayProp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α Cd : ℝ) : Prop :=
  ∀ (x₀ : E) (R M K KG Kf : ℝ) (F G : E → E) (f : E → ℝ)
      (ã : E → E →L[ℝ] E) (Ks : E →L[ℝ] E), ContinuousLinearMap.adjoint Ks = -Ks → 0 < R →
      AEStronglyMeasurable F (volume.restrict (ball x₀ R)) → (∀ y ∈ ball x₀ R, ‖F y‖ ≤ M) →
      IsWeakCurlFree F (ball x₀ R) →
      AEStronglyMeasurable ã (volume.restrict (ball x₀ R)) →
      (∀ y ∈ ball x₀ R, ‖ã y - (1 + Ks)‖ ≤ K * dist y x₀ ^ α) →
      AEStronglyMeasurable G (volume.restrict (ball x₀ R)) →
      (∀ y ∈ ball x₀ R, ‖G y - G x₀‖ ≤ KG * dist y x₀ ^ α) →
      (∀ y ∈ ball x₀ R, |f y| ≤ Kf) →
      IsWeakEqOn ã G f F (ball x₀ R) (ball x₀ R) →
      ∀ ρ ∈ Ioc 0 R, ∫ y in ball x₀ ρ, ‖F y - ⨍ z in ball x₀ ρ, F z‖ ^ 2 ≤
        Cd * ((ρ / R) ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (∫ y in ball x₀ R, ‖F y - ⨍ z in ball x₀ R, F z‖ ^ 2) +
          ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (K ^ 2 * M ^ 2 + KG ^ 2 + Kf ^ 2 * R ^ (2 - 2 * α)))

/-- **Decay in normalized coordinates.** With `T z = x₀ + M z` as in the module docstring, the
field `F̃ = M† (∇w ∘ T)` satisfies the one-point decay on `B_{δ/s}(0)` (`s ≥ ‖M‖`,
`1/l ≥ ‖M⁻¹‖`). -/
private theorem transported_decay {α : ℝ≥0} (hα : 0 < α) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hdec : DecayProp E α Cd) {U : Set E} {Ka KG : ℝ≥0} {Mf M₀ δ : ℝ}
    {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ} {w : E → ℝ} {x₀ : E} (hU : IsOpen U)
    (ha : HolderOnWith Ka α a U) (hG : HolderOnWith KG α G U)
    (hfb : ∀ y ∈ U, |f y| ≤ Mf) (hw : IsWeakSolOn a G f U w) (hδ : 0 < δ)
    (hball : ball x₀ δ ⊆ U) (hM₀ : ∀ y ∈ ball x₀ δ, ‖∇ w y‖ ≤ M₀)
    {M : E ≃L[ℝ] E} {s l : ℝ} (hs : 0 < s) (hl : 0 < l) (hMn : ‖(M : E →L[ℝ] E)‖ ≤ s)
    (hMn' : ‖(M.symm : E →L[ℝ] E)‖ ≤ 1 / l) {Ks : E →L[ℝ] E}
    (hconj : (M.symm : E →L[ℝ] E) ∘L a x₀ ∘L ContinuousLinearMap.adjoint (M.symm : E →L[ℝ] E) =
      1 + Ks)
    (hKs : ContinuousLinearMap.adjoint Ks = -Ks) :
    ∀ ρ ∈ Ioc 0 (δ / s),
      ∫ z in ball 0 ρ, ‖ContinuousLinearMap.adjoint (M : E →L[ℝ] E) (∇ w (x₀ + M z)) -
          ⨍ z' in ball 0 ρ, ContinuousLinearMap.adjoint (M : E →L[ℝ] E) (∇ w (x₀ + M z'))‖ ^ 2 ≤
        Cd * ((ρ / (δ / s)) ^ ((finrank ℝ E : ℝ) + 2 * α) *
            ((s * M₀) ^ 2 * volume.real (ball (0 : E) (δ / s))) +
          ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            ((Ka * s ^ (α : ℝ) / l ^ 2) ^ 2 * (s * M₀) ^ 2 + (KG * s ^ (α : ℝ) / l) ^ 2 +
              Mf ^ 2 * (δ / s) ^ (2 - 2 * (α : ℝ)))) := by
  intro ρ hρ
  set T : E → E := fun z ↦ x₀ + M z with hT
  set R := δ / s with hR
  have hR0 : 0 < R := div_pos hδ hs
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hx₀U : x₀ ∈ U := hball (mem_ball_self hδ)
  have hMz : ∀ z, ‖M z‖ ≤ s * ‖z‖ := fun z ↦
    ((M : E →L[ℝ] E).le_opNorm z).trans (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))
  have hdistT : ∀ z, dist (T z) x₀ ≤ s * dist z 0 := fun z ↦ by
    rw [dist_eq_norm, dist_zero_right, hT]
    simp only [add_sub_cancel_left]
    exact hMz z
  have hTb : ∀ z ∈ ball (0 : E) R, T z ∈ ball x₀ δ := fun z hz ↦ by
    rw [mem_ball] at hz ⊢
    calc dist (T z) x₀ ≤ s * dist z 0 := hdistT z
      _ < s * R := mul_lt_mul_of_pos_left hz hs
      _ = δ := by rw [hR]; field_simp
  have hTU : ∀ z ∈ ball (0 : E) R, T z ∈ U := fun z hz ↦ hball (hTb z hz)
  have hcontT : Continuous T := continuous_const.add M.continuous
  have hpreU : IsOpen (T ⁻¹' U) := hU.preimage hcontT
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ w y := fun y hy ↦
    (hw.1.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  have hgradc : ContinuousOn (∇ w) U := by
    have := hw.1.continuousOn_fderiv_of_isOpen hU le_rfl
    exact (toDual ℝ E).symm.continuous.comp_continuousOn this
  have haC : ContinuousOn a U := ha.continuousOn hα
  have hGC : ContinuousOn G U := hG.continuousOn hα
  have hmapsT : MapsTo T (ball 0 R) U := fun z hz ↦ hTU z hz
  -- the transported data
  set adjM := ContinuousLinearMap.adjoint (M : E →L[ℝ] E)
  set adjMi := ContinuousLinearMap.adjoint (M.symm : E →L[ℝ] E)
  have hadjM : ‖adjM‖ ≤ s := by
    rw [show ‖adjM‖ = ‖(M : E →L[ℝ] E)‖ from LinearIsometryEquiv.norm_map _ _]; exact hMn
  have hadjMi : ‖adjMi‖ ≤ 1 / l := by
    rw [show ‖adjMi‖ = ‖(M.symm : E →L[ℝ] E)‖ from LinearIsometryEquiv.norm_map _ _]
    exact hMn'
  have hwT := (hw.2.comp_affine M x₀).restrict_ball hpreU.measurableSet
    (fun z hz ↦ hTU z hz) (fun z hz ↦ hTU z hz) (c := 0) (r := R)
  -- curl-freeness of `F̃ = ∇(w ∘ T)`
  have hwt : ContDiffOn ℝ 1 (fun z ↦ w (x₀ + M z)) (ball 0 R) :=
    hw.1.comp (contDiff_const.add M.contDiff).contDiffOn hmapsT
  have hcurl : IsWeakCurlFree (fun z ↦ adjM (∇ w (x₀ + M z))) (ball 0 R) :=
    (isWeakCurlFree_gradient_of_contDiffOn isOpen_ball hwt).congr measurableSet_ball
      fun z hz ↦ gradient_comp_affine M x₀ (hdiff _ (hTU z hz))
  -- bounds
  have hFt : ∀ z ∈ ball (0 : E) R, ‖adjM (∇ w (x₀ + M z))‖ ≤ s * M₀ := fun z hz ↦
    (adjM.le_opNorm _).trans (mul_le_mul hadjM (hM₀ _ (hTb z hz)) (norm_nonneg _) hs.le)
  have hat : ∀ z ∈ ball (0 : E) R,
      ‖(M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjMi - (1 + Ks)‖ ≤
        Ka * s ^ (α : ℝ) / l ^ 2 * dist z 0 ^ (α : ℝ) := fun z hz ↦ by
    rw [← hconj]
    refine (norm_comp_comp_sub_le _ _ _ _).trans ?_
    have h1 : ‖a (x₀ + M z) - a x₀‖ ≤ Ka * (s ^ (α : ℝ) * dist z 0 ^ (α : ℝ)) := by
      rw [← dist_eq_norm]
      refine (ha.dist_le (hTU z hz) hx₀U).trans (mul_le_mul_of_nonneg_left ?_ Ka.2)
      rw [← Real.mul_rpow hs.le dist_nonneg]
      exact Real.rpow_le_rpow dist_nonneg (hdistT z) α.2
    calc ‖(M.symm : E →L[ℝ] E)‖ * ‖adjMi‖ * ‖a (x₀ + M z) - a x₀‖
        ≤ 1 / l * (1 / l) * (Ka * (s ^ (α : ℝ) * dist z 0 ^ (α : ℝ))) := by
          gcongr
      _ = _ := by field_simp
  have hGt : ∀ z ∈ ball (0 : E) R,
      ‖M.symm (G (x₀ + M z)) - M.symm (G (x₀ + M 0))‖ ≤
        KG * s ^ (α : ℝ) / l * dist z 0 ^ (α : ℝ) := fun z hz ↦ by
    rw [map_zero, add_zero, ← map_sub]
    have h1 : ‖G (x₀ + M z) - G x₀‖ ≤ KG * (s ^ (α : ℝ) * dist z 0 ^ (α : ℝ)) := by
      rw [← dist_eq_norm]
      refine (hG.dist_le (hTU z hz) hx₀U).trans (mul_le_mul_of_nonneg_left ?_ KG.2)
      rw [← Real.mul_rpow hs.le dist_nonneg]
      exact Real.rpow_le_rpow dist_nonneg (hdistT z) α.2
    calc ‖M.symm (G (x₀ + M z) - G x₀)‖
        ≤ ‖(M.symm : E →L[ℝ] E)‖ * ‖G (x₀ + M z) - G x₀‖ :=
          (M.symm : E →L[ℝ] E).le_opNorm _
      _ ≤ 1 / l * (KG * (s ^ (α : ℝ) * dist z 0 ^ (α : ℝ))) := by gcongr
      _ = _ := by field_simp
  have hft : ∀ z ∈ ball (0 : E) R, |f (x₀ + M z)| ≤ Mf := fun z hz ↦ hfb _ (hTU z hz)
  -- measurability
  have hFtm : AEStronglyMeasurable (fun z ↦ adjM (∇ w (x₀ + M z)))
      (volume.restrict (ball 0 R)) :=
    (adjM.continuous.comp_continuousOn (hgradc.comp hcontT.continuousOn hmapsT))
      |>.aestronglyMeasurable measurableSet_ball
  have hatm : AEStronglyMeasurable
      (fun z ↦ (M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjMi) (volume.restrict (ball 0 R)) :=
    (continuousOn_const.clm_comp ((haC.comp hcontT.continuousOn hmapsT).clm_comp
      continuousOn_const)).aestronglyMeasurable measurableSet_ball
  have hGtm : AEStronglyMeasurable (fun z ↦ M.symm (G (x₀ + M z)))
      (volume.restrict (ball 0 R)) :=
    ((M.symm : E →L[ℝ] E).continuous.comp_continuousOn (hGC.comp hcontT.continuousOn hmapsT))
      |>.aestronglyMeasurable measurableSet_ball
  have h := hdec 0 R (s * M₀) (Ka * s ^ (α : ℝ) / l ^ 2) (KG * s ^ (α : ℝ) / l) Mf
    (fun z ↦ adjM (∇ w (x₀ + M z))) (fun z ↦ M.symm (G (x₀ + M z))) (fun z ↦ f (x₀ + M z))
    (fun z ↦ (M.symm : E →L[ℝ] E) ∘L a (x₀ + M z) ∘L adjMi) Ks hKs hR0 hFtm hFt hcurl hatm
    hat hGtm hGt hft hwT ρ hρ
  refine h.trans ?_
  -- `ψ̃(R) ≤ ∫ ‖F̃‖² ≤ (s M₀)² |B_R|`
  have hL := memLp_restrict_ball_of_bound hFtm hFt
  have hψR : ∫ y in ball (0 : E) R, ‖adjM (∇ w (x₀ + M y)) -
      ⨍ z in ball (0 : E) R, adjM (∇ w (x₀ + M z))‖ ^ 2 ≤
        (s * M₀) ^ 2 * volume.real (ball (0 : E) R) := by
    refine (setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hL.integrable one_le_two) (integrable_norm_sq' hL) 0).trans ?_
    refine setIntegral_le_of_abs_le fun z hz ↦ ?_
    rw [sub_zero, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hFt z hz) 2
  have hρR : 0 ≤ ρ / R := div_nonneg hρ.1.le hR0.le
  gcongr

variable (E) in
/-- **Campanato decay of `∇w` at an interior point** (GM). There is
`C = C(E, α, lam, Λ) ≥ 0` such that, for a weak solution `w ∈ C¹(U)` of `-div (a ∇w - G) = f` on
an open `U` (`a` uniformly elliptic with constants `lam`, `Λ`, not necessarily symmetric,
`K_a`-Hölder; `G` `K_G`-Hölder; `|f| ≤ M_f`), a ball `B_δ(x₀) ⊆ U` on which `‖∇w‖ ≤ M₀`, any set
`S` and `0 < ρ ≤ √(lam/Λ) δ`:
`∫_{B_ρ(x₀) ∩ S} ‖∇w - (∇w)_{B_ρ(x₀) ∩ S}‖² ≤
  C ρ^{d+2α} (M₀² δ^{-2α} + K_a² M₀² + K_G² + M_f² δ^{2-2α})`.
See the module docstring for the proof. -/
theorem gradient_campanato_at_point {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Λ : ℝ}
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set E) (Ka KG : ℝ≥0) (Mf M₀ δ : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ) (x₀ : E),
      IsOpen U → IsUniformlyElliptic lam Λ a U → HolderOnWith Ka α a U →
      HolderOnWith KG α G U → (∀ y ∈ U, |f y| ≤ Mf) → IsWeakSolOn a G f U w →
      0 < δ → ball x₀ δ ⊆ U → (∀ y ∈ ball x₀ δ, ‖∇ w y‖ ≤ M₀) →
      ∀ (S : Set E) (ρ : ℝ), 0 < ρ → ρ ≤ √(lam / Λ) * δ →
        ∫ y in ball x₀ ρ ∩ S, ‖∇ w y - ⨍ z in ball x₀ ρ ∩ S, ∇ w z‖ ^ 2 ≤
          C * ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            (M₀ ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * M₀ ^ 2 + (KG : ℝ) ^ 2 +
              Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ))) := by
  obtain ⟨Cd, hCd, hdec⟩ := campanato_decay_at_point_skew E (α := (α : ℝ))
    (by exact_mod_cast hα) (by exact_mod_cast hα1)
  set s := √Λ with hsdef
  set l := √lam with hldef
  set d := finrank ℝ E
  set b : ℝ := (d : ℝ) + 2 * α with hb
  have hl : 0 < l := Real.sqrt_pos.2 hlam
  set Q := gradCampanatoCoeff (unitBallVolume E) s l α
  have hQ : 0 ≤ Q := gradCampanatoCoeff_nonneg unitBallVolume_pos.le (Real.sqrt_nonneg _)
  refine ⟨s ^ d / lam * Cd * l ^ (-b) * Q, by
    have := Real.rpow_nonneg hl.le (-b); have := Real.sqrt_nonneg Λ; positivity, ?_⟩
  intro U Ka KG Mf M₀ δ a G f w x₀ hU hell ha hG hfb hw hδ hball hM₀ S ρ hρ hρδ
  have hX : 0 ≤ M₀ ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * M₀ ^ 2 + (KG : ℝ) ^ 2 +
      Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) := by
    have := Real.rpow_nonneg hδ.le (-(2 * (α : ℝ)))
    have := Real.rpow_nonneg hδ.le (2 - 2 * (α : ℝ))
    positivity
  have hρb : 0 ≤ ρ ^ b := Real.rpow_nonneg hρ.le _
  have hC0 : 0 ≤ s ^ d / lam * Cd * l ^ (-b) * Q := by
    have := Real.rpow_nonneg hl.le (-b); have := Real.sqrt_nonneg Λ; positivity
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : ∀ y, ‖∇ w y - ⨍ z in ball x₀ ρ ∩ S, ∇ w z‖ ^ 2 = 0 := fun y ↦ by
      simp [Subsingleton.elim (∇ w y - ⨍ z in ball x₀ ρ ∩ S, ∇ w z) 0]
    simp_rw [this, integral_zero]
    positivity
  have hx₀U : x₀ ∈ U := hball (mem_ball_self hδ)
  -- `lam ≤ Λ`
  have hlamΛ : lam ≤ Λ := by
    obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
    have hξ0 : 0 < ‖ξ‖ ^ 2 := by positivity
    have h1 := (hell x₀ hx₀U).1 ξ
    have h2 : ⟪a x₀ ξ, ξ⟫ ≤ Λ * ‖ξ‖ ^ 2 :=
      (real_inner_le_norm _ _).trans (by
        calc ‖a x₀ ξ‖ * ‖ξ‖ ≤ ‖a x₀‖ * ‖ξ‖ * ‖ξ‖ :=
              mul_le_mul_of_nonneg_right ((a x₀).le_opNorm ξ) (norm_nonneg _)
          _ ≤ Λ * ‖ξ‖ * ‖ξ‖ := by
              gcongr; exact (hell x₀ hx₀U).2
          _ = Λ * ‖ξ‖ ^ 2 := by ring)
    nlinarith
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  have hs : 0 < s := Real.sqrt_pos.2 hΛ
  have hls : l ≤ s := Real.sqrt_le_sqrt hlamΛ
  obtain ⟨M, -, hMn, hMn', hconj, hskew⟩ := exists_sqrt_symPart hlam (hell x₀ hx₀U).1
    (hell x₀ hx₀U).2
  have hraw := transported_decay hα hCd hdec hU ha hG hfb hw hδ hball hM₀ hs hl hMn hMn'
    hconj hskew
  set ρt := ρ / l with hρt
  have hρt0 : 0 < ρt := div_pos hρ hl
  have hρδ' : ρ ≤ l / s * δ := by
    rwa [hsdef, hldef, ← Real.sqrt_div' lam hΛ.le]
  have hρtR : ρt ≤ δ / s := by
    rw [hρt, div_le_div_iff₀ hl hs]
    calc ρ * s ≤ l / s * δ * s := mul_le_mul_of_nonneg_right hρδ' hs.le
      _ = δ * l := by field_simp
  have hψt := hraw ρt ⟨hρt0, hρtR⟩
  rw [measureReal_ball_eq (div_pos hδ hs)] at hψt
  replace hψt := hψt.trans (gradCampanato_raw_bound_le (d := d) (Ka := (Ka : ℝ))
    (KG := (KG : ℝ)) (Mf := Mf) (M₀ := M₀) hs hl hδ hρt0 hCd unitBallVolume_pos.le)
  -- back to the original coordinates
  set adjM := ContinuousLinearMap.adjoint (M : E →L[ℝ] E)
  set adjMi := ContinuousLinearMap.adjoint (M.symm : E →L[ℝ] E)
  have hadjMi : ‖adjMi‖ ≤ 1 / l := by
    rw [show ‖adjMi‖ = ‖(M.symm : E →L[ℝ] E)‖ from LinearIsometryEquiv.norm_map _ _]
    exact hMn'
  have hinv : ∀ v, adjMi (adjM v) = v := fun v ↦ by
    rw [← ContinuousLinearMap.comp_apply, adjoint_symm_comp_adjoint, one_apply_eq_self]
  set T : E → E := fun z ↦ x₀ + M z with hT
  set Ft : E → E := fun z ↦ adjM (∇ w (x₀ + M z)) with hFt
  set ct := ⨍ z in ball 0 ρt, Ft z
  set c := adjMi ct
  -- integrability of `∇w` on `B_δ(x₀)`
  have hgradc : ContinuousOn (∇ w) U := by
    have := hw.1.continuousOn_fderiv_of_isOpen hU le_rfl
    exact (toDual ℝ E).symm.continuous.comp_continuousOn this
  have hgL : MemLp (∇ w) 2 (volume.restrict (ball x₀ δ)) :=
    memLp_restrict_ball_of_bound ((hgradc.mono hball).aestronglyMeasurable measurableSet_ball) hM₀
  have hgc : IntegrableOn (fun y ↦ ‖∇ w y - c‖ ^ 2) (ball x₀ δ) :=
    integrable_norm_sq' (hgL.sub (memLp_const c))
  have hρle : ρ ≤ δ := hρδ'.trans (by
    have : l / s ≤ 1 := (div_le_one hs).2 hls
    nlinarith)
  have hsubδ : ball x₀ ρ ∩ S ⊆ ball x₀ δ := inter_subset_left.trans (ball_subset_ball hρle)
  have hTB : T '' ball 0 ρt ⊆ ball x₀ δ := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_ball, dist_eq_norm, hT]
    simp only [add_sub_cancel_left]
    rw [mem_ball_zero_iff] at hz
    calc ‖M z‖ = ‖(M : E →L[ℝ] E) z‖ := rfl
      _ ≤ s * ‖z‖ := ((M : E →L[ℝ] E).le_opNorm z).trans
          (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))
      _ < s * (δ / s) := mul_lt_mul_of_pos_left (hz.trans_le hρtR) hs
      _ = δ := by field_simp
  have hBT : ball x₀ ρ ⊆ T '' ball 0 ρt := by
    have := ball_subset_image_affine_ball M x₀ (K' := 1 / l) (by positivity)
      (fun y ↦ ((M.symm : E →L[ℝ] E).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right hMn' (norm_nonneg _))) 0 ρ
    rwa [map_zero, add_zero, one_div_mul_eq_div] at this
  -- step 1: the mean minimizes, and monotonicity in the domain
  have hs1 : ∫ y in ball x₀ ρ ∩ S, ‖∇ w y - ⨍ z in ball x₀ ρ ∩ S, ∇ w z‖ ^ 2 ≤
      ∫ y in T '' ball 0 ρt, ‖∇ w y - c‖ ^ 2 := by
    have hfin : volume (ball x₀ ρ ∩ S) ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
    refine (setIntegral_norm_sub_setAverage_sq_le hfin
      (IntegrableOn.mono_set (hgL.integrable one_le_two) hsubδ)
      (IntegrableOn.mono_set (integrable_norm_sq' hgL) hsubδ) c).trans ?_
    exact setIntegral_mono_set (hgc.mono_set hTB) (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (inter_subset_left.trans hBT).eventuallyLE
  -- step 2: change of variables
  have hTinj : Function.Injective T := fun z z' h ↦ M.injective (add_left_cancel h)
  have hdet0 : LinearMap.det (M : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  have hcov := setIntegral_comp_affine M x₀ (fun y ↦ ‖∇ w y - c‖ ^ 2) (T '' ball 0 ρt)
  rw [Set.preimage_image_eq _ hTinj] at hcov
  have hs2 : ∫ y in T '' ball 0 ρt, ‖∇ w y - c‖ ^ 2 =
      |LinearMap.det (M : E →ₗ[ℝ] E)| * ∫ z in ball 0 ρt, ‖∇ w (x₀ + M z) - c‖ ^ 2 := by
    rw [hcov, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hdet0), one_mul]
  -- step 3: compare with `ψ̃`
  have hpt : ∀ z, ∇ w (x₀ + M z) - c = adjMi (Ft z - ct) := fun z ↦ by
    rw [map_sub, hFt]; simp only [hinv]; rfl
  have hFtL : MemLp Ft 2 (volume.restrict (ball 0 ρt)) := by
    refine memLp_restrict_ball_of_bound ?_ (M := s * M₀) fun z hz ↦ ?_
    · have hmaps : MapsTo T (ball 0 ρt) U := fun z hz ↦ hball (hTB ⟨z, hz, rfl⟩)
      exact (adjM.continuous.comp_continuousOn (hgradc.comp
        (continuous_const.add M.continuous).continuousOn hmaps)).aestronglyMeasurable
        measurableSet_ball
    · have hadjM : ‖adjM‖ ≤ s := by
        rw [show ‖adjM‖ = ‖(M : E →L[ℝ] E)‖ from LinearIsometryEquiv.norm_map _ _]
        exact hMn
      exact (adjM.le_opNorm _).trans (mul_le_mul hadjM (hM₀ _ (hTB ⟨z, hz, rfl⟩))
        (norm_nonneg _) hs.le)
  have hs3 : ∫ z in ball 0 ρt, ‖∇ w (x₀ + M z) - c‖ ^ 2 ≤
      (1 / l) ^ 2 * ∫ z in ball 0 ρt, ‖Ft z - ct‖ ^ 2 := by
    rw [← integral_const_mul]
    simp_rw [hpt]
    refine integral_mono (integrable_norm_sq'
      (adjMi.lipschitzWith.comp_memLp (by simp) (hFtL.sub (memLp_const ct))))
      ((integrable_norm_sq' (hFtL.sub (memLp_const ct))).const_mul _) fun z ↦ ?_
    calc ‖adjMi (Ft z - ct)‖ ^ 2 ≤ (‖adjMi‖ * ‖Ft z - ct‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (adjMi.le_opNorm _) 2
      _ ≤ (1 / l * ‖Ft z - ct‖) ^ 2 := by gcongr
      _ = (1 / l) ^ 2 * ‖Ft z - ct‖ ^ 2 := by ring
  have hdet := abs_det_le_pow_of_norm_le hs hMn
  have hψt0 : 0 ≤ ∫ z in ball 0 ρt, ‖Ft z - ct‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _
  have hl2 : l ^ 2 = lam := Real.sq_sqrt hlam.le
  have hρtb : ρt ^ b = ρ ^ b * l ^ (-b) := by
    rw [hρt, Real.div_rpow hρ.le hl.le, Real.rpow_neg hl.le, div_eq_mul_inv]
  calc _ ≤ ∫ y in T '' ball 0 ρt, ‖∇ w y - c‖ ^ 2 := hs1
    _ = |LinearMap.det (M : E →ₗ[ℝ] E)| * ∫ z in ball 0 ρt, ‖∇ w (x₀ + M z) - c‖ ^ 2 := hs2
    _ ≤ s ^ d * ((1 / l) ^ 2 * ∫ z in ball 0 ρt, ‖Ft z - ct‖ ^ 2) := by
        gcongr
    _ ≤ s ^ d * ((1 / l) ^ 2 * (Cd * ρt ^ b * Q *
          (M₀ ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * M₀ ^ 2 + (KG : ℝ) ^ 2 +
            Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ))))) := by
        gcongr
    _ = _ := by
        rw [hρtb, div_pow, one_pow, hl2]
        ring

end BasicElliptic.Div
