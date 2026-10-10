/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Boundary.Decay
public import BasicElliptic.Div.Boundary.InteriorDecay
import BasicElliptic.Normalize.ChangeOfVariables
import BasicElliptic.Campanato.Density

/-!
# Near-boundary patching: Campanato bounds at all points of a half ball

`BasicElliptic.Div.campanato_patch` (GM): for a conormal solution on `D = halfBall ν z R`
and a point `p ∈ D` with `B_δ(p) ⊆ B_R(z)`, every measurable `S ⊆ halfSpace ν` and
`0 < t ≤ (lam/Λ) δ / 4`,

`∫_{B_t(p) ∩ S} ‖∇w - (∇w)_{B_t(p) ∩ S}‖²`
  `≤ C t^{d+2α} ((M₀ + M_G)² δ^{-2α} + K_a² (M₀ + M_G)² + K_G² + M_f² δ^{2-2α})`.

## Proof

Let `h = ⟪p, ν⟫ ≥ 0`, `p̄ = p - h ν` its foot point, `κ = √(lam/Λ) ≤ 1`.

* **Boundary scales `t ≥ κ h`:** `B_t(p) ⊆ B_{t+h}(p̄)`, `t + h ≤ 2t/κ ≤ κ δ/2`; apply the flat
  decay (`campanato_decay_at_flat_point`) at `p̄` on `halfBall ν p̄ (δ/2)` with the set
  `B_t(p) ∩ S`.
* **Interior scales `t < κ h`, `h ≤ κ δ/4`:** `B_h(p) ⊆ B_R(z) ∩ {⟪·, ν⟫ > 0}` where `w` is an
  interior weak solution; apply `gradient_campanato_at_point_osc` at `p` from scale `h`, and bound
  the starting oscillation `∫_{B_h(p)} ‖∇w - c‖²` by the flat decay at `p̄` at scale `2h`
  (`B_h(p) ⊆ B_{2h}(p̄)`), which is `O(h^{d+2α})`.
* **Interior scales, `h > κ δ/4`:** the same from scale `κ δ/4` with the crude starting bound
  `M₀² |B|`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012. (GM)
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace Module
open scoped Gradient Topology NNReal

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Restriction of a conormal solution to a smaller half ball. -/
theorem IsConormalSolOn.restrict_halfBall {ν x y : E} {r s : ℝ} {a : E → E →L[ℝ] E}
    {G : E → E} {f : E → ℝ} {w : E → ℝ} (hν : ‖ν‖ = 1) (h : IsConormalSolOn ν a G f x r w)
    (hs : 0 < s) (hy : -s < ⟪y, ν⟫) (hsub : closedBall y s ⊆ closedBall x r)
    (hsub' : ball y s ⊆ ball x r) : IsConormalSolOn ν a G f y s w :=
  IsWeakSolWithin.restrict h hsub' (inter_subset_inter_left _ hsub)
    (fun _ hz ↦ ⟨ball_subset_closedBall hz.2, hz.1.2⟩) (measurableSet_halfBall ν x r)
    (measurableSet_halfBall ν y s) (uniqueDiffOn_halfBall hν hs hy)

/-- A conormal solution is an interior weak solution on `ball x r ∩ openHalfSpace ν`. -/
theorem IsConormalSolOn.isWeakSolOn {ν x : E} {r : ℝ} {a : E → E →L[ℝ] E}
    {G : E → E} {f : E → ℝ} {w : E → ℝ} (h : IsConormalSolOn ν a G f x r w) :
    IsWeakSolOn a G f (ball x r ∩ openHalfSpace ν) w := by
  set U := ball x r ∩ openHalfSpace ν with hU
  have hUo : IsOpen U := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hUB : U ⊆ halfBall ν x r := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, mem_halfSpace.2 (mem_openHalfSpace.1 hz.2).le⟩
  have h' := IsWeakSolWithin.restrict h inter_subset_left hUB
    (fun _ hz ↦ hz.2) (measurableSet_halfBall ν x r) hUo.measurableSet hUo.uniqueDiffOn
  refine ⟨h'.1, fun φ hφ ↦ ?_⟩
  have key := h'.2 φ hφ
  have hg : ∀ y ∈ U, gradientWithin w U y = ∇ w y := fun y hy ↦ by
    rw [gradientWithin, gradient, fderivWithin_of_isOpen hUo hy]
  rw [setIntegral_congr_fun hUo.measurableSet (g := fun y ↦ ⟪a y (∇ w y), ∇ φ y⟫)
    fun y hy ↦ by simp only [hg y hy]] at key
  exact key


/-- The mean-square oscillation over a measurable set only depends on the values there. -/
theorem setIntegral_norm_sub_setAverage_sq_congr {s : Set E} (hs : MeasurableSet s)
    {F F' : E → E} (h : EqOn F F' s) :
    ∫ y in s, ‖F y - ⨍ z in s, F z‖ ^ 2 = ∫ y in s, ‖F' y - ⨍ z in s, F' z‖ ^ 2 := by
  have ha : ⨍ z in s, F z = ⨍ z in s, F' z :=
    setAverage_congr_fun hs (Eventually.of_forall fun z hz ↦ h hz)
  rw [ha]
  exact setIntegral_congr_fun hs fun y hy ↦ by simp only [h hy]

/-! ### The two decay inputs, as predicates -/

/-- The conclusion of `campanato_decay_at_flat_point` with constant `CF`. -/
private def FlatDecayProp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α : ℝ≥0) (lam Λ CF : ℝ) :
    Prop :=
  ∀ (ν x₀ : E) (Ka KG : ℝ≥0) (Mf M₀ MG δ : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → ⟪x₀, ν⟫ = 0 → 0 < δ →
      IsUniformlyElliptic lam Λ a (halfBall ν x₀ δ) → IsSymmetricOn a (halfBall ν x₀ δ) →
      HolderOnWith Ka α a (halfBall ν x₀ δ) → HolderOnWith KG α G (halfBall ν x₀ δ) →
      ‖G x₀‖ ≤ MG →
      AEStronglyMeasurable f (volume.restrict (halfBall ν x₀ δ)) →
      (∀ y ∈ halfBall ν x₀ δ, |f y| ≤ Mf) → IsConormalSolOn ν a G f x₀ δ w →
      (∀ y ∈ halfBall ν x₀ δ, ‖gradientWithin w (halfBall ν x₀ δ) y‖ ≤ M₀) →
      ∀ (S : Set E), S ⊆ halfSpace ν → ∀ ρ : ℝ, 0 < ρ → ρ ≤ √(lam / Λ) * δ →
        ∫ y in ball x₀ ρ ∩ S, ‖gradientWithin w (halfBall ν x₀ δ) y -
            ⨍ z in ball x₀ ρ ∩ S, gradientWithin w (halfBall ν x₀ δ) z‖ ^ 2 ≤
          CF * ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
            ((M₀ + MG) ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 +
              (KG : ℝ) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)))

/-- The conclusion of `gradient_campanato_at_point_osc` with constant `CI`. -/
private def IntDecayProp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α : ℝ≥0) (lam Λ CI : ℝ) :
    Prop :=
  ∀ (U : Set E) (Ka KG : ℝ≥0) (Mf M₀ δ : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ) (x₀ c : E),
      IsOpen U → IsUniformlyElliptic lam Λ a U → HolderOnWith Ka α a U →
      HolderOnWith KG α G U → (∀ y ∈ U, |f y| ≤ Mf) → IsWeakSolOn a G f U w →
      0 < δ → ball x₀ δ ⊆ U → (∀ y ∈ ball x₀ δ, ‖∇ w y‖ ≤ M₀) →
      ∀ (S : Set E) (ρ : ℝ), 0 < ρ → ρ ≤ √(lam / Λ) * δ →
        ∫ y in ball x₀ ρ ∩ S, ‖∇ w y - ⨍ z in ball x₀ ρ ∩ S, ∇ w z‖ ^ 2 ≤
          CI * ((ρ / δ) ^ ((finrank ℝ E : ℝ) + 2 * α) * (∫ y in ball x₀ δ, ‖∇ w y - c‖ ^ 2) +
            ρ ^ ((finrank ℝ E : ℝ) + 2 * α) *
              ((Ka : ℝ) ^ 2 * M₀ ^ 2 + (KG : ℝ) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ))))

/-! ### The flat and interior steps -/

/-- The flat decay at the foot point `p - ⟪p, ν⟫ ν` of `p`, on `halfBall ν p̄ (δ/2)`, for the
within-gradient on the big half ball. -/
private theorem flat_step {α : ℝ≥0} {lam Λ CF : ℝ} (hflat : FlatDecayProp E α lam Λ CF)
    {ν z : E} {Ka KG : ℝ≥0} {Mf M₀ MG R δ : ℝ} {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hδ : 0 < δ)
    (hell : IsUniformlyElliptic lam Λ a (halfBall ν z R)) (hsym : IsSymmetricOn a (halfBall ν z R))
    (ha : HolderOnWith Ka α a (halfBall ν z R)) (hG : HolderOnWith KG α G (halfBall ν z R))
    (hMG : ∀ y ∈ halfBall ν z R, ‖G y‖ ≤ MG)
    (hfm : AEStronglyMeasurable f (volume.restrict (halfBall ν z R)))
    (hfb : ∀ y ∈ halfBall ν z R, |f y| ≤ Mf) (hw : IsConormalSolOn ν a G f z R w)
    (hM₀ : ∀ y ∈ halfBall ν z R, ‖gradientWithin w (halfBall ν z R) y‖ ≤ M₀)
    {p : E} (hp : p ∈ halfBall ν z R) (hpδ : dist p z + δ ≤ R) (hhδ : ⟪p, ν⟫ ≤ δ / 2)
    (hκ1 : √(lam / Λ) ≤ 1) :
    ∀ S' : Set E, MeasurableSet S' → S' ⊆ halfSpace ν → ∀ ρ' : ℝ, 0 < ρ' →
      ρ' ≤ √(lam / Λ) * (δ / 2) →
      ∫ y in ball (p - ⟪p, ν⟫ • ν) ρ' ∩ S', ‖gradientWithin w (halfBall ν z R) y -
          ⨍ y' in ball (p - ⟪p, ν⟫ • ν) ρ' ∩ S', gradientWithin w (halfBall ν z R) y'‖ ^ 2 ≤
        CF * ρ' ^ ((finrank ℝ E : ℝ) + 2 * α) *
          ((M₀ + MG) ^ 2 * (δ / 2) ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 +
            (KG : ℝ) ^ 2 + Mf ^ 2 * (δ / 2) ^ (2 - 2 * (α : ℝ))) := by
  intro S' hS'm hS' ρ' hρ' hρ'δ
  set D := halfBall ν z R
  set h := ⟪p, ν⟫ with hhdef
  have hh0 : 0 ≤ h := hp.2
  set pb := p - h • ν with hpb
  set δ₁ := δ / 2 with hδ₁
  have hδ₁0 : 0 < δ₁ := by positivity
  have hpbν : ⟪pb, ν⟫ = 0 := by
    rw [hpb, inner_sub_left, real_inner_smul_left, real_inner_self_of_norm_eq_one hν]; ring
  have hdppb : dist p pb = h := by
    rw [hpb, dist_eq_norm, sub_sub_cancel, norm_smul, hν, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hh0]
  have hRsub : closedBall pb δ₁ ⊆ closedBall z R := fun y hy ↦ by
    rw [mem_closedBall] at hy ⊢
    have := dist_triangle4 y pb p z
    rw [dist_comm pb p, hdppb] at this
    linarith
  have hRsub' : ball pb δ₁ ⊆ ball z R := fun y hy ↦ by
    rw [mem_ball] at hy ⊢
    have := dist_triangle4 y pb p z
    rw [dist_comm pb p, hdppb] at this
    linarith
  have hD₁ : halfBall ν pb δ₁ ⊆ D := inter_subset_inter_left _ hRsub
  have hpbx : -δ₁ < ⟪pb, ν⟫ := by rw [hpbν]; linarith
  have hw₁ := hw.restrict_halfBall hν hδ₁0 hpbx hRsub hRsub'
  have hu₁ := uniqueDiffOn_halfBall hν hδ₁0 hpbx
  have hgeq : EqOn (gradientWithin w (halfBall ν pb δ₁)) (gradientWithin w D)
      (halfBall ν pb δ₁) :=
    fun y hy ↦ gradientWithin_eq_of_subset hD₁ (hu₁ y hy)
      (hw.1.differentiableOn one_ne_zero y (hD₁ hy))
  have hpbB : pb ∈ halfBall ν pb δ₁ :=
    ⟨mem_closedBall_self hδ₁0.le, mem_halfSpace.2 hpbν.ge⟩
  have hρ'δ₁ : ρ' ≤ δ₁ := hρ'δ.trans (mul_le_of_le_one_left hδ₁0.le hκ1)
  have hsub : ball pb ρ' ∩ S' ⊆ halfBall ν pb δ₁ := fun y hy ↦
    ⟨ball_subset_closedBall (ball_subset_ball hρ'δ₁ hy.1), hS' hy.2⟩
  have key := hflat ν pb Ka KG Mf M₀ MG δ₁ a G f w hν hpbν hδ₁0 (hell.mono hD₁)
    (fun y hy ↦ hsym y (hD₁ hy)) (ha.mono hD₁) (hG.mono hD₁) (hMG pb (hD₁ hpbB))
    (hfm.mono_measure (Measure.restrict_mono hD₁ le_rfl)) (fun y hy ↦ hfb y (hD₁ hy)) hw₁
    (fun y hy ↦ by rw [hgeq hy]; exact hM₀ y (hD₁ hy)) S' hS' ρ' hρ' hρ'δ
  rwa [setIntegral_norm_sub_setAverage_sq_congr (measurableSet_ball.inter hS'm)
    (hgeq.mono hsub)] at key

/-- The interior decay at `p` from scale `η ≤ ⟪p, ν⟫`, for the within-gradient on the big half
ball. -/
private theorem int_step {α : ℝ≥0} (hα1 : α < 1) {lam Λ CI : ℝ}
    (hint : IntDecayProp E α lam Λ CI)
    {ν z : E} {Ka KG : ℝ≥0} {Mf M₀ R δ : ℝ} {a : E → E →L[ℝ] E} {G : E → E} {f : E → ℝ}
    {w : E → ℝ} (hν : ‖ν‖ = 1) (hell : IsUniformlyElliptic lam Λ a (halfBall ν z R))
    (ha : HolderOnWith Ka α a (halfBall ν z R)) (hG : HolderOnWith KG α G (halfBall ν z R))
    (hfb : ∀ y ∈ halfBall ν z R, |f y| ≤ Mf) (hw : IsConormalSolOn ν a G f z R w)
    (hM₀ : ∀ y ∈ halfBall ν z R, ‖gradientWithin w (halfBall ν z R) y‖ ≤ M₀)
    {p : E} (hpδ : dist p z + δ ≤ R) {η : ℝ} (hη : 0 < η) (hηh : η ≤ ⟪p, ν⟫) (hηδ : η ≤ δ)
    (c : E) {S : Set E} (hSm : MeasurableSet S) {t : ℝ} (ht : 0 < t)
    (htη : t ≤ √(lam / Λ) * η) (hκ1 : √(lam / Λ) ≤ 1) (hCI : 0 ≤ CI) :
    ∫ y in ball p t ∩ S, ‖gradientWithin w (halfBall ν z R) y -
        ⨍ y' in ball p t ∩ S, gradientWithin w (halfBall ν z R) y'‖ ^ 2 ≤
      CI * ((t / η) ^ ((finrank ℝ E : ℝ) + 2 * α) *
          (∫ y in ball p η, ‖gradientWithin w (halfBall ν z R) y - c‖ ^ 2) +
        t ^ ((finrank ℝ E : ℝ) + 2 * α) *
          ((Ka : ℝ) ^ 2 * M₀ ^ 2 + (KG : ℝ) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)))) := by
  set D := halfBall ν z R
  set U := ball z R ∩ openHalfSpace ν with hU
  have hUo : IsOpen U := isOpen_ball.inter (isOpen_openHalfSpace ν)
  have hUD : U ⊆ D := fun y hy ↦
    ⟨ball_subset_closedBall hy.1, mem_halfSpace.2 (mem_openHalfSpace.1 hy.2).le⟩
  have hgU : ∀ y ∈ U, gradientWithin w D y = ∇ w y := fun y hy ↦ gradientWithin_halfBall_eq hy
  have hballU : ball p η ⊆ U := fun y hy ↦ by
    rw [mem_ball] at hy
    refine ⟨?_, ?_⟩
    · rw [mem_ball]; have := dist_triangle y p z; linarith
    · rw [mem_openHalfSpace]
      have h1 : |⟪y - p, ν⟫| ≤ ‖y - p‖ * ‖ν‖ := abs_real_inner_le_norm (y - p) ν
      rw [hν, mul_one] at h1
      have h2 := (abs_le.1 h1).1
      rw [inner_sub_left, ← dist_eq_norm] at h2
      linarith
  have hκη : t ≤ η := htη.trans (mul_le_of_le_one_left hη.le hκ1)
  have hsubU : ball p t ∩ S ⊆ U := inter_subset_left.trans ((ball_subset_ball hκη).trans hballU)
  have key := hint U Ka KG Mf M₀ η a G f w p c hUo (hell.mono hUD) (ha.mono hUD) (hG.mono hUD)
    (fun y hy ↦ hfb y (hUD hy)) hw.isWeakSolOn hη hballU
    (fun y hy ↦ by rw [← hgU y (hballU hy)]; exact hM₀ y (hUD (hballU hy))) S t ht htη
  rw [setIntegral_norm_sub_setAverage_sq_congr (measurableSet_ball.inter hSm)
    (fun y hy ↦ hgU y (hsubU hy)),
    setIntegral_congr_fun measurableSet_ball (g := fun y ↦ ‖∇ w y - c‖ ^ 2)
      (fun y hy ↦ by simp only [hgU y (hballU hy)])]
  refine key.trans ?_
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  have he : η ^ (2 - 2 * (α : ℝ)) ≤ δ ^ (2 - 2 * (α : ℝ)) :=
    Real.rpow_le_rpow hη.le hηδ (by linarith)
  apply mul_le_mul_of_nonneg_left _ hCI
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_left he (sq_nonneg _)


/-! ### The three regimes -/

/-- Boundary scales `t ≥ κ h`. -/
private theorem caseA {F : E → E} {ν p pb : E} {S : Set E} {CF κ δ t h b X : ℝ}
    (hSm : MeasurableSet S) (hS : S ⊆ halfSpace ν)
    (hstep : ∀ S' : Set E, MeasurableSet S' → S' ⊆ halfSpace ν → ∀ ρ' : ℝ, 0 < ρ' →
      ρ' ≤ κ * (δ / 2) →
      ∫ y in ball pb ρ' ∩ S', ‖F y - ⨍ y' in ball pb ρ' ∩ S', F y'‖ ^ 2 ≤ CF * ρ' ^ b * (4 * X))
    (hdppb : dist p pb = h) (hh0 : 0 ≤ h) (hκpos : 0 < κ) (hκ1 : κ ≤ 1) (ht : 0 < t)
    (htκ : t ≤ κ ^ 2 / 4 * δ) (hA : κ * h ≤ t) (hb0 : 0 ≤ b) (hCF : 0 ≤ CF) (hX0 : 0 ≤ X) :
    ∫ y in ball p t ∩ S, ‖F y - ⨍ y' in ball p t ∩ S, F y'‖ ^ 2 ≤
      4 * CF * (2 / κ) ^ b * t ^ b * X := by
  have hht : h ≤ t / κ := by rw [le_div_iff₀ hκpos]; linarith
  have ht1 : t ≤ t / κ := le_div_self ht.le hκpos hκ1
  have htκ' : t / κ ≤ κ * δ / 4 := by
    rw [div_le_iff₀ hκpos]
    calc t ≤ κ ^ 2 / 4 * δ := htκ
      _ = κ * δ / 4 * κ := by ring
  have hρ' : t + h ≤ κ * (δ / 2) := by linarith
  have hball : ball p t ⊆ ball pb (t + h) := fun y hy ↦ by
    rw [mem_ball] at hy ⊢
    have := dist_triangle y p pb
    rw [hdppb] at this; linarith
  have heq : ball pb (t + h) ∩ (ball p t ∩ S) = ball p t ∩ S :=
    inter_eq_right.2 (inter_subset_left.trans hball)
  have key := hstep (ball p t ∩ S) (measurableSet_ball.inter hSm)
    (fun y hy ↦ hS hy.2) (t + h) (by positivity) hρ'
  rw [heq] at key
  refine key.trans ?_
  have h2 : (t + h) ^ b ≤ (2 / κ) ^ b * t ^ b := by
    rw [← Real.mul_rpow (by positivity) ht.le]
    refine Real.rpow_le_rpow (by positivity) ?_ hb0
    calc t + h ≤ t / κ + t / κ := by linarith
      _ = 2 / κ * t := by ring
  calc CF * (t + h) ^ b * (4 * X) ≤ CF * ((2 / κ) ^ b * t ^ b) * (4 * X) := by gcongr
    _ = 4 * CF * (2 / κ) ^ b * t ^ b * X := by ring

/-- Interior scales `t < κ h`, `h ≤ κ δ / 4`: start the interior decay at scale `h`. -/
private theorem caseB1 {F : E → E} {ν p pb : E} {S : Set E} {CF CI κ δ t h b X Y : ℝ}
    (hstep : ∀ S' : Set E, MeasurableSet S' → S' ⊆ halfSpace ν → ∀ ρ' : ℝ, 0 < ρ' →
      ρ' ≤ κ * (δ / 2) →
      ∫ y in ball pb ρ' ∩ S', ‖F y - ⨍ y' in ball pb ρ' ∩ S', F y'‖ ^ 2 ≤ CF * ρ' ^ b * (4 * X))
    (hdppb : dist p pb = h) (hh : 0 < h) (hhδ : h ≤ κ * δ / 4) (hballH : ball p h ⊆ halfSpace ν)
    (hint : ∫ y in ball p t ∩ S, ‖F y - ⨍ y' in ball p t ∩ S, F y'‖ ^ 2 ≤
      CI * ((t / h) ^ b * (∫ y in ball p h, ‖F y - ⨍ y' in ball p h, F y'‖ ^ 2) + t ^ b * Y))
    (hY : Y ≤ X) (ht : 0 < t) (hCI : 0 ≤ CI) :
    ∫ y in ball p t ∩ S, ‖F y - ⨍ y' in ball p t ∩ S, F y'‖ ^ 2 ≤
      CI * (4 * CF * 2 ^ b + 1) * t ^ b * X := by
  have hball : ball p h ⊆ ball pb (2 * h) := fun y hy ↦ by
    rw [mem_ball] at hy ⊢
    have := dist_triangle y p pb
    rw [hdppb] at this; linarith
  have heq : ball pb (2 * h) ∩ ball p h = ball p h := inter_eq_right.2 hball
  have key := hstep (ball p h) measurableSet_ball hballH (2 * h) (by positivity) (by linarith)
  rw [heq] at key
  refine hint.trans ?_
  have htb : 0 ≤ t ^ b := Real.rpow_nonneg ht.le _
  have hth : 0 ≤ (t / h) ^ b := Real.rpow_nonneg (by positivity) _
  have e : (t / h) ^ b * (2 * h) ^ b = 2 ^ b * t ^ b := by
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by norm_num) ht.le]
    congr 1; field_simp
  calc CI * ((t / h) ^ b * (∫ y in ball p h, ‖F y - ⨍ y' in ball p h, F y'‖ ^ 2) + t ^ b * Y)
      ≤ CI * ((t / h) ^ b * (CF * (2 * h) ^ b * (4 * X)) + t ^ b * X) := by gcongr
    _ = CI * (4 * CF * ((t / h) ^ b * (2 * h) ^ b) * X + t ^ b * X) := by ring
    _ = CI * (4 * CF * 2 ^ b + 1) * t ^ b * X := by rw [e]; ring

/-- Interior scales far from the flat part: start at scale `η` with the crude bound. -/
private theorem caseB2 {F : E → E} {p : E} {S : Set E} {CI t η b Q X Y : ℝ}
    (hint : ∫ y in ball p t ∩ S, ‖F y - ⨍ y' in ball p t ∩ S, F y'‖ ^ 2 ≤
      CI * ((t / η) ^ b * (∫ y in ball p η, ‖F y - 0‖ ^ 2) + t ^ b * Y))
    (hbase : (t / η) ^ b * (∫ y in ball p η, ‖F y - 0‖ ^ 2) ≤ t ^ b * (Q * X))
    (hY : Y ≤ X) (ht : 0 < t) (hCI : 0 ≤ CI) :
    ∫ y in ball p t ∩ S, ‖F y - ⨍ y' in ball p t ∩ S, F y'‖ ^ 2 ≤
      CI * (Q + 1) * t ^ b * X := by
  have htb : 0 ≤ t ^ b := Real.rpow_nonneg ht.le _
  refine hint.trans ?_
  calc CI * ((t / η) ^ b * (∫ y in ball p η, ‖F y - 0‖ ^ 2) + t ^ b * Y)
      ≤ CI * (t ^ b * (Q * X) + t ^ b * X) := by gcongr
    _ = CI * (Q + 1) * t ^ b * X := by ring


variable (E) in
/-- **Campanato bounds at all points of a half ball** (GM). See the module
docstring. The constant depends only on `E`, `α`, `lam`, `Λ`. -/
theorem campanato_patch {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Λ : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν z : E) (Ka KG : ℝ≥0) (Mf M₀ MG R δ : ℝ) (a : E → E →L[ℝ] E)
      (G : E → E) (f : E → ℝ) (w : E → ℝ),
      ‖ν‖ = 1 → 0 < δ →
      IsUniformlyElliptic lam Λ a (halfBall ν z R) → IsSymmetricOn a (halfBall ν z R) →
      HolderOnWith Ka α a (halfBall ν z R) → HolderOnWith KG α G (halfBall ν z R) →
      (∀ y ∈ halfBall ν z R, ‖G y‖ ≤ MG) →
      AEStronglyMeasurable f (volume.restrict (halfBall ν z R)) →
      (∀ y ∈ halfBall ν z R, |f y| ≤ Mf) → IsConormalSolOn ν a G f z R w →
      (∀ y ∈ halfBall ν z R, ‖gradientWithin w (halfBall ν z R) y‖ ≤ M₀) →
      ∀ p ∈ halfBall ν z R, dist p z + δ ≤ R →
      ∀ (S : Set E), MeasurableSet S → S ⊆ halfSpace ν →
      ∀ t : ℝ, 0 < t → t ≤ lam / Λ / 4 * δ →
        ∫ y in ball p t ∩ S, ‖gradientWithin w (halfBall ν z R) y -
            ⨍ y' in ball p t ∩ S, gradientWithin w (halfBall ν z R) y'‖ ^ 2 ≤
          C * t ^ ((finrank ℝ E : ℝ) + 2 * α) *
            ((M₀ + MG) ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 +
              (KG : ℝ) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ))) := by
  obtain ⟨CF, hCF, hflat⟩ := campanato_decay_at_flat_point E hα hα1 hlam
  obtain ⟨CI, hCI, hint⟩ := gradient_campanato_at_point_osc E hα hα1 hlam
  set κ := √(lam / Λ) with hκ
  set d := finrank ℝ E
  set b : ℝ := (d : ℝ) + 2 * α with hb
  set vB := unitBallVolume E
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hvB : 0 ≤ vB := unitBallVolume_pos.le
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  have hb0 : 0 ≤ b := by positivity
  have e2κ : 0 ≤ (2 / κ) ^ b := Real.rpow_nonneg (by positivity) _
  have eκ4 : 0 ≤ (κ / 4) ^ (-(2 * (α : ℝ))) := Real.rpow_nonneg (by positivity) _
  have e2b : 0 ≤ (2 : ℝ) ^ b := Real.rpow_nonneg (by norm_num) _
  set C₁ := 4 * CF * (2 / κ) ^ b
  set C₂ := CI * (4 * CF * 2 ^ b + 1)
  set C₃ := CI * (vB * (κ / 4) ^ (-(2 * (α : ℝ))) + 1)
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  have hC₃ : 0 ≤ C₃ := by positivity
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro ν z Ka KG Mf M₀ MG R δ a G f w hν hδ hell hsym ha hG hMG hfm hfb hw hM₀ p hp hpδ S hSm
    hS t ht htδ
  set gW := gradientWithin w (halfBall ν z R) with hgW
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have : Nontrivial E := ⟨⟨ν, 0, hν0⟩⟩
  have hlamΛ : lam ≤ Λ := by
    obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
    have hξ0 : 0 < ‖ξ‖ ^ 2 := by positivity
    have h1 := (hell p hp).1 ξ
    have h2 : ⟪a p ξ, ξ⟫ ≤ Λ * ‖ξ‖ ^ 2 :=
      (real_inner_le_norm _ _).trans (by
        calc ‖a p ξ‖ * ‖ξ‖ ≤ ‖a p‖ * ‖ξ‖ * ‖ξ‖ :=
              mul_le_mul_of_nonneg_right ((a p).le_opNorm ξ) (norm_nonneg _)
          _ ≤ Λ * ‖ξ‖ * ‖ξ‖ := by
              gcongr; exact (hell p hp).2
          _ = Λ * ‖ξ‖ ^ 2 := by ring)
    nlinarith
  have hΛ : 0 < Λ := hlam.trans_le hlamΛ
  have hκsq : κ ^ 2 = lam / Λ := Real.sq_sqrt (by positivity)
  have hκpos : 0 < κ := Real.sqrt_pos.2 (by positivity)
  have hκ1 : κ ≤ 1 := by
    rw [hκ, Real.sqrt_le_one]; exact (div_le_one hΛ).2 hlamΛ
  have htκ : t ≤ κ ^ 2 / 4 * δ := by rw [hκsq]; linarith
  have hκδ : κ * δ ≤ δ := mul_le_of_le_one_left hδ.le hκ1
  have htκδ : t ≤ κ * (κ * δ / 4) := by
    calc t ≤ κ ^ 2 / 4 * δ := htκ
      _ = κ * (κ * δ / 4) := by ring
  set h := ⟪p, ν⟫ with hhdef
  have hh0 : 0 ≤ h := hp.2
  set pb := p - h • ν with hpb
  have hdppb : dist p pb = h := by
    rw [hpb, dist_eq_norm, sub_sub_cancel, norm_smul, hν, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hh0]
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ p hp)
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG p hp)
  set X := (M₀ + MG) ^ 2 * δ ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 +
    (KG : ℝ) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) with hX
  have hdα : 0 ≤ δ ^ (-(2 * (α : ℝ))) := Real.rpow_nonneg hδ.le _
  have hdα' : 0 ≤ δ ^ (2 - 2 * (α : ℝ)) := Real.rpow_nonneg hδ.le _
  have hX0 : 0 ≤ X := by positivity
  have hX1 : (M₀ + MG) ^ 2 * (δ / 2) ^ (-(2 * (α : ℝ))) + (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 +
      (KG : ℝ) ^ 2 + Mf ^ 2 * (δ / 2) ^ (2 - 2 * (α : ℝ)) ≤ 4 * X := by
    have e1 : (δ / 2) ^ (-(2 * (α : ℝ))) ≤ 4 * δ ^ (-(2 * (α : ℝ))) := by
      rw [Real.div_rpow hδ.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        neg_neg, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ hdα
      calc (2 : ℝ) ^ (2 * (α : ℝ)) ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have e2 : (δ / 2) ^ (2 - 2 * (α : ℝ)) ≤ δ ^ (2 - 2 * (α : ℝ)) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have i1 := mul_le_mul_of_nonneg_left e1 (sq_nonneg (M₀ + MG))
    have i2 := mul_le_mul_of_nonneg_left e2 (sq_nonneg Mf)
    have i3 : 0 ≤ (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 + (KG : ℝ) ^ 2 := by positivity
    have i4 : 0 ≤ Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) := by positivity
    rw [hX]; linarith
  have hstep : h ≤ δ / 2 → ∀ S' : Set E, MeasurableSet S' → S' ⊆ halfSpace ν →
      ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ κ * (δ / 2) →
      ∫ y in ball pb ρ' ∩ S', ‖gW y - ⨍ y' in ball pb ρ' ∩ S', gW y'‖ ^ 2 ≤
        CF * ρ' ^ b * (4 * X) := fun hhδ S' hS'm hS' ρ' hρ' hρ'δ ↦
    (flat_step hflat hν hδ hell hsym ha hG hMG hfm hfb hw hM₀ hp hpδ hhδ hκ1 S' hS'm hS' ρ'
      hρ' hρ'δ).trans (mul_le_mul_of_nonneg_left hX1 (mul_nonneg hCF
        (Real.rpow_nonneg hρ'.le _)))
  have htb : 0 ≤ t ^ b := Real.rpow_nonneg ht.le _
  have hfinal : ∀ C', C' ≤ C₁ + C₂ + C₃ → (C' * t ^ b * X ≤ (C₁ + C₂ + C₃) * t ^ b * X) :=
    fun C' hC' ↦ mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' htb) hX0
  by_cases hA : κ * h ≤ t
  · have hhδ : h ≤ δ / 2 := by
      have := le_of_mul_le_mul_left (hA.trans htκδ) hκpos
      linarith
    refine (caseA hSm hS (hstep hhδ) hdppb hh0 hκpos hκ1 ht htκ hA hb0 hCF hX0).trans
      (hfinal _ (by linarith))
  push Not at hA
  have hhpos : 0 < h := by
    by_contra hh; push Not at hh
    have : κ * h ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ0 hh
    linarith
  have hY : ∀ η, 0 < η → η ≤ δ →
      (Ka : ℝ) ^ 2 * M₀ ^ 2 + (KG : ℝ) ^ 2 + Mf ^ 2 * δ ^ (2 - 2 * (α : ℝ)) ≤ X := by
    intro η _ _
    have hk : (Ka : ℝ) ^ 2 * M₀ ^ 2 ≤ (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM₀0 (by linarith) 2) (sq_nonneg _)
    have := mul_nonneg (sq_nonneg (M₀ + MG)) hdα
    rw [hX]; linarith
  by_cases hB : h ≤ κ * δ / 4
  · -- interior scales near the flat part
    have hhδ : h ≤ δ / 2 := by linarith
    have hballH : ball p h ⊆ halfSpace ν := fun y hy ↦ by
      rw [mem_ball] at hy
      rw [mem_halfSpace]
      have h1 : |⟪y - p, ν⟫| ≤ ‖y - p‖ * ‖ν‖ := abs_real_inner_le_norm (y - p) ν
      rw [hν, mul_one] at h1
      have h2 := (abs_le.1 h1).1
      rw [inner_sub_left, ← dist_eq_norm] at h2
      linarith
    have hi := int_step hα1 hint hν hell ha hG hfb hw hM₀ hpδ hhpos le_rfl (by linarith)
      (⨍ y' in ball p h, gW y') hSm ht hA.le hκ1 hCI
    refine (caseB1 (hstep hhδ) hdppb hhpos hB hballH hi (hY h hhpos (by linarith)) ht hCI).trans
      (hfinal _ (by linarith))
  · -- interior scales away from the flat part
    push Not at hB
    set η := κ * δ / 4 with hη
    have hη0 : 0 < η := by positivity
    have htη : t ≤ κ * η := htκδ
    have hηδ : η ≤ δ := by rw [hη]; linarith
    have hi := int_step hα1 hint hν hell ha hG hfb hw hM₀ hpδ hη0 hB.le hηδ
      0 hSm ht htη hκ1 hCI
    have hgc : ∀ y ∈ ball p η, ‖gW y - 0‖ ^ 2 ≤ M₀ ^ 2 := fun y hy ↦ by
      rw [sub_zero]
      have hyB : y ∈ halfBall ν z R := by
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall]; rw [mem_ball] at hy
          have := dist_triangle y p z
          linarith
        · rw [mem_halfSpace]; rw [mem_ball] at hy
          have h1 : |⟪y - p, ν⟫| ≤ ‖y - p‖ * ‖ν‖ := abs_real_inner_le_norm (y - p) ν
          rw [hν, mul_one] at h1
          have h2 := (abs_le.1 h1).1
          rw [inner_sub_left, ← dist_eq_norm] at h2
          linarith
      exact pow_le_pow_left₀ (norm_nonneg _) (hM₀ y hyB) 2
    have hbase0 : ∫ y in ball p η, ‖gW y - 0‖ ^ 2 ≤ M₀ ^ 2 * (η ^ d * vB) := by
      rw [← measureReal_ball_eq hη0 (x := p)]
      refine (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const
        measure_ball_lt_top fun y hy ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hgc y hy
    have hbase : (t / η) ^ b * (∫ y in ball p η, ‖gW y - 0‖ ^ 2) ≤
        t ^ b * ((vB * (κ / 4) ^ (-(2 * (α : ℝ)))) * X) := by
      have e1 : (t / η) ^ b * η ^ d = t ^ b * η ^ (-(2 * (α : ℝ))) := by
        rw [Real.div_rpow ht.le hη0.le, ← Real.rpow_natCast, div_mul_eq_mul_div, mul_div_assoc,
          ← Real.rpow_sub hη0, hb]
        congr 2; ring
      have e2 : η ^ (-(2 * (α : ℝ))) = (κ / 4) ^ (-(2 * (α : ℝ))) * δ ^ (-(2 * (α : ℝ))) := by
        rw [hη, show κ * δ / 4 = κ / 4 * δ by ring, Real.mul_rpow (by positivity) hδ.le]
      have hM : M₀ ^ 2 * δ ^ (-(2 * (α : ℝ))) ≤ X := by
        have : M₀ ^ 2 ≤ (M₀ + MG) ^ 2 := pow_le_pow_left₀ hM₀0 (by linarith) 2
        have := mul_le_mul_of_nonneg_right this hdα
        have : 0 ≤ (Ka : ℝ) ^ 2 * (M₀ + MG) ^ 2 + (KG : ℝ) ^ 2 + Mf ^ 2 *
          δ ^ (2 - 2 * (α : ℝ)) := by positivity
        rw [hX]; linarith
      calc (t / η) ^ b * (∫ y in ball p η, ‖gW y - 0‖ ^ 2)
          ≤ (t / η) ^ b * (M₀ ^ 2 * (η ^ d * vB)) :=
            mul_le_mul_of_nonneg_left hbase0 (Real.rpow_nonneg (by positivity) _)
        _ = t ^ b * ((κ / 4) ^ (-(2 * (α : ℝ))) * vB * (M₀ ^ 2 * δ ^ (-(2 * (α : ℝ))))) := by
            rw [show (t / η) ^ b * (M₀ ^ 2 * (η ^ d * vB)) = ((t / η) ^ b * η ^ d) * M₀ ^ 2 * vB
              by ring, e1, e2]; ring
        _ ≤ t ^ b * ((κ / 4) ^ (-(2 * (α : ℝ))) * vB * X) := by gcongr
        _ = t ^ b * ((vB * (κ / 4) ^ (-(2 * (α : ℝ)))) * X) := by ring
    refine (caseB2 hi hbase (hY η hη0 hηδ) ht hCI).trans (hfinal _ (by linarith))

end BasicElliptic.Div
