/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Div.Projection.GradientField
public import BasicElliptic.Harmonic.WeylAE
import BasicElliptic.Div.Projection.TestPoincare
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Harmonic replacement for gradient fields

Let `B = B_R(x₀)`, `H = L²(B; E)`, `X ⊆ H` the closure of `{∇φ : φ ∈ C_c^∞(B)}` and `P` the
orthogonal projection onto `X`. For a weakly curl-free `F ∈ H` put `V := F - P F`.

* `BasicElliptic.Div.weaklyHarmonic_of_mem_curlFree_of_mem_orthogonal`: a weakly curl-free,
  weakly divergence-free `V ∈ L²(U; E)` has weakly harmonic components.
* `BasicElliptic.Div.exists_harmonic_ae_eq_of_mem_curlFree_of_mem_orthogonal`: hence (a.e. Weyl
  lemma) `V` agrees a.e. on `U` with a harmonic field.
* `BasicElliptic.Div.exists_harmonic_replacement`: the one-step energy comparison
  `‖F - V‖ ≤ ‖(I - ã)F‖ + ‖G - c‖ + 2R |B|^{1/2} M_f`, `‖V‖ ≤ ‖F‖` (norms in `L²(B)`), for a
  harmonic `V`, assuming only the weak identity `∫⟪ãF, ∇φ⟫ = ∫⟪G, ∇φ⟫ + ∫ f φ`.

## Mathematics

**(i) Weak curl-freeness passes to `L²` limits.** `curlFree U` is the orthogonal complement of the
fixed `L²` fields `(∂_w ψ) u - (∂_u ψ) w`, hence closed; it contains the test gradients
(`∫ ∂_u φ ∂_w ψ = ∫ ∂_w φ ∂_u ψ`, integration by parts twice and symmetry of `D²ψ`), hence `X`
(`gradClosure_le_curlFree`). So `V = F - P F` is curl-free when `F` is; and `V ⊥ X`, i.e. `V` is
weakly divergence-free.

**(ii) Curl-free and divergence-free give harmonic components.** Let `(b_j)` be an orthonormal
basis, `e ∈ E` and `ψ ∈ C_c^∞(U)`. Then `Δψ = Σ_j ∂_j ∂_j ψ`, and curl-freeness with the test
function `∂_j ψ` and the pair `(u, w) = (e, b_j)` gives
`∫ ⟪V, e⟫ ∂_j(∂_j ψ) = ∫ ⟪V, b_j⟫ ∂_e(∂_j ψ) = ∫ ⟪V, b_j⟫ ∂_j(∂_e ψ)` (symmetry of `D²ψ`).
Summing over `j`, `Σ_j ⟪V, b_j⟫ ∂_j χ = Dχ(V) = ⟪V, ∇χ⟫` with `χ = ∂_e ψ ∈ C_c^∞(U)`, so
`∫ ⟪V, e⟫ Δψ = ∫ ⟪V, ∇(∂_e ψ)⟫ = 0` by divergence-freeness. The a.e. Weyl lemma
(`exists_harmonic_ae_eq_of_weaklyHarmonic_field`) then gives a harmonic representative.

**(iii) Energy.** Since `V ⊥ X ∋ P F`, `‖P F‖² = ⟪F, P F⟫`. For `t = ∇φ`, the weak identity and
`∫ ⟪c, ∇φ⟫ = 0` give
`⟪F, ∇φ⟫ = ⟪F - ãF, ∇φ⟫ + ⟪G - c, ∇φ⟫ + ∫ f φ`,
and `|∫_B f φ| ≤ M_f |B|^{1/2} ‖φ‖_{L²} ≤ 2R |B|^{1/2} M_f ‖∇φ‖_{L²}` by Cauchy–Schwarz and the
Poincaré inequality for test functions (`abs_setIntegral_mul_le`). So `|⟪F, t⟫| ≤ K ‖t‖` on the
test gradients with `K = ‖F - ãF‖ + ‖G - c‖ + 2R|B|^{1/2} M_f`; this passes to `X` by continuity,
and with `t = P F` gives `‖F - V‖ = ‖P F‖ ≤ K` (`norm_starProjection_le_of_forall_inner_le`).
Finally `‖V‖ ≤ ‖F‖` by Pythagoras. No symmetry or ellipticity of `ã` is used, and no regularity
of `ã`, `G` beyond measurability: at the use sites `‖ã(y) - I‖ ≤ K‖y - x₀‖^α` and `c = G(x₀)`, so
only pointwise-at-`x₀` Hölder data enter.
-/

open MeasureTheory Metric Set Filter RealInnerProductSpace InnerProductSpace
open scoped Gradient ContDiff Topology Laplacian

public section

namespace BasicElliptic.Div

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- `Δψ = Σ_j ∂_{b_j} ∂_{b_j} ψ` for smooth `ψ` and an orthonormal basis `b`. -/
private theorem laplacian_eq_sum_fderiv_fderiv' {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : E) :
    Δ ψ x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ ψ y (b i)) x (b i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by simp)).differentiable (by simp) x
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

variable {U : Set E}

/-- **Curl-free and divergence-free fields have weakly harmonic components.** If `V ∈ L²(U; E)`
is weakly curl-free and orthogonal to the test gradients, then `∫ ⟪V, e⟫ Δψ = 0` for every
`e ∈ E` and `ψ ∈ C_c^∞(U)`. See the module docstring, (ii), for the derivation. -/
theorem weaklyHarmonic_of_mem_curlFree_of_mem_orthogonal {V : L2Field U}
    (hcurl : V ∈ curlFree U) (hdiv : V ∈ (gradClosure U)ᗮ) (e : E) {ψ : E → ℝ}
    (hψ : IsSmoothTestFn U ψ) : ∫ y, ⟪(V : E → E) y, e⟫ * Δ ψ y = 0 := by
  set b := stdOrthonormalBasis ℝ E
  have hc := isWeakCurlFree_of_mem_curlFree hcurl
  have hd := isWeakDivFree_of_mem_orthogonal hdiv
  have hΔ := laplacian_eq_sum_fderiv_fderiv' b hψ.1
  -- the integrand vanishes off `U`
  have hoff : ∀ y ∉ U, ⟪(V : E → E) y, e⟫ * Δ ψ y = 0 := by
    intro y hy
    rw [hΔ y, Finset.sum_eq_zero, mul_zero]
    intro i _
    have : y ∉ tsupport (fun z ↦ fderiv ℝ ψ z (b i)) :=
      fun h ↦ hy ((hψ.fderiv_apply (b i)).2.2 h)
    rw [fderiv_of_notMem_tsupport ℝ this, zero_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
  simp_rw [hΔ, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ integrable_inner_mul V e
    ((hψ.fderiv_apply (b i)).fderiv_apply (b i))]
  -- curl-freeness with the test function `∂_{b_i} ψ`
  have hstep : ∀ i, ∫ y in U, ⟪(V : E → E) y, e⟫ *
      fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b i)) y (b i) =
      ∫ y in U, ⟪(V : E → E) y, b i⟫ * fderiv ℝ (fun z ↦ fderiv ℝ ψ z e) y (b i) := by
    intro i
    rw [hc _ (hψ.fderiv_apply (b i)) e (b i)]
    simp_rw [fderiv_fderiv_apply_comm hψ.1 _ e (b i)]
  simp_rw [hstep]
  set χ : E → ℝ := fun z ↦ fderiv ℝ ψ z e
  have hχ : IsSmoothTestFn U χ := hψ.fderiv_apply e
  rw [← integral_finsetSum _ fun i _ ↦ integrable_inner_mul V (b i) (hχ.fderiv_apply (b i))]
  have hsum : ∀ y, ∑ i, ⟪(V : E → E) y, b i⟫ * fderiv ℝ χ y (b i) =
      ⟪(V : E → E) y, ∇ χ y⟫ := by
    intro y
    rw [real_inner_comm, inner_gradient_left]
    conv_rhs => rw [← b.sum_repr' ((V : E → E) y)]
    simp [map_sum, map_smul, real_inner_comm, mul_comm]
  simp_rw [hsum]
  exact hd χ hχ

/-- **Harmonic representative.** A weakly curl-free, weakly divergence-free `V ∈ L²(U; E)` on an
open set `U` agrees a.e. on `U` with a harmonic field. -/
theorem exists_harmonic_ae_eq_of_mem_curlFree_of_mem_orthogonal (hU : IsOpen U)
    {V : L2Field U} (hcurl : V ∈ curlFree U) (hdiv : V ∈ (gradClosure U)ᗮ) :
    ∃ H : E → E, HarmonicOnNhd H U ∧ (∀ e : E, HarmonicOnNhd (fun y ↦ ⟪H y, e⟫) U) ∧
      (V : E → E) =ᵐ[volume.restrict U] H := by
  have hloc : LocallyIntegrableOn (V : E → E) U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp V).locallyIntegrable (by norm_num))
  exact exists_harmonic_ae_eq_of_weaklyHarmonic_field hU hloc fun e ψ h1 h2 h3 ↦
    weaklyHarmonic_of_mem_curlFree_of_mem_orthogonal hcurl hdiv e ⟨h1, h2, h3⟩

/-- **Harmonic replacement (one-step energy comparison.** Let `B = B_R(x₀)`, let
`F ∈ L²(B; E)` be weakly curl-free, and suppose
`∫_B ⟪ã F, ∇φ⟫ = ∫_B ⟪G, ∇φ⟫ + ∫_B f φ` for all `φ ∈ C_c^∞(B)`,
with `ã` measurable and bounded, `G ∈ L²(B)` and `|f| ≤ M_f` on `B`. Then for every constant
vector `c` there is a field `V ∈ L²(B)` with harmonic components on `B` and
`‖F - V‖_{L²(B)} ≤ ‖F - ãF‖_{L²(B)} + ‖G - c‖_{L²(B)} + 2R |B|^{1/2} M_f`,
`‖V‖_{L²(B)} ≤ ‖F‖_{L²(B)}`.
`V` is (a representative of) `F - P F`, `P` the projection onto the closure of the test
gradients. No symmetry or ellipticity of `ã` is assumed. See the module docstring, (iii). -/
theorem exists_harmonic_replacement {x₀ : E} {R : ℝ} (hR : 0 < R) {F G : E → E} {f : E → ℝ}
    {ã : E → E →L[ℝ] E} {Λ : ℝ} (c : E) (hF : MemLp F 2 (volume.restrict (ball x₀ R)))
    (hcurl : IsWeakCurlFree F (ball x₀ R))
    (hã : AEStronglyMeasurable ã (volume.restrict (ball x₀ R)))
    (hãb : ∀ y ∈ ball x₀ R, ‖ã y‖ ≤ Λ)
    (hG : MemLp G 2 (volume.restrict (ball x₀ R))) {Mf : ℝ} (hf : ∀ y ∈ ball x₀ R, |f y| ≤ Mf)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x₀ R →
      ∫ y in ball x₀ R, ⟪ã y (F y), ∇ φ y⟫ =
        (∫ y in ball x₀ R, ⟪G y, ∇ φ y⟫) + ∫ y in ball x₀ R, f y * φ y) :
    ∃ V : E → E, (∀ e, HarmonicOnNhd (fun y ↦ ⟪V y, e⟫) (ball x₀ R)) ∧
      MemLp V 2 (volume.restrict (ball x₀ R)) ∧
      √(∫ y in ball x₀ R, ‖F y - V y‖ ^ 2) ≤
        √(∫ y in ball x₀ R, ‖F y - ã y (F y)‖ ^ 2) + √(∫ y in ball x₀ R, ‖G y - c‖ ^ 2) +
          2 * R * √(volume.real (ball x₀ R)) * Mf ∧
      ∫ y in ball x₀ R, ‖V y‖ ^ 2 ≤ ∫ y in ball x₀ R, ‖F y‖ ^ 2 := by
  set B := ball x₀ R
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hf x₀ (mem_ball_self hR))
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- in dimension zero every field vanishes
    refine ⟨F, fun e y _ ↦ ?_, hF, ?_, le_rfl⟩
    · have : (fun y ↦ ⟪F y, e⟫) = fun _ ↦ (0 : ℝ) := by
        ext y; simp [Subsingleton.elim e 0]
      rw [this]
      exact harmonicAt_const _
    · simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, integral_zero, Real.sqrt_zero]
      positivity
  -- the fields in `L²(B)`
  have haF_meas : AEStronglyMeasurable (fun y ↦ ã y (F y)) (volume.restrict B) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hã.prodMk hF.aestronglyMeasurable)
  have haF : MemLp (fun y ↦ ã y (F y)) 2 (volume.restrict B) := by
    refine hF.of_le_mul (c := Λ) haF_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact (ã y).le_opNorm (F y) |>.trans (mul_le_mul_of_nonneg_right (hãb y hy) (norm_nonneg _))
  have hD : MemLp (fun y ↦ F y - ã y (F y)) 2 (volume.restrict B) := hF.sub haF
  have hGc : MemLp (fun y ↦ G y - c) 2 (volume.restrict B) := hG.sub (memLp_const c)
  set Fl : L2Field B := hF.toLp F
  set K : ℝ := ‖hD.toLp _‖ + ‖hGc.toLp _‖ + 2 * R * √(volume.real B) * Mf
  have hK : 0 ≤ K := by positivity
  -- the bound on test gradients
  have hbound : ∀ t ∈ testGradients B, |⟪Fl, t⟫| ≤ K * ‖t‖ := by
    rintro t ⟨φ, hφ, ht⟩
    have htφ : t = hφ.memLp_gradient.toLp (∇ φ) :=
      Lp.ext (ht.trans hφ.memLp_gradient.coeFn_toLp.symm)
    have hnorm : ‖t‖ = √(∫ y in B, ‖∇ φ y‖ ^ 2) := by
      rw [htφ, norm_toLp_eq_sqrt_integral]
    have hint : ∀ {g : E → E}, MemLp g 2 (volume.restrict B) →
        Integrable (fun y ↦ ⟪g y, ∇ φ y⟫) (volume.restrict B) :=
      fun {g} hg ↦ (L2.integrable_inner (hg.toLp g) (hφ.memLp_gradient.toLp _)).congr
        (by filter_upwards [hg.coeFn_toLp, hφ.memLp_gradient.coeFn_toLp] with y h1 h2
            rw [h1, h2])
    have hsplit : ⟪Fl, t⟫ = ⟪hD.toLp _, t⟫ + ⟪hGc.toLp _, t⟫ + ∫ y in B, f y * φ y := by
      rw [htφ, inner_toLp_toLp, inner_toLp_toLp, inner_toLp_toLp]
      have h1 : ∫ y in B, ⟪F y, ∇ φ y⟫ =
          (∫ y in B, ⟪F y - ã y (F y), ∇ φ y⟫) + ∫ y in B, ⟪ã y (F y), ∇ φ y⟫ := by
        rw [← integral_add (hint hD) (hint haF)]
        simp_rw [inner_sub_left, sub_add_cancel]
      have h2 : ∫ y in B, ⟪G y, ∇ φ y⟫ = ∫ y in B, ⟪G y - c, ∇ φ y⟫ := by
        have h0 := setIntegral_inner_gradient_eq_zero hφ c
        have hc : Integrable (fun y ↦ ⟪c, ∇ φ y⟫) (volume.restrict B) := hint (memLp_const c)
        simp_rw [inner_sub_left]
        rw [integral_sub (hint hG) hc, h0, sub_zero]
      rw [h1, hweak φ hφ.1 hφ.2.1 hφ.2.2, h2, add_assoc]
    have hfφ := abs_setIntegral_mul_le hf hφ
    rw [hsplit, ← hnorm] at *
    calc |⟪hD.toLp _, t⟫ + ⟪hGc.toLp _, t⟫ + ∫ y in B, f y * φ y|
        ≤ |⟪hD.toLp _, t⟫| + |⟪hGc.toLp _, t⟫| + |∫ y in B, f y * φ y| :=
          abs_add_three _ _ _
      _ ≤ ‖hD.toLp _‖ * ‖t‖ + ‖hGc.toLp _‖ * ‖t‖ + 2 * R * √(volume.real B) * Mf * ‖t‖ := by
          gcongr
          · exact abs_real_inner_le_norm _ _
          · exact abs_real_inner_le_norm _ _
      _ = K * ‖t‖ := by ring
  -- projection and harmonic representative
  set P := (gradClosure B).starProjection
  have hP : ‖P Fl‖ ≤ K := norm_starProjection_le_of_forall_inner_le _ Fl hK hbound
  set Vl : L2Field B := Fl - P Fl
  have hVdiv : Vl ∈ (gradClosure B)ᗮ := Submodule.sub_starProjection_mem_orthogonal Fl
  have hVcurl : Vl ∈ curlFree B :=
    (curlFree B).sub_mem (IsWeakCurlFree.toLp_mem hF hcurl)
      (gradClosure_le_curlFree (Submodule.starProjection_apply_mem _ Fl))
  obtain ⟨H, -, hH, hVH⟩ :=
    exists_harmonic_ae_eq_of_mem_curlFree_of_mem_orthogonal isOpen_ball hVcurl hVdiv
  refine ⟨H, hH, (Lp.memLp Vl).ae_eq hVH, ?_, ?_⟩
  · have hae : ∀ᵐ y ∂(volume.restrict B), ‖F y - H y‖ ^ 2 = ‖(P Fl : E → E) y‖ ^ 2 := by
      filter_upwards [hVH, Lp.coeFn_sub Fl (P Fl), hF.coeFn_toLp] with y h1 h2 h3
      rw [← h1, h2, Pi.sub_apply, h3, sub_sub_cancel]
    rw [integral_congr_ae hae, ← norm_eq_sqrt_integral, ← norm_toLp_eq_sqrt_integral hD,
      ← norm_toLp_eq_sqrt_integral hGc]
    exact hP
  · have h1 : ∫ y in B, ‖H y‖ ^ 2 = ‖Vl‖ ^ 2 := by
      rw [norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [hVH] with y h
      rw [h]
    have h2 : ∫ y in B, ‖F y‖ ^ 2 = ‖Fl‖ ^ 2 := by
      rw [norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [hF.coeFn_toLp] with y h
      rw [h]
    rw [h1, h2]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_starProjection_le _ Fl) 2

end BasicElliptic.Div
