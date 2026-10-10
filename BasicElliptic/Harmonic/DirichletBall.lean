/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Basic.HalfSpace
public import BasicElliptic.Harmonic.Limit
public import BasicElliptic.Harmonic.MaxPrinciple
import ViscositySolns.Applications.Laplace.Dirichlet
import ViscositySolns.Applications.Laplace.ExteriorSphere

/-!
# The Dirichlet problem on a ball

Let `E` be a finite-dimensional real inner product space, `x : E` and `r > 0`.

* `BasicElliptic.exists_lipschitzWith_abs_sub_le_of_continuousOn`: a function continuous on a
  compact set `S` of a pseudometric space is uniformly approximated on `S` by globally Lipschitz
  functions (the inf-convolutions `y ↦ ⨅ z ∈ S, g z + K dist y z`).
* `BasicElliptic.HarmonicAt.comp_linearIsometryEquiv`,
  `BasicElliptic.HarmonicOnNhd.comp_linearIsometryEquiv`: harmonicity is invariant under linear
  isometries.
* `BasicElliptic.exists_harmonic_ball_boundary_of_lipschitzWith`: the Dirichlet problem on
  `ball x r` with Lipschitz data, from
  `ViscositySolns.dirichlet_harmonic_modulus_of_uniformExteriorSphere` (Perron's method with
  exterior-sphere barriers, in the `viscosity_solns` dependency), transported from
  `EuclideanSpace ℝ (Fin (finrank ℝ E))` to `E` by an orthonormal basis.
* `BasicElliptic.exists_harmonic_ball_boundary`: the Dirichlet problem on `ball x r` with data
  continuous on `sphere x r`: there is `h`, continuous on `closedBall x r`, harmonic in
  `ball x r`, with `h = g` on `sphere x r`.
* `BasicElliptic.eqOn_closedBall_of_harmonic_of_eqOn_sphere` (uniqueness) and
  `BasicElliptic.abs_le_of_harmonic_ball` (`sup |h| ≤ sup |g|`), from the weak maximum principle.
* `BasicElliptic.eqOn_comp_of_harmonic_ball`, `BasicElliptic.eqOn_neg_comp_of_harmonic_ball`:
  invariance of the solution under a linear isometry `L` fixing the centre, when `g ∘ L = ± g`
  on the sphere.
* `BasicElliptic.apply_reflect_eq_of_harmonic_ball`,
  `BasicElliptic.apply_reflect_eq_neg_of_harmonic_ball`: the special case `L = reflect ν` with
  the centre on `flatPart ν`: even (odd) data give even (odd) solutions.

## Proof of `exists_harmonic_ball_boundary`

Approximate `g` on the sphere `S = sphere x r` within `1/(n+1)` by Lipschitz `G n`, and let `h n`
solve the Dirichlet problem with data `G n`. By the weak maximum principle
(`le_of_harmonic_boundary`) `|h n - h m| ≤ 1/(n+1) + 1/(m+1)` on `closedBall x r`, so `h n`
converges uniformly there to some `h`. The limit is continuous on `closedBall x r`, harmonic in
`ball x r` (`harmonicOnNhd_of_tendstoLocallyUniformlyOn`) and equals `g` on `S`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001.

## Provenance

Ported from elliptic-bernoulli-foundations (W. M. Feldman),
`EllipticBernoulli/Harmonic/DirichletBall.lean`, commit
ea02c735ae1af1b0eab48928ff959c41ed49e9a8: `exists_lipschitzWith_abs_sub_le_of_continuousOn`
(verbatim), `exists_harmonic_ball_boundary_of_lipschitzWith` and
`exists_harmonic_ball_boundary`. Changes: namespace `BasicElliptic`; `E d` generalized to a
finite-dimensional inner product space `E` (transport by `(stdOrthonormalBasis ℝ E).repr`);
`exists_harmonic_ball_boundary` is stated directly rather than as EB's
`DirichletBallStatement`, and the `1 ≤ d` hypothesis is replaced by a case split on
`Nontrivial E`. Uniqueness, the maximum bound and the symmetry statements are new.
-/

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian NNReal

public section

namespace BasicElliptic

/-! ### Lipschitz approximation -/

/-- **Lipschitz approximation on a compact set.** If `g` is continuous on a compact subset `S`
of a pseudometric space, then for every `δ > 0` there is a globally Lipschitz `G` with
`|G - g| ≤ δ` on `S`. -/
theorem exists_lipschitzWith_abs_sub_le_of_continuousOn {X : Type*} [PseudoMetricSpace X]
    {S : Set X} (hS : IsCompact S) {g : X → ℝ} (hg : ContinuousOn g S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ≥0, ∃ G : X → ℝ, LipschitzWith K G ∧ ∀ y ∈ S, |G y - g y| ≤ δ := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨0, fun _ ↦ 0, LipschitzWith.const _, by simp⟩
  have : Nonempty S := hSne.coe_sort
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hg
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ hSne.some_mem)
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hg) δ hδ
  set K : ℝ≥0 := ⟨2 * B / η, by positivity⟩ with hK
  have hKη : (K : ℝ) * η = 2 * B := by
    change 2 * B / η * η = 2 * B
    field_simp
  set G : X → ℝ := fun y ↦ ⨅ z : S, (g z + K * dist y z) with hG
  have hBdd : ∀ y : X, BddBelow (range fun z : S ↦ g z + K * dist y (z : X)) := fun y ↦ by
    refine ⟨-B, ?_⟩
    rintro w ⟨z, rfl⟩
    have h1 := hB z z.2
    rw [Real.norm_eq_abs, abs_le] at h1
    have : 0 ≤ (K : ℝ) * dist y z := by positivity
    dsimp only
    linarith
  refine ⟨K, G, LipschitzWith.of_le_add_mul K fun y₁ y₂ ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← sub_le_iff_le_add]
    refine le_ciInf fun z ↦ ?_
    rw [sub_le_iff_le_add]
    calc G y₁ ≤ g z + K * dist y₁ z := ciInf_le (hBdd y₁) z
      _ ≤ g z + K * dist y₂ z + K * dist y₁ y₂ := by
        rw [add_assoc, ← mul_add, add_comm (dist y₂ z)]
        gcongr
        exact dist_triangle _ _ _
  · have hup : G y ≤ g y := by
      simpa using ciInf_le (hBdd y) ⟨y, hy⟩
    have hlow : g y - δ ≤ G y := by
      refine le_ciInf fun z ↦ ?_
      by_cases hyz : dist y z < η
      · have := hηg y hy z z.2 hyz
        rw [Real.dist_eq, abs_lt] at this
        have : 0 ≤ (K : ℝ) * dist y z := by positivity
        linarith
      · have h1 := hB z z.2
        have h2 := hB y hy
        rw [Real.norm_eq_abs, abs_le] at h1 h2
        have : (K : ℝ) * η ≤ K * dist y z := by gcongr; exact not_lt.1 hyz
        linarith
    rw [abs_le]
    constructor <;> linarith

/-! ### Invariance of harmonicity under linear isometries -/

section Isometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-- Harmonicity is invariant under linear isometries: if `f` is harmonic at `L y`, then `f ∘ L`
is harmonic at `y`. -/
theorem HarmonicAt.comp_linearIsometryEquiv {f : E' → ℝ} (L : E ≃ₗᵢ[ℝ] E') {y : E}
    (hf : HarmonicAt f (L y)) : HarmonicAt (f ∘ L) y := by
  refine ⟨hf.1.comp y L.contDiff.contDiffAt, ?_⟩
  rw [ViscositySolns.Analysis.laplacian_comp_linearIsometryEquiv_right]
  exact hf.2.comp_tendsto (L.continuous.tendsto y)

/-- Harmonicity on a set is invariant under linear isometries. -/
theorem HarmonicOnNhd.comp_linearIsometryEquiv {f : E' → ℝ} {s : Set E'} (L : E ≃ₗᵢ[ℝ] E')
    (hf : HarmonicOnNhd f s) : HarmonicOnNhd (f ∘ L) (L ⁻¹' s) :=
  fun _ hy ↦ HarmonicAt.comp_linearIsometryEquiv L (hf _ hy)

end Isometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Lipschitz data -/

/-- The Euclidean case of `exists_harmonic_ball_boundary_of_lipschitzWith`, from
`viscosity_solns`. -/
private theorem exists_harmonic_ball_boundary_of_lipschitzWith_euclidean {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) {K : ℝ≥0}
    {G : EuclideanSpace ℝ (Fin d) → ℝ} (hG : LipschitzWith K G) :
    ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closedBall x r) ∧
      HarmonicOnNhd h (ball x r) ∧ EqOn h G (sphere x r) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn
    hG.continuous.continuousOn
  obtain ⟨ϖ, -, hsol⟩ := ViscositySolns.dirichlet_harmonic_modulus_of_uniformExteriorSphere
    isOpen_ball isBounded_ball (ViscositySolns.uniformExteriorSphere_ball x hr) K M
  rw [closure_ball x hr.ne'] at hsol
  obtain ⟨h, hc, h2, hΔ, hfr, -⟩ := hsol G hG.lipschitzOnWith fun y hy ↦ by
    simpa [Real.norm_eq_abs] using hM y hy
  refine ⟨h, hc, (harmonicOnNhd_iff_contDiffOn_laplacian_eq_zero isOpen_ball).2 ⟨h2, hΔ⟩,
    fun y hy ↦ hfr y ?_⟩
  rwa [frontier_ball x hr.ne']

/-- **The Dirichlet problem on a ball with Lipschitz data** (`viscosity_solns`). -/
theorem exists_harmonic_ball_boundary_of_lipschitzWith (x : E) {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0} {G : E → ℝ} (hG : LipschitzWith K G) :
    ∃ h : E → ℝ, ContinuousOn h (closedBall x r) ∧ HarmonicOnNhd h (ball x r) ∧
      EqOn h G (sphere x r) := by
  set e := (stdOrthonormalBasis ℝ E).repr
  have hG' : LipschitzWith K (G ∘ e.symm) := by
    simpa using hG.comp e.symm.isometry.lipschitzWith
  obtain ⟨h, hc, hh, hfr⟩ := exists_harmonic_ball_boundary_of_lipschitzWith_euclidean (e x) hr hG'
  refine ⟨h ∘ e, hc.comp e.continuous.continuousOn fun y hy ↦ ?_,
    fun y hy ↦ HarmonicAt.comp_linearIsometryEquiv e (hh _ ?_), fun y hy ↦ ?_⟩
  · rwa [mem_closedBall, e.dist_map]
  · rwa [mem_ball, e.dist_map]
  · have : e y ∈ sphere (e x) r := by rwa [mem_sphere, e.dist_map]
    simpa using hfr this

/-! ### Continuous data -/

/-- **The Dirichlet problem on a ball with continuous data** ([GT]). For `g`
continuous on `sphere x r` there is `h`, continuous on `closedBall x r` and harmonic in
`ball x r`, with `h = g` on `sphere x r`. -/
theorem exists_harmonic_ball_boundary (x : E) {r : ℝ} (hr : 0 < r) {g : E → ℝ}
    (hg : ContinuousOn g (sphere x r)) :
    ∃ h : E → ℝ, ContinuousOn h (closedBall x r) ∧ HarmonicOnNhd h (ball x r) ∧
      EqOn h g (sphere x r) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- in dimension zero the sphere of positive radius is empty
    refine ⟨fun _ ↦ 0, continuousOn_const, fun y _ ↦ harmonicAt_const 0, fun y hy ↦ ?_⟩
    rw [mem_sphere, Subsingleton.elim y x, dist_self] at hy
    exact absurd hy hr.ne
  -- Lipschitz approximations `G n` and their harmonic extensions `h n`
  have happrox : ∀ n : ℕ, ∃ K : ℝ≥0, ∃ G : E → ℝ, LipschitzWith K G ∧
      ∀ y ∈ sphere x r, |G y - g y| ≤ 1 / ((n : ℝ) + 1) := fun n ↦
    exists_lipschitzWith_abs_sub_le_of_continuousOn (isCompact_sphere x r) hg (by positivity)
  choose K G hGL hGg using happrox
  have hsol : ∀ n, ∃ h : E → ℝ, ContinuousOn h (closedBall x r) ∧
      HarmonicOnNhd h (ball x r) ∧ EqOn h (G n) (sphere x r) := fun n ↦
    exists_harmonic_ball_boundary_of_lipschitzWith x hr (hGL n)
  choose H hHc hHh hHG using hsol
  have hcl : closure (ball x r) = closedBall x r := closure_ball x hr.ne'
  have hfr : frontier (ball x r) = sphere x r := frontier_ball x hr.ne'
  -- uniform Cauchy estimate
  have hcauchy : ∀ n m, ∀ y ∈ closedBall x r,
      |H n y - H m y| ≤ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
    intro n m
    have key : ∀ n m, ∀ y ∈ closedBall x r,
        H n y ≤ H m y + (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) := by
      intro n m y hy
      have hk : HarmonicOnNhd (fun z ↦ H m z + (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)))
          (ball x r) := fun z hz ↦ by
        have := (hHh m z hz).add (harmonicAt_const (c := (1 / ((n : ℝ) + 1) +
          1 / ((m : ℝ) + 1))))
        exact this
      refine le_of_harmonic_boundary isOpen_ball isBounded_ball (hHh n) hk
        (by rw [hcl]; exact hHc n) (by rw [hcl]; exact (hHc m).add continuousOn_const)
        (fun z hz ↦ ?_) y (by rw [hcl]; exact hy)
      rw [hfr] at hz
      rw [hHG n hz, hHG m hz]
      have h1 := hGg n z hz
      have h2 := hGg m z hz
      rw [abs_le] at h1 h2
      linarith
    intro y hy
    rw [abs_le]
    constructor
    · linarith [key m n y hy]
    · linarith [key n m y hy]
  -- the pointwise limit
  have hcs : ∀ y ∈ closedBall x r, CauchySeq fun n ↦ H n y := by
    intro y hy
    refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Real.dist_eq]
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hb : ∀ k : ℕ, N ≤ k → 1 / ((k : ℝ) + 1) < ε / 2 := fun k hk ↦ by
      rw [div_lt_iff₀ (by positivity)]
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      have := (div_lt_iff₀ hε).1 hN
      nlinarith
    have := hcauchy n N y hy
    linarith [hb n hn, hb N le_rfl]
  set h : E → ℝ := fun y ↦ limUnder atTop fun n ↦ H n y with hh_def
  have hlim : ∀ y ∈ closedBall x r, Tendsto (fun n ↦ H n y) atTop (𝓝 (h y)) :=
    fun y hy ↦ (hcs y hy).tendsto_limUnder
  have hdist : ∀ n, ∀ y ∈ closedBall x r, |H n y - h y| ≤ 1 / ((n : ℝ) + 1) := by
    intro n y hy
    have ht : Tendsto (fun m : ℕ ↦ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) atTop
        (𝓝 (1 / ((n : ℝ) + 1) + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at ht
    exact le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub (hlim y hy)).abs) ht
      (Eventually.of_forall fun m ↦ hcauchy n m y hy)
  have hunif : TendstoUniformlyOn H h atTop (closedBall x r) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    filter_upwards [eventually_ge_atTop N] with n hn y hy
    rw [Real.dist_eq, abs_sub_comm]
    refine (hdist n y hy).trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    have := (div_lt_iff₀ hε).1 hN
    nlinarith
  refine ⟨h, hunif.continuousOn (Frequently.of_forall hHc), ?_, fun y hy ↦ ?_⟩
  · exact (harmonicOnNhd_of_tendstoLocallyUniformlyOn isOpen_ball hHh
      (hunif.mono ball_subset_closedBall).tendstoLocallyUniformlyOn).1
  · have hy' : y ∈ closedBall x r := sphere_subset_closedBall hy
    have hle : ∀ n : ℕ, |h y - g y| ≤ 2 / ((n : ℝ) + 1) := fun n ↦ by
      have h1 := hdist n y hy'
      have h2 := hGg n y hy
      rw [hHG n hy] at h1
      calc |h y - g y| ≤ |G n y - h y| + |G n y - g y| := by
            rw [abs_sub_comm (G n y) (h y)]; exact abs_sub_le _ _ _
        _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_le_add h1 h2
        _ = 2 / ((n : ℝ) + 1) := by ring
    have ht : Tendsto (fun n : ℕ ↦ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
      rw [mul_zero] at this
      exact this.congr fun n ↦ mul_one_div _ _
    have h0 : |h y - g y| ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hle)
    have := abs_nonpos_iff.1 h0
    linarith


/-! ### Uniqueness and the maximum bound -/

/-- **Uniqueness for the Dirichlet problem on a ball.** Two functions harmonic in `ball x r`,
continuous on `closedBall x r` and equal on `sphere x r` are equal on `closedBall x r`. -/
theorem eqOn_closedBall_of_harmonic_of_eqOn_sphere [Nontrivial E] {x : E} {r : ℝ} (hr : 0 < r)
    {h k : E → ℝ} (hh : HarmonicOnNhd h (ball x r)) (hk : HarmonicOnNhd k (ball x r))
    (hhc : ContinuousOn h (closedBall x r)) (hkc : ContinuousOn k (closedBall x r))
    (hfr : EqOn h k (sphere x r)) : EqOn h k (closedBall x r) := by
  rw [← closure_ball x hr.ne'] at hhc hkc ⊢
  exact eqOn_of_harmonic_of_eqOn_frontier isOpen_ball isBounded_ball hh hk hhc hkc
    (by rwa [frontier_ball x hr.ne'])

/-- **Maximum bound for the Dirichlet problem on a ball.** If `h` is harmonic in `ball x r`,
continuous on `closedBall x r` and `|h| ≤ M` on `sphere x r`, then `|h| ≤ M` on
`closedBall x r`. -/
theorem abs_le_of_harmonic_ball [Nontrivial E] {x : E} {r : ℝ} (hr : 0 < r) {h : E → ℝ}
    (hh : HarmonicOnNhd h (ball x r)) (hhc : ContinuousOn h (closedBall x r)) {M : ℝ}
    (hM : ∀ y ∈ sphere x r, |h y| ≤ M) : ∀ y ∈ closedBall x r, |h y| ≤ M := by
  rw [← closure_ball x hr.ne'] at hhc
  have hfr : frontier (ball x r) = sphere x r := frontier_ball x hr.ne'
  intro y hy
  rw [← closure_ball x hr.ne'] at hy
  rw [abs_le]
  constructor
  · have := le_of_harmonic_boundary isOpen_ball isBounded_ball (fun z _ ↦ harmonicAt_const (-M))
      hh continuousOn_const hhc (fun z hz ↦ ?_) y hy
    · exact this
    · rw [hfr] at hz; exact (abs_le.1 (hM z hz)).1
  · refine le_of_harmonic_boundary isOpen_ball isBounded_ball hh (fun z _ ↦ harmonicAt_const M)
      hhc continuousOn_const (fun z hz ↦ ?_) y hy
    rw [hfr] at hz; exact (abs_le.1 (hM z hz)).2

/-! ### Symmetric data give symmetric solutions -/

/-- The solution of the Dirichlet problem on `ball x r` is invariant under a linear isometry `L`
fixing the centre whenever the boundary data are: if `h` is harmonic in `ball x r`, continuous on
`closedBall x r`, and `h (L y) = h y` on `sphere x r`, then `h (L y) = h y` on `closedBall x r`. -/
theorem eqOn_comp_of_harmonic_ball [Nontrivial E] {x : E} {r : ℝ} (hr : 0 < r)
    (L : E ≃ₗᵢ[ℝ] E) (hLx : L x = x) {h : E → ℝ} (hh : HarmonicOnNhd h (ball x r))
    (hhc : ContinuousOn h (closedBall x r)) (hfr : ∀ y ∈ sphere x r, h (L y) = h y) :
    ∀ y ∈ closedBall x r, h (L y) = h y := by
  have hmaps : MapsTo L (closedBall x r) (closedBall x r) := fun y hy ↦ by
    rw [mem_closedBall, ← hLx, L.dist_map]; exact hy
  have hpre : L ⁻¹' ball x r = ball x r := by
    ext y; rw [mem_preimage, mem_ball, mem_ball]; nth_rewrite 1 [← hLx]; rw [L.dist_map]
  have hk : HarmonicOnNhd (h ∘ L) (ball x r) := hpre ▸ HarmonicOnNhd.comp_linearIsometryEquiv L hh
  exact eqOn_closedBall_of_harmonic_of_eqOn_sphere hr hk hh (hhc.comp L.continuous.continuousOn
    hmaps) hhc hfr

/-- The odd version of `eqOn_comp_of_harmonic_ball`: if `h (L y) = -h y` on `sphere x r`, then
`h (L y) = -h y` on `closedBall x r`. -/
theorem eqOn_neg_comp_of_harmonic_ball [Nontrivial E] {x : E} {r : ℝ} (hr : 0 < r)
    (L : E ≃ₗᵢ[ℝ] E) (hLx : L x = x) {h : E → ℝ} (hh : HarmonicOnNhd h (ball x r))
    (hhc : ContinuousOn h (closedBall x r)) (hfr : ∀ y ∈ sphere x r, h (L y) = -h y) :
    ∀ y ∈ closedBall x r, h (L y) = -h y := by
  have hmaps : MapsTo L (closedBall x r) (closedBall x r) := fun y hy ↦ by
    rw [mem_closedBall, ← hLx, L.dist_map]; exact hy
  have hpre : L ⁻¹' ball x r = ball x r := by
    ext y; rw [mem_preimage, mem_ball, mem_ball]; nth_rewrite 1 [← hLx]; rw [L.dist_map]
  have hk : HarmonicOnNhd (h ∘ L) (ball x r) := hpre ▸ HarmonicOnNhd.comp_linearIsometryEquiv L hh
  have hn : HarmonicOnNhd (fun y ↦ - h y) (ball x r) := fun y hy ↦ (hh y hy).neg
  exact eqOn_closedBall_of_harmonic_of_eqOn_sphere hr hk hn (hhc.comp L.continuous.continuousOn
    hmaps) hhc.neg hfr

omit [FiniteDimensional ℝ E] in
/-- `reflect ν` fixes the points of `flatPart ν` (no normalization of `ν` is needed). -/
private theorem reflect_eq_self_of_inner_eq_zero {ν y : E} (hy : y ∈ flatPart ν) :
    reflect ν y = y :=
  Submodule.reflection_mem_subspace_eq_self
    ((Submodule.mem_orthogonal_singleton_iff_inner_right).2 (by
      rw [real_inner_comm]; exact hy))

/-- **Even data give even solutions.** Let the centre `x` lie on `flatPart ν`. If `h` is harmonic
in `ball x r`, continuous on `closedBall x r`, and `h ∘ reflect ν = h` on `sphere x r`, then
`h ∘ reflect ν = h` on `closedBall x r`. -/
theorem apply_reflect_eq_of_harmonic_ball [Nontrivial E] {ν x : E} (hx : x ∈ flatPart ν) {r : ℝ}
    (hr : 0 < r) {h : E → ℝ} (hh : HarmonicOnNhd h (ball x r))
    (hhc : ContinuousOn h (closedBall x r)) (hfr : ∀ y ∈ sphere x r, h (reflect ν y) = h y) :
    ∀ y ∈ closedBall x r, h (reflect ν y) = h y :=
  eqOn_comp_of_harmonic_ball hr (reflect ν) (reflect_eq_self_of_inner_eq_zero hx) hh hhc hfr

/-- **Odd data give odd solutions.** Let the centre `x` lie on `flatPart ν`. If `h` is harmonic
in `ball x r`, continuous on `closedBall x r`, and `h ∘ reflect ν = - h` on `sphere x r`, then
`h ∘ reflect ν = - h` on `closedBall x r`. -/
theorem apply_reflect_eq_neg_of_harmonic_ball [Nontrivial E] {ν x : E} (hx : x ∈ flatPart ν)
    {r : ℝ} (hr : 0 < r) {h : E → ℝ} (hh : HarmonicOnNhd h (ball x r))
    (hhc : ContinuousOn h (closedBall x r)) (hfr : ∀ y ∈ sphere x r, h (reflect ν y) = -h y) :
    ∀ y ∈ closedBall x r, h (reflect ν y) = -h y :=
  eqOn_neg_comp_of_harmonic_ball hr (reflect ν) (reflect_eq_self_of_inner_eq_zero hx) hh hhc hfr

end BasicElliptic
