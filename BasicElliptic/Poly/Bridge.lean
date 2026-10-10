/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import BasicElliptic.Statements.Bridge
public import BasicElliptic.Poly.Extract
public import BasicElliptic.Poly.InteriorBalls
import BasicElliptic.Holder.Algebra

/-!
# Polynomial approximation and the closed-region `C^{1,α}` / `C^{2,α}` bridges

Let `S` be a set, `u : E → ℝ`, and suppose that at every `p ∈ S` a quadratic polynomial `P p`
(`BasicElliptic.QuadPoly`) approximates `u` to order `k + α` within `S`:
`|u q - (P p).eval (q - p)| ≤ A |q - p|^{k+α}` for `q ∈ S`, `|q - p| < ρ₀`
(`BasicElliptic.PolyApproxOn k α A ρ₀ u S P`). The expansions are one-sided at boundary points of
`S`, and derivatives are taken within `S`.

* `PolyApproxOn.hasFDerivWithinAt`: `u` has within-derivative `(P p).lin` at `p` (`k ≥ 1`).
* `PolyApproxOn.near`: comparing the expansions at `p` and `p'` on a ball of radius
  `κ |p - p'|` inside `S` (`HasUniformInteriorBalls`) bounds `‖D²P_p - D²P_{p'}‖` and
  `‖DP_p(p' - p) - DP_{p'}(0)‖` (PBT `two_expansions`, with balls replaced by interior balls).
* `contDiffOn_two_of_polyApprox` (`k = 2`, `S` convex, bounded, with nonempty interior):
  `ContDiffHolderOn 2 α u S`, `fderivWithin ℝ u S = lin`, and the second within-derivative is
  the symmetrized `hess`.
* `contDiffHolderOn_two_of_polyApprox`: the frozen `PolyApproxBridgeStatement`.

Local Hölder bounds are made global on convex bounded sets by chaining along segments
(`dist_le_of_convex_of_near`).

## Provenance

Closed-region, elliptic adaptation of `PolyApprox`, `PolyApprox.hasGradientAt`, `near2`,
`PolyApprox.hasFDerivAt_fderiv_slice` and `isC21On_of_polyApprox` in parabolic-basic-theory,
`ParabolicBasic/Schauder/Campanato.lean` (own repository, commit
`2507d9a800377e91c591862286b2ba2d6464d918`): open sets and `fderiv` are replaced by a closed or
convex `S` with `fderivWithin`, uniqueness of derivatives comes from `UniqueDiffOn` of convex sets
with nonempty interior, and coefficient comparison happens on interior balls of `S`.
`hasFDerivWithinAt_of_norm_le_rpow` is the within-set version of `hasFDerivAt_of_norm_le_rpow` in
elliptic-bernoulli-foundations, `EllipticBernoulli/Flatness/GraphAux.lean` (own repository).
-/

public section

open Set Metric Filter Topology Asymptotics
open scoped NNReal

namespace BasicElliptic

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A first-order Taylor bound `‖f y - f x - L (y - x)‖ ≤ K ‖y - x‖^{1+β}` for `y ∈ s` near `x`
(`β > 0`) gives `HasFDerivWithinAt f L s x`. -/
theorem hasFDerivWithinAt_of_norm_le_rpow {f : E → F} {L : E →L[ℝ] F} {s : Set E} {x : E}
    {δ K β : ℝ} (hδ : 0 < δ) (hβ : 0 < β)
    (h : ∀ y ∈ s, ‖y - x‖ ≤ δ → ‖f y - f x - L (y - x)‖ ≤ K * ‖y - x‖ ^ (1 + β)) :
    HasFDerivWithinAt f L s x := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have ht : Tendsto (fun y : E ↦ K * ‖y - x‖ ^ β) (𝓝 x) (𝓝 0) := by
    have : Continuous (fun y : E ↦ K * ‖y - x‖ ^ β) :=
      continuous_const.mul
        ((continuous_id.sub continuous_const).norm.rpow_const fun _ ↦ Or.inr hβ.le)
    simpa [Real.zero_rpow hβ.ne'] using this.tendsto x
  filter_upwards [nhdsWithin_le_nhds (ht.eventually (gt_mem_nhds hc)),
    nhdsWithin_le_nhds (closedBall_mem_nhds x hδ), self_mem_nhdsWithin] with y hy1 hy2 hy3
  rw [mem_closedBall, dist_eq_norm] at hy2
  calc ‖f y - f x - L (y - x)‖ ≤ K * ‖y - x‖ ^ (1 + β) := h y hy3 hy2
    _ = (K * ‖y - x‖ ^ β) * ‖y - x‖ := by
      rw [Real.rpow_add' (norm_nonneg _) (by positivity), Real.rpow_one]; ring
    _ ≤ c * ‖y - x‖ := mul_le_mul_of_nonneg_right hy1.le (norm_nonneg _)

/-- **Chaining.** On a convex set of diameter `≤ D`, a Hölder bound for pairs at distance `≤ η`
gives a global one, with constant multiplied by `D / η + 1`. -/
theorem dist_le_of_convex_of_near {Y : Type*} [PseudoMetricSpace Y] {f : E → Y} {S : Set E}
    (hS : Convex ℝ S) {η K D β : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hD : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (h : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ η → dist (f x) (f y) ≤ K * dist x y ^ β) :
    ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ K * (D / η + 1) * dist x y ^ β := by
  intro x hx y hy
  set L := dist x y with hL
  have hL0 : 0 ≤ L := dist_nonneg
  set n : ℕ := ⌊L / η⌋₊ + 1 with hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by simp [hn]
  have hnD : (n : ℝ) ≤ D / η + 1 := by
    have h1 : (⌊L / η⌋₊ : ℝ) ≤ L / η := Nat.floor_le (by positivity)
    have h2 : L / η ≤ D / η := by gcongr; exact hD x hx y hy
    simp only [hn]; push_cast; linarith
  have hLn : L / n ≤ η := by
    rw [div_le_iff₀ hn0]
    have := Nat.lt_floor_add_one (L / η)
    rw [div_lt_iff₀ hη] at this
    simp only [hn]; push_cast; linarith
  set g : ℕ → E := fun i ↦ x + ((i : ℝ) / n) • (y - x) with hg
  have hgS : ∀ i ≤ n, g i ∈ S := fun i hi ↦
    hS.add_smul_sub_mem hx hy ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast hi) hn0.le⟩
  have hgd : ∀ i, dist (g i) (g (i + 1)) = L / n := by
    intro i
    have : g i - g (i + 1) = ((i : ℝ) / n - ((i + 1 : ℕ) : ℝ) / n) • (y - x) := by
      simp only [g, sub_smul]; abel
    rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, ← dist_eq_norm, dist_comm y x,
      show (i : ℝ) / n - ((i + 1 : ℕ) : ℝ) / n = -(1 / n) by push_cast; field_simp; ring,
      abs_neg, abs_of_pos (by positivity)]
    ring
  have hg0 : g 0 = x := by simp [g]
  have hgn : g n = y := by simp [g]
  calc dist (f x) (f y) = dist (f (g 0)) (f (g n)) := by rw [hg0, hgn]
    _ ≤ ∑ i ∈ Finset.range n, dist (f (g i)) (f (g (i + 1))) :=
        dist_le_range_sum_dist (fun i ↦ f (g i)) n
    _ ≤ ∑ _i ∈ Finset.range n, K * (L / n) ^ β := Finset.sum_le_sum fun i hi ↦ by
        have hi' := Finset.mem_range.1 hi
        have := h _ (hgS i hi'.le) _ (hgS (i + 1) hi') (by rw [hgd]; exact hLn)
        rwa [hgd] at this
    _ = n * (K * (L / n) ^ β) := by simp
    _ ≤ (D / η + 1) * (K * L ^ β) := by
        refine mul_le_mul hnD (mul_le_mul_of_nonneg_left ?_ hK) (by positivity) (by linarith)
        exact Real.rpow_le_rpow (by positivity) (div_le_self hL0 hn1) hβ
    _ = K * (D / η + 1) * L ^ β := by ring

end Calculus

section PolyApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform pointwise polynomial approximation of order `k + α` on `S`: at every `p ∈ S`, the
polynomial `P p` (of degree `≤ k`) approximates `u` within `S` with
`|u q - (P p).eval (q - p)| ≤ A dist(q, p)^{k+α}` for `dist(q, p) < ρ₀`. -/
structure PolyApproxOn (k : ℕ) (α : ℝ≥0) (A ρ₀ : ℝ) (u : E → ℝ) (S : Set E)
    (P : E → QuadPoly E) : Prop where
  deg : ∀ p ∈ S, (P p).IsDegLE k
  approx : ∀ p ∈ S, ∀ q ∈ S, dist q p < ρ₀ →
    |u q - (P p).eval (q - p)| ≤ A * dist q p ^ ((k : ℝ) + α)

namespace PolyApproxOn

variable {k : ℕ} {α : ℝ≥0} {A ρ₀ : ℝ} {u : E → ℝ} {S : Set E} {P : E → QuadPoly E}

theorem mono_const (h : PolyApproxOn k α A ρ₀ u S P) {A' : ℝ} (hA : A ≤ A') :
    PolyApproxOn k α A' ρ₀ u S P :=
  ⟨h.deg, fun p hp q hq hd ↦ (h.approx p hp q hq hd).trans
    (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg dist_nonneg _))⟩

/-- The constant term is the value: `(P p).const = u p`. -/
theorem const_eq (h : PolyApproxOn k α A ρ₀ u S P) (hρ : 0 < ρ₀) (hk : 0 < (k : ℝ) + α)
    {p : E} (hp : p ∈ S) : (P p).const = u p := by
  have := h.approx p hp p hp (by simpa using hρ)
  rw [dist_self, Real.zero_rpow hk.ne', mul_zero, sub_self, QuadPoly.eval_zero] at this
  exact (sub_eq_zero.1 (abs_nonpos_iff.1 this)).symm

/-- **First derivative.** For `k + α > 1`, `u` has within-derivative `(P p).lin`. -/
theorem hasFDerivWithinAt (h : PolyApproxOn k α A ρ₀ u S P) (hρ : 0 < ρ₀)
    (hkα : 1 < (k : ℝ) + α) {p : E} (hp : p ∈ S) : HasFDerivWithinAt u (P p).lin S p := by
  set β := min ((k : ℝ) + α - 1) 1 with hβdef
  have hβ : 0 < β := lt_min (by linarith) one_pos
  have hβ1 : β ≤ (k : ℝ) + α - 1 := min_le_left _ _
  have hβ2 : β ≤ 1 := min_le_right _ _
  have hc := h.const_eq hρ (by linarith) hp
  refine hasFDerivWithinAt_of_norm_le_rpow (δ := min 1 (ρ₀ / 2))
    (K := max A 0 + ‖(P p).quad‖) (by positivity) hβ fun q hq hqd ↦ ?_
  set z := q - p with hz
  have hz1 : ‖z‖ ≤ 1 := hqd.trans (min_le_left _ _)
  have hzρ : dist q p < ρ₀ := by
    rw [dist_eq_norm]; linarith [min_le_right 1 (ρ₀ / 2)]
  have e := h.approx p hp q hq hzρ
  rw [dist_eq_norm] at e
  have hγ : ‖z‖ ^ ((k : ℝ) + α) ≤ ‖z‖ ^ (1 + β) :=
    Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hz1 (by linarith) (by linarith)
  have h2 : ‖z‖ ^ (2 : ℝ) ≤ ‖z‖ ^ (1 + β) :=
    Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hz1 (by linarith) (by linarith)
  rw [Real.rpow_two] at h2
  have hq2 : |(P p).quad z z| ≤ ‖(P p).quad‖ * ‖z‖ ^ 2 := by
    have := (P p).quad.le_opNorm₂ z z
    rw [Real.norm_eq_abs] at this; nlinarith [norm_nonneg z]
  have key : u q - u p - (P p).lin z = (u q - (P p).eval z) + (1 / 2 : ℝ) * (P p).quad z z := by
    rw [QuadPoly.eval, hc]; ring
  rw [Real.norm_eq_abs, key]
  have a1 : A * ‖z‖ ^ ((k : ℝ) + α) ≤ max A 0 * ‖z‖ ^ (1 + β) :=
    mul_le_mul (le_max_left _ _) hγ (Real.rpow_nonneg (norm_nonneg _) _) (le_max_right _ _)
  have a2 : ‖(P p).quad‖ * ‖z‖ ^ 2 ≤ ‖(P p).quad‖ * ‖z‖ ^ (1 + β) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have a3 : 0 ≤ ‖(P p).quad‖ * ‖z‖ ^ 2 := by positivity
  calc |(u q - (P p).eval z) + (1 / 2 : ℝ) * (P p).quad z z|
      ≤ |u q - (P p).eval z| + |(1 / 2 : ℝ) * (P p).quad z z| := abs_add_le _ _
    _ ≤ A * ‖z‖ ^ ((k : ℝ) + α) + (1 / 2 : ℝ) * (‖(P p).quad‖ * ‖z‖ ^ 2) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; gcongr
    _ ≤ (max A 0 + ‖(P p).quad‖) * ‖z‖ ^ (1 + β) := by nlinarith

/-- **Near comparison** of the expansions at `p` and `p'` (`0 < δ = dist p p' ≤ r₁`,
`2δ < ρ₀`), on interior balls of `S`. -/
theorem near (h : PolyApproxOn k α A ρ₀ u S P) (hk : k ≤ 2) (hα1 : α ≤ 1) (hA : 0 ≤ A)
    {r₁ κ : ℝ} (hκ : 0 < κ) (hS : HasUniformInteriorBalls S r₁ κ) {p p' : E} (hp : p ∈ S)
    (hp' : p' ∈ S) (hδ0 : 0 < dist p p') (hδ1 : dist p p' ≤ r₁) (hδρ : 2 * dist p p' < ρ₀) :
    ‖(P p).hess - (P p').hess‖ ≤ 288 / κ ^ 2 * A * dist p p' ^ ((k : ℝ) + α - 2) ∧
      ‖(P p).lin + (P p).hess (p' - p) - (P p').lin‖ ≤
        (18 / κ + 288 / κ ^ 2) * A * dist p p' ^ ((k : ℝ) + α - 1) := by
  obtain ⟨y, hy, hyp⟩ := hS p' hp' _ hδ0 hδ1
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα1
  exact QuadPoly.two_expansions_coeff (by positivity) (by linarith) hA (h.approx p hp)
    (h.approx p' hp') hδρ hp' hκ hδ0 hy hyp

end PolyApproxOn

/-- **The second-order bridge** on a convex body. If `u` has uniform pointwise second-order
expansions of order `2 + α` on a bounded convex set `S` with nonempty interior, then `u` is
`C^{2,α}` on `S` (derivatives within `S`), `fderivWithin ℝ u S p = (P p).lin` and
`fderivWithin ℝ (fderivWithin ℝ u S) S p = (P p).hess`. -/
theorem contDiffOn_two_of_polyApprox {S : Set E} {u : E → ℝ} {P : E → QuadPoly E} {α : ℝ≥0}
    {A ρ₀ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ₀) (hS : Convex ℝ S)
    (hSb : Bornology.IsBounded S) (hSi : (interior S).Nonempty)
    (h : PolyApproxOn 2 α A ρ₀ u S P) :
    ContDiffHolderOn 2 α u S ∧ (∀ p ∈ S, fderivWithin ℝ u S p = (P p).lin) ∧
      ∀ p ∈ S, fderivWithin ℝ (fderivWithin ℝ u S) S p = (P p).hess := by
  have hU : UniqueDiffOn ℝ S := uniqueDiffOn_convex hS hSi
  obtain ⟨r₁, κ, hr₁, hκ, -, hB⟩ := exists_hasUniformInteriorBalls hS hSb hSi
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hSb
  have hD0 : 0 ≤ D := by
    obtain ⟨x, hx⟩ := hSi
    simpa using hD (interior_subset hx) (interior_subset hx)
  have hP := h.mono_const (le_max_left A 0)
  set A' := max A 0 with hA'def
  have hA' : 0 ≤ A' := le_max_right _ _
  set η := min r₁ (ρ₀ / 3) with hηdef
  have hη : 0 < η := by positivity
  have hα : (0 : ℝ) < α := hα0
  have hc2 : ((2 : ℕ) : ℝ) + α - 2 = α := by push_cast; ring
  have hc1 : ((2 : ℕ) : ℝ) + α - 1 = 1 + α := by push_cast; ring
  have hnear : ∀ p ∈ S, ∀ p' ∈ S, dist p p' ≤ η →
      ‖(P p).hess - (P p').hess‖ ≤ 288 / κ ^ 2 * A' * dist p p' ^ (α : ℝ) ∧
      ‖(P p).lin + (P p).hess (p' - p) - (P p').lin‖ ≤
        (18 / κ + 288 / κ ^ 2) * A' * dist p p' ^ (1 + (α : ℝ)) := by
    intro p hp p' hp' hd
    rcases (dist_nonneg (x := p) (y := p')).eq_or_lt with h0 | h0
    · obtain rfl : p = p' := dist_eq_zero.1 h0.symm
      simp [Real.zero_rpow hα.ne', Real.zero_rpow (by positivity : (1 + (α : ℝ)) ≠ 0)]
    · have := hP.near le_rfl hα1 hA' hκ hB hp hp' h0 (hd.trans (min_le_left _ _))
        (by linarith [min_le_right r₁ (ρ₀ / 3)])
      rwa [hc2, hc1] at this
  have hu : ∀ p ∈ S, HasFDerivWithinAt u (P p).lin S p := fun p hp ↦
    hP.hasFDerivWithinAt hρ (by push_cast; linarith) hp
  have hlin : ∀ p ∈ S, HasFDerivWithinAt (fun x ↦ (P x).lin) (P p).hess S p := by
    intro p hp
    refine hasFDerivWithinAt_of_norm_le_rpow (K := (18 / κ + 288 / κ ^ 2) * A') hη hα
      fun p' hp' hd ↦ ?_
    have := (hnear p hp p' hp' (by rwa [dist_comm, dist_eq_norm])).2
    rw [dist_comm, dist_eq_norm] at this
    rw [show (P p').lin - (P p).lin - (P p).hess (p' - p) =
      -((P p).lin + (P p).hess (p' - p) - (P p').lin) by abel, norm_neg]
    exact this
  have hHnear : ∀ p ∈ S, ∀ p' ∈ S, dist p p' ≤ η →
      dist (P p).hess (P p').hess ≤ 288 / κ ^ 2 * A' * dist p p' ^ (α : ℝ) :=
    fun p hp p' hp' hd ↦ by rw [dist_eq_norm]; exact (hnear p hp p' hp' hd).1
  have hHglob := dist_le_of_convex_of_near hS hη hα.le (by positivity) hD hHnear
  set C := 288 / κ ^ 2 * A' * (D / η + 1) with hCdef
  have hC : 0 ≤ C := by positivity
  have hcontH : ContinuousOn (fun p ↦ (P p).hess) S :=
    (holderOnWith_of_dist_le hC hHglob).continuousOn hα0
  have hfd : ∀ p ∈ S, fderivWithin ℝ u S p = (P p).lin := fun p hp ↦
    (hu p hp).fderivWithin (hU p hp)
  have hfd2 : ∀ p ∈ S, fderivWithin ℝ (fderivWithin ℝ u S) S p = (P p).hess := fun p hp ↦ by
    rw [fderivWithin_congr (fun x hx ↦ hfd x hx) (hfd p hp)]
    exact (hlin p hp).fderivWithin (hU p hp)
  have hC1 : ContDiffOn ℝ 1 (fun x ↦ (P x).lin) S := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_fderivWithin hU]
    refine ⟨fun p hp ↦ (hlin p hp).differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hcontH.congr fun p hp ↦ (hlin p hp).fderivWithin (hU p hp)
  have hC2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) u S := by
    rw [show ((2 : ℕ) : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderivWithin hU]
    exact ⟨fun p hp ↦ (hu p hp).differentiableWithinAt, by simp, hC1.congr hfd⟩
  refine ⟨⟨hC2, Real.toNNReal C, holderOnWith_of_dist_le hC fun p hp p' hp' ↦ ?_⟩, hfd, hfd2⟩
  calc dist (iteratedFDerivWithin ℝ 2 u S p) (iteratedFDerivWithin ℝ 2 u S p')
      ≤ dist (P p).hess (P p').hess := by
        rw [dist_eq_norm, dist_eq_norm]
        refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m ↦ ?_
        rw [sub_apply, iteratedFDerivWithin_two_apply u hU hp,
          iteratedFDerivWithin_two_apply u hU hp', hfd2 p hp, hfd2 p' hp', Fin.prod_univ_two,
          ← sub_apply, ← sub_apply, ← mul_assoc]
        exact ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ C * dist p p' ^ (α : ℝ) := hHglob p hp p' hp'

end PolyApprox

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **`PolyApproxBridgeStatement`**: uniform pointwise second-order expansions on a
bounded convex set with nonempty interior give `C^{2,α}` with `Du = P1`. Proved by packaging
`P0, P1, P2` as a `QuadPoly` and applying `contDiffOn_two_of_polyApprox`. -/
theorem contDiffHolderOn_two_of_polyApprox : PolyApproxBridgeStatement E := by
  intro α hα0 hα1 S u P0 P1 P2 A ρ₀ hS hSb hSi hρ happrox
  have hP : PolyApproxOn 2 α A ρ₀ u S (fun p ↦ ⟨P0 p, P1 p, P2 p⟩) :=
    ⟨fun _ _ ↦ trivial, fun p hp q hq hd ↦ by
      have := happrox p hp q hq hd
      push_cast
      exact this⟩
  obtain ⟨h1, h2, -⟩ := contDiffOn_two_of_polyApprox hα0 hα1.le hρ hS hSb hSi hP
  exact ⟨h1, h2⟩

end BasicElliptic
