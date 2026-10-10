# elliptic-schauder-theory

`BasicElliptic` is a Lean 4 / Mathlib library for linear elliptic **Schauder theory**:
- Hölder spaces on sets, and Campanato's characterization of them;
- interior and **flat-boundary** `C^{1,α}` and `C^{2,α}` regularity, in divergence form (conormal boundary
  condition) and in nondivergence form (conormal-compatible and Dirichlet boundary conditions);
- the quasilinear conormal problem `div Φ(∇w) = 0`, with `⟪Φ(∇w), ν⟫ = 0` on the flat part.

Regularity is **qualitative**. Solutions are assumed only `C¹` up to the flat boundary in divergence form, and `C²` in
nondivergence form. The theorems prove that they are `C^{k,α}`, with scaled estimates whose constants are chosen
before the solution.

The library has about 28,300 lines of Lean in 88 files (87 under `BasicElliptic/` plus the root `BasicElliptic.lean`).
Every file is a Lean module, and everything lives in the namespace `BasicElliptic`.

**Status.** Every headline theorem is proved. The library contains no `sorry`, `admit`, `axiom` or `native_decide`, and
the 16 headline theorems depend exactly on the axioms `propext`, `Classical.choice` and `Quot.sound`. Every headline
theorem is restated over Mathlib alone in the comparator challenges in [`challenges/`](challenges/README.md) (see
[Verification](#verification)).

## Headline theorems

Each headline is a `…Statement : Prop` in `BasicElliptic/Statements/*`, and the theorem listed has exactly that
`Prop` as its type (names are in the namespace `BasicElliptic`). Source keys are expanded under
[References](#references).

| Result | Source | Lean theorem (namespace `BasicElliptic`) | Status |
|---|---|---|---|
| Interior `C^{1,α}` regularity, divergence form | GM; GT | `Div.contDiffHolderOn_one_of_isWeakSolution` | ✓ |
| Scaled interior `C^{1,α}` estimate, divergence form | GM | `Div.c1Holder_ball_estimate` | ✓ |
| Conormal flat-boundary `C^{1,α}` regularity | GM; GT (Dirichlet analogue); Lieberman Ch. 4 | `Div.contDiffHolderOn_one_halfBall_of_isConormalSolution` | ✓ |
| Scaled conormal flat-boundary `C^{1,α}` estimate | GM | `Div.c1Holder_halfBall_estimate` | ✓ |
| Strong ⇒ weak, linear conormal problem | — | `Div.isConormalSolOn_of_strong` | ✓ |
| Strong ⇒ weak, quasilinear conormal problem | — | `Div.isQuasilinearConormalSolOn_of_strong` | ✓ |
| Even reflection with measurable coefficients | — | `Div.IsConormalSolOn.evenReflect` | ✓ |
| Linear conormal `C^{2,α}` from `C^{1,α}` coefficients | GM; GT (by analogy) | `Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff` | ✓ |
| Quasilinear conormal regularity, `C^{k+1}` up to the flat part | Kinderlehrer–Nirenberg-type; GM | `Div.contDiffOn_halfBall_of_quasilinear_conormal` | ✓ |
| Scaled quasilinear conormal estimate | GM, applied to the derivative equations | `Div.quasilinear_conormal_estimate` | ✓ |
| Interior Schauder regularity, nondivergence form | GT; Caffarelli | `Nondiv.contDiffHolderOn_two_of_isSolution` | ✓ |
| Scaled interior Schauder estimate, nondivergence form | GT | `Nondiv.schauder_ball_estimate` | ✓ |
| Boundary Schauder, conormal-compatible condition | GT | `Nondiv.schauder_halfBall_conormal` | ✓ |
| Boundary Schauder, Dirichlet condition | GT | `Nondiv.schauder_halfBall_dirichlet` | ✓ |
| Campanato's characterization of `C^α` on half balls | GM; Campanato | `holderOnWith_of_campanato` | ✓ |
| Polynomial approximation ⇒ `C^{2,α}` on a convex body | Caffarelli; GT | `contDiffHolderOn_two_of_polyApprox` | ✓ |

Toolkit results are cited in their docstrings. They include:
- the Campanato iteration lemma (`campanato_iteration`) and the absorption lemma (`le_of_absorption`);
- the harmonic toolkit: a.e. Weyl lemma, derivative bounds, Campanato decay, the maximum principle and the Dirichlet
  problem on a ball;
- the gradient-field projection (`Div.exists_harmonic_replacement`);
- normalization by a linear change of variables.

## Proof routes

- **No Sobolev spaces in divergence form.** L² Campanato runs on the gradient field in `L²(B; E)`. The harmonic
  comparison field is `V = F − P F`, where `P` projects onto the closure of the test gradients. Hypotheses are
  classical: `w` is `C¹`, and the weak identity holds against `C¹_c` tests. Interior results allow nonsymmetric `a`.
- **Boundary = interior argument + normalization + reflection.** Conormal problems need symmetric `a`
  (respectively, symmetric `DΦ`). With a nonsymmetric `a`, the reflected problem is oblique; that case is not covered.
- **Nondivergence form uses sup-norm Campanato** (Caffarelli's polynomial approximation). Coefficients are
  frozen pointwise and Hölder at the point, and the estimate closes by absorption. Absorption is legitimate because
  `C²` on the compact region has been proved.
- **Nondivergence boundary conditions.** The boundary condition is either conormal-compatible, `⟪a ν, ∇w⟫ = γ`
  with `a ν` and `γ` in `C^{1,α}`, or Dirichlet with `g ∈ C^{2,α}`. Centres lie on the flat part, and the statements
  are qualitative. General oblique conditions are not covered.
- **Closed regions.** Derivatives on half balls are `fderivWithin` on the closed half ball. No extension theorem is
  used.
- **Coordinate-free half spaces.** `halfSpace ν = {x | 0 ≤ ⟪x, ν⟫}` with `‖ν‖ = 1`, in a finite-dimensional real
  inner product space `E`.
- **Hölder seminorms.** `HolderOnWith` (Mathlib) is the predicate. `eHolderSeminormOn` / `holderSeminormOn` are the
  seminorms, and `ContDiffHolderOn k α f s` is `C^{k,α}` on a set.

Statement conventions:
- Estimates take explicit bound hypotheses (`MG`, `Mf`) rather than suprema.
- Interior conclusions are on closed balls.
- The sign convention is `∫⟪a∇w, ∇φ⟫ = ∫⟪G, ∇φ⟫ + ∫ f φ`, the weak form of `−div(a∇w − G) = f`.

## Verification

Run from the repository root after `lake exe cache get`. CI (`.github/workflows/ci.yml`) runs exactly these steps.

```bash
lake build --wfail 2>&1 | tee build.log                 # the library, warnings as errors
python3 scripts/check_integrity.py --build-log build.log
lake env lean scripts/check_axioms.lean                 # axioms of the 16 headline theorems
ruby scripts/check-formalization-manifest.rb            # formalization.yaml: names, axioms, pins
python3 scripts/check_notation.py                       # binder precedence in the statement definitions
scripts/check-challenges.sh                             # challenge workspaces elaborate; solution axioms
python3 scripts/challenge-prep.py check                 # challenge vocabulary in sync with the library
```

- **Proof integrity.** `scripts/check_integrity.py` fails on `sorry`, `admit`, `axiom` or `native_decide` outside
  comments and strings, on any file that is not a Lean module, and on `declaration uses 'sorry'` in the build log.
- **Axioms.** `scripts/check_axioms.lean` runs `#print axioms` on each headline theorem under `#guard_msgs`, so it
  fails unless the answer is exactly `[propext, Classical.choice, Quot.sound]`.
  `scripts/check-formalization-manifest.rb` (adapted from elliptic-bernoulli-foundations) checks the same for every
  declaration listed in `formalization.yaml`. It also checks the toolchain and dependency pins against
  `lake-manifest.json`.
- **Comparator challenges.** [`challenges/`](challenges/README.md) restates all 16 headline theorems over Mathlib
  alone, in two workspaces (divergence form and nondivergence form). CI only checks that the challenges and solutions
  elaborate and that the solutions use the three standard axioms. Statement equality is checked by
  [Comparator](https://github.com/leanprover/comparator) in the release workflow
  (`.github/workflows/release-comparator.yml`), whose attestation is attached to each GitHub release.
- **Notation.** `scripts/check_notation.py` prints every statement and definition (`Statements/`, `Defs/`,
  `Basic/HalfSpace`) with `pp.notation false`. It flags any big-operator binder (`∫`, `⨍`, `∑`, `⨆`, …) whose body is a
  sum or difference containing another big operator, which is the shape of a binder that swallowed the next summand.
  It flags nothing.

## Building

The toolchain and dependencies are pinned in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`:
- Lean `v4.35.0-rc3`;
- Mathlib `v4.35.0-rc3` (commit `c55e6e7`),
  [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4);
- viscosity-solution-theory `v0.4.0` (Lake package `viscosity_solns`, commit `b9dc82d`),
  [willmfeldman/viscosity-solution-theory](https://github.com/willmfeldman/viscosity-solution-theory).
  - It supplies the continuous Weyl lemma and Perron's method for the Dirichlet problem on a ball, and is used only in
    `BasicElliptic/Harmonic/`.
  - It pulls in aleksandrov-differentiability `v0.4.0` (commit `5e5c2ec`), which this library does not import
    directly.

The other packages in `lake-manifest.json` are Mathlib's own dependencies. All dependencies are Apache-2.0.

```bash
lake exe cache get
lake build
```

## Layout

| Path | Contents |
|---|---|
| `BasicElliptic/Basic/`, `Defs/` | Half spaces and reflections; solution notions, ellipticity, Hölder seminorms |
| `BasicElliptic/Statements/` | Headline statements |
| `BasicElliptic/Common/` | Absorption lemma, uniform limits, within-derivative helpers, shared real-arithmetic and ball-measure helpers |
| `BasicElliptic/Campanato/`, `Holder/` | Campanato characterization and iteration (also with a small multiplicative term); Hölder algebra, closure lemmas, directional `C^{m,α}` classes, interpolation |
| `BasicElliptic/Harmonic/` | Harmonic toolkit: mean value, a.e. Weyl, estimates, decay, Taylor, maximum principle, Dirichlet ball |
| `BasicElliptic/Normalize/` | Cholesky-type normalization and linear changes of variables |
| `BasicElliptic/Poly/` | Quadratic polynomials and the polynomial-approximation bridge |
| `BasicElliptic/Div/Projection/` | Gradient-field projection and harmonic replacement |
| `BasicElliptic/Div/Interior/`, `Div/Boundary/`, `Div/Reflection.lean` | Divergence form: interior and conormal boundary `C^{1,α}`, strong ⇒ weak, reflection |
| `BasicElliptic/Div/Higher/` | Linear conormal `C^{2,α}` |
| `BasicElliptic/Div/Quasilinear/` | Quasilinear conormal problem: small-oscillation Campanato engine, `C^{k+1}` regularity, scaled estimate |
| `BasicElliptic/Nondiv/Interior/`, `Nondiv/Boundary/` | Nondivergence form: interior and flat-boundary Schauder |
| `challenges/` | Comparator challenge workspaces for the headline theorems |
| `scripts/` | Integrity, axiom, manifest, notation and challenge checks; the release comparator driver |

## References

- S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup. Pisa (3) 17 (1963),
  175–188.
- L. A. Caffarelli, *Interior a priori estimates for solutions of fully non-linear equations*, Ann. of Math. (2) 130
  (1989), no. 1, 189–213.
- **GM:** M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems, Harmonic Maps
  and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
- **GT:** D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics in
  Mathematics, Springer, 2001 (reprint of the 1998 edition).
- D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 4
  (1977), no. 2, 373–391.
- G. M. Lieberman, *Oblique Derivative Problems for Elliptic Equations*, World Scientific, 2013.
- E. Milakis, L. E. Silvestre, *Regularity for fully nonlinear elliptic equations with Neumann boundary data*, Comm.
  Partial Differential Equations 31 (2006), no. 8, 1227–1252.
- L. Simon, *Schauder estimates by scaling*, Calc. Var. Partial Differential Equations 5 (1997), no. 5, 391–407.
- L. C. Evans, *Partial Differential Equations*, 2nd ed., Grad. Stud. Math. 19, Amer. Math. Soc., 2010.

## Credits

Some files contain code adapted from other Apache-2.0 Lean projects. Each such file keeps the upstream copyright line
and has a `## Provenance` section. [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) lists them:
- LeanPool/lean-pool (<https://github.com/LeanPool/lean-pool>, `LeanPool/EllipticPDE/Campanato/*`, by Alejandro Soto
  Franco): Campanato average comparison and dyadic telescoping, in `Campanato/Holder.lean`;
- TauCeti (<https://github.com/TauCetiProject/TauCeti>, the Tau Ceti contributors): Green's identity and weak
  harmonicity and the mean-value property, in `Harmonic/Basic.lean` and
  `Harmonic/MeanValue.lean`, received via elliptic-bernoulli-foundations.

Several files also adapt the author's own Apache-2.0 projects. Their `## Provenance` sections name the source:
- elliptic-bernoulli-foundations (EB): the harmonic toolkit (gradient estimates, maximum principle, harmonic limits,
  the Dirichlet problem on a ball by Perron's method) and the TauCeti files above;
- parabolic-basic-theory (PBT, `ParabolicBasic/Schauder/*`): the polynomial-approximation iteration, the Hölder
  algebra, quadratic polynomials and the one-dimensional Taylor bounds;
- viscosity-solution-theory (Lake dependency `viscosity_solns`): the continuous Weyl lemma and Perron's method, used as
  a library in `Harmonic/`.

LeanPool `EllipticPDE/Regularity/Caccioppoli.lean`, TauCeti `Analysis/PDE/Caccioppoli/Basic.lean` and the calabi-yau
project's Hölder interpolation were design references only. No code was taken from them.

The Lean proofs were written by AI coding agents (Claude, by Anthropic) under the author's mathematical direction and
review. The theorem statements and proof routes were reviewed by the author. Correctness rests on Lean's kernel check,
together with the comparator challenges in `challenges/`.

## Citation

If you use this formalization, please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0 ([LICENSE](LICENSE)). Adapted third-party code is listed in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
