# Comparator Challenges

This directory contains the release comparator workspaces for the 16 headline theorems of
`BasicElliptic`, covering the nine targets of `formalization.yaml`. The targets are grouped into
two workspaces by the library modules their solutions import, since Comparator's cost is mostly
per workspace (it exports and replays the solution's whole import closure):

- `divergence-form`: the divergence-form targets and Campanato's characterization, whose solutions
  import 61 of the library's 87 modules;
- `nondivergence-form`: the nondivergence-form targets and the polynomial-approximation bridge,
  whose solutions import the other 26 modules (38 with shared infrastructure).

Each subdirectory is a standalone Lake workspace with:

- `Vocabulary.lean`: the library definitions the statements use, restated over Mathlib only (see
  below);
- `Challenge.lean`: the trusted statement surface. It imports Mathlib modules only: the vocabulary is
  copied into a generated block at its top, followed by the challenge statements with `sorry`;
- `Solution.lean`: the solution, importing the library modules that prove the statements;
- `config.json`: comparator module names, theorem names and permitted axioms;
- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`: workspace metadata pinned through the
  parent project.

Every `.lean` file is a Lean module.

## Vocabulary files

The library vocabulary is restated with the library's names, the library's definitions verbatim,
and the library's declaration order, one part per library file:

| Vocabulary part | Library file | Definitions |
|---|---|---|
| half spaces | `Basic/HalfSpace.lean` | `halfSpace`, `openHalfSpace`, `flatPart`, `halfBall`, `reflect`, `fold`, `evenExt`, `oddExt`, `reflectField`, `reflectCoeff` |
| Hölder spaces | `Defs/Holder.lean` | `eHolderSeminormOn`, `holderSeminormOn`, `ContDiffHolderOn`, `regionOsc` |
| ellipticity | `Defs/Elliptic.lean` | `IsUniformlyElliptic`, `IsSymmetricOn` |
| divergence form | `Defs/Div.lean` | `IsTestFn`, `divergence`, `Div.IsWeakEqOn`, `Div.IsWeakSolWithin`, `Div.IsWeakSolOn`, `Div.IsConormalSolOn`, `Div.IsWeakSolOnField`, `Div.IsQuasilinearConormalSolOn` |
| nondivergence form | `Defs/Nondiv.lean` | `Nondiv.op`, `Nondiv.IsSolOn`, `Nondiv.HasConormalBC`, `Nondiv.HasDirichletBC` |

Each workspace restates only the parts its statements need. Each part drops the library file's
theorems and imports the same Mathlib modules as the library file; workspaces also import the
Mathlib modules of the corresponding `BasicElliptic/Statements/*` file, so that instance search
elaborates the statements as the library does. `scripts/challenge-prep.py sync` copies
`Vocabulary.lean` into the generated block of `Challenge.lean`, and `scripts/challenge-prep.py
check` checks that the copy is current. Comparator then checks every restated definition reached
from a challenge statement against the library's, by name and by value.

These definitions are built from Mathlib notions (`HolderOnWith`, `ContDiffOn`,
`iteratedFDerivWithin`, `fderivWithin`, Bochner integrals against the Haar `volume`, `ContDiff`
test functions with compact support), and a referee should read them: the challenges certify the
theorems for exactly these definitions. Points to note:

- Weak solutions in divergence form are classical-regularity functions: `w ∈ C¹` on the region
  (derivatives within the region) satisfying the weak identity against `C¹_c` test functions. The
  theorems are therefore regularity statements for `C¹` weak solutions, not for `H¹` weak
  solutions; no Sobolev spaces are used.
- The weak identity `∫ ⟪a ∇w, ∇φ⟫ = ∫ ⟪G, ∇φ⟫ + ∫ f φ` is the weak form of
  `-div (a ∇w - G) = f`. In conormal problems the tests need not vanish on the flat part.
- `holderSeminormOn α f s` is the real part of the extended Hölder seminorm, so it is `0` when the
  seminorm is infinite. The estimate challenges are meaningful together with the corresponding
  qualitative challenges, which give finiteness.
- The nondivergence trace `tr (a(y) D²w(y))` is written `∑ i, D²w(y) (a(y) eᵢ, eᵢ)` over the
  orthonormal basis `stdOrthonormalBasis ℝ E`, which is basis-independent.

## Challenge set

| Workspace | Target (`formalization.yaml`) | Statements | Library theorems used by the solution |
|---|---|---|---|
| `divergence-form` | `div-interior-c1alpha` | interior `C^{1,α}` regularity and the scaled estimate, divergence form, `a` not necessarily symmetric (Giaquinta–Martinazzi; Gilbarg–Trudinger) | `Div.contDiffHolderOn_one_of_isWeakSolution`, `Div.c1Holder_ball_estimate` |
| | `div-conormal-c1alpha` | conormal flat-boundary `C^{1,α}` regularity and the scaled estimate at an arbitrary centre, `a` symmetric (Giaquinta–Martinazzi; Gilbarg–Trudinger (Dirichlet analogue)) | `Div.contDiffHolderOn_one_halfBall_of_isConormalSolution`, `Div.c1Holder_halfBall_estimate` |
| | `div-strong-weak-reflection` | strong solutions of the linear and quasilinear conormal problems are weak solutions; the even reflection of a conormal weak solution with measurable coefficients solves the reflected problem on the full ball | `Div.isConormalSolOn_of_strong`, `Div.isQuasilinearConormalSolOn_of_strong`, `Div.IsConormalSolOn.evenReflect` |
| | `div-conormal-c2alpha` | linear conormal `C^{2,α}` regularity from `C^{1,α}` coefficients | `Div.contDiffHolderOn_two_halfBall_of_c1Holder_coeff` |
| | `div-quasilinear-conormal` | `C^{k+1}` regularity of `C¹` quasilinear conormal weak solutions of `div Φ(∇w) = 0`, and the scaled small-gradient estimate of `∇w` and `D²w` at the centre | `Div.contDiffOn_halfBall_of_quasilinear_conormal`, `Div.quasilinear_conormal_estimate` |
| | `campanato-characterization` | Campanato's characterization of Hölder continuity on closed half balls (Campanato 1963; Giaquinta–Martinazzi) | `holderOnWith_of_campanato` |
| `nondivergence-form` | `nondiv-interior-schauder` | interior Schauder regularity and the scaled estimate, nondivergence form (Gilbarg–Trudinger) | `Nondiv.contDiffHolderOn_two_of_isSolution`, `Nondiv.schauder_ball_estimate` |
| | `nondiv-boundary-schauder` | flat-boundary Schauder regularity, nondivergence form, under the conormal-compatible condition or the Dirichlet condition (Gilbarg–Trudinger, flat case) | `Nondiv.schauder_halfBall_conormal`, `Nondiv.schauder_halfBall_dirichlet` |
| | `polynomial-approximation-bridge` | uniform pointwise second-order polynomial approximation on a bounded convex set with nonempty interior gives `C^{2,α}`, with `Du = P1` | `contDiffHolderOn_two_of_polyApprox` |

A Comparator failure is reported per workspace; its log names the theorem that failed.

These are the 16 headline theorems of the README and `scripts/check_axioms.lean`. The statements
are spelled out in full in each `Challenge.lean`; they do not refer to the library's `…Statement`
definitions. There are no model-case or non-vacuity challenges (for example, a concrete solution to
which a headline theorem applies).

## Toolchain

- Lean: `leanprover/lean4:v4.35.0-rc3`
- Mathlib: `v4.35.0-rc3` (`c55e6e7`)
- viscosity_solns `v0.4.0` and AleksandrovDifferentiability `v0.4.0`: pinned through the parent
  `lake-manifest.json`
- Comparator: `leanprover/comparator` at `fd5d5bcf14177b187f66d4502071268d877887c3`, with
  lean4export `66f1fb4bc256072069767fce52d39480e4524869` and landrun
  `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, pinned in `scripts/release-comparator.sh` and
  recorded in `formalization.yaml`

Every workspace sets `packagesDir = "../../.lake/packages"` in its `lakefile.toml` (and records
the same folder in its `lake-manifest.json`), so both share the root workspace's dependency
checkouts and builds. The manifests lock the same revisions as the root manifest. Each workspace
defaults to its `Vocabulary` and `Challenge` targets only, so a plain `lake build` never
elaborates `Solution.lean`. The workspaces set `autoImplicit = false`.

## Acceptance

In a trusted checkout, build the root library first, then the workspaces, then run the local
checks:

```sh
lake build
./scripts/check-challenges.sh
./scripts/fingerprint-challenges.sh
```

`scripts/check-challenges.sh` (run by CI) builds `Vocabulary`, `Challenge` and `Solution` in every
workspace and checks that every solution theorem depends on exactly `propext`, `Classical.choice`
and `Quot.sound`. It does not compare statements. `scripts/build-challenges.sh --trusted-all`
builds the same targets without the axiom check.

`scripts/fingerprint-challenges.sh` emulates Comparator's statement and definition-equality
check. For each workspace, it hashes the types and definition values of the challenge theorems and
of every `BasicElliptic` constant they depend on, once in the `Challenge` environment and once in
the `Solution` environment, and diffs the results. It does not replay proofs or check axioms.

For a Comparator release run, treat `Solution.lean` as potentially adversarial, and review and
trust each workspace's `Vocabulary.lean`, `Challenge.lean`, `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain` and `config.json`. The release workflow `.github/workflows/release-comparator.yml`
(dispatched by hand, and run on `release/**` branches and `v*` tags) then:

1. validates the challenge inventory against `formalization.yaml`
   (`scripts/check-formalization-manifest.rb --metadata-only`);
2. installs the pinned Comparator tools (`scripts/release-comparator.sh install`);
3. builds only the trusted `Vocabulary` and `Challenge` targets outside the sandbox;
4. runs Comparator in its sandbox on each workspace's `config.json`, without first building
   `Solution` (`scripts/release-comparator.sh run`), which checks statement and definition
   equality and that each theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`;
5. uploads an attestation (`comparator-report/attestation.json` and the logs).

Per-commit CI only elaborates the workspaces and checks the solutions' axioms; exact equality
between the trusted statements and the solution statements is checked only by the release
comparator workflow.

**Status.**
- Both build-challenges modes are green locally.
- `fingerprint-challenges.sh` reports both workspaces IDENTICAL.
- `check-challenges.sh` reports exactly the three permitted axioms for all 16 solution theorems.
- No Comparator run has been recorded yet. Each release is checked by a Comparator run on the
  public commit, and its attestation is attached to the GitHub release.

## References

- S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup.
  Pisa (3) 17 (1963), 175–188.
- L. A. Caffarelli, *Interior a priori estimates for solutions of fully non-linear equations*,
  Ann. of Math. (2) 130 (1989), no. 1, 189–213.
- M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Edizioni della Normale, Pisa, 2012.
- D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, reprint
  of the 1998 edition, Classics in Mathematics, Springer, 2001.
- D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Scuola Norm. Sup.
  Pisa Cl. Sci. (4) 4 (1977), no. 2, 373–391.
- G. M. Lieberman, *Oblique Derivative Problems for Elliptic Equations*, World Scientific, 2013.
