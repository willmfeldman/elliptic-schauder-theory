# Third-party code

This repository is released under the Apache License 2.0. Files adapted from third-party projects keep the upstream
copyright line (in the file header or, for files that also contain original code, in the `## Provenance` section of the
module docstring) and describe the extent of the adaptation there.

| Upstream | License | Upstream copyright | Files here |
|---|---|---|---|
| LeanPool/lean-pool, <https://github.com/LeanPool/lean-pool>, commit `2d2ff0720fb4979f0265226ee62f1d573d0a9085`: `LeanPool/EllipticPDE/Campanato/{Basic,Compare,Telescope,Holder}.lean` | Apache-2.0 | Copyright (c) 2026 Alejandro Soto Franco. All rights reserved. | `BasicElliptic/Campanato/Holder.lean` (average comparison `sq_ballAverage_sub_le`, `abs_ballAverage_sub_half_le`, `abs_ballAverage_sub_of_dist_le`; dyadic telescoping `abs_ballAverage_sub_dyadic`; adapted) |
| TauCeti, <https://github.com/TauCetiProject/TauCeti>, commit `90cca67c0c8e91cd30b0d46cb58101f8c5c59236`: `TauCeti/Analysis/Sobolev/WeakDeriv/Laplacian.lean` | Apache-2.0 | Copyright (c) 2026 The Tau Ceti contributors. All rights reserved. | `BasicElliptic/Harmonic/Basic.lean` (`integral_laplacian_mul_eq_integral_mul_laplacian`, `HarmonicOnNhd.weaklyHarmonicOn`; adapted, via elliptic-bernoulli-foundations) |
| TauCeti, same commit: `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean` | Apache-2.0 | Copyright (c) 2026 The Tau Ceti contributors. All rights reserved. | `BasicElliptic/Harmonic/MeanValue.lean` (`HarmonicOnNhd.setIntegral_ball_eq`; via elliptic-bernoulli-foundations) |

TauCeti has no `NOTICE` file at the cited commit (recorded in `Harmonic/Basic.lean`).

LeanPool/lean-pool **does** have a `NOTICE` file at the cited commit. As Apache-2.0 §4(d) requires, the attribution
notices relevant to the adapted code are reproduced here verbatim (from `NOTICE`, commit
`2d2ff0720fb4979f0265226ee62f1d573d0a9085`):

```
Lean Pool
=========

Copyright the Lean Pool contributors and the respective project authors.

Lean Pool is licensed under the Apache License, Version 2.0. See the LICENSE
file for the full license text.

Lean Pool is an aggregation of third-party Lean 4 formalizations. Each project
under LeanPool/ is the work of its original authors, who retain copyright as
recorded in the per-file headers and in the project registry. This NOTICE file
records, for every pooled project, the upstream repository it was imported from
and the license under which it was originally published.

[...]
Projects originally licensed under the Apache License, Version 2.0
[...]
  LeanPool/EllipticPDE               https://github.com/alejandro-soto-franco/EllipticPDE
```

Code adapted from the author's own Apache-2.0 projects (elliptic-bernoulli-foundations, parabolic-basic-theory,
viscosity-solution-theory) is credited in the `## Provenance` sections of the files concerned and in the README. Files
that cite other projects only as design references contain no code from them.

Lake dependencies are used as ordinary libraries and are not redistributed here: Mathlib (Apache-2.0) and
viscosity-solution-theory (`viscosity_solns`, Apache-2.0, which pulls in aleksandrov-differentiability, Apache-2.0).
