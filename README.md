# RiemannGaussian

[![Archive RH CI](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/alpoge_archive_ci.yml/badge.svg)](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/alpoge_archive_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

## A Shorter Lean Proof of the Riemann Hypothesis

RiemannGaussian’s principal-character optimisation proves Mathlib’s
`RiemannHypothesis` using **165,070 archive modules**, a reduction of
**10,104 modules (5.8%)** from our earlier 175,174-module route.
[Explore the shorter proof](https://dbsanfte.github.io/RiemannGaussian/rh-proof/)
· [Checked Lean theorem](scripts/CheckAlpogePrincipalArchivedGeometryRH.lean#L710).

The original mathematical proof and Lean archive are due to **Levent Alpöge,
working with Claude**. Alpöge released the archive with his 20 November 2026
announcement. [Alpöge’s original announcement](https://alpo.ge/remark.pdf).

The theorem says that every nontrivial zero `s` of the Riemann zeta function
satisfies

```math
\Re(s)=\frac{1}{2}.
```

Our original optimisation constructs the arithmetic window directly for the
principal character and uses one family of reciprocity-based bundles for the
geometric comparisons. This removes the archive’s general shape and
all-character assembly from the import closure.
[Proof assembly and module counts](docs/research-evidence/alpoge-archive-rh/README.md).

Lean 4.33.1 checked the theorem with no hypotheses. Standalone kernel replay
passed locally, and the axiom audit reported only `propext`,
`Classical.choice` and `Quot.sound`.
[Archive verification workflow](.github/workflows/alpoge_archive_ci.yml).

## Verify the Shorter Proof

The archive workflow checks the public download by SHA-256 and mounts its
compiled `.olean` files as a read-only filesystem. GitHub Actions caches
the packed image under a key tied to the public archive checksum. The
verifier elaborates 31 local modules with Lean 4.33.1 and replays the final
kernel declaration. [Pinned compiled archive](https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/tree/9036e64326acf4acfae159b96664e9708445c1d1)
· [Source pins and local setup](docs/research-evidence/alpoge-archive-rh/README.md).

```sh
python3 scripts/verify_alpoge_archive_rh.py /path/to/extracted/lean /path/to/public/objects --sandbox
```

## Related Research

- At least 67.31% of nontrivial zeros in sufficiently large cumulative and
  dyadic windows have multiplicity one. The starting height is unevaluated.
  [Simplicity certificate](docs/numerical-certificate.md).
- Earlier native analytic estimates and Gaussian–Suzuki theory.
  [Zero-free bounds and provenance](docs/zero-free-regions/README.md)
  · [Native theorem explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/native.html).
- Deterministic semiprime factoring.
  [Lean proofs and runtime bounds](https://dbsanfte.github.io/RiemannGaussian/semiprime-proof/).

## Native Library

The native library uses Lean 4.34.1 and its own pinned Mathlib revision.
[Native Lean root](RiemannGaussian.lean)
· [Theorem families](docs/theorem-families/README.md)
· [Native CI](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml).

With elan installed, run from the repository root. On Linux the build may
require `sudo sysctl -w vm.max_map_count=262144`. [Install elan](https://github.com/leanprover/elan).

```sh
lake exe cache get
lake build --wfail
```

Contributor checks cover linting, generated proof assets and the commit hook.
[Development and verification rules](AGENTS.md#mandatory-local-gates).

## License

Copyright 2026 David Sanftenberg. RiemannGaussian is licensed under the
[Apache License, Version 2.0](LICENSE). Third-party sources retain their
original attribution and terms.
