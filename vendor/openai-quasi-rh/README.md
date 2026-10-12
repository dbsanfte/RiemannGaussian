# Pinned OpenAI quasi-RH proof dependency

This path dependency contains the source closure of OpenAI's `7/8`
nonvanishing theorem and its sufficient `23/24` intermediate theorem,
at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a` of
https://github.com/openai/math.

The package uses Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Its local Lake configuration
exposes the necessary modules through the main project's dependency graph.
OAI sources are unchanged. `upstream-pin.json` records every file hash
and the original analytic dependency revisions.

Only four required PrimeNumberTheoremAnd modules and fifteen required
RellichKondrachov modules are included. They use OpenAI's official
compatibility patches, retained in `patches/`. The licenses are in
`LICENSE`, `PNT-LICENSE`, and `RELLICH-LICENSE`. Unrelated unfinished
source modules from the analytic dependency repositories are not vendored.

The main root imports `RiemannGaussian.ZetaQuasiRHOpenAI`, which applies
the actual upstream theorem to the unchanged frozen terminal definition.
`scripts/verify_openai_quasi_rh.py` checks source and dependency pins.
`scripts/CheckQuasiRHIntegration.lean` checks the unconditional root-chain
endpoint, namespace linters and every imported declaration's transitive
axioms. The only permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`.

The imported half-plane has a strict boundary `Re(s) > 7/8`. This is an
attributed external baseline; the full Riemann Hypothesis remains open.
