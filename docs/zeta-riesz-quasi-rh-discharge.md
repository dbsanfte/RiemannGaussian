# Frozen Riesz discharge in the current proof chain

The ordinary `RiemannGaussian` root now imports
[RiemannGaussian.ZetaQuasiRHOpenAI](../RiemannGaussian/ZetaQuasiRHOpenAI.lean),
which instantiates the transfer with the actual pinned OpenAI proof:

```lean
theorem RiemannGaussian.ZetaQuasiRHOpenAI.noPersistentError :
  RiemannGaussian.ZetaPrimeMomentTerminal.NoPersistentError
```

The project is pinned to Lean 4.34.1, Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and LeanCert revision
`7f91b6eb3567437f6cfac03ed279706603ee22f4`. The composition has no
external nonvanishing parameter or added axiom.

## Mathematical scope and attribution

The external theorem is
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, from OpenAI revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its exact target is Mathlib's
`riemannZeta`, with the strict condition `7/8 < s.re`.
The [pinned upstream source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)
and the [vendored package documentation](../vendor/openai-quasi-rh/README.md)
provide attribution, license provenance and source hashes. OAI sources are
unchanged. The four required PrimeNumberTheoremAnd and fifteen required
RellichKondrachov modules use OpenAI's official compatibility patches.

The unconditional project consequences are:

* `nonvanishing`: all heights with `7/8 < Re(s)`.
* `campaign_nonvanishing`: the original closed strip `19999/20000 ≤ Re(s)`.
* `campaign_noncoherent`: the original all-height, all-multiplicity criterion.
* `noPersistentError`: the exact original signed Chebyshev-error endpoint,
  with `1/2 < u ≤ 10001/20000`, `54 ≤ |y|`, and every positive integer `m`.
* `noncoherent_of_lt_five_eighths` and
  `strip_noncoherent_of_lt_five_eighths`: the larger strict bound `u < 5/8`.
* `no_errorSource_limit`: the literal signed error-limit exclusion on that
  larger interval, retaining `1 ≤ |y|` from its checked transfer.
* `false_of_campaign_zero`: contradiction from a nontrivial campaign zero.
* `analytic_three_fifths`, `exists_ordinary_radius_bound`, and
  `exists_coupled_geometric_bound`: the genuine fixed Cauchy radius and the
  complete joined-energy estimate, retaining all correlation credit.

The last estimate is

```text
|D_N(u,y) - Q_N(u,y)| ≤ (41/12) C_y^2 (10001/12000)^(N-1), N ≥ 65536,
```

on the original radius interval and at campaign heights. The constant may
depend on height. The frozen terminal source remains byte-for-byte unchanged
from commit `24444671cee3bf643ff1307909b961a329372a9e`, with SHA256
`1f1982b283004b821ae80f78dcf1f4f7864f61c5c2140d5277f704e20a78ad93`.

This is an attributed external baseline. The original native Riesz carrier
floor/ceiling and full RH remain open. A full contradiction still needs to
exclude the remaining right-half interval `1/2 < Re(rho) ≤ 7/8`.
The boundary `Re(s) = 7/8` is retained explicitly.

## Verification in the current project

The strict ordinary target build and default build passed with Lean 4.34.1.
The whole-project declaration lint and all 15 namespace linters on each new
module passed. The integration audit checked **6,001 imported modules,
154,320 declarations and 116,362 theorem declarations**, including private
and generated helpers. It covers all 2,943 pinned external proof modules.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in their axiom
closures. The generated project status records the same unconditional endpoint.
The [main-project verification record](zeta-riesz-quasi-rh-discharge-audit.json)
contains the source pins, local source hashes, gate results and audit counts.

Run from `riemann/formal`:

```bash
python3 scripts/verify_openai_quasi_rh.py
lake build --wfail
lake build OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion --wfail
lake env lean -DwarningAsError=true scripts/LintProject.lean
lake env lean -DwarningAsError=true scripts/CheckQuasiRHIntegration.lean
lake env lean -DwarningAsError=true scripts/GenerateProjectStatus.lean
python3 scripts/test_numerical_certificate_build_config.py
```

The integration checker imports the actual root, runs all 15 namespace
linters on both new local modules, and audits every declaration, including
private and generated helpers, in the imported project and external proof
modules. Every transitive axiom must be one of `propext`, `Classical.choice`,
or `Quot.sound`. Its detailed report is
`.lake/lean434-integration/axioms.json`. CI runs the source verifier and
integration checker in addition to the existing whole-project gates.

The migration preserves the original ordinary elaboration mode and warning
as error policy. The numerical certificate remains opt-in. Compatibility
changes update deprecated aliases, finite-product and logarithmic-derivative
APIs, and proof steps whose conversion goals changed. Two generic product
integrability helpers now state the newer Mathlib `SFinite` requirement:
`integrable_etaSignedCompletedPair` and
`integrable_gaussianLaplaceHeatJoint`. Their existing callers already have
finite or s-finite measures; their endpoint statements gain no premise.

The older Zeta23 Sobolev/Fourier compatibility copies now use namespace
`Zeta23.FromPNTPlus`, isolating 152 overlapping global declarations from the
OpenAI dependency. Their mathematical definitions and statements are
preserved under the qualified names. No OpenAI proof source was changed.

Existing untracked research leaves remain outside the registered build roots.
Inventory and explorer checks use a snapshot of the actual registered source
closure, preserving those held files in the main workspace. Lean builds,
linters, status generation and the complete axiom audit run in the actual
main project.

## Historical isolated checkpoint

The earlier standalone Lean 4.34.1 project verified the sufficient `23/24`
baseline and the exact frozen terminal, with 1,474 imported modules,
49,523 declarations and 41,126 theorem declarations. That standalone
verification remains a separate historical snapshot. The live project uses the stronger
`7/8` proof through its own root chain; the historical isolated counts are
not the current integration audit counts.
