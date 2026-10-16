# RiemannGaussian

[![Lean Action CI](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

RiemannGaussian is an open research project building toward a complete,
kernel-checked Lean proof of the Riemann hypothesis. The repository contains
the evolving Lean 4 proof development and supporting analytic and finite-model
theory. The proof is not complete; in the meantime, the extensive Lean theorems and formalizations are provided to the wider community. Only declarations accepted by Lean and the
repository's verification gates count as established results.

> **Research agents:** GPT-5.6 Sol, GPT-6.1 Sol, and GPT-6 Astra with **Max** reasoning effort, running in the
> **Codex CLI harness**.

## Proved Zero-Free Region

[![Zero-free region comparison: independent native analytic bounds with a magnified right-edge view](docs/zero-free-regions/comparison.svg)](docs/zero-free-regions/comparison.svg)

This comparison records the independent native analytic bounds. The stronger
imported OpenAI half-plane is stated below.
[Comparison data, sources and scope](docs/zero-free-regions/README.md)
· [Graph proof audit](docs/zero-free-regions/audit.json).

**The project now imports OpenAI's all-height `7/8` nonvanishing proof**, pinned
at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a` and rebuilt with the
ordinary Lean root. For the meromorphic zeta function, its region is

<table>
<tr><td>

```math
\boxed{\Re(s)>\frac78,\quad s\ne1
\quad\Longrightarrow\quad\zeta(s)\ne0.}
```

</td></tr>
</table>

The bound is strict at `7/8` and has no height threshold. This is an attributed
external result. It discharges the exact frozen Riesz `NoPersistentError`
condition and supplies the complete coupled geometric estimate. Full RH and
the original native carrier floor/ceiling remain open.
[Lean composition](RiemannGaussian/ZetaQuasiRHOpenAI.lean)
· [Scope, source pins and verification](docs/zeta-riesz-quasi-rh-discharge.md)
· [Explore the imported discharge](https://dbsanfte.github.io/RiemannGaussian/#endpoint=openai-quasi-rh).

### [▶ Open the interactive theorem explorer](https://dbsanfte.github.io/RiemannGaussian/)

[![Click to explore the zero-free theorem chain, grouped by mathematical family](docs/theorem-explorer/preview.svg)](https://dbsanfte.github.io/RiemannGaussian/)

Zoom, expand branches, inspect theorem metadata and open exact Lean source lines.
[Family metadata](docs/theorem-explorer/metadata.json)
· [Proof audit](docs/theorem-explorer/audit.json)
· [Reproduce locally](docs/theorem-explorer.md).

The independent native explicit and eventual bounds remain documented in
[the unified region](docs/zeta-unified-zero-free.md) and
[the Vinogradov–Korobov union](docs/vinogradov-zero-free.md), with their exact
threshold scopes.

## Proved Numerical Certificate: 67.31%

[![Numerical certificate verification](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/numerical_certificate.yml/badge.svg)](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/numerical_certificate.yml)

**Lean proves that at least 67.31% of zeta zeros are simple and on the critical
line**, in every sufficiently large cumulative `(0, T]` and dyadic `(T, 2T]`
window. The denominator counts analytic multiplicity; **the starting height
is unevaluated**. This improves Anthropic/Zeta23's two-thirds certificate,
including its stronger underlying coefficient of approximately **67.25007%**.

The published checkpoint was verified with Lean 4.33.1. Its frozen input
fingerprint remains checked; the complete optional audit under the project's
new Lean 4.34.1 toolchain is pending.

### [▶ Explore the 67.31% certificate proof](https://dbsanfte.github.io/RiemannGaussian/numerical-certificate/)

[![Numerical certificate comparison: two thirds, the Anthropic/Zeta23 coefficient and our improved coefficient, with the proved 67.31% bound marked](docs/numerical-certificate/comparison.svg)](https://dbsanfte.github.io/RiemannGaussian/numerical-certificate/)

Click the chart to inspect the continuous cover, analytic transfer, exact
Lean source lines and proof audits.
[Enlarge chart](docs/numerical-certificate/comparison.svg)
· [Lean proof](RiemannGaussian/External/Zeta23SevenWindowIntegerCertificate.lean)
· [Successful complete verification](https://github.com/dbsanfte/RiemannGaussian/actions/runs/34802730942)
· [Full axiom audit](docs/numerical-certificate-audit.json)
· [Sources, metadata and reproduction](docs/numerical-certificate.md).

<!-- RH_DIRECTION:START -->
## Current RH Proof Direction

### [▶ Explore the current RH proof chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/)

[![Current RH proof explorer: the checked active theorem chain, grouped by mathematical family](docs/rh-proof-explorer/preview.png)](https://dbsanfte.github.io/RiemannGaussian/rh-proof/)

Study the global Suzuki signal and complete Gaussian/Weil correlation using actual integer arithmetic. An independent one-sided subexponential bound for the signed Suzuki signal would imply RH for all multiplicities through the checked Landau criterion. OpenAI's imported 7/8 baseline discharges the restricted Riesz terminal. The original carrier bounds and the remaining RH interval are open. Finite-height coverage remains a separate track.

[Direction and remaining obstruction](docs/rh-proof-direction.md)
· [Campaign metadata](docs/rh-proof-explorer/metadata.json)
· [Proof audit](docs/rh-proof-explorer/audit.json).

### Latest Update

**Semiprime checkpoint and portable certificate source links.** Registers three semiprime arithmetic proof modules with explicit hypotheses, archives the research evidence, and makes historical certificate source links independent of locally installed toolchains. The guaranteed sixth-rate factorization algorithm remains unproved.
The semiprime research goal is paused. Universal cheap acquisition and the complete Lean bit-complexity proof remain open; the RH arithmetic obligation is unchanged.
[Current checked endpoint](RiemannGaussian/SuzukiLaplaceCompensator.lean#L246)
· [Proof details](docs/semiprime-factorisation-investigation.md#2026-10-16-publication-checkpoint).
<!-- RH_DIRECTION:END -->

## Notable Formalisations

Ten major results and frameworks. The linked Lean sources state their exact
hypotheses; the [family index](docs/theorem-families/README.md) covers the full library.

| Area | What is formalised | Lean entry points |
| --- | --- | --- |
| **Zero-free proof chain** | The pinned OpenAI all-height `7/8` proof and frozen Riesz discharge, alongside independent native explicit and eventual Littlewood/VK bounds. | [OpenAI composition](RiemannGaussian/ZetaQuasiRHOpenAI.lean), [native explicit region](RiemannGaussian/ZetaUnifiedZeroFree.lean), [native eventual union](RiemannGaussian/ZetaVinogradovSummedZeroFree.lean) |
| **67.31% numerical certificate** | At least 67.31% of zeros are simple and on the critical line in sufficiently large cumulative and dyadic windows. The threshold is unevaluated; exhaustive verification is optional. | [literal-count certificate](RiemannGaussian/External/Zeta23SevenWindowIntegerCertificate.lean) |
| **Gaussian/Weil explicit formula** | The arithmetic Gaussian expression, including prime-power and Archimedean terms, equals the complete multiplicity-weighted symmetric zero sum for every positive width. | [canonical explicit formula](RiemannGaussian/GaussianXiLogDerivativeGrowth.lean#L1235) |
| **Gaussian heat and reflected-zero Grams** | The complete Gaussian correlation equals the boundary heat-residue sum. Its vanishing at positive heat time is equivalent to RH; that vanishing remains unproved. | [correlation identity and RH equivalence](RiemannGaussian/RiemannXiBoundaryGaussianGram.lean#L187) |
| **Suzuki arithmetic and spectral formulas** | Suzuki's arithmetic function equals its spectral expansion in the safe half-plane. The literal arithmetic Psi is strictly positive on a nonzero punctured neighbourhood of the origin. | [spectral identity](RiemannGaussian/RiemannXiSuzukiWeilVerticalLimit.lean#L462), [local positivity](RiemannGaussian/RiemannXiSuzukiPointwiseLocalPositivity.lean#L298) |
| **Vinogradov moments and Dirichlet sums** | Explicit degree-dependent moments and actual damped Dirichlet savings feed a proved VK zero-free region. Its coefficient is conservative and its starting height unevaluated. | [moment and block bounds](docs/vinogradov-narrow-packet.md), [complete zero-free proof](docs/vinogradov-zero-free.md) |
| **Exact phase optimiser and arithmetic floor** | The specified phase cost has a unique eight-frequency optimiser across all feasible finite or infinite integer-frequency families, with a proved arithmetic floor. | [exact optimiser](RiemannGaussian/ZetaPhaseExactOptimizer.lean), [arithmetic floor and exclusion criterion](RiemannGaussian/ZetaPhaseBinomialScale.lean) |
| **Eta heat and continuous phase matrices** | Exact eta heat/spectral correspondence and small-width matrix coercivity for distinct integer probes retain the full complex Gram correlations. | [heat/spectral identity](RiemannGaussian/EtaSupportGapGaussianSpectral.lean), [continuous matrix coercivity](RiemannGaussian/Hybrid/EtaSupportGapPhaseCoercivity.lean#L276) |
| **Prime-source characterization and frozen Riesz reduction** | Target-strip nonvanishing is equivalent to absence of coherent negative-integer prime moments and their actual Chebyshev-error transform. The all-height arithmetic premise remains open. | [terminal theorem](RiemannGaussian/ZetaPrimeMomentTerminal.lean), [reduction and audited no-gos](docs/zeta-riesz-terminal.md) |
| **Montgomery–Vaughan weighted Hilbert inequality** | An attributed Apache-2.0 formalisation with exact diagonal constant 13 and bilinear constant 26. | [both inequalities](RiemannGaussian/MontgomeryVaughan/Final.lean#L28) |

## Accomplishments

Ten major results, selected for mathematical significance. Detailed auxiliary
results and their exact scope remain in the [family index](docs/theorem-families/README.md)
and the [proof inventory](docs/proof-status.json).

- **A proved explicit zero-free region at every height.** The
  [complete explicit region](RiemannGaussian/ZetaUnifiedZeroFree.lean)
  and [proved eventual Littlewood/Vinogradov–Korobov union](RiemannGaussian/ZetaVinogradovSummedZeroFree.lean)
  form the region displayed above. Eventual thresholds are unevaluated.
  The [extended comparison](RiemannGaussian/ZetaGaussianExpandedComparison.lean)
  and [literature audit](docs/zero-free-literature-frontier.md) state precisely
  which benchmark functions it improves and where.
- **The critical high-order Vinogradov moment exponent, with every positive ε.**
  [The global theorem](RiemannGaussian/VinogradovCriticalExponent.lean)
  covers every k≥2, u≥k at all sufficiently large endpoints without an
  assumed moment estimate. A [finite descent](docs/vinogradov-linear-constants.md)
  now retains the cost A^n·k! at every positive integer cutoff, with an
  explicit profile multiplier. A [quantitative continuation](docs/vinogradov-narrow-packet.md)
  now pays all degree-dependent moment coefficients at the stated order.
  The full Gaussian degree window now also gives a [power saving for original
  Dirichlet blocks](docs/vinogradov-gaussian-power-saving.md) throughout the
  stated continuous intervals, including the actual zeta damping. Gaussian
  costs and the complete original block estimate have explicit constants.
- **At least 67.31% of nontrivial zeros are simple and on the critical line.**
  [The literal-count theorem](RiemannGaussian/External/Zeta23SevenWindowIntegerCertificate.lean)
  proves this for every sufficiently large cumulative or dyadic window.
  The starting height is unevaluated. We reproduce the
  [Anthropic/Zeta23 baseline](RiemannGaussian/External/Zeta23Baseline.lean)
  and improve it with unequal seven-point weights and a complete checked cover.
  [Exact coefficient, provenance and optional cached verification](docs/numerical-certificate.md).
  No `13/18` certificate is claimed.
- **An exact phase optimiser over all admissible integer frequencies.**
  [existsUnique_phaseContactOptimizer](RiemannGaussian/ZetaPhaseExactOptimizer.lean)
  proves existence and uniqueness, including infinite competitors, for the
  specified cost and shift. Its tiny higher frequencies are necessary for
  that optimum; this is not an intrinsic frequency count for zeta zeros.
- **A complete Gaussian prime identity coupled to the signed strip detector.**
  [The complex identity](RiemannGaussian/ZetaGaussianSmoothedIdentity.lean)
  retains the actual prime series, xi response, pole and completion.
  [The full phase-family theorem](RiemannGaussian/ZetaGaussianStripPhaseFamily.lean)
  couples all three arithmetic responses before using positivity, preserving
  selected zeros and multiplicities in the chain to the proved region.
- **A height-uniform direct zeta truncation remainder.**
  [norm_remainder_le_power](RiemannGaussian/ZetaEulerUniformRemainder.lean)
  bounds the actual Euler remainder by `(N+1)^(-Re(s))` throughout
  `0<Re(s)<=1` once `N+1>=abs(Im(s))`. Its Fourier argument feeds the
  actual line estimates and general phase-family budgets.
- **Uniform decay of the complete squarefree divisor matrix.**
  [The actual band transport](RiemannGaussian/ZetaSquarefreeGaussianBand.lean)
  and [moving-matrix theorem](RiemannGaussian/ZetaSquarefreeGaussianSieve.lean)
  give one vanishing allowance across the explicit center band, including
  moving selected zeros, cutoffs and bounded complex weights. Ordinary
  primes remain included; the independent isolated prime-tail bound is open.
- **A uniform critical heat law on the literal eta support.**
  [The Gaussian leakage theorem](RiemannGaussian/EtaSupportGapGaussian.lean#L349)
  has one explicit error bound for every ordinate. Its
  [spectral identity](RiemannGaussian/EtaSupportGapGaussianSpectral.lean)
  retains the actual eta/gap correlation, and the
  [signed polynomial heat law](RiemannGaussian/EtaPolynomialHeatReflection.lean)
  preserves the reflected endpoint structure.
- **Quantitative positivity for the full continuous eta phase matrix.**
  [The coercivity theorem](RiemannGaussian/Hybrid/EtaSupportGapPhaseCoercivity.lean#L276)
  retains all mixed phase interference and an explicit dimension cost.
  [The cubic-phase extension](RiemannGaussian/Hybrid/EtaCubicHeatGram.lean)
  proves convergence of the full mixed matrix and positivity of its limit.
  This auxiliary positivity does not close the reflected RH criterion.
- **Geometric separation of literal eta features for every finite zero window.**
  [The packed-feature rank theorem](RiemannGaussian/Hybrid/EtaGeometricPackedFeatureRank.lean#L210)
  supplies one odd prime sampling base making all sufficiently late feature
  blocks linearly independent, with completion factors retained. It
  distinguishes the represented zeros without implying they lie on the
  critical line.

All entries have checked Lean proofs. Attribution is explicit for external
results; wider priority of the project-developed auxiliary mathematics has
not been established. RH remains open.

## Repository Structure

**[Browse the complete theorem-family index](docs/theorem-families/README.md)**
for Gaussian heat, Suzuki, eta, phase positivity, hybrid matrices, arithmetic
and the other families. It is generated from the explorer's shared metadata.

| Location | Contents |
| --- | --- |
| [RiemannGaussian/](RiemannGaussian/) · [root imports](RiemannGaussian.lean) | Lean sources, including the `Hybrid`, `HermitianRankTrace`, `MontgomeryVaughan` and `External` subdirectories |
| [docs/](docs/) · [theorem explorer](docs/theorem-explorer/) | Proof notes, literature audits, family indexes and generated proof metadata |
| [vendor/zeta23/](vendor/zeta23/) | Pinned external proofs, licenses and provenance |
| [scripts/](scripts/) | Lean audits, metadata generation and browser checks |
| [.github/workflows/](.github/workflows/) · [.githooks/](.githooks/) | Remote and local verification gates |
| [.devcontainer/](.devcontainer/) · [AGENTS.md](AGENTS.md) | Development environment and proof-maintenance rules |

## Rigor and Verification

The formal target is Mathlib's `RiemannHypothesis`. Every accepted proof
slice must preserve a continuous chain from imported Mathlib definitions to
the current frontier.

The enforced checks are:

- no Lean source may contain `sorry`, `admit`, or a direct use of Lean's
  unresolved-proof axiom;
- the entire library builds with warnings treated as errors;
- all registered project declaration linters pass;
- every compiled project declaration is audited for unresolved-proof
  dependencies, and project-defined axioms are rejected;
- displayed frontier theorems may depend only on Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms;
- the generated SVG and JSON must exactly match the compiled environment; and
- GitHub Actions must pass on the exact pushed commit before it is reported
  as remotely verified; local proof work can continue while CI runs.

Numerical experiments, symbolic calculations, research notes, and literature
dispatches are used only to discover candidate mathematics. Nothing from them
is trusted until it has been re-derived in Lean and passed every gate.

## Build and Check

The project is pinned to Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. With
[elan](https://github.com/leanprover/elan) installed, run from the repository
root:

```bash
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true scripts/LintProject.lean
lake env lean -DwarningAsError=true scripts/GenerateProjectStatus.lean
git diff --exit-code -- docs/proof-status.json docs/proof-status.svg
```

Enable the tracked pre-commit gate once per clone:

```bash
git config core.hooksPath .githooks
```

The hook repeats the source-placeholder scan, warning-as-error build,
whole-project lint, compiled-environment audit, dashboard freshness check, and
staged whitespace check. GitHub Actions remains authoritative because local
hooks can be bypassed.

## Research Method

Work proceeds in small theorem slices. Each slice isolates a real obstruction,
proves a reusable Lean lemma without weakening definitions or moving the
obstruction into assumptions, audits its axioms, runs all local gates, and is
then committed and pushed. Work resumes only after CI succeeds on that exact
commit.

Every representation is treated as an information-flow decision. Rich source
objects are retained while norms, traces, asymptotic limits, and triangle
bounds are exposed only as downstream views; phase, sign, orientation,
multiplicity, scale, and channel colour are collapsed only when a proved
estimate gains leverage from doing so.

Lean is also used as a research engine for deriving and testing new
mathematics across analysis, operator theory, spectral theory, number theory,
and mathematical physics. Numerical or symbolic experiments may suggest a
lemma, but only a kernel-checked theorem grounded in the existing chain counts
as progress. See [AGENTS.md](AGENTS.md) for the full methodology.

## License

Copyright 2026 David Sanftenberg.

RiemannGaussian is licensed under the [Apache License, Version 2.0](LICENSE)
(`Apache-2.0`). Third-party source retains its original copyright and
attribution notices; see the notices for
[Zeta23](vendor/zeta23/NOTICE),
[OpenAI's Quasi RH proof and analytic dependencies](vendor/openai-quasi-rh/README.md),
[HermitianRankTrace](RiemannGaussian/HermitianRankTrace/NOTICE), and
[MontgomeryVaughan](RiemannGaussian/MontgomeryVaughan/NOTICE).
