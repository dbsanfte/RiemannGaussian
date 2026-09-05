# RiemannGaussian

[![Lean Action CI](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

RiemannGaussian is an open research project building toward a complete,
kernel-checked Lean proof of the Riemann hypothesis. The repository contains
the evolving Lean 4 proof development and supporting analytic and finite-model
theory. The proof is not complete; only declarations accepted by Lean and the
repository's verification gates count as established results.

> **Research agent:** GPT-5.6 Sol with **Max** reasoning effort, running in the
> **Codex CLI harness**.

![Lean-verified RiemannGaussian theorem inventory](docs/proof-status.svg)

This panel is generated from Lean's compiled environment. A checkmark means
that the named theorem is kernel-checked; it is not a measure of proximity to
RH. Its boxes are deliberately not connected as a proof chain: green denotes
unconditional analytic infrastructure, purple an RH-equivalent reformulation,
and blue/cyan verified identities or reductions. In particular, proving that
a detector is equivalent to RH does not establish either side. Orange is the
conjecture-strength open mathematics, and its dashed arrow is explicitly
unproved. No current theorem derives an RH-equivalent vanishing condition from
unconditional arithmetic estimates. CI rejects a stale generated panel. The
machine-readable companion is [docs/proof-status.json](docs/proof-status.json).

## Current Direction

RiemannGaussian is seeking stronger literal simple-critical-zero certificates through inverse sampling and phase-sensitive fourth moments. The checked frontier remains `HD(1) < C₀ < C₁`. The next arithmetic target is an unconditional bound above `17/25`, followed by `13/18` and `18/18`; the required prime-correlation estimates remain open.

## Latest Update

The fourth-moment research now includes a correctly scaled finite spectral
bound in `zeta23_simple_lower_of_scaledFourthMoment`, the exact continuum-core
value `-1/48` in `fourthMomentContinuumCore_eq_neg_one_div_fortyEight`, and a
summable frequency majorant in `fourthMomentArcMass_summable`. The new modules
also check phase-colour identities, a separable tensor Montgomery--Vaughan
bound, and obstructions to two proposed shortcuts. These are auxiliary
results: the prime-moment asymptotics needed for a stronger literal
certificate remain open. No `13/18` certificate exists.

## Notable Formalisations

Selected entry points into the Lean library are listed below. Each link names
a compiled theorem; its source records the precise domains and hypotheses.

| Area | What is formalised | Lean entry points |
| --- | --- | --- |
| **Gaussian/Weil explicit formula** | The arithmetic Gaussian expression, including prime-power and Archimedean terms, equals the canonical multiplicity-weighted symmetric zeta-zero sum for every positive width. | [gaussianArithmeticExplicitFormula_eq_canonical](RiemannGaussian/GaussianXiLogDerivativeGrowth.lean#L1235) |
| **Gaussian heat and reflected-zero Grams** | The complete matched Gaussian correlation equals the boundary heat-residue sum. At positive heat time, its vanishing is equivalent to RH. | [riemannXiUpperReflectedPairGaussianTotal_eq_boundaryHeatResidueTotal](RiemannGaussian/RiemannXiBoundaryGaussianGram.lean#L187), [riemannXiUpperReflectedPairGaussianTotal_eq_zero_iff_rh](RiemannGaussian/RiemannXiBoundaryGaussianGram.lean#L197) |
| **Suzuki arithmetic and spectral formulas** | Suzuki's positive-time arithmetic function equals its spectral expansion on `Im z > 1/2`. The literal arithmetic `Psi` is strictly positive on a nonzero punctured neighbourhood of the origin. | [riemannXiSuzukiArithmeticPPositive_eq_spectral_safe](RiemannGaussian/RiemannXiSuzukiWeilVerticalLimit.lean#L462), [exists_pos_on_abs_riemannXiSuzukiPsi](RiemannGaussian/RiemannXiSuzukiPointwiseLocalPositivity.lean#L298) |
| **Xi growth and divisor summability** | Unconditional `exp(O(R log R))` xi growth and convergence of the multiplicity-weighted inverse-square zero series. | [riemannXi_logLinearGrowth](RiemannGaussian/GaussianXiLogLinearGrowth.lean#L315), [summable_distinct_zetaZeroInverseSquareNorm](RiemannGaussian/GaussianXiInverseSquareSummability.lean#L294) |
| **Finite Hardy-space geometry** | Orthogonality in genuine boundary `L²`, including repeated roots, and a basis-independent determinant formula for the residual Gram operator. | [finiteModelBoundaryLp_inner_residualInner_negative_eq_zero](RiemannGaussian/FiniteHardyOrthogonality.lean#L260), [finiteHardyCrossAngleComplementGramOperator_det_eq_basisResidual_ratio](RiemannGaussian/FiniteHardyMetricDeterminant.lean#L294) |
| **Eta as a positive-measure Laplace transform** | On `Re s > 0`, paired eta divided by `s` is exactly the Laplace transform of Lebesgue measure restricted to the alternating logarithmic intervals `(log(2n+1), log(2n+2)]`. | [integral_exp_neg_mul_pairedEtaLogMeasure_eq_pairedEtaCore_div](RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure.lean#L219) |
| **Multiplicity-aware rank--trace inequalities** | The attributed Anthropic linear-algebra stack is specialised to actual finite eta zero windows, retaining analytic multiplicity and the signed off-line contribution. | [pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_ledger](RiemannGaussian/EtaEnergyFiniteWindowMultiplicityRankTrace.lean#L78) |
| **Montgomery--Vaughan weighted Hilbert inequality** | An attributed Apache-2.0 formalisation with exact diagonal constant `13` and bilinear constant `26`. | [MontgomeryVaughan.mvDiag_thirteen](RiemannGaussian/MontgomeryVaughan/Final.lean#L28), [MontgomeryVaughan.mvHilbert_twentySix](RiemannGaussian/MontgomeryVaughan/Final.lean#L31) |

The RH equivalences in this inventory are reformulations. Their open
positivity or vanishing direction remains unproved.

## Accomplishments

- **Reproduced Anthropic's `2/3` certificate in Lean.**
  [externalZeta23_twoThirds_distinctCritical](RiemannGaussian/External/Zeta23Baseline.lean#L30)
  rechecks the unconditional statement that, for every `ε > 0` and all
  sufficiently large `T`, `(2/3 - ε) N(T,2T) ≤ N₀*(T,2T)`. Here `N` counts
  nontrivial zeta zeros with analytic multiplicity and `N₀*` counts distinct
  critical-line zeros in `T < Im rho ≤ 2T`. This reproduces external prior
  work from the pinned Apache-2.0 source; see its
  [provenance and compatibility notes](vendor/zeta23/UPSTREAM.md).
- **Rechecked the stronger Montgomery--Taylor simple-zero benchmark.**
  [externalZeta23_montgomeryTaylor_simpleCritical](RiemannGaussian/External/Zeta23Baseline.lean#L50)
  proves the corresponding bound with exact constant `HD(1)` and a numerator
  counting only simple critical-line zeros. The project also proves
  [externalZeta23_HD_one_gt_two_thirds](RiemannGaussian/External/Zeta23Benchmark.lean#L211),
  so the comparison with `2/3` is checked without a decimal approximation.
- **Formalised two strict improvements over that external benchmark.**
  [Zeta23InverseSampling.externalZeta23_montgomeryTaylor_uncapped_strictly_stronger](RiemannGaussian/External/Zeta23InverseSamplingEndgame.lean#L1779)
  constructs `HD(1) < C₀ < C₁` and proves
  `(Cᵢ - ε) N(T,2T) ≤ N₀ˢ(T,2T)` eventually for each constant, with all
  arithmetic and analytic premises discharged. These are exact existential
  constants obtained from a positive compact minimum; no numerical bound
  above `17/25` or `13/18` has been established. The three-point mechanism
  has [related prior work](https://github.com/ainta/zeta-simple-zeros/blob/main/docs/proof.md#3-the-3-point-certificate).
- **Developed auxiliary theorems for inverse sampling.**
  [montgomeryTaylorKernel_no_additive_zero_below_six_pi](RiemannGaussian/MontgomeryTaylorInverseSampling.lean#L458)
  proves that the kernel cannot vanish at both nonnegative gaps and their
  sum when the span is at most `6π`.
  [exists_montgomeryTaylorTripleEnergy_floor](RiemannGaussian/MontgomeryTaylorInverseSampling.lean#L538)
  supplies a uniform positive energy floor, and
  [Zeta23InverseSampling.ZeroBlockData.three_quarters_tripleOffDiagEnergy_le_sum_simpleDefect](RiemannGaussian/External/Zeta23InverseSamplingZeroSide.lean#L350)
  transports `3/4` of the off-diagonal energy into the spectral defect of a
  positive three-column Gram block with diagonal entries at most one. These
  checked auxiliary estimates feed the literal certificate above.
- **Proved geometric separation of literal eta features.**
  [exists_prime_eventually_linearIndependent_pairedEtaGeometricPackedHyperbolicFeature](RiemannGaussian/Hybrid/EtaGeometricPackedFeatureRank.lean#L210)
  shows that every finite zeta-zero window admits one odd prime sampling base
  for which all sufficiently late packed eta-feature blocks are linearly
  independent. This preserves the information needed to distinguish every
  represented zero, including its completion factors and multiplicity-aware
  features; it supplies no critical-line proportion by itself.
- **Built a library of more than 10,000 audited project theorems.** The
  [generated inventory](docs/proof-status.json) covers more than 500 compiled
  project modules, with zero project-defined axioms, zero placeholder-dependent
  declarations, and no nonstandard theorem axioms.

The auxiliary contributions above have project-developed Lean proofs.
Priority or novelty relative to the wider mathematical literature has not
been established. The library also contains checked fourth-moment research,
but no `13/18` certificate or proof of RH is claimed.

## Mathematical Program

The current program combines four connected lines:

- The **finite certificate branch** adapts rank--trace and inertia methods to
  genuine symmetric eta zero windows. Its carrier retains cutoff, phase,
  multiplicity, reflected-zero colour, and coherent cross-zero interference,
  with separate positive and signed matrices joined by exact channel laws.
- The **eta arithmetic branch** realizes completed eta moments as explicit
  finite interval and endpoint sums, develops exact cutoff work laws, and uses
  geometric sampling to produce full-rank actual feature families and their
  multiplicity-weighted positive Gram companion, signed reflection normal
  form, and information-loss diagnosis for complete whitening.
- The **Gaussian/heat branch** supplies positive and signed heat flows,
  higher and mixed-scale moment Grams, projection leakage, closed paths, and
  the odd proper-time transform connecting heat kernels to the checked
  Montgomery--Vaughan inequality.
- The **Suzuki/contour branch** connects arithmetic screw-line quantities to
  the spectral xi logarithmic derivative and an RH-equivalent boundary-heat
  detector through rigorously controlled finite contours and limits.

The older finite Hardy, Blaschke, Pick-matrix, zero-counting, and
finite-to-entire developments remain checked supporting infrastructure and
alternative interfaces to the missing rigidity theorem. None of these
reformulations establishes the open arithmetic direction by itself.

## Repository Structure

- [RiemannGaussian.lean](RiemannGaussian.lean) is the root library module and
  fixes the complete import graph built by CI.
- [RiemannGaussian/](RiemannGaussian/) contains the Lean proof modules.
  Module families named `Gaussian*`, `Finite*`, `RiemannXi*`, and
  `Suzuki*` correspond to the principal parts of the program.
- [RiemannGaussian/HermitianRankTrace/](RiemannGaussian/HermitianRankTrace/)
  contains the attributed Apache-2.0 adaptation of the finite-dimensional
  rank--trace stack used by the eta specialization.
- [RiemannGaussian/MontgomeryVaughan/](RiemannGaussian/MontgomeryVaughan/)
  contains the attributed Apache-2.0 proof of the weighted Hilbert inequality
  and its explicit constants.
- [vendor/zeta23/](vendor/zeta23/) contains the pinned, warning-clean
  transitive source closure for the attributed external zero-proportion
  baselines, with upstream commit and compatibility changes recorded there.
- [scripts/GenerateProjectStatus.lean](scripts/GenerateProjectStatus.lean)
  audits the compiled environment and generates the status artifacts in
  [docs/](docs/).
- [scripts/LintProject.lean](scripts/LintProject.lean) runs all registered
  declaration linters over the complete project namespace.
- [AGENTS.md](AGENTS.md) records the proof discipline, workflow, and mandatory
  gates for research agents.
- [.github/workflows/lean_action_ci.yml](.github/workflows/lean_action_ci.yml)
  and [.githooks/pre-commit](.githooks/pre-commit) implement the remote and
  local verification gates.

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
- GitHub Actions must pass on the exact pushed commit before another proof
  slice begins.

Numerical experiments, symbolic calculations, research notes, and literature
dispatches are used only to discover candidate mathematics. Nothing from them
is trusted until it has been re-derived in Lean and passed every gate.

## Build and Check

The project is pinned to Lean 4.33.1 and Mathlib 4.33.1. With
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
[HermitianRankTrace](RiemannGaussian/HermitianRankTrace/NOTICE), and
[MontgomeryVaughan](RiemannGaussian/MontgomeryVaughan/NOTICE).
