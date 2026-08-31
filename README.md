# RiemannGaussian

[![Lean Action CI](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/lean_action_ci.yml)

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

The active research direction is a phase-preserving finite zero-window
certificate inspired by Anthropic's `zeta23` rank--trace architecture. The
project has instantiated its linear-algebraic skeleton on genuine
multiplicity-weighted eta features and enriched it with signed Gaussian heat,
higher and cross-scale spectral moments, cutoff transport, reflected-zero
colour, and coherent zero-pair correlations. The first benchmark is a literal
eta-arithmetic certificate stronger than the earlier two-thirds result; the
ultimate method target is `18/18`, or 100% of every finite symmetric zero
window.

Lean currently proves a sharp abstract `13/18` degree-four certificate, but
that number is not yet a zeta-zero proportion: the prescribed degree-four
moments have not been derived from the literal eta window. The coupled
zero-index data are the positive eta metric `K = CᴴC` and the critical-line
reflection permutation `P`. The mixed hierarchy `Re tr((PK)^r)` remains
available as a phase-preserving companion channel, but its spectrum has the
wrong zero-atom semantics when `K` is positive definite. The certificate
carrier is instead the positive reflection-even compression
`A₊ = E₊KE₊`, where `E₊ = (I+P)/2`; its nullity is exactly the upper
off-line-pair count while its nonzero eigenvalues retain eta arithmetic.

The normalized finite eigenvalue-atom model of `A₊` is now checked in Lean,
including an exact ordinary-heat separator: its literal critical-zero
fraction is greater than `13/18` exactly when a normalized heat trace of `A₊`
crosses below `5/36` at some nonnegative scale. That heat trace is now
transported to the genuine coordinate carrier `C E₊ Cᴴ`, proved equal to the
positive on-line-plus-off-line-real eta block, and expanded into ordered paths
that retain both colours on every edge. Lean now also proves that this
carrier's rank is exactly `#critical + #upper-off-line` and converts its first
two coloured path moments into explicit sufficient certificate targets. The
immediate frontier is an eta-arithmetic proof of the strict `13/18` target;
successively stronger information-preserving moment bounds are the route
toward `18/18`. No improved zeta-zero proportion will be claimed until one of
those arithmetic premises is itself checked in Lean.

## Latest Update

For every Hermitian matrix, Lean now derives the effective-rank inequality
`rtrace(A)² ≤ rank(A) · frobSq(A)` directly from its nonzero eigenvalues.
On the reflection-even eta coordinate carrier, both moments are exactly the
real parts of the length-one and length-two colour-resolved closed-path sums.
Actual feature separation supplies one odd prime base for which these
interfaces hold at every sufficiently late geometric block. If `N` is the
represented window size, the checked implication
`31 N Re(path₂) < 36 Re(path₁)²` yields a critical-zero fraction greater
than `13/18`. The stronger ceiling `N Re(path₂) ≤ Re(path₁)²` yields
`#critical = N`, the finite-window `18/18` endpoint. Neither arithmetic
inequality has been proved for eta data yet; they are now the literal targets.

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
