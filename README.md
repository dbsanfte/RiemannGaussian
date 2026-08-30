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
moments and separator bound have not been derived from the literal eta window.
Lean now proves eventual linear
independence of the actual packed two-channel eta features and an exact
multiplicity-weighted positive coordinate Gram whose rank is the number of
represented distinct zeros. On every symmetric window, Lean now couples that
Gram to the complex-symmetric signed eta block through two exact positive
channels, `Gram − Signed` and `Gram + Signed`. Pulling the same synthesis back
to zero-index space gives an eventually positive-definite metric `K = Cᴴ C`
whose inverse is also positive definite. Lean now uses this metric to normalize
the signed pullback into a Hermitian matrix `A` satisfying both `I − A ⪰ 0`
and `I + A ⪰ 0`. Lean further determines this fully whitened matrix exactly:
it is the permutation `P` sending each enumerated zero to its critical-line
reflection. Thus complete whitening cancels the eta amplitudes. The immediate
route instead retains the coupled normal form `B = K P K`, the normalized
mixed trace `Re tr(PK) / Re tr(K)`, the full ordered same-scale hierarchy
`Re tr((PK)^r)`, and two-step cross-scale words. Lean now realizes this entire
hierarchy on the exact positive support of a Hermitian packed-coordinate
carrier, without adding the artificial zero eigenspace or cancelling `K`.
That support now yields a normalized positive-semidefinite Hankel model for
every finite family of mixed moment orders. The next route is to extract or
bypass an explicit finite-atom representation and derive eta-arithmetic bounds
strong enough to exclude the sharp `13/18` adversary. No stronger zero
proportion will be claimed until those steps are checked.

## Latest Update

Lean now flattens the exact supported powers `Q S^k` into feature columns. For
every finite order family `(kᵢ)`, their Hermitian column Gram is positive
semidefinite and its `(i,j)` entry is proved exactly equal to
`Re tr((P K)^(kᵢ+kⱼ))`. This turns the complete phase-preserving mixed eta
hierarchy into an actual Hankel Gram, including its correctly supported
zeroth moment.

Writing `N` for the represented distinct-zero count and
`m₀ = Re tr(K)`, Lean also checks the dimensionless normalization
`νᵣ = N⁻¹ (N/m₀)^r Re tr((PK)^r)`. Every finite matrix
`(ν_(kᵢ+kⱼ))` is positive semidefinite; on a nonempty separated window,
`ν₀ = 1` and `ν₁ = Re tr(PK)/Re tr(K)`. Lean derives the universal Hankel
inequality `ν_(a+b)^2 ≤ ν_(2a)ν_(2b)`. This is not yet a stronger zero
proportion: the live problem is an eta-arithmetic bound on these normalized
moments or heat observables that excludes the sharp `13/18` adversary.

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
