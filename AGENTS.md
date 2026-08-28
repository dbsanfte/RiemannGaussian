# RiemannGaussian agent guide

## Project mission

RiemannGaussian is a research project seeking a complete, kernel-checked Lean
proof of the Riemann hypothesis. The target is Mathlib's
`RiemannHypothesis`; finite models, numerical certificates, asymptotic
experiments, and reformulations are useful only when they strengthen a
rigorous chain to that target.

The proof is not complete. The generated dashboard in
`docs/proof-status.svg` is the canonical compact status summary. At present,
the Gaussian/Weil and Suzuki/contour branches prove that the complete
safe-axis logarithmic defect is asymptotic, with `o(1)` error, to its positive
Poisson linearization, which is exactly height-scaled Blaschke derivative
variation. A checked dyadic Tauberian theorem now identifies decay of those
quantities with `H(T) / T → 0`, where `H` is cumulative upper spectral height.
That sublinear law is not RH and does not exclude a finite or sparse off-line
divisor. The missing theorem must derive a genuine zero-location constraint
from xi's arithmetic or entire-function structure; a restatement, hidden
limit interchange, or conditional implication is not a substitute.

## Soundness invariant

The repository must remain a continuous, bottom-up Lean proof chain after
every commit.

- Do not use `sorry`, `admit`, introduce custom axioms, use compiler-trusting
  proof shortcuts, or add declarations whose purpose is to assume the missing
  mathematics.
- Do not weaken `RiemannHypothesis`, redefine a frontier quantity to make it
  trivial, hide the frontier in a typeclass or hypothesis, or report a
  conditional reduction as a proof of its premise.
- Lean's standard logical axioms `propext`, `Classical.choice`, and
  `Quot.sound` are permitted. Any other transitive axiom dependency is a
  failed gate unless the user has explicitly approved and documented it.
- Every mathematical progress claim must name a compiled theorem. Comments,
  Markdown, Python output, numerical evidence, and successful examples are
  not proof.
- External research notes are leads, not trusted inputs. Re-derive every fact
  in Lean from already checked definitions and theorems.
- Numerical and symbolic computation may explore conjectures, find constants,
  or produce exact certificates. The final theorem must check in Lean without
  trusting Python or floating-point output.
- Preserve genuine definitions and all analytic side conditions, including
  convergence, integrability, zero avoidance, multiplicity, domains, and
  limit hypotheses. Never silently totalize a singular expression and then
  reason as though the original identity held there.

The compiled project must contain no project-defined axioms. The status
generator rejects any such axiom, even when it is disconnected from a
displayed frontier theorem.

## Proof-slice workflow

Work in one coherent slice at a time. A slice should close a real lemma or
interface needed by the current RH frontier, not merely add parallel
abstractions.

1. Inspect `git status`, the imported theorem chain, the current dashboard
   data, and any newly supplied research dispatch before editing.
2. State the exact mathematical obstruction and the theorem that removes a
   concrete part of it. Check that its assumptions are available upstream.
3. Put new mathematics in a focused module with a module docstring and
   theorem-level documentation. Import it from `RiemannGaussian.lean` so the
   root environment and full build contain it.
4. Compile the changed module directly with warnings treated as errors.
5. Run the whole-package declaration linter, which includes every new public
   declaration. Use its verbose form during an audit when the individual
   results need to be recorded. Fix all findings; do not suppress them merely
   to pass.
6. Run `#print axioms` on the slice's terminal theorems. The result may contain
   only `propext`, `Classical.choice`, and `Quot.sound`.
7. Run the source placeholder scan, whole-project declaration lint, focused
   build, full build, generated-status check, and whitespace check described
   below.
8. Update the README only for stable explanatory changes. Update the milestone
   list in `scripts/GenerateProjectStatus.lean` when and only when a new
   theorem genuinely advances the displayed frontier, then regenerate the
   artifacts.
9. Commit and push the complete slice. Wait for GitHub Actions on that exact
   commit SHA to finish successfully before beginning another slice.

Lake builds independent modules in parallel. Direct elaboration of one Lean
module is normally one process; do not mistake that focused check for the
parallel full-library build.

## Commit and check-in invariant

The repository history is the durable record of verified progress. Enforce
this regime yourself; do not rely on the user to request individual commits,
pushes, or CI checks.

- Begin a new slice only from a clean worktree whose current `HEAD` has a
  successful GitHub Actions run with exactly the same full commit SHA.
- Keep one coherent mathematical or infrastructure slice per commit. Do not
  mix unrelated cleanup into it, and do not leave concrete verified progress
  only in the working tree.
- Before committing, stage the complete intended slice and verify the staged
  content with all applicable local gates, `git diff --cached --check`, and
  the tracked pre-commit hook. Documentation-only and CI-only commits are not
  exempt from the gate.
- Do not bypass the pre-commit hook. If an exceptional environment prevents
  the hook from running, execute every command it enforces manually and record
  that fact in the handoff.
- Push each passing commit promptly, record its full SHA, locate the workflow
  run whose `headSha` is exactly that SHA, and require a `success` conclusion.
- While exact-SHA CI is pending, do not start or commit the next slice. If CI
  fails, work only on repairing that same slice, rerun every affected local
  gate, push the repair as a new commit, and verify the replacement SHA.
- Progress reports and handoffs must distinguish local success from remote
  verification and should cite both the exact commit SHA and CI run number.

## Mandatory local gates

Use the repository's pinned Lean toolchain. In environments where `lake` is
not already on `PATH`, invoke the pinned binary through the configured
`ELAN_HOME` rather than changing the project version.

Enable the tracked pre-commit gate once in every fresh clone:

```bash
git config core.hooksPath .githooks
```

The hook repeats the staged placeholder scan, warning-as-error build,
whole-project declaration lint, compiled-environment/dashboard audit, and
staged whitespace check. CI remains authoritative because local hooks can be
bypassed and a partially staged commit may differ from the working tree.

For a changed module `RiemannGaussian/NewSlice.lean`, the minimum gate is:

```bash
lake env lean -DwarningAsError=true RiemannGaussian/NewSlice.lean
lake env lean -DwarningAsError=true /tmp/RiemannGaussianAudit.lean
if git grep -nE '\<(sorry|admit|sorryAx)\>' -- '*.lean'; then exit 1; fi
lake env lean -DwarningAsError=true scripts/LintProject.lean
lake build RiemannGaussian.NewSlice --wfail
lake build --wfail
lake env lean -DwarningAsError=true scripts/GenerateProjectStatus.lean
git diff --exit-code -- docs/proof-status.json docs/proof-status.svg
git diff --check
```

The temporary audit file must import the root library. Its verbose lint command
and explicit axiom commands for terminal theorems have this form:

```lean
import RiemannGaussian
import Mathlib.Tactic.Linter
#lint+ in RiemannGaussian
#print axioms RiemannGaussian.newFrontierTheorem
```

The generator is also a soundness gate. It scans every declaration in
compiled project modules for indirect placeholder dependencies, rejects all
project-defined axioms and disallowed transitive axioms, and verifies that
every green dashboard milestone is an actual project theorem using only the
three permitted standard axioms.

## GitHub gate

Do not infer remote success from a local build or from a workflow attached to
another commit. After pushing:

1. Record `git rev-parse HEAD`.
2. Locate the GitHub Actions run whose `headSha` is exactly that value.
3. Wait for it to finish and require conclusion `success`.
4. Confirm the worktree is clean before starting the next proof slice.

If CI fails, repair the same slice, rerun every affected local gate, push the
repair, and verify the new exact commit. Never stack a new mathematical slice
on an unverified commit.

## Research discipline

- Prefer exact identities, coercion lemmas, summable dominators, and explicit
  quantitative estimates that can be reused downstream.
- Distinguish finite-window, infinite-sum, boundary-limit, and large-height
  statements in names and hypotheses.
- Treat division, logarithmic derivatives, contour deformation, exchanged
  limits, derivatives under integrals, and sum-integral swaps as proof
  obligations requiring their own hypotheses and Lean theorems.
- New mathematics is welcome. Grow it from the checked chain, isolate its
  genuinely novel lemma, test finite or numerical shadows when useful, and
  then prove the general statement in Lean.
- Never claim RH is proved until the completion audit reaches an unconditional
  term of `RiemannHypothesis` and all local and exact-commit remote gates pass.
