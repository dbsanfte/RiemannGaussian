# A 67.31% simple-critical-zero certificate

Lean proves that **at least 6731/10000 (67.31%)** of the literal nontrivial
zeta zeros in every sufficiently large cumulative window `(0, T]` are simple
and lie on the critical line. The same statement holds on `(T, 2T]`.
The denominator counts zeros with analytic multiplicity; the numerator
counts actual critical-line zeros of multiplicity one.
**The starting height is not numerically evaluated.**

The closed theorems are
[`simpleCritical_6731_cumulative_eventually` and
`simpleCritical_6731_eventually`](../RiemannGaussian/External/Zeta23SevenWindowIntegerCertificate.lean).
They have no remaining numerical, arithmetic or analytic premise.
The complete optional verification also passed on hosted runners in
[run 34802730942](https://github.com/dbsanfte/RiemannGaussian/actions/runs/34802730942),
at source revision `d3476d4d6b97e954927b94e6b43846876586ccb2`. That run
checked all 21 data modules and 231 cover groups, assembled both literal
endpoints, passed the transitive axiom audit, and rejected a conditional
replacement without writing a success report.

[![Numerical certificate verification](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/numerical_certificate.yml/badge.svg)](https://github.com/dbsanfte/RiemannGaussian/actions/workflows/numerical_certificate.yml)

### [Open the dedicated certificate theorem explorer](https://dbsanfte.github.io/RiemannGaussian/numerical-certificate/)

[![Comparison of the proved certificate with two thirds and the pinned external coefficient](numerical-certificate/comparison.svg)](https://dbsanfte.github.io/RiemannGaussian/numerical-certificate/)

The badge links to the live optional workflow. The successful run above and
its [verification provenance](numerical-certificate/verification.json) identify
the exact fully checked source and input fingerprint. Ordinary presentation
CI is recorded separately by the explorer's deployment link.

The exact coefficient before rounding is

```math
C_* = \frac{5{,}180{,}000h-10{,}320}{5{,}160{,}013},
\qquad h=\frac32-\frac{\cot(1/\sqrt2)}{\sqrt2}.
```

Lean proves the strict enclosure
`0.6731055996 < C_* < 0.6731055998` and a gain `C_* - h > 3/5000`
over the pinned external Montgomery–Taylor baseline, approximately 67.25007%.
This is the stronger coefficient in the
[attributed Anthropic/Zeta23 source snapshot](../vendor/zeta23/UPSTREAM.md),
beyond its headline two-thirds result. The gain of more than 0.06 percentage
points compares the exact coefficient with that baseline; the rounded
67.31% headline has a slightly smaller gain.
[Exact comparison proofs](../RiemannGaussian/External/Zeta23SevenWindowTarget.lean).
The exact-coefficient statement permits every positive epsilon; its strict
margin above `6731/10000` pays that error and gives the eventual rational
bound without epsilon. This does not provide a numerical starting height.

## From a continuous inequality to literal zero counts

The construction assigns unequal rational weights to pairs in seven ordered
positions. Its six gap pressures have total `1/500`; each separation's pair
weights have total two. These exact budgets let 253 overlapping seven-point
inequalities supply a 259-point sampling block. The complete analytic
endgame transfers that block's retained Gram energy to literal zero counts.

The local floor is a continuous inequality over every real six-gap vector,
not a check at finitely many sampled points. Small and large gaps are settled
analytically. The remaining domain `[1/3, 20]^6` is covered by closed boxes,
with their shared boundaries retained. Interval leaves and signed gradient
and curvature leaves together prove the whole compact inequality.

| Proof stage | Lean source |
| --- | --- |
| Rational weights and their exact budgets | [SevenWindowParameters](../RiemannGaussian/MontgomeryTaylorSevenWindowParameters.lean) |
| Small/large-gap reductions and model error | [SevenWindowModel](../RiemannGaussian/MontgomeryTaylorSevenWindowModel.lean) |
| 9,306 continuous range bounds | [IntegerRanges.table_valid](../RiemannGaussian/CertificateData/MontgomeryTaylorIntegerRanges.lean) |
| 944 anchors, with 17,936 point enclosures | [IntegerAnchors.lookup_valid](../RiemannGaussian/CertificateData/MontgomeryTaylorIntegerAnchors.lean) |
| Signed gradient and complete curvature checks | [checkAnchor_sound](../RiemannGaussian/MontgomeryTaylorIntegerBoxCertificate.lean) |
| Complete closed-cover soundness | [compact_floor_of_check](../RiemannGaussian/MontgomeryTaylorIntegerCover.lean) |
| Acceptance of the actual complete tree | [Cover.checked](../RiemannGaussian/CertificateData/MontgomeryTaylorCover.lean) |
| Compact floor, unrestricted floor and literal counts | [IntegerCertificate](../RiemannGaussian/External/Zeta23SevenWindowIntegerCertificate.lean) |

The proved cover has 353,434 interval leaves, 43,460 anchor leaves and
396,893 splits: 793,787 expanded nodes. The integer range and anchor data
are checked against their rational proofs. Python-generated proposals are
untrusted; Lean checks every accepted bound and every part of the cover.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted by the
[transitive axiom audit](numerical-certificate-audit.json).

## Optional, cached verification

Ordinary `lake build --wfail`, push/PR CI and the pre-commit gate build
`RiemannGaussian`. They include the reusable analytic work, while the
generated certificate data and every module importing it belong to the
separate `NumericalCertificate` target. The
[build metadata](numerical-certificate.json) and
[import guard](../scripts/numerical_certificate.py) enforce this boundary.

Run the complete certificate explicitly:

```bash
python3 scripts/verify_numerical_certificate.py --jobs 4
```

The driver bounds concurrent heavy compiler processes, builds prerequisite
tables first, checks all 231 proof groups, assembles the original root and
runs the full declaration and transitive-axiom audit. It records live
progress, individual logs and the input digest in
`.lake/numerical-certificate/`. The underlying optional target is
`lake build NumericalCertificate --wfail`. Lake reuses each unchanged
checked module on subsequent runs; a cold repeat is unnecessary after
unrelated edits.

The [compressed proposal](../certificates/seven-window/cover-proposal.json.gz)
and [source generator](../scripts/generate_montgomery_taylor_cover.py) reproduce
the 1,255 pieces in 231 source groups. Each kernel reduction handles at most
31 nodes; proved child-box equalities assemble the results without one giant
reduction of the whole tree. Inspect a running driver's actual process before
restarting it, and keep its proof inputs fixed until it terminates.

The manual-only **Optional numerical certificate verification** workflow
has one prerequisite-data job, eight disjoint cover shards, then a final
assembly and audit job. No push or pull request triggers it. Component
caches use a SHA-256 digest of the actual transitive local proof imports,
toolchain, dependency pins, proposal, generator and verification inputs.
Lake still validates restored traces. The `cold` input skips restoration
of project certificate artifacts while retaining the standard mathlib cache.

Hosted runners compile one prerequisite or two cover modules concurrently,
with eight GiB of additional swap in every job. The dedicated
`NumericalCertificateData` library owns the existing `CertificateData`
submodules and uses
`weakLeanArgs = ["-DElab.async=false"]` to elaborate each module serially;
this changes scheduling without invalidating already checked proof traces.
A strict cold check of `MontgomeryTaylorAnchors00` passed in 8 minutes
13 seconds with a 7.5 GiB peak resident set. The same check with asynchronous
elaboration exceeded a 12 GiB memory limit. Independent modules can still
compile concurrently within the driver's process cap. Ordinary proofs retain
their established elaboration mode. Tiny compiled probes check this boundary
in the hook and both workflows; they do not run the exhaustive certificate.
Heartbeats report available
memory, swap and disk space. A terminated verifier stops its owned compiler
process group, records an interrupted verdict and removes success markers.
The interruption regression also checks an actual spawned descendant.
The first hosted attempt terminated during four concurrent anchor builds.
The current complete hosted run passed with reduced concurrency and serial
elaboration confined to optional data. Its source, declaration inventory
and verification-input digest are recorded in the
[hosted complete audit](numerical-certificate/hosted-audit.json).

Cold checks are split across jobs because of the
[six-hour GitHub-hosted job limit](https://docs.github.com/en/actions/reference/limits).
Checked prerequisites and all eight shards are transported as artifacts
from the same workflow run, so inter-job correctness does not depend on
cache retention. The final job gathers those artifacts and checks
the complete selected target again. Successful data or shard jobs are labelled
partial; they do not certify the full result. Logs, input digest and source
revision are uploaded by each job. The complete hosted run passed with input digest
`7049e4abb818982305ff0747a870b964f6d2d11589604dc3de8c82840954c53d`.
Its audit covered 432,974 declarations and 167,613 theorems in 304 compiled
project modules, using only the three permitted standard axioms. The digest
includes build and verification configuration as well as proof inputs.
The local explorer snapshot has a separately recorded generated-helper
inventory; its full audit has the same proof-input fingerprint and axiom policy.

The audit explicitly type-checks the unconditional literal dyadic and
cumulative statements and inspects their proof axioms before writing a
success report. The driver removes stale success reports on failure. After
building the full target, its rejection test can also be run explicitly:

```bash
python3 scripts/test_numerical_certificate_audit.py
```

This first requires the genuine audit to pass, then replaces one closed
endpoint with its conditional precursor and requires rejection without a
success report. It uses temporary audit outputs and does not rerun the
expensive kernel computations for unchanged cover modules.

## Mathematical provenance and scope

The analytic baseline is the attributed
[pinned Zeta23 development](../vendor/zeta23/UPSTREAM.md), whose exact
Montgomery–Taylor constant is approximately `0.672500703679`.
The prior seven-position numerical construction in
[ainta/zeta-simple-zeros](https://github.com/ainta/zeta-simple-zeros)
is a separate external lead, reporting approximately `0.673008527927`.
The present result uses unequal pair weights and a complete continuous,
signed-curvature box proof. No broader priority or record claim is made.

This numerical certificate neither proves RH nor enlarges the repository's
zero-free region. The independent signed arithmetic bound in the RH
argument remains open.

## Evergreen chart and theorem explorer

The [dedicated explorer](https://dbsanfte.github.io/RiemannGaussian/numerical-certificate/)
starts at the unconditional cumulative 67.31% theorem. Select dyadic counts
or the exact coefficient for the companion chains. Hover, zoom and expand
actual dependency paths; each theorem links to its Lean declaration and
complete transitive axiom set. The family taxonomy is shared with the
zero-free explorer, with [certificate reading labels](numerical-certificate-explorer/metadata.json).

To keep the graph usable, generated range tables, anchors and the accepted
cover appear as **explicit generated-data proof boundaries**. Their full
transitive axioms are checked, and the separately linked optional audit
checks all underlying components. The compact graph is not the exhaustive
expanded cover. External Lean, mathlib and pinned Zeta23 declarations are
also boundary leaves; Zeta23 source links preserve its vendored snapshot
and [upstream attribution](../vendor/zeta23/UPSTREAM.md).

The [frozen graph manifest](numerical-certificate-explorer/snapshot.json)
records the optional input fingerprint, every local imported source hash,
exporter hash and complete local audit hash. Refresh it explicitly after a
changed optional proof has passed its full target and audit:

```bash
python3 scripts/build_numerical_certificate_explorer.py --refresh
lake env lean -DwarningAsError=true scripts/ExportNumericalCertificatePlot.lean
.lake/plot-venv/bin/python scripts/build_numerical_certificate_plot.py
```

The chart reads only exact rational enclosures exported by the lightweight
Lean script, alongside the checked endpoint snapshot. Its
[plot metadata](numerical-certificate/metadata.json),
[coefficient export](numerical-certificate/coefficients.json) and
[drawing audit](numerical-certificate/audit.json) are committed together.
The full 0–100% context and labelled magnification distinguish the limiting
coefficients from the closed rational endpoint; the picture supplies no new
numerical theorem.

Ordinary CI and the hook run the lightweight exporter and both builders'
`--check` modes. These reject stale plots, proof fingerprints, source links
and graph paths **without compiling the optional certificate**. Browser
checks exercise both explorers and the README through GitHub's actual
renderer. The dedicated Pages site pins presentation source links to its
ordinary CI commit; its exhaustive verification link remains attached to
the separately recorded successful certificate run and identical inputs.
