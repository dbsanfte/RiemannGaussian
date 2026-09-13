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
This is a local Lean result; no remote CI verdict is claimed for the
uncommitted worktree.

The exact coefficient before rounding is

```math
C_* = \frac{5{,}180{,}000h-10{,}320}{5{,}160{,}013},
\qquad h=\frac32-\frac{\cot(1/\sqrt2)}{\sqrt2}.
```

Lean proves the strict enclosure
`0.6731055996 < C_* < 0.6731055998` and a gain `C_* - h > 3/5000`
over the pinned external Montgomery–Taylor baseline.
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

Cold checks are split across jobs because of the
[six-hour GitHub-hosted job limit](https://docs.github.com/en/actions/reference/limits).
Checked prerequisites and all eight shards are transported as artifacts
from the same workflow run, so inter-job correctness does not depend on
cache retention. The final job gathers those artifacts and checks
the complete selected target again. Successful data or shard jobs are labelled
partial; they do not certify the full result. Logs, input digest and source
revision are uploaded by each job. The full workflow has not yet been
validated on hosted runners.

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
