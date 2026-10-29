# Actual physical-Hermite report rate and source score prefixes, 2026-10-27

Status: **verified report-rate progress; whole primitive-bit scaling remains open**.
The new physical-Hermite caller has its own original-input resource bound and
proved subpower report growth. For every fixed epsilon > 0, Lean proves

```text
∀ᶠ N in atTop, (HermiteBitsScheduledController.run N).work ≤ N^epsilon
```

with natural work cast to the reals. In particular, the same actual report is
eventually at most N^(1/6). This concerns the retained execution report. It does
not yet identify that report, or a fixed polynomial of its resources, with the
complete original-input primitive bit/address execution.

## Actual implementation and cost chain

The previously verified physical caller is unchanged. Its new bound derives the
original source guards, physical entry cost, and literal indexed design head,
rank and summary bounds for every reachable prefix. It retains repeated source
and raw setup, node acquisition, native word arithmetic, physical Hermite,
control allowances, the final decode allowance and the public decoder/search.
No count-work or acquired-design budget is an unexplained premise.

`HermiteWidthPolynomial` bounds the actual computed reconstruction width by an
explicit monotone polynomial. `HermiteReportStagePolynomial` preserves local
truth-table cardinalities, local head counts, summary counts and weighted support
counts as separate resources. It never replaces them by 2^S. The original
source-derived input bit width is bounded by its proved polynomial; it is not
incorrectly assumed at most the scalar dimension S.

`HermiteReportEnvelope` bounds the actual setup/counter cost by a fixed polynomial
in those resources and constructs uniform monomial witnesses. The public bound
uses the actual physical designs and original entry checks. A fixed inflation
of the resource sum pays the physical entry constant factors.
`PublicHermiteReportPolynomial` proves the resulting bound for the literal
`HermiteBitsScheduledController.run.work` with constants independent of N.

`PublicResourceRate` applies the existing **numerical schedule/resource** estimates
to any fixed resource polynomial. `HermiteFullReportRate.run_report_subpower`
and `run_report_sixth` instantiate that theorem using the newly proved actual
caller bound. They do not transfer an older controller's runtime through value
equality. Earlier `FullReportRate` theorems remain frozen results about their
older implementation.

## A preprocessing height gap also closed

`SourceScorePrefixHeight` proves original-derived representations for the actual
score expectation recursion, every child partial sum and right-recursive suffix,
support-four local terms, objective suffix sums and the final offset-subtracted
score. These are uniform symbolic bounds, not finite input examples.

The actual source scales are x=epsilon*M/U and y=n/(2r). Their shared denominator
and numerator bounds are derived from original epsilon data; the scheduled
specialization uses epsilon=1/(r*lambda). The universal-type bank size
U=r^(2Q) is distinct from the averaging word-alphabet length L=r^Q. With a shared
scale denominator D, the support-four averaging denominator is D^2*L^4.
Empty-alphabet representations are handled algebraically; reduced-height uses
the actual nonempty alphabet. No terminal-score or intermediate-height answer
is supplied.

The [critical-path audit](whole-clock-critical-path-audit.md) names the remaining
executed loops and the precise invariants needed to complete source preprocessing
and a uniform bit simulation. The new prefix theorem does not cover every
universal numerator, interpolation subtree, offset scratch value or memory state.

## Evidence and limits

[Verification](verification.json) records the eight new modules and exact
strict/linter/axiom/isolation counts. The [combined audit](CombinedHermiteReportRateAudit.lean)
uses the ordinary repository root, all 15 scoped linters and transitive axiom
checks for every generated declaration. Imported dependency names come from
the actual compiler environment header, with every source/object pair pinned
before and after isolated recompilation.

Independent reviews inspect [the complete rate chain](review-hermite-rate.md)
and [resource estimates and source-prefix scope](review-resource-and-source.md).
The [manifest](manifest.json) and [provenance](archive-provenance.json) seal the
evidence. Earlier work, concurrent files and journal prefixes are preserved.
There is no commit or push in this checkpoint.

The next substantive step is the original-source preprocessing state/height
bound for actual offset powers, universal differences/contributions/suffix sums,
and interpolation AST subtrees/convolution prefixes. Then derive total stored
cells and attach a fixed-polynomial deterministic bit simulation, including
schedules, guards, indices, allocation, addressing, bookkeeping and final
word conversion/floor. The numerical resource-rate theorem can then be applied
to that complete simulation budget. Subexponential space is permitted; it still
has to be charged. The guaranteed full bit-complexity 1/6 goal remains ACTIVE.
