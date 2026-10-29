# Executed word-valued node packets, 2026-10-27

Status: **progress; the full original-input primitive bit/address clock remains open**.
This checkpoint extends the actual factoring caller: acquired native group results
remain binary words through head scans, summary products and sums, and signed
support accumulation. Only a completed node crosses the scalar Hermite boundary.
The new caller has all-input value correctness and soundness, and an attached
original-source setup/counter report bound. It does not yet have the final
public report-rate composition or a complete primitive-machine clock.

## What is established

* `NativeGroupBitsHeight` derives a shared group denominator and numerator bound
  from original source representations, dimensions and the original Boolean entry
  bound. No group value, intermediate fit or height oracle is supplied.
* `WordPacketWidth` computes a sufficient physical width from original dimensions
  and the actual head, summary and support cardinalities. `WordPacketWidthBudget`
  proves fixed-polynomial growth, including the source-derived input width.
* `WordFoldArithmetic` and `WordFoldBounds` implement and bound actual rational-word
  addition, multiplication, gating and literal signed accumulation. The prefix
  invariants derive the arithmetic fits. Rejected gates skip their callbacks;
  their test costs remain charged.
* `MaterializedWordFibre` and its bounds execute the same head/summary/ternary
  support traversal as the previous scalar evaluator. Shared denominators are
  held fixed across sums. Products use the group-count power of that denominator;
  head/summary/support counts multiply numerator bounds. The runtime preserves
  the actual support cutoff and has no new global truth-table traversal.
* `WordPacketCounter` acquires source getters and positive interpolation-node
  encodings once. Group words flow directly into the word-valued node. Its exact
  decoded output equals the previous evaluator for all inputs satisfying the
  original mathematical guards. Value equality never supplies a cost equality.
* `WordPacketCounterBudget` retains actual group and outer-fold reports, node
  control allowances, one decode allowance per completed node, cached source
  getters, node encoding and the Hermite consumer. The former group budget is
  a conservative upper bound on the actual new callback; its extra nonnegative
  group-decode allowance is overestimation, not a runtime conversion.
* `WordPacketSetupCounter` derives the original source guards internally.
  `WordPacketSetupBudget` proves the exact report split into actual existing setup,
  additional source encoding, and actual new counter work, then a closed bound
  from original source/entry/design dimensions. The public and scheduled callers
  invoke this path, with all-natural value/soundness/completeness proofs.

The main cost has the same actual traversal resources: local `2^H` head scans,
actual summary count `Y`, weighted support count `Cq`, and local `2^arity` groups.
The chosen word width is polynomial in those resources and original dimensions.
It is deliberately conservative; this is not a practical performance claim.

## Review and reproducibility

[Verification](verification.json) records exact module/declaration counts, all
strict/root-linter/axiom checks, isolated object equality and imported-dependency
pins. The [combined audit](CombinedWordPacketAudit.lean) imports the ordinary
repository root and checks all generated declarations, not only named theorems.
Dependency names come from the **actual compiler environment header**; every
imported source and object is resolved and hashed before and after replay.

Independent reviews cover [common-denominator mathematics](review-outer-word-folds.md),
[the live caller path](review-callpath.md), and [actual retained costs](review-word-packet-counter-budget.md).
A small [physical-node smoke check](WordFibreSmoke.lean) exercises real native
groups, empty summary bins, both local head words and all three signed-support
callbacks. It is a functional check, not scaling evidence.

The [manifest](manifest.json) covers every sealed file except itself;
[provenance](archive-provenance.json) records every copied source.
All prior protected files, concurrent work and append-only journal prefixes
are preserved. There is no commit or push in this checkpoint.

## Remaining route to the goal

The earlier `FullReportRate` subpower/sixth-rate theorems remain frozen results
for the **older** mixed-report controller. The new controller needs its own
public original-resource bound and rate composition; output equivalence alone
cannot transfer a runtime theorem. The paper-level factoring interpretation,
allowing subexponential storage, is unchanged.

The next executed arithmetic boundary is Hermite reconstruction. Original source
production and canonical digit encoding, scalar cached head tests, graph/schedule/
floor/fallback operations, and finite index/address/control refinements also
remain. The retained control and rational-decode allowances are not yet proved
whole-machine primitive clocks. The native long-query soft-K exponent has not
improved in this checkpoint, and a guaranteed full bit-complexity 1/6 result is
not being claimed.
