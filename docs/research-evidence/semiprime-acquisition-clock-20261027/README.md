# Paid acquisition, physical row selection and retained controller work

Goal ACTIVE. This packet advances the formal implementation and cost proof of
the factor-count route. The previous independently reviewed paper-level
`N^o(1)` bit-time result with subexponential storage remains unchanged. A complete
Lean theorem bounding the original-input factorer's primitive bit time is
**still open**. No practical timing improvement or new native long-query rate
is claimed.

## Concrete progress

- **Finite inputs are constructed and charged.** Four enumeration modules
  execute the actual finite menus, materialize word coordinates into arrays,
  preserve the old ordering exactly, and join their reports to the original
  coefficient and integer-constraint producers. The native bounds depend on
  explicit network dimensions, not supplied labels or row answers.
- **The original integer constraint family is acquired.** Five modules execute
  the original word search, packing, universal numerator caching, padded row
  naming and every original-coordinate entry. The acquired order is exact.
  Four actual list scans read each entry. The native acquisition envelope is
  a fixed polynomial; the complete alphabet pays the subset expansion.
- **The full row selector executes binary arithmetic.** Two modules compute
  residuals, the first nonzero pivot, normalization and back-elimination using
  actual rational-word primitives and cached finite lists. The entire returned
  matrix, active flags and selected original row IDs refine the previous
  selector exactly. Intermediate widths follow from the original integer
  input bound and the actual pivot-minor invariant. The complete selector has
  an explicit polynomial bit-primitive/list-control ledger.
- **The public controller retains all returned query work.** Four modules run
  the actual counter once per query, accumulate its full report, perform paid
  prefix traversal/decoding and retain fallback work. The new N-only endpoint
  preserves all-natural-input factor correctness and completeness. Its uniform
  aggregate bound remains conditional on a bound for the actual counter report.

The newest original-input endpoint is
[PaidScheduledController.run](SemiprimePaidScheduledController.lean).
The newly charged acquisition and physical selector are **not yet substituted
into that endpoint's legacy raw/build design path**. Output equivalence and
component cost bounds do not alone close that integration.

## What remains

The next task is an executed integer-word encoder and cached design builder,
followed by their substitution into one complete counter. The stored integer
family is untruncated; the matrix readout theorem applies on actual head
columns. The builder must respect those columns or perform the head mask.
Source and constraint acquisition currently reconstruct labels/packing
independently; both reports must be paid unless concrete sharing is added.

Then derive the public controller's uniform counter bound, charge public macro
graph and schedule/guard setup, and join physical arithmetic plus all finite
memory/address/control costs throughout the same run. The selector's current
clock combines primitive bit work with metadata-cell/control work; it is not
a compiled tape/address clock. The source and controller ledgers remain scalar
at their stated boundaries. The existing resource-rate theorem can only be
applied after this complete fixed-polynomial simulation is established.

See [integration frontier](integration-frontier.md),
[constraint acquisition details](root-constraint-acquisition-notes.md),
[enumeration details](enumeration-acquisition-notes.md),
[physical selector details](physical-selector-notes.md), and
[controller details](paid-controller-notes.md).
Independent reviews: [constraints](review-paid-constraints.md) and
[physical selector](review-paid-selector.md).

## Verification

All **15 new modules**, comprising **885 generated declarations and 504 theorem
constants**, pass strict `autoImplicit=false` / `warningAsError=true` compilation,
ordinary-root fifteen-linter checks and transitive standard-axiom audits.
All 15 isolated objects are byte-identical to their canonical objects.
Dependency pins use **17585 actual compiler-imported module names**;
every source and object is resolved and unchanged. Existing dependencies were
pinned, not rebuilt. The original external SAT audit remains frozen.

The prior 2349 protected files, 24 concurrent files and two append-only document
prefixes are preserved. One journal note records this packet. No commit or push
was performed. Small enumeration, integer-row, selector and controller controls
exercise the actual compiled data flow and edge cases; they are not scaling
or finite-semiprime coverage evidence.

[Verification metadata](verification.json) ·
[Combined audit](CombinedAcquisitionAudit.log) ·
[Isolated verification](final-isolated/summary.json) ·
[Reproducible verifier](verify_acquisition.py)
