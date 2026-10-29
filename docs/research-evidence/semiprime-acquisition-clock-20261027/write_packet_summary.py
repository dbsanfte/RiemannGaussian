from pathlib import Path
import json,re
w=Path('/tmp/semiprime-acquisition-clock-20261027')
x=json.loads((w/'final-isolated/summary.json').read_text())
assert all(x[k] for k in ('complete','strict_pass','all_objects_match','dependency_snapshot_unchanged'))
log=(w/'CombinedAcquisitionAudit.log').read_text()
match=re.search(r'TOTAL modules=(\d+), declarations=(\d+), theorems=(\d+), standard_axioms_only=true',log)
assert match
m,d,t=map(int,match.groups())
(w/'README.md').write_text(f'''# Paid acquisition, physical row selection and retained controller work

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

All **{m} new modules**, comprising **{d} generated declarations and {t} theorem
constants**, pass strict `autoImplicit=false` / `warningAsError=true` compilation,
ordinary-root fifteen-linter checks and transitive standard-axiom audits.
All {m} isolated objects are byte-identical to their canonical objects.
Dependency pins use **{x['actual_compiler_imported_modules']} actual compiler-imported module names**;
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
''')
(w/'journal-append.md').write_text(f'''

## Paid acquisition, physical selection and aggregated controller, 2026-10-27

Packet: docs/research-evidence/semiprime-acquisition-clock-20261027.
Goal ACTIVE; substantive formal execution/cost PROGRESS. Prior paper-level
N^o(1) factoring bit-time with subexponential storage remains. The complete
kernel-checked original-input primitive bit clock is still OPEN. Native long
query remains softK^1.25; no practical timing improvement is claimed.

{m} NEW modules strict+ordinary-root15+all-generated standard3 PASS:
{d} declarations/{t} theorem constants. All{m} isolated objects byte-identical.
{x['actual_compiler_imported_modules']} ACTUAL compiler-imported module source/object pairs fully resolved,
unchanged before/after. Dependencies pinned, not rebuilt; old SAT audit frozen.
Prior2349 files,24 concurrent files,2 append-only prefixes preserved. No push.

PaidFiniteEnumerationLists/Enumerations build actual finite menus, cached word
coordinate arrays and full zero scans; exact old ordering and polynomial
indexed-work bound. PaidEnumeratedSource/Constraints attach indexed acquisition
to actual original coefficient/integer-family producers; no supplied list,
label, packing, row or coefficient answer. Public Macro graph lists are a
SEPARATE setup obligation, not silently paid by this source enumerator.

PaidConstraintCache/Rows/PackingSnapshot/Acquisition/OriginalConstraints acquire
actual chosen labels, buckets/minimum/addresses, cached universal numerators,
all padded row names and the Q*r*p*n integer table. Native acquisition has a
closed fixed-polynomial envelope using2^(2Q)<=D and blocks<=M; every owner scan
and universal/address/label read is retained. Four literal list reads return
exact old matrix entries ON HEAD COLUMNS. Stored rows are untruncated; future
builder must select those columns or mask. Source/constraints currently repeat
label/packing acquisition; pay both unless actual shared storage is supplied.

RowSelectionBitArithmetic/Bits execute full original-row selector on physical
rational words: cached residual, firstpivotbit scan, normalization, backupdate,
flags and selectedIDs. run_decoded_eq proves exact old whole-state equality.
run_clock gives explicit fixedpoly m,n,W,rowcount; intermediate Fits derive
from original C bound and actualpivot minors, no state/minor/output advice.
Original integerword encoding and template acquisition remain to execute.
Clock combines bitprimitive work and finite-list/metadata control; literal
bitaddress/tape simulation remains separate. Independent reviews PASS.

PaidPrefix/Decoder/Public/ScheduledController retain every actual counter
report once/query, actual index scans/finite range lists/decoding/fallback.
N-only run accepts onlyN; all-natural exact output/soundness/completeness.
Uniform fast bound remains conditional on B for actual CachedSourceCounter
report; paid terminal callback budget derived. Current finalcounter STILL
uses old raw/build and initial enum outside its source/native report. New
acquisition/physicalselector replacement is not yet joined there. No whole
bit theorem inferred from generic hb or report-retention identities.

NEXT: execute bounded integerword encoding and cached head/group/design build;
feed acquired integerfamily into physicalselector once pernode/head; substitute
actualcomplete setup into ONE counter and derive uniform B; charge public graph,
schedule/guard and all source/native/Hermite/controller arithmetic/memory/control
primitive costs; only then apply existing MaterializedRate for formal1/6.
Do not restart representations/numerical campaigns or require polynomialspace.
''')
print({'modules':m,'declarations':d,'theorems':t,'imports':x['actual_compiler_imported_modules']})
