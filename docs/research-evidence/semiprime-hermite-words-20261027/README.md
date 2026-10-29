# Executed physical Hermite reconstruction, 2026-10-27

Status: **progress; the full original-input primitive bit/address clock remains open**.
The actual factoring caller now keeps query packets as binary words through
Hermite reconstruction. Its cardinal construction, normalized inverse,
quotient convolution, evaluation and final accumulation execute on words.
Only the final scalar count crosses the existing rational/floor boundary.
Original source guards supply all intermediate arithmetic fits and packet
heights internally. This is a caller implementation and cost refinement, not
a new asymptotic theorem or a finite-instance factoring campaign.

## What changed

`CardinalInputBits` acquires the original slopes in their exact order. It encodes
integer indices, performs physical signed subtraction and reciprocal construction,
and copies each cached slope J times. The self-node slope is literal zero.
The negative evaluation point is acquired from the same target index. Its value,
width, common Q! representation and explicit acquisition budget are proved.
The initial natural index/digit operations remain an explicit scalar boundary.

`AffineJetBits` mirrors the scalar cardinal builder, retaining the singleton
empty product and computing each recursive suffix once. `NormalizedInverseBits`
executes the cached inverse recurrence. Its constant coefficient is 1, so no
reciprocal coefficient or pivot is supplied. Original shared denominator bounds
control every partial dot product and sign operation. The evaluation modules
execute the actual affine-at-zero product and ascending-power evaluation;
`ScalarWordSum` retains each chronological callback and its complete clock.

`HermiteWordWidth` combines sufficient widths for those stages from original
packet bounds and public dimensions. `HermiteNodeBitsCorrectness` proves the
whole physical node equals intrinsic Hermite and retains its common output
representation. `AcquiredHermiteBits` proves the complete streamed reconstruction,
validity and all-prefix bounds. Its clock includes every actual packet callback,
every physical node stage and every physical addition. Value equality with the
previous scalar consumer is proved separately from these new reports.

`WordPacketHermiteInput` discharges the apparent common-packet-height interface
from the original source and actual query nodes. It allows different node layouts:
a proof-only product denominator clears all packets, while the sum of their
actual node widths gives a sufficient public bit exponent. This denominator is
never manufactured on the runtime path. No packet value, intermediate fit,
inverse, cardinal coefficient or arbitrary group-work budget is supplied.

`HermiteBitsCounter` caches source getters and interpolation-node words once,
passes its actual word nodes directly to physical reconstruction, and retains one
final scalar decode allowance. Its budget pays original group and node reports,
new Hermite work, cached acquisition, all encoders and retained control costs.
`HermiteBitsSetupBudget` proves the exact split into actual existing setup,
additional actual source encoding, and actual new counter work. The public and
scheduled callers invoke this path and have all-natural correctness proofs.

## Evidence

The [verification record](verification.json) gives exact counts for all 19 new
modules. [Combined checks](CombinedHermiteWordsAudit.lean) import the ordinary
repository root, run its 15 linters, and inspect transitive axioms for every
generated declaration. Isolated objects are compared with canonical objects.
All imported dependency names come from the actual compiler environment header;
every source/object pair is resolved and pinned before and after replay.

Independent reviews cover the [affine builder](root-affine-review.md),
[whole intrinsic node](review-hermite-node.md), and
[actual caller and retained costs](review-hermite-callpath.md).
Small physical controls check signs, empty prefixes, cancellation, slope order
and complete interpolation. These are functional checks, not scaling evidence.
The [manifest](manifest.json) and [provenance](archive-provenance.json) record the
sealed evidence. Older files and concurrent work are preserved; there is no
commit or push in this checkpoint.

## Remaining route to 1/6

The new controller still needs its own public resource/rate composition. The
frozen `FullReportRate` results apply to an older mixed-report controller and
cannot transfer by value equality. The paper-level time-only factoring route
with subexponential storage is unchanged; no new native long-query exponent or
practical speedup is claimed here.

The rational jet and Hermite arithmetic now have executed word implementations
on the caller path. Original source production and canonical source encoding,
scalar cached-head tests, graph/schedule/floor/fallback operations, natural
control and finite memory/address refinements remain. The control and final
decode allowances are retained ledgers, not already complete primitive-machine
clock theorems. Those remaining obligations, and the new public rate join,
must close before claiming guaranteed full bit-complexity 1/6 scaling. The
[whole-clock handoff](next-whole-clock-handoff.md) identifies the next proof route.
