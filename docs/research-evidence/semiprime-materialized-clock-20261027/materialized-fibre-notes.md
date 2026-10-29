# Materialized head fibres: executed arrays, native factors, and full count

This slice adds only `SemiprimeMaterializedFibre.lean`,
`SemiprimeMaterializedFibrePacket.lean`, and
`SemiprimeMaterializedFibreNative.lean`. Previous packets and modules are unchanged.
The algorithm follows the complete materialization in the sealed
`semiprime-paid-materialization-20261027/paid_integer_counter.py`, with the
allowed FULL signed summary box instead of a dictionary of attained keys.

## Runtime algorithm

1. `acquireHead` materializes exactly `2^h` records. Each record contains the
   actual Boolean word and every actual integer dot product, computed by
   `RepresentativeExecution.dotRun`. `acquireHeads` stores all heads in one
   homogeneous `Array HeadCache`, so heterogeneous head sizes do not introduce
   polynomial proof indices into executable data.
2. For a summary tuple, `acquireReps` searches the cached measurements WITHOUT
   forced bits. Its actual found word and its search report are stored once.
   The proved representative is exactly the old false-first representative,
   including the empty-fibre false-word default.
3. `scanHead` scans explicit local word codes. It compares cached measurements,
   tests actual forced bits, and invokes the value constructor ONLY for a
   passing word. It adds the resulting coefficient arrays.
4. `fibreCached` multiplies the separate head sums. `sumCached` decodes and visits
   the full paid mixed-radix summary box; no product of head-assignment sets is
   enumerated. Empty summary fibres contribute zero.
5. `Native.node` acquires head tables ONCE outside the entire signed-support
   traversal. Each value constructor is the EXISTING real `nativeGroup`, which
   runs `nativeLocal` from supplied source coefficient arrays and paid original
   Boolean entries. No group value, fibre value, representative, Taylor packet,
   or count answer is an input.
6. `Native.count` invokes these actual nodes and the existing executed Hermite
   reconstruction. Its correctness theorem returns the original tensor
   contraction under the existing source-row/design/degree hypotheses.

## Formal endpoints

- `acquireHead_size`, `acquireHead_entry_sizes`: actual local allocation sizes.
- `cachedRepresentative_eq`: cached search selects the same unforced word.
- `scanHead_spec`, `fibreCached_spec`: exact finite local sums and product.
- `fibreCached_coefficient_eq`: equality to the old verified `fibreAt`.
- `Native.fibre_spec`: existing `CounterCompose.fibrePacket`, with the actual
  native local evaluator substituted, not a free local-value premise.
- `Native.node_spec`: actual global Taylor coefficients.
- `Native.count_correct`: original contraction, with no count oracle.

## Work and boundaries

`acquisitionWork_le` bounds one-time table acquisition by

    r * 2^H * (H + M*(4*H+2) + 3) + r + 1.

`oneSummaryBudget` is explicitly a polynomial in J,r,H,M and callback budget B,
multiplied by `2^H`, plus polynomial terms. `sumCached_work` multiplies this by
`Y = summaryCount`. `Native.node_work` adds the one-time acquisition and
multiplies the summary traversal by the already proved support count Cq.
`Native.count_work` retains every node's acquisition and the executed Hermite
work. The callback budget is the existing actual `groupBudget`, including local
`2^w` traversal and paid entry reports. There is no global `2^n` loop in these
runtime definitions. The `2^n` in this paragraph refers only to global variables;
`wordCode n` in the core module uses n for ONE head's local dimension.

These `.work` fields are the existing selected rational/integer-operation,
array-access and control ledger, NOT a newly proved primitive bit-machine
clock. In particular binary mixed-radix encode/decode, dependent finite-index
bookkeeping, function-valued partition/assignment access, allocator/physical
array addressing, and arbitrary callback computation beyond its supplied
paid report retain the separate polynomial simulation/resource obligation.
The explicit local code and signed-box sizes show that this obligation need
not introduce a global assignment enumeration. This slice does not relabel
that separate bridge as already proved.

The precise remaining INPUT seam is the original source coefficient arrays and
polynomial-free RuntimeDesigns. Existing concrete source/design acquisition
modules already supply these with their proofs. The NEW generic count is not
yet substituted into the sealed N-only public wrapper; that connection is a
new integration step, not a missing scalar/group/count oracle in this code.
No polynomial-space claim is made for materialized tables.

## Executable controls

`MaterializedFibreSmoke.lean` evaluates the NEW count on runtime-only arrays
and designs: indicator/constant-one/constant-zero entries give 1,2,0. A head
with two equal measurement-one words selects the unforced representative
(false,true); forcing its first bit still leaves the distinct (true,false)
word in the local sum. The full five-key summary box returns four words.
These are exact tiny execution diagnostics, not native coverage examples,
a factoring campaign, or evidence for a new asymptotic rate.
