# Independent controller execution review

Reviewed RepresentativeExecution, FibreArrayExecution, PacketArrayExecution and the MixedRadix dependency, pinned in the accompanying JSON. No source changes were made. This is an execution review, not another kernel audit.

## Disposition

PASS for the abstract rational-operation/read ledger and finite polynomial semantics. No expensive-closure caching error or exponential materialization was found. The exact `.work` inequalities are not primitive bit/control-step bounds without the polynomial finite-encoding overhead detailed below.

## Actual execution

`findBits` binds the false search result once and executes the true branch only on failure. Its returned word captures a path, not a retained search tree. `acquireRepresentatives` binds each measured search once and stores its found word. `fibreAt` binds this family once before the group scans. The proof-only extensional expression using `summaryRepresentative` does not replace the actual cache with repeated search.

`gateRun` takes a Unit thunk, so rejected words do not invoke the local callback. Each group scans its own assignments; `productList` multiplies those local sums. The cost is a sum of local exponential scans, not a Cartesian global Boolean scan. Empty fibres contribute zero despite their arbitrary all-false fallback representative. Representatives need not satisfy forcing; the later scan separately imposes forcing.

`sumFrom` streams a current array accumulator. `sumCodes` visits a numeric code range rather than constructing a list of summaries. `supportRun` executes its absent/S-only/S-and-U branches once each, with support cutoff J−1. A zero remaining budget follows only the absent branch. Earlier sibling arrays retained during later recursion require only depth-many arrays. `signedFibre` computes and charges actual repeated sign negation. At J=0 coefficient specifications are vacuous; production reconstruction needs positive J.

## Necessary accounting qualification and repair

* `dotRun` charges logical row/word reads and integer additions. Function-encoded words via Fin.cons, family indexing and Function.update do not have automatically constant primitive lookup cost. Cached arrays or a polynomial lookup factor resolve this.
* `summaryCode` executes div/mod decoding, but `fibreSum_work` does not count these operations. Its equivalence may reconstruct/decode components again at each access. Charge these uses polynomially in summary-coordinate count and bit length, or decode the current tuple once. Neither option materializes the full box.
* Finset insertion/cardinality/equality, group-list construction, index arithmetic and loop-counter maintenance are not all charged by the displayed exact constants. On explicit public finite coordinate encodings, they have polynomial overhead. Bit-vector supports are a straightforward alternative to the current finite-set representation.
* Arbitrary callback/indexing functions remain supplied interfaces. Their reports account for declared callback work, not a certification of arbitrary implementations. NativeLocal/NativeGroup discharge the important free factor-value callback; actual row acquisition, grouping/enumerations and primitive rational arithmetic require their own joins.

A safe concrete bound is a polynomial in public dimensions, label lengths and maximum word width times the proved ledger, plus polynomial initialization. The present closures/lists can be simulated with that overhead, or concretized as arrays/current decoded tuples. This preserves the exponential-rate envelope but is not an exact primitive-step identity. Do not use constant-time unbounded integer arithmetic or division in the final theorem.

## Memory and semantic scope

Boolean/ternary traversals retain polynomial-depth paths and sibling jets. The summary loop retains one code and accumulator. Representatives occupy r local words. No Y-sized or 2^h-sized retained list is needed. This statement is separate from a compiler/garbage-collection theorem, and rational/integer word widths still need the established height bounds.

The summary box is coarser than Python's per-row absolute radii. Extra labels are empty and gated to zero; an exact matching code enumeration is unnecessary. `rawRun_native_spec` requires a complete noduplicate coordinate list and actual fibre callback specifications. `rawRun_taylor_spec` additionally uses the native degree/certificate theorem. The callbacks are not desired packet values supplied at runtime, but their premise is discharged by the new native-group/node join, not by PacketArrayExecution alone. No whole primitive-machine runtime claim follows merely from these semantic identities.
