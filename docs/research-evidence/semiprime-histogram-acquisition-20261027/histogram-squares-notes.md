# Actual physical streaming square-count histogram

Two NEW modules implement and verify the generic internal key-list consumer needed by the sixteen original feature passes:

* `SemiprimeSourceHistogramSquares` — executed Boolean trie/counter fold and exact semantic invariants;
* `SemiprimeSourceHistogramSquaresBounds` — original-input physical widths, complete retained clock and node inventory.

No prior source was edited. The original feature-key acquisition must supply and pay for its actual key list separately; no caller-supplied frequency, histogram, count, truth or encoded counter is accepted.

## Executed algorithm

`State` stores the actual trie, compact total bits and cumulative clock. `initial` is empty trie, empty zero bits and clock 1. For every key, `step` materializes exactly once:

1. `HistogramTrie.bump state.trie key`, returning a physically copied old frequency k and the updated trie;
2. `CompactBits.increment (false :: changed.old)`, physically acquiring 2k+1 by little-endian shift and increment;
3. `CompactBits.add state.bits term.bits`, acquiring the new compact total.

The state clock retains the previous clock, all three lower reports, key/returned-payload length-control visits and fixed control. `fold` traverses the original key list chronologically. It adds its actual recursive branch/done control. `acquire` invokes that fold from the real empty state.

There is no second lookup to acquire k, no native integer encoding of k or the total, no loop over pairs, and no final enumeration of distinct bins. The proof-side `collisions` double sum is never called by runtime `step`, `fold` or `acquire`.

## Exact semantic endpoints

`step_value` proves the actual physical total becomes old total+2*old frequency+1. `collisions_append` proves appending one original occurrence creates exactly the same number of ordered equal-key pairs.

`Good processed state` names literal occurrence counts at EVERY trie query, the exact original collision total, compact stored counters and compact total. `initial_good`, `step_good` and `fold_good` establish this invariant by the actual recursion. It is not a desired final-state premise supplied by the public `acquire` caller.

The final endpoints are:

```
lookup_final keys key:
  bitValue (Trie.lookup (acquire keys).trie key).bits = keys.count key

acquire_squares keys:
  bitValue (acquire keys).bits = Σkey∈keys.toFinset (keys.count key)^2.
```

These cover absent keys, duplicate occurrences, the empty Boolean key and keys that are prefixes of other keys. Trie terminals distinguish a prefix counter from all descendants. Key equality here is exact physical Boolean-list equality; a caller encoding semantic tuples must prove its chosen encoding injective/canonical, not silently identify padded aliases.

## Original-derived widths and clock

Set M=keys.length and assume only that each actual input key has length ≤B. The proof derives from literal counts:

* every final counter ≤M and compact width ≤clog2(M+1);
* total collision count ≤M² and compact total width ≤clog2(M²+1);
* every reachable processed-prefix count/total has the same corresponding original cap;
* the internally selected common arithmetic width is
  `W(M)=clog2((M+1)^2+1)+2`, including the actual shifted old counter and its increment;
* the actual current trie has at most M(B+1) logical nodes.

`step_clock` uses the proved prefix invariant, qhol's actual `bump_clock` bound, and the real compact increment/add clock bounds. No arbitrary arithmetic or intermediate Fits hypothesis is provided. The final theorem has ONLY actual input key-width premises:

```
acquire_clock keys B (forall key in keys, key.length<=B):
  (acquire keys).clock <= M*(100*(B+W(M)+2)+103)+2.
```

Thus the retained primitive-arithmetic plus finite/native metadata ledger is O(M*(B+log(M+1))). `width_mono` and `budget_mono` allow larger original caps without an oracle. The empty input has total=0 and clock=2, and satisfies the same theorem. Node and word bounds are actual recursive data-structure bounds, not a supplied maximal live-state condition.

The trie backend explicitly reuses immutable untouched sibling references. The current logical-node inventory bound does not purport to count every obsolete persistent version, host stack frame, physical pointer/address bit or primitive auxiliary heap allocation. Input key production, full machine representation, pointer/cell encoding and final public caller composition remain separate. This module does not transfer the clock merely because its numeric result equals an older histogram.

## Tiny executable control and evidence

For the exact list `[[], [false], [], [false,true], [false]]`, executed prefix totals are `[0,1,2,5,6,9]`. The final counter is 9, selected lookups are `[2,2,1,0]`, retained clock is 799 and current trie has 3 nodes. Empty input returns `(0,2)`. These are deterministic algebra/data-structure controls, not factoring examples or a complexity experiment.

Both canonical strict builds pass with autoImplicit=false and warningAsError=true. Ordinary-root fifteen linters and all-generated standard-three-axiom checks pass: core 54 declarations/28 theorems; Bounds 29 declarations/26 theorems. Separate output-path recompiles are byte-identical. Exact pins are in `histogram-squares-verification.json`.
