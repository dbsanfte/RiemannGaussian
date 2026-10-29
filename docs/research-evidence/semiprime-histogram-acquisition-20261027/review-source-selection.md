# Independent original-selector review

PASS. Root reviewed the final frozen SourceHistogramSearch implementation,
its exact original count/order adapters and the existing reachable-menu controller.
The selector implementation author was the Skein agent. Live reviewed canonical
source/object pins are in review-source-selection-pins.json.

The sole runtime definition run invokes Setup.acquire once, takes that cache's
actual compact bank and actual index-list length, and supplies the concrete
Query.score closure to ChoiceBits.run. It neither acquires original score terms,
invokes the old count callback, decodes a native Word nor accepts advised scores,
counts, labels or intermediate widths. Its report retains cache.clock and the
whole controller result.work, plus the actual native index-length traversal.
There is no old-clock equality or numerical bound inferred from value equality.

The first and tail menu proofs use CompactWordBank.default_head and ids_indexed.
Thus the exact canonical original candidate order is preserved despite different
physical ID padding. candidates_valid and run_valid establish actual menu
membership, and run_length derives the actual n+F selected-ID count from actual
new metadata. The run_decode instantiation supplies structural score_valid and
query_order for every reached menu prefix; the old controller's actual
comparison and left-on-tie decision remain unchanged.

counts_indexed identifies the actual old term/indices/alphabet and reverse-prefix
environment, rather than assuming an arbitrary proportional count answer.
query_integerValue uses the independently kernel-checked original histogram
score equality. query_order then uses the existing original integer_le_iff with
r>0, lambda>0 and the exact L^4=U^2 cardinality identity. It divides by neither n
nor M, so empty incidence families and zero weight/count ties are retained.
The map of the new physical output equals the actual old indexed caller in
indexed_refines and the actual computedList for every shared proof-side offset
in indexed_original. These are all-family theorems, not fixture coverage.

The mathematical decoder and quadratic old constructor are confined to
specification/theorem declarations. Full heap/tape/native-control/report-erasure
refinement and a new public caller composition remain open. Cost closure belongs
to the separate QueryBounds/SetupBounds/SearchBudget/Resources chain; this review
does not infer a primitive-machine exponent or near-linear whole setup cost.
