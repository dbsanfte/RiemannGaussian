# Independent review: physical-word row selection

PASS for the stated exact refinement and bit-primitive plus finite-cell/metadata
ledger. Read-only review of `SemiprimeRowSelectionBitArithmetic` and
`SemiprimeRowSelectionBits`; no canonical edits or duplicate build/audit.
Author confirmed final source freeze after strict/root15/all-generated audits
passed (266 declarations / 145 theorems, standard axioms only). Final source and
object hashes are recorded alongside this review.

## Runtime versus theorem inputs

The runtime `run` takes n, a literal Boolean width template, cached lists of
physical rational-word rows, and a list of original bounded row IDs. Its state
contains only physical word/flag lists and original IDs. It does NOT take C,
a logical rational elimination state, pivot minors, a selected-row answer,
intermediate arithmetic values, or intermediate fit certificates.

`run_refines`/`run_decoded_eq` use C only in specifications. The original-input
premise `hinput` supplies exactly the normal input-encoding contract: each
original row has n cached cells, a positive physical denominator, bounded
PHYSICAL padding width, and the stated original integer value. This is not an
intermediate elimination answer. `hC` bounds actual original integer entries;
`ht` identifies the chosen template width. `run_clock` additionally bounds the
input-row list length to pay the actual original-row read. These remain genuine
input/encoding prerequisites for a future source-to-selector constructor.

The semantic result is stronger than equal row spaces: `run_decoded_eq`
identifies all returned flags, rational matrix entries and selected ORIGINAL
row IDs, including their order, with the frozen actual logical selector.

## Heights, normalization and intermediate fits

Actual pivot determinants, proved nonzero by the old run invariant, give a
positive SQUARED common denominator. The representation covers active working
rows and inactive literal zeros. The denominator/numerator bit envelopes are
derived from original integer minor bounds and selected-rank<=n, not assumed.

The residual computes an ALL-column dot product. Inactive cached rows are
proved zero, so this equals the old active-column elimination without a free
active-set oracle. The physical dot loop computes each suffix once. Common
input denominators and the entire n-term count bound every multiply and partial
sum, independently of cancellation. The final sign change/subtraction, pivot
normalization reciprocal/product, and each back-update product/subtraction
have Fits derived from actual C and the corresponding original-run expression
bounds. No caller supplies these intermediate Fits.

`operation_width` is deliberately unconditional about physical clipping; it is
used for cost propagation. Semantic correctness is separately obtained from
DERIVED Fits. Thus an arbitrary too-short width is not silently declared exact.
Physical numerator nonzero scans also correctly handle signed zero; legality
of the denominator is required and propagated. Mathematical total inverse at
zero causes no hidden unit premise; the actual chosen first pivot is nonzero,
and the refinement identifies precisely that first pivot.

## Actual caches and whole-loop accounting

`runRow` and `acquirePairs` first materialize the executed report lists. Later
payload maps and clock maps/folds read those stored reports. `insert` retains
the residual cache for both pivot scan and normalization, retains the normalized
row for all updates, and stores every update report. `normalizeRow` reads its
pivot once. Each active update row reads its coefficient once. The reciprocal
itself is recomputed per normalized coordinate, but this is correctly paid by
the n-fold normalization bound; no unclaimed reciprocal cache is assumed.

The runtime never calls the old functional rational elimination. Appearances
of `run C ids`, determinant ratios, canonical Rat values and expression traces
in the proofs are erased specifications, not uncharged executable callbacks.
The traversal processes the SAME tail-first ID order as the old algorithm.

I raised the finite-cache allowance convention with the author. The final
sources conservatively charge `10*n+5` for report-list acquisition and its
payload/clock maps/folds in both runRow/acquirePairs, and `20*n+20` for the
outer insertion caches. Budgets/proofs were rebuilt accordingly. Actual list
reads are separately charged, including matrix row+cell scans and input-row
scans. Whole-loop `runBudget` is an explicit fixed polynomial in m,n,W and the
literal supplied ID-list length, including the allocated empty state.

## Remaining resource/attachment boundaries

The clock sums actual Boolean rational-arithmetic primitive reports plus
finite list-cell/register/metadata traversal allowances. It is NOT yet a
single literal encoded-Nat/address/tape-machine clock. Word references/headers,
index encoding, physical list/array addressing/copying, metadata/Nat counter
arithmetic and control-store simulation require their separate refinement.
No polynomial-space claim is inferred.

The new run does not yet acquire the original integer source family, construct
its signed rational-word encodings, acquire the width template or ID metadata,
or connect the selected IDs to the final native RuntimeDesign supplier. Those
future joins must derive hinput/ht/hshape from the actual acquired source and
retain their acquisition costs. The selector's OWN empty-state initialization
is already included; this remaining gap concerns source/input/template and
metadata acquisition, not a missing ideal selected-state premise.

No substantive semantic or stated-clock-scope defect found.
