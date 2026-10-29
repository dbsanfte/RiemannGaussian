# Independent read-only review of paid original integer constraints

PASS for exact finite semantics and the stated scalar/list/register report
scope. Reviewed `PaidConstraintCache`, `PaidConstraintRows`,
`PaidPackingSnapshot`, `PaidConstraintAcquisition`, `PaidOriginalConstraints`.
No source changes or duplicate build/audit performed by this review.

## Semantic checks

- ConstraintCache acquires the Q-by-D-by-D original numerator family and the
  clearing power of two once. Later `read` performs actual node/key/key scans.
  Its joint-head/slot tests and equality correction match the original padded
  universal constraint, including all zero branches and R-1 Nat subtraction.
  Completeness of keys is sufficient for the first-position lookup proof;
  repeated keys would repeat identical constructed rows rather than introduce
  a hidden distinctness premise.
- ConstraintRows computes complete-block entries from the actual cached
  original incidence address. A different block contributes zero; an uncovered
  incidence contributes zero to every complete-block row. The proof correctly
  uses the complete-block injection and lookup, not a free inverse-packing
  answer. Leftover rows check no address, the actual head, and equality of the
  named original incidence. That branch executes the label producer even when
  the address exists, and its work includes that producer call.
- The owner pullback actually scans ALL original incidences for each variable
  and sums matching entries. Its budget pays that full M factor; it does not
  assume a short owner-fibre list has been acquired from the owner load bound.
- PackingSnapshot genuinely retains labels, bucket lists, minimum, and output
  addresses from the SAME acquired run. The extra metadata field does not
  repeat the source label search, and the work proof retains all lower reports.
- Row names are all natural block IDs crossed with the full universal alphabet,
  followed by all original incidences. `names_packing` proves precisely the old
  padded enumeration order after encoding dependent block IDs. Entries are
  materialized as Q/head/row/original-variable lists in that order.
- OriginalConstraints closes the generic producer premise using the ACTUAL
  original computed label producer. No final label, packing, integer row,
  locality, rank or acquired matrix answer is a runtime input. Its final read
  executes four nested list scans and has the claimed stored-dimension bound.

## Crucial scope: head columns versus global truncation

The stored table is the UNTRUNCATED original owner-pullback row family. The final
`read_acquire` theorem correctly requires

    head owner factor en eps t v = g.

Only on that actual head column does it identify the stored entry with the old
`SourceConstraintAcquisition.matrix`. The old matrix additionally truncates
outside-head columns. The new family must not be installed as that global
matrix without applying the same head mask in the future runtime builder.
There is no global old-matrix equality theorem here, and the current source
comments/theorems do not assert one.

## Caching and size accounting

`acquire` obtains the packing snapshot, universal cache, row names and entire
entry table into actual let-bound lists before reads. Runtime `read family`
uses those stored lists; spelling `read (acquire ...).value` in a theorem does
not mean a future caller may reacquire the whole family for each entry without
paying it. The intended parent builder must cache this `family` once.

If both source coefficient arrays and this constraint family are acquired,
the current two constructors independently reconstruct original words/packing.
The future counter must pay BOTH reports unless a new shared-cache program is
actually supplied. No free cross-constructor sharing follows from equal values.

No global Boolean assignment loop is hidden. The largest explicit universal
family has Q*D*D entries. Row names have blocks*D+M entries, and full acquisition
has Q*r*(blocks*D+M)*n original entries, each paying its M-incidence scan and
actual address/label/universal-read calls. The native polynomial theorem
legitimately absorbs the original 2^(2Q) expansion because r>=2 gives
2^(2Q)<=D=r^(2Q). `blocks<=M` is conservative but valid and sufficient for this
fixed-polynomial envelope. It is not a claim that the universal alphabet or
all row names are free.

## Report boundaries retained

Initial finite-enumeration construction, owner/factor data acquisition and
functional/index/word-coordinate access, equality of encoded descriptors,
physical list/register addressing and integer/rational bit arithmetic remain
separate refinements. Generic owner/label functions cannot be assigned a
uniform primitive bit cost solely from finite cardinalities. The final native
acquisition theorem removes label/row/budget ADVICE, but is a scalar/list
ledger theorem, not already the complete new source-to-counter/public bit
clock. In particular this constructor is not yet the final counter runtime
path; the cache-to-raw design/masking/selection join still has to execute.

No substantive semantic or stated-report defect found.
