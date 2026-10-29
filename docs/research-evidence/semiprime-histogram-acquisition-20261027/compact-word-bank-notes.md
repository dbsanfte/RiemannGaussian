# Direct original-input compact word IDs and physical bank

Two NEW modules replace the padded-ID acquisition path without changing any frozen source:

* `SemiprimeSourceCompactWordIds`: actual compact ascending ID acquisition;
* `SemiprimeSourceCompactWordBank`: actual original coordinate rows plus those directly acquired IDs, with the existing Bank data type.

## Executed IDs, not a proof-only re-encoding

`CompactWordIds.ascending current n` executes a physical `CompactBits.copy current`, a physical `CompactBits.increment current` (including high-zero trim), and the remaining recursion. It retains copy/increment reports and loop/cell control. `acquire n` starts from literal []. It never acquires the old padded sequence and never receives advised encoded indices, a final menu, or a numeric-ID callback.

Theorems prove its bitValues are exactly range n in order, length n, every acquired word Compact, no duplicate ID, and the actual first ID is [] when n>0. `compact_value_injective` proves canonical physical magnitudes with equal bitValue are equal lists, by tail/parity induction including the compact-zero boundary.

Every acquired ID has actual physical length at most `clog2(n+1)`. This is derived from its compactness and its proved in-range value, not a width premise. The full acquisition clock is

```
(acquire n).work <= n * (30*(clog2(n+1)+2)+20) + 1.
```

The constructor even pays its last unused next-counter increment. The generic induction assumes only compactness of its actual current input and a numerical original remaining-count cap; the final original zero-initialized endpoint discharges both. There is no intermediate Fits or callback clock oracle.

## Actual bank

`CompactWordBank.acquire r Q` first materializes the actual `SourceWordBankRows.rows r Q` once, then executes `CompactWordIds.acquire table.value.length` once. Its output is the ordinary pure runtime Bank {rows,ids,clock}; no Word-valued function, Data certificate, polynomial index or decoder enters the runtime signature. Its clock retains the complete row and compact-ID acquisition reports plus original finite setup/list-size control.

The old padded-ID `SourceWordBank.acquire/ascending` does NOT occur in this runtime body. It occurs only in proof-side row/reader equalities used to reuse established physical-row theorems.

The actual rows have cardinality L=r^Q. The new ID bitValues are exactly range L, its IDs are Compact with widths <=clog2(L+1), and the IDs decode to the canonical finite words in EXACT original order. `ids_indexed` gives the original zero-first/filter-tail indexed menu, not merely coverage or a permutation. Default membership/head/decoded-zero/nonempty and decode injectivity are proved for the new acquired menu. This includes r=1 and Q=0. The semantic complete-word decoder is the frozen proof-only function of bitValue; no decoder runs during ID or bank construction.

`readRow_coordinates` proves the new valid ID reads the original decoded coordinate row, even if the old padded ID for the same value had different bits. It uses the actual rows' canonical coordinate ordering, not an assumption that new compact IDs belong to the old padded menu. Actual physical row validity and width r+1 and exact Q coordinate length are proved. `readRow_eq` equates whole reader reports ONLY for identical address bits and identical cached row data; it does not transport acquisition work or equate differently padded-address clocks.

`readRow_clock` keeps the actual row scan explicit and uses the NEW logarithmic address width. It remains a linear-in-bank-length reader, not an indexed constant-time or hash lookup claim. Candidate sweeps can instead traverse the already acquired row/ID lists together if a later algorithm requires near-linear total access.

## Original setup bound and remaining scope

For L=r^Q, the proved bank clock is at most

```
colourBudget(r) + 2 + Q*rowStage(r,Q,L) + 3
  + L*CompactWordIds.stepBudget(L) + 1 + L + 4.
```

The colour acquisition and all cached-tail row construction/copy/list stages are the established ACTUAL original physical row producer, retained in full. `rowStage` is linear in L for fixed original r,Q; the new ID stage is O(L log(L+1)). There is no L² padded-ID term and no need to pay such a term before trimming IDs. Colour production/native row-list/control overhead remains explicitly present; no claim is made that it is linear in binary log r.

The actual old public controller still uses its frozen original bank until a new caller explicitly invokes this constructor and adapts menu validity to the new IDs. Exact word-order equivalence enables that adaptation but does not itself transfer any clock. This deliverable closes direct compact ID/bank acquisition; tuple-key framing, original prefix state, histogram caller integration, physical address/storage representation and the full public primitive machine clock remain separate joins.

## Verification and executable controls

Both canonical strict builds pass with autoImplicit=false, warningAsError=true. All fifteen root linters and all-generated standard-three-axiom checks pass: IDs41 declarations/33 theorems, Bank27 declarations/25 theorems. Separate output-path builds are byte-identical. Pins appear in `compact-word-bank-verification.json`.

A deterministic structural control acquires IDs0..7 with lengths `[0,1,2,2,3,3,3,3]` and retained work488. The actual r=2,Q=2 bank gives ordered coordinate rows `[[0,0],[0,1],[1,0],[1,1]]`, IDs0..3 with lengths `[0,1,2,2]`, clock479. Q=0 has one empty row and literal empty ID; r=1,Q=3 has one three-coordinate row and empty ID. These exercise actual new constructors, not the old padded bank. They are not factoring examples or timing evidence.
