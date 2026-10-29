# Paid runtime design acquisition

The two NEW modules `SemiprimeRuntimeDesignCache` and `SemiprimePaidRuntimeDesign` are strict-compiled and frozen. The latter supplies `build d source bits : SemiprimeMaterializedSourceUniversal.Run (RuntimeDesign n F)`. Here `d` is a pure raw integer design and `source` returns an `IntRun` for each original integer cell; no Layout.Data, polynomial, basis, selected-index answer, encoded-word answer or fit oracle is a runtime input.

`build_eq d source bits hs hb` proves exact equality of the returned runtime design with the old `RuntimeDesignAcquisition.build d`, assuming only that source cell values equal `d.rows` and their absolute values are at most `2^bits`. These are correctness/height premises about actual original inputs, not selection answers. Every old scalar `selectedIndices`/`build` reference is proof-side; the new runtime uses the actual physical `EncodedRowSelection.select`.

The program acquires finite global indices, caches original head labels, scans columns once per head in canonical order, invokes the integer encoder/physical selector ONCE per head, and retains the selector's SAME acquired original integer matrix. It reads selected rows from that retained matrix, not from the original callback again. The resulting selected row arrays, grouping directions, W and assigned-factor metadata are cached. The returned dependent `h` shape is the original bounded head-size filter; it is not claimed memoized. Its finite metadata recomputation is included in the stated coarse metadata/cache allowance, under the explicit cached-scalar raw-field model. It contains no repeated elimination or search.

## Exact retained work

`group_work` bounds each head by

```
groupBudget(m,h,b,B) =
  EncodedRowSelection.budget(m,h,b,2h+B+4)
  + m(2m+5h+4) + 10m + 5.
```

The first term includes source reads, scalar integer encoding, original matrix storage, template/IDs, and the ENTIRE physical selector. Each source callback is acquired once per matrix cell. The remaining terms cover selected-original-row list reads/copies and report-list construction.

`build_work` proves the actual returned work is at most

```
3(n+1)^2 + r(5n+1)
+ sum_g groupBudget(count_g,headSize_g,b,B)
+ 100(n+F+r+1)^4 (1+sum_g count_g).
```

This is an explicit fixed polynomial ledger in finite dimensions, bits and cached-reader budget: headSize_g<=n and, if count_g<=M, there are r polynomial summands with row dimension at most M. The frozen encoder budget and selectorWidth are literal Nat polynomials; no asymptotic rank or intermediate-size answer is assumed. The last term is a deliberately coarse scalar/list metadata/cache allowance, not a proved physical address/tape simulation. Scalar integer digit extraction has its existing explicit interpretation. The physical selector's primitive arithmetic subclock is already attached, but this module alone does not turn ALL raw metadata, addresses, or whole original-N setup into a primitive machine clock.

## Checks

Ordinary strict compilation used autoImplicit=false and warningAsError=true. Root15 lint and all-generated-declaration standard-axiom checks pass:

- RuntimeDesignCache: 20 declarations, 17 theorems.
- PaidRuntimeDesign: 62 declarations, 46 theorems.

Only propext, Classical.choice and Quot.sound occur transitively. The tiny runtime control constructs a raw 1x1 integer matrix [-1], feeds the real physical selector, and reads the resulting design; it is a compiler/data-path control, not a factoring campaign or complexity evidence.

No frozen source or sealed packet was changed. Parent's cached raw/source acquisition and public counter wrappers are separate joins; equality `build_eq` permits their semantic transfer without an old runtime elimination call.
