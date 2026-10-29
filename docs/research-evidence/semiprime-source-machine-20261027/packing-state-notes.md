# Executed packing state and row-name invariants

NEW `SemiprimeSourcePackingState` adds proofs only; every runtime function is the frozen actual packing/snapshot/name constructor. No correct packing, label function answer, desired heap bound or producer work budget is assumed by the numeric/state results.

For original incidence-list length M and universal-key-list length D, the actual labels list has length M; its incidence fields are input members and both Q-coordinate words have colours below r. Every bucket has only original cached incidence IDs and has length at most M. Their materialized bank has D rows and at most DM incidence payload cells. Every minimum recursion suffix returns at most its original cap M. Every position recursion suffix returns at most its original scanned-list length. In the actual `place` call the looked-up bucket/default list has length at most M, so the internal position scalar is at most M even if the eventual address is a leftover. Emitted addresses have block ID strictly less than the actual minimum and hence M, and retain their original label.

`PaidPackingSnapshot.acquire` stores exactly M address rows and a block count at most M, without a semantic packing premise. `blockNames_bound`, `names_bound` and `snapshot_names_bound` show generated block IDs are bounded and labels come from the original keys; leftover IDs are original incidence-list members. Actual snapshot row-name count is at most MD+M. All blockNames recursion-frame lengths at depths below the actual block count are bounded by MD. `original_packing_bounds` instantiates these statements at the actual computed-word producer and original source enumerations, including original x/y scale expressions, rather than leaving a producer-answer interface at the caller.

Several storage counts are attached to the SAME executed report. `mapPaid_cells_le_work` retains callback charges and output cons cells. `labels_cells_le_work` pays label pair/list constructors without requiring any producer-cost hypothesis. `bucketAllocations` follows the actual equality branch and counts its new cons cells; it equals actual output length and is at most the actual bucket work. The bucket-bank allocator includes its output list and all callback allocations. `blockNameAllocations` follows actual recursive block collection plus append copies; `name_allocations_le_work` also includes the leftover collector and final append copies. None substitutes an independent algorithm or a measured cost oracle.

`bucketFrameCells` is a conservative proof view of all returned suffix lists, bounded by (M+1)M; it is not a runtime supplier or an asserted live heap. `retainedCells` explicitly counts the principal input key/vertex fields, cached label fields, bucket bank, snapshot addresses and generated names. It is bounded by

```
M + D(2Q+1) + M(2Q+2) + D + DM
  + M(2Q+4) + (MD+M)(2Q+3) + 1.
```

This field/payload model counts original opaque incidence IDs as fields, and type-indexed universal coordinates as 2Q fields. It does not assert unit bit width for incidence IDs, actual array/closure representation, all simultaneously live recursive frames, allocator bookkeeping or a deterministic tape/address simulation. Original finite index encodings and a whole reachable-state/storage join must still attach those costs. Previous all-input packing correctness and paid work results remain unchanged; this module supplies additional actual state invariants needed by that join.
