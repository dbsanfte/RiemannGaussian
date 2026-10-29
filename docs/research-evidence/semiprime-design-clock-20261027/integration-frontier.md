# Actual original-input design integration and the remaining clock

## Executed connection

The new endpoint is `SemiprimeFullSetupScheduledController.run N`. Its fast branch calls `FullSetupPublicController.factor`, which performs actual prefix count queries and physical factor decoding. Each query calls `FullSetupCounter.count`:

1. Execute `PaidFiniteEnumerations.indexed` once and retain its full report.
2. Execute `MaterializedOriginalSource.acquire` on that enumeration; retain coefficient source arrays and its report.
3. Execute `PaidRawAcquisition.acquire`: original head/assignment metadata, the entire original integer family, literal padded row count and actual measurement-bound power. All separately executed deterministic searches are charged; no shared-search saving is assumed.
4. For every interpolation node execute `PaidRuntimeDesign.build`. It filters the original head columns, obtains report-bearing integer entries, encodes them in bounded signed binary words, invokes the physical selector once per head, and copies selected ORIGINAL integer rows from the same cache. Cache both grouping directions, assignments, bounds and measurement values.
5. Execute the existing materialized native fibre/summary contraction and Hermite scalar reconstruction using those designs and coefficient arrays.
6. Sum enumeration, source, raw, every design, native-counter and joining reports. The public wrapper retains the resulting report on every actual count query, plus prefix/floor/decoder/controller work.

The old `AcquiredSourceCounter.raw`, `RuntimeDesignAcquisition.build` and scalar `selectedIndices` are proof comparison endpoints here. They are not executed to supply a selection or layout in the new fast path. Shape/head metadata scans still have a separately stated scalar/cached-read model and polynomial allowance, not a completed literal tape simulation.

## Exact data and selection

`CachedRawConstraints.data_eq` identifies the ENTIRE acquired raw record with the old searched record, including original padded row ordering and zero entries outside each head. It is stronger than equality restricted to selected head columns. `PaidSourceMetadata` explicitly caches the incidence/type dimensions and the chosen word list, then materializes all variable and factor coordinates, including unowned ones. `PaidRawAcquisition.acquire_raw` transports dimensions and row indices correctly; its callbacks read retained data only.

The number of padded rows is at most M*D+M, where M is the incidence menu length and D the universal-type menu length. Raw acquisition has a closed fixed-polynomial selected-operation envelope. Each cached raw read is at most `2*(Q+r+p+n)+14` in its stated scalar/list ledger, where p is the ACTUAL retained row count.

The measurement width is acquired from parameters only:

    bits(B,Q,R) = B + 2 + 2*R*(Q+3)
    measurementBound(B,Q,R) <= 2^bits(B,Q,R).

The physical encoder accepts every integer with absolute value at most 2^bits, including both endpoints. No encoded row, pivot minor, basis, intermediate Fits, or selected-index answer is input. Selection returns the exact former selected original-row IDs, with all actual matrix-entry callback reports retained. The complete builder has one explicit polynomial selector budget per head, column scans, selected-cache reads, and its stated metadata/cache allowance.

`FullSetupCounter.physical_design` uses original occurrence and interpolation guards to prove each executed new design equals the old correct design. `count_correct` then yields the original network contraction. The public specialization uses actual occurrence bound B=2. `FullSetupScheduledController.run_value`, `run_sound` and `run_none_iff` retain all-natural correctness; `eventually_run_fullSetup` proves that sufficiently large inputs execute the new branch. These are semantic and executed-cost integration results, not a completed asymptotic clock theorem.

## Remaining work toward the formal scaling result

The public fast-work theorem still assumes a uniform B bounding the ACTUAL new internal counter report for reachable prefixes. The counter is fully specified and executed; B is an open quantitative theorem, not a supplied runtime oracle. The next useful slice is to discharge it from the existing resource envelope, using actual head/rank/summary bounds rather than the exponential-in-n trivial bounds. Repeated source/raw setup per query must remain in this bound.

The full original-input primitive-bit clock additionally needs public macro graph/scopes/coordinate acquisition, schedule/guard computation, literal address/index/metadata operations, native rational/Hermite intermediate widths and arithmetic, floor and fallback arithmetic, and the complete controller composition. In particular `SourceArrayAcquisition.read` uses the enumeration equivalence inverse; its finite index search has no free constant-time bit implementation. The builder's finite shape/grouping allowance is not an independently instrumented primitive memory machine.

The existing `MaterializedRate` theorem can be applied only AFTER the actual whole-program clock is bounded by the appropriate fixed polynomial in the subexponential resource envelope. No such application is made in this packet. The earlier reviewed paper-level N^o(1) bit-time route allowing subexponential space remains separate; this packet advances its formal execution connection. Native long-query soft-K^1.25 and practical timing claims are unchanged.
