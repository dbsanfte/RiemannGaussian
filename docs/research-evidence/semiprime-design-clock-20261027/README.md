# Paid raw rows and physical designs in the actual factor counter

**Status: PROGRESS. Goal ACTIVE. Complete formal original-input primitive bit clock OPEN.**

This packet connects the previously separate paid raw-row acquisition and physical row selector to the actual N-only factorization controller. It acquires original metadata and integer rows, masks each head correctly, encodes the original integers, selects once per node/head, caches the resulting design, and retains every returned setup/counter report. Lean proves exact equality with the former correct counter and all-input factor correctness.

The concrete endpoint is `SemiprimeFullSetupScheduledController.run N`. Its fast branch has no row, basis, coefficient, count or factor answer supplied from outside. The old raw/build/selectedIndices routines occur only as proof comparison endpoints. See [the runtime connection and open clock](integration-frontier.md) and the independent [full-callpath review](review-full-setup-callpath.md).

## Verified scope

Ten NEW modules: **456 generated declarations / 242 theorem constants**. Strict `autoImplicit=false`, `warningAsError=true`, ordinary-root fifteen-linter checks, and every generated declaration's transitive standard-three-axiom audit pass. All ten final isolated objects are byte-identical to their canonical objects. The dependency checkpoint records **17,591 actual Lean compiler-imported module names**, each with a resolved source and object, unchanged before/after. Existing upstream dependencies are pinned rather than rebuilt. See [verification](verification.json), [combined audit](CombinedDesignAudit.log), and [isolated summary](final-isolated/summary.json).

The prior 2,443 protected files, 24 concurrent files and both append-only prefixes are preserved. One new packet note is appended to each journal. No commit or push is part of this packet.

| Modules | Advance |
| --- | --- |
| CachedRawConstraints, PaidSourceMetadata, PaidRawAcquisition | Exact original row order, head masking, full original metadata, cached callback reads and polynomial acquisition ledger |
| PaidMeasurementBound, EncodedRowSelection | Parameter-only inclusive integer width, actual signed encoding, exact physical selected IDs and original cache reuse |
| RuntimeDesignCache, PaidRuntimeDesign | One selector per head, selected ORIGINAL matrix, both grouping directions, complete retained design ledger |
| FullSetupCounter, FullSetupPublicController, FullSetupScheduledController | Actual replacement in each count query, report aggregation, all-natural correctness and eventual execution of the new branch |

Independent reviews cover [raw acquisition](review-original-raw-acquisition.md), [encoding and selection](review-encoded-row-selection.md), and [the public callpath](review-full-setup-callpath.md). The functional controls include actual negative-entry selection, inclusive encoding endpoints and empty columns, an actual one-by-one physical design, the entire empty-network counter returning `(value,work)=(1,2361)`, and finite fallback cases. These exercise runtime connections; they do not establish scaling or useful practical speed.

## What remains

The public work theorem remains conditional on a uniform bound for the ACTUAL new counter report. Closing it requires composing the acquired setup/design budgets with the actual head/rank/summary/native/Hermite bounds. The complete primitive bit/address model additionally needs public descriptor and schedule acquisition, integer encoding's scalar operations, metadata/index searches, native rational and floor arithmetic, and the controller/fallback join. The previous rate theorem is not yet applied to a closed whole-program clock. The [next counter-budget plan](next-counter-budget-plan.md) identifies the exact reusable theorems and the indexed-enumeration bridge; it is a plan, not a proved bound.

The previously reviewed paper-level N^o(1) bit-time route allowing subexponential storage is unchanged. Native long-query soft-K^1.25 is unchanged. This packet proves the execution connection needed for formal closure, not a new native soft-K bound or a completed formal N^1/6 theorem.
