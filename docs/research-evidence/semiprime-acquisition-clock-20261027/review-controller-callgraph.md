# Independent current acquisition/controller callgraph check

PASS within stated scope; read-only review. Pins review-controller-callgraph-pins.json. No files edited.

The actual final scalar/list controller calls:

    PaidScheduledController.run N
      -> PaidPublicController.factor/search/prefixRun
      -> PaidPublicController.counter
      -> SEALED CachedSourceCounter.count
      -> SEALED MaterializedOriginalSource.acquire + old raw/build designs
      -> materialized native counter/Hermite.

It does NOT yet call NEW PaidEnumeratedSource, PaidEnumeratedConstraints or RowSelectionBits. Their existence and semantic equality do not automatically substitute these new producers into the old counter. The controller's source/native report is retained, and at most one initial plus one per-wire count query is aggregated, but any bound passed to factor_work must bound that actual old counter report. The public callback is not an arbitrary count oracle: it is explicitly CachedSourceCounter.count. Its bound premise is a later resource composition obligation, not the correctness hypothesis for the result.

Prefix restrictions remain on original scopes; every returned counter result is acquired once per branch. False-first choice keeps the chosen actual positive branch, not a mixture of witnesses. The scheduled runtime has only N as input, preserves original fallback value and all-natural soundness/completeness. The new fallback allocates its trial range and charges each tested remainder as a scalar event, not a full division-bit clock. The literal schedule/guard and old public edge-list construction remain separate costs, as its module header says.

The new enum-inclusive source and constraint wrappers are actual executable producers with retained setup work and exact old values. Their correct integration is a NEW full-setup counter that calls them (or shares one acquired enum record across both), materializes head matrices, executes the new physical selector, and retains all setup work before the native count. The present fifteen-module collection is progress toward that join, not a completed replacement at the final runtime endpoint. Module docs correctly keep old raw/build, setup and primitive bit refinements open. No hidden final-counter substitution or whole-bit-time claim was found.
