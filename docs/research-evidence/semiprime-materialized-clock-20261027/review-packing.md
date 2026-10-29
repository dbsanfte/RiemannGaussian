# Independent materialized packing review

PASS within the stated scalar/register/list ledger. Read-only review of frozen SemiprimeMaterializedPacking.lean; source pin in review-packing-sources.json.

Labels are invoked once per original incidence by labels/mapPaid; their returned clocks are included. Every universal bucket scans the cached labelled incidences with the actual full word-equality run; there is no re-invocation of the producer during bucket/address processing. The minimum traverses actual materialized bucket lists and pays their lengths. Each place call looks up its cached bucket, performs the actual idxOf-equivalent position scan, and compares to the common block count. This yields the original typed PackingData.lookup converted to a Nat block index, including all uncovered leftovers.

acquire_value depends on producer.value=P.label to identify the source packing; it does not assume a requested address. acquire_work also requires an explicit producer work bound and retains it M times. Its remaining terms are fixed polynomials in M,D,Q; cache labels/buckets are shared by actual lets. The theorem does not silently enumerate all complete global labellings or all head assignments.

The clock is the defined scalar/register/list trace, as the module says. Primitive bit costs, concrete function-coordinate access implementations and initial producer/finite-enumeration construction are separate refinements. A coefficient or rank supplier is not present. The subsequent SourceAcquisition adapter can compose these addresses with acquired universal arrays and original-coordinate pullback without importing an address answer.
