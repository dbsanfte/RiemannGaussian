# Actual counter and cost join

Root-owned modules: `SemiprimeWordPacketCounter` and
`SemiprimeWordPacketCounterBudget`. Both strict canonical compiles passed;
the final combined audit and isolated replay provide their final frozen pins.

The live group callback retains `NativeGroupBits.run.words` and its actual
clock, plus the existing family-access allowance. It performs no scalar decode.
`headCap = 1 + sum_g 2^(h_g)` bounds each head and is at most `1+r*2^H`.
`nodeWidth` uses that actual head count, the actual summary count, and
`weightedCount n (J-1)`. The physical node proof derives its common denominator
and numerator bound from actual original native group representations.

The `count` implementation caches every source getter report once and every
positive interpolation-node word once. A completed node is decoded for the
existing acquired Hermite consumer. `count_value_eq_native` is strictly a value
refinement; the final work theorem follows the new call graph separately.

`group_clock_le_legacy` proves an inequality between actual reports: the old
callback includes all new physical group work plus a nonnegative rational
boundary allowance. It is used only as a conservative majorizer. The resulting
closed group bound depends on original dimensions, original entry clock/width,
actual source word lengths and row sizes. No group-work premise is exported.

`node_clock` pays every actual head/summary/support callback and word operation,
then adds `nodeControl`. Structural physical size and boundedness justify the
single completed-node decode allowance. `reductionBudget` sums those actual node
budgets and adds the acquired Hermite work bound. `count_work` then includes all
actual cached source getter reports, node-word encoders and input control.
The setup theorem discharges the source guards from the original acquisition.

This remains a mixed physical/scalar report. `nodeControl`, source parameter
arithmetic, indexing and canonical rational decoding still need a literal
primitive-memory execution refinement. Scalar Hermite arithmetic remains live.
