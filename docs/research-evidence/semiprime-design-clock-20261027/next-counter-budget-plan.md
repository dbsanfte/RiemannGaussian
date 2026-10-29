# Next slice: one bound on the actual full-setup counter

This is a read-only proof plan, not a completed bound or a complete bit-clock theorem. The target is to discharge the actual `B` premise of `SemiprimeFullSetupScheduledController.run_fast_work`, uniformly over every prefix of length at most `wireCount N`. Do not replace the native controller by enumeration of all `2^n` assignments.

## Exact target and resource names

Write `L = N.size`, `n = wireCount N`, `F = factorCount N`, `I = sum_e indexedArity N e = 2*n`, `r = groups N`, `Q = points N`, `R = degree N`, `J = precision N`, `D = r^(2*Q)`, and `Aword = r^Q`. These are different from the FFT length and from the per-node selected measurement ranks. The new theorem should bound **the actual** `FullSetupPublicController.counter ... fixed).work`, with its literal full-setup execution, rather than bound an extensionally equal old counter's work.

A useful final statement is: fixed constants `C,a,d,k` exist such that on the eventual scheduled guard, for all reachable `fixed`, actual counter work is at most `C*n^a*(SemiprimeMaterializedRate.budget d n)^k`. A natural-number closed envelope can instead be used throughout, followed by a cast. Only after proving this statement should the current `run_fast_work` multiply it by the actual at-most-`n+1` queries and decoder/controller polynomial.

## 1. Close the literal setup sum first

Unfold only `SemiprimeFullSetupCounter.count` to expose the exact additive ledger:

`en.work + source.work + raw.work + sum designs.work + native.work + 10*Q + 20`.

All components already have executed work theorems:

* `SemiprimePaidFiniteEnumerations.indexed_work_polynomial` bounds enumeration acquisition; `indexed_work` is an alternative literal formula.
* `SemiprimeMaterializedOriginalSource.acquire_work` and its `budget` bound the actually attached source, including searched labels, packing, universal numerator, interpolation and pullback. Do not use just final coefficient size as a cost estimate.
* `SemiprimePaidRawAcquisition.acquire_work_native` bounds metadata plus the original padded integer family. Its `acquire_reader_work` bounds each later stored-cell read.
* `SemiprimePaidRuntimeDesign.build_work`/`buildBudget` bind the actual encoded selector call, retained original integer cache, selected row extraction, head scans and runtime metadata. Inputs are supplied by `PaidRawAcquisition.reader_value`, `acquire_bounded` and `PaidMeasurementBound.bound_le`; there is no extra encoded-word or intermediate-Fits premise.
* `SemiprimeCachedRawConstraints.acquired_count_le` gives the candidate count at most `I*D+I`. This is the **candidate matrix** dimension, not selected rank. `PaidRawAcquisition.acquire_count` connects its snapshot count to the original row family.

Replace actual enumeration lengths by the already proved `PaidFiniteEnumerations.indexed_incidence_length`, `indexed_universal_length`, `indexed_score_length` (`I^2+Q*n^2`), and `indexed_indices_length` (`n+F`). The word-tail length is at most `Aword`, via the actual filtered full-word list and `FiniteEnumerations.words_length`; it is not `Q-1`. `PaidMeasurementBound.bits B Q R` is polynomial in `B,Q,R`, even though the integer measurement magnitude is exponential in `R log Q`. This distinction is essential for the physical selector budget.

NEW BRIDGE, OPEN: package these substitutions and the finite `Q`-node/group sums into one fixed polynomial setup envelope in `n,F,I,Q,R,D,Aword`, using candidate row count at most `I*(D+1)`, head column count at most `n`, and the explicit reader budget. Do not turn the large measurement magnitude itself into an input dimension of this polynomial. The integer-to-word encoder's scalar-digit and primitive-bit categories retain their documented distinction.

## 2. Bind the actual native execution, without losing its three separate exponentials

`SemiprimeMaterializedFibreNative.count_work` is the immediate reusable whole-native theorem. It retains:

* `Cq = SemiprimeCounterEnumeration.weightedCount n (J-1)`;
* the actual `SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W` at each node;
* the one-time head acquisition factor `2^H`;
* actual local table evaluation, whose bound contains `2^w`, where `w = scopeBound L`.

Its hypotheses are just uniform head sizes, selected measurement counts, scope bounds, and original table-report bounds. Use `FullSetupPublicController.entry_work_le` with `fixed.length <= n` for both arithmetic and reads, and `PublicAcquiredExecution.indexedArity_le`. This makes the **same** `A = entryBudget N` valid at every reached prefix. Prefixing changes only the local Boolean entries; all source designs are independent of `fixed`.

Use the actual design equality `FullSetupCounter.physical_design` to expose `RuntimeDesignAcquisition.build (AcquiredSourceCounter.raw ...)`. `AcquiredSourceCounter.selected_count_source` proves each selected `m_g` is the corresponding source constraint rank. `RuntimeDesignAcquisition.headSize` and `columns` give the required exact head-subtype cardinality bridge. Candidate counts may be used as a coarse polynomial bound on `m_g`, but **not** in the exponent controlling summary count.

NEW BRIDGE, OPEN: an indexed-layout quantitative certificate with

`h_g <= ceil(3*n/(2*r))`, `sum_g m_g * (r*lambda) <= 4*n`, and actual `W_g = measurementBound 2 Q R`.

Then the literal summary product is at most

`(2*n*measurementBound 2 Q R + 1)^(floor(4*n/(r*lambda)))`.

This needs a small product/power monotonicity lemma on `PacketArrayExecution.summaryCount`, the selected-rank sum equality, and positive `r*lambda`; no genericity assumption or rank oracle is needed. The individual `hm` premise of `count_work` can be discharged by the same total rank bound, or a conservative polynomial bound. The head exponential must use the balanced `H`, never `H=n`.

Combining `count_work`, its `fibreBudget`, and the setup bound gives one complete fixed polynomial in the polynomial dimensions plus `Cq`, actual summary envelope, `2^H`, and `2^w`. Products between these resources are allowed: a fixed power of their sum bounds them. This is exactly why `MaterializedRate` proves fixed-polynomial closure.

## 3. Important enumeration/tie-order gap: do not identify two different layouts for free

The actual counter uses `SemiprimeFiniteEnumerations.indexed`, through the paid constructor. `PaidFiniteEnumerations.indexed_value` proves **exact equality of all data fields**, including list order, word-first/word-tail, scores and indices, to that indexed construction. Incidences are ordered dependent `Fin` lists, words are the explicit word enumeration with zero moved to the first position, scores retain their explicit incidence-pair/variable-pair order, and indices are variable-then-factor lists. Therefore actual deterministic ties/search results are fixed, and must remain fixed in the proof.

However, `SemiprimeConstructedCounter.layout` uses `SourceLayout.defaultEnumerations`, and `ScheduledCounter.actual_rank_budget`, `actual_summary_log_bound`, `public_summary_log_bound`, plus `MaterializedRate.public_summary_le`, `public_head_card_le`, and `actualBudget_le` currently refer to that default-constructed layout. They are **not** automatically exact identities for the indexed counter's source, and equality of contraction values does not identify their work or support cardinalities.

The preferable new bridge does **not** prove arbitrary tie-order equality. Instead instantiate the already enumeration-parametric theorems `SemiprimeSourceLayout.builtLayout_head_bound` and `builtLayout_total_rank` directly with `FiniteEnumerations.indexed`. Their proofs work for every valid enumeration, and hence for the actual searched indexed words/packing. Reuse the numerical `ScheduledCounter.packingGuard` argument (with the indexed coordinate/arity and actual incidence count), or factor that numerical argument into an enumeration-independent helper. Then repeat the short algebra of `ScheduledCounter.actual_rank_budget`/`actual_summary_log_bound` for this indexed layout. This preserves real tie order while proving the same quantitative bound. Existing `AcquiredSourceCounter.raw_covers`, `raw_from_source`, `selected_count_source` already bridge the padded family to precisely this indexed source.

An alternative is a new indexed version of the scheduled certificate from the outset. Do not assert `defaultEnumerations = indexed` or equate their selected IDs without a separate proof.

## 4. Finish with the existing actual schedule/rate statements

* `PublicAcquiredExecution.wireCount_eq`, `indexed_incidence_count`, and the macro parameter graph bounds connect the actual public network to `n=variableCount L`, total incidence `2*n`, and growing scope `<=512*L^(3/4)`. An explicit polynomial bound on `factorCount N` from the finite vertex enumeration/public graph size remains a small bookkeeping bridge if not already exported; do not assume it just from occurrence two when zero-arity factors are possible in a generic network.
* `ScheduledFactorExecution.precision_formula` identifies `J-1` exactly with `ScheduledSupportRate.cutoff n`. Thus the actual support count is the one bounded by `scheduled_support_subexponential`, not a fresh cutoff or full assignment count.
* `CounterRate.scheduled_dimension_budget_input` proves `D^128 < 2*n`; `scheduled_dimension_square_le` is its real envelope. The finite source menus therefore contribute polynomial preprocessing, rather than a hidden exponential in `n`. The other scheduled scalar dimensions and the width `PaidMeasurementBound.bits` are polynomially bounded.
* Reuse `SourceLayoutRate.source_summary_binary_rate`, `source_signature_base_le_power`, `source_inverse_group_budget`, and the source rank/head calculations to obtain the **indexed** summary/head envelopes. `MaterializedRate.budget` is independent of enumeration, so `public_fixed_polynomial_subpower` and `public_fixed_polynomial_sixth` can be used once the actual indexed work is bounded by a fixed polynomial in that budget. There is no need to pretend the default-layout `actualBudget` is the indexed runtime.
* Finally supply the single proven actual-counter bound to `FullSetupScheduledController.run_fast_work`. The resulting controller bound includes at most `n+1` actual source acquisitions/counts and the decoder, rather than silently sharing setup across queries. A later actual setup cache could improve constants, but cannot be assumed by this theorem.

## Deliverable boundary

The next substantive slice should produce the single uniform `FullSetupCounter.count.work` theorem and its public-prefix specialization, including the indexed quantitative certificate above. That closes the **current mixed report** premise B. It does not, by itself, turn scalar source construction, digit extraction, schedule guards, arbitrary data addressing or every rational operation into a single literal primitive-bit/tape execution theorem. The existing rate theorem is ready to consume a fixed polynomial resource bound; it is not itself that missing execution refinement.
