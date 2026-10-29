# Actual source acquisition and original-network counting

**PROGRESS, 27 October 2026.** The executed counter now constructs its own source coefficient arrays and integer measurement matrices from the original indexed network. Its Lean correctness theorem reaches the original scalar contraction without supplied coefficient, constraint, locality, selected-rank, Taylor-value or count answers. The guaranteed all-input factoring bit-time goal remains **OPEN**.

The new endpoint is `RiemannGaussian.SemiprimeAcquiredSourceCounter.count_correct`. Its runtime inputs are an original finite indexed network, local integer table evaluators, and public layout/precision parameters. The theorem assumes an owner-fibre bound, positive Q and J, the actual source interval start at most Q, and sufficient total interpolation precision. It derives the source representation and locality internally. Arbitrary table callback resource costs still have to be paid.

## What changed

* **Actual binomial acquisition:** an integer reverse triangular recurrence solves the source binomial system through its two Pascal factors. No general inverse or supplied parity vector is needed. Pascal entries, targets, solve prefixes and integer heights are proved. The fully tracked version counts its actual integer arithmetic and reads.
* **Actual source coefficients:** commuting swap differences permit a computable sorted subset order. The finite universal numerator, rational mismatch interpolation and coefficient-array interpreter are proved equal to the published source formulas. Complete blocks, leftover identities and the original-variable pullback then construct and cache the entire original source array family.
* **Actual measurement matrices:** enumerate complete-block universal rows and original incidences, giving at most twice the incidence count in candidate rows. Every semantic source row occurs, and each padded row is either zero or exactly an old row. This proves equal integer kernels and rational row spaces. Computed original-row selection therefore retains exactly the source rank and entry bound. No mathematical choice of a finite row numbering is executed.
* **Actual source-to-scalar computation:** cached source arrays and computed node designs feed the existing local/group/fibre/support/Hermite interpreter. The returned value equals `originalContraction` on the original network, with all intermediate value suppliers discharged.
* **Actual local prefix heights:** Horner suffixes, corrected-port sums, both recursive truth-table branches, products and convolution subtotals have proved common-denominator bounds. Their binary widths are polynomial; the proof does not rely on cancellation in the final answer.

The source-expression tree has at most `6Q²+8Q+3` nodes. Its actual universal coefficient-array arithmetic/read report is at most that quantity times `2(R+1)(R+2)+3(R+1)`. The original owner-pullback array report is also bounded explicitly. These reports exclude acquiring rational constants, words, packing and finite addresses. They are not the complete runtime of source acquisition.

## Resource interpretation

[Independent preprocessing review](review-source-preprocessing.md) finds a constructive polynomial bound in the numerical source/network dimensions under the scheduled alphabet assumptions. In particular, the apparent subset expansion costs at most `3^Q`, which is at most `D=r^(2Q)` for r>=2; D is already a paid polynomial-sized source parameter on the schedule. It does not enumerate all original Boolean assignments.

The review explicitly charges lazy repetition: binding a packing record does not cache the word search, and caching selected entries does not imply one elimination per group. The finite, acyclic repetitions remain polynomial. Intermediate rational heights are bounded through syntax subtrees and original-matrix minors, rather than inferred from small final coefficients. This resource argument remains paper-level; no numerical aggregate polynomial exponent is asserted.

The new counter's `.work` is the inherited packet/Hermite ledger. It **does not include all source or design preprocessing**. The acquisition code materializes values but discards some operation reports. A complete bit theorem must attach those costs, concrete rational primitives, addressing, copying, storage and control to the same executed run.

## Verification

All **20 new modules** pass strict Lean compilation (`autoImplicit=false`, `warningAsError=true`). The ordinary root import plus all 15 scoped linters passes. Every emitted declaration, including private/generated constants, was checked for transitive axioms: **573 declarations, 361 theorem constants**, only `propext`, `Classical.choice` and `Quot.sound`.

The archive verifier additionally requires all 20 independently compiled isolated objects to match their canonical objects, stable transitive dependencies, every source/review hash, and unchanged prior evidence. See [verification.json](verification.json) for the completed machine-readable result and [CombinedSourceAcquisitionAudit.log](CombinedSourceAcquisitionAudit.log) for the full declaration audit.

Execution controls exercise the actual integer solver, a nonconstant universal correction row, an original packed/pulled-back array family, the padded matrix, and the entire source-to-scalar counter. Whole-source table controls return 1, 2 and 0. These diagnose executability and erased proof indices; they are not finite semiprime coverage or runtime evidence.

## What remains

1. Attach the actual source-expression and elimination scratch bounds to primitive execution, then compose all source/design and counter bit, indexing, control and storage costs.
2. Instantiate this executed endpoint on the public equality-subdivided factor network and its paid local entry evaluators, and join original-input prefix restriction and factor recovery.
3. Assemble the scheduled guard, finite fallback, recovery and asymptotic estimate into one all-input factoring bit-complexity theorem.

The candidate generic-counter route remains `N^o(1)` pending these joins. This packet proves neither that rate nor the guaranteed 1/6 rate. The older native long-query bound remains soft `K^(5/4)`; it is not silently replaced by a new soft-K acquisition theorem.

## External Lean proof

The previously completed [pinned external proof audit](../semiprime-layout-assembly-20261026/external-final-audit.md) remains unchanged. It verified the exact `SqrtLogSpace.exact_count_and_sat` endpoint and its 2,569-module source closure at OpenAI commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. The verified fixed-width k-CNF rate is the older `2^{O_k(n(loglog n)^2/sqrt(log n))}` times a polynomial in input length, with polynomial visited-tape space. The newer manuscript's sharper rate and generic growing-arity contraction are not consequences of that endpoint alone. This packet extends our generic source counter; it does not re-run or overstate the external audit.

No commit or push was performed. Earlier packets, vendored sources, root imports and unrelated concurrent work are preserved.
