# Uniform actual counter budget and subpower retained report

**Status: PROGRESS. Goal ACTIVE. Original-input primitive bit/address clock OPEN.**

The actual N-only factor controller now has a derived uniform counter budget, and its retained mixed-operation report has a proved subpower rate. The theorem `SemiprimeFullReportRate.run_report_subpower` states:

> For every real epsilon > 0, eventually for every natural N,
> `(SemiprimeFullSetupScheduledController.run N).work <= N^epsilon`.

`run_report_sixth` specializes this to epsilon=1/6. The constants and threshold are independent of the particular input. The public controller's former assumed count-report bound B is discharged using the original indexed graph, actual packing guards and every reachable prefix. No rank, head, summary, count, coefficient or factor answer is supplied.

**The proved quantity is `run.work`, a retained mixed scalar/list/physical-subroutine report. A complete primitive bit-runtime theorem has NOT been proved.** The previous reviewed paper-level N^o(1) bit-time route allowing subexponential storage remains separate. No practical speedup or new native long-query bound is claimed.

## What closes here

* The exact executed setup/native work split retains paid finite enumeration, coefficient source, separately acquired raw integer families, every physical node/head selection, native contraction, Hermite reconstruction, and all reported prefix/decoder/controller work. Repeated setup on each query is paid.
* The actual indexed layout has balanced heads and a total selected-rank bound. Generic layout theorems apply directly to the executed enumeration; no equality with the older default enumeration or its tie choices is assumed.
* A complete parameter-only summary bound uses the floor of the total-rank budget. Candidate row count is used in polynomial preprocessing, never substituted for rank in the summary exponent. Rounding the balanced head bound is paid explicitly.
* Source alphabets and all other scalar dimensions have proved polynomial bounds under the actual fast guard. Support, summary, head-table and local-table terms remain separately at their established scales.
* Concrete setup/native/scalar/controller expressions have constructed fixed-monomial bounds. Their constants and exponents are chosen BEFORE the eventual input. The existing rate theorem then applies to the ACTUAL report of the fixed N-only controller.

See [the quantitative connection and scope](counter-rate-connection.md), independent [cost-callpath review](review-actual-counter-budget.md), and independent [indexed/rate review](review-indexed-report-rate.md).

## Verification

Thirteen NEW modules: **213 generated declarations / 182 theorem constants**. Strict `autoImplicit=false`, `warningAsError=true`, ordinary-root fifteen-linter checks, and every generated declaration's transitive standard-three-axiom audit pass. All thirteen isolated objects are byte-identical to their canonical objects. **17,608 actual Lean compiler-imported names** have fully resolved source/object pins, unchanged before/after. Existing dependencies are pinned rather than rebuilt.

See [verification](verification.json), [combined audit](CombinedCounterBudgetAudit.log), and [isolated summary](final-isolated/summary.json). Independent reviews inspected the full runtime/cost and mathematical rate connections. This packet is a symbolic proof of uniform/eventual bounds; no finite factoring campaign or new timing experiment is used as scaling evidence.

All 2,524 protected files, 24 concurrent files and both append-only prefixes are preserved. One note is appended to each journal. No commit or push is part of this packet.

## Remaining goal

The next required result is an executed primitive-bit and finite-memory refinement, with all remaining public graph/schedule acquisition, source arithmetic, integer encoding, native rational/Hermite/floor arithmetic, and address/control costs bounded by a fixed polynomial of the same resources and proved bit heights. That refinement is not supplied by this numerical report theorem. The [next primitive-clock plan](next-primitive-clock-plan.md) identifies the existing physical components, exact height theorems and missing execution joins. The actual factor algorithm's semantic correctness remains proved; the full guaranteed bit-runtime goal stays ACTIVE.
