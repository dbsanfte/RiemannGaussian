# Independent review of cancelled-count source search

**PASS at the stated physical-score plus typed-metadata boundary.** Read-only review of the six frozen root sources pinned in `review-physical-score-search-pins.json`. No source/object builds or edits were performed for this review. No correction is required.

## Cancellation and exact original counts

`SourceScoreCancellation.clear_denominators` uses the positive common factor `4*r^2*lambda^2*U^4`. The incidence coefficient is `n^2*lambda^2*U^2`, and the head coefficient is `4*M^2`; these agree with x=M/(r*lambda*U), y=n/(2r) and averaging denominator U^2. Adding the same offset before clearing denominators cancels exactly. `weight_le_iff` preserves <= in BOTH directions, hence equality and the source tie rule. It needs positive r,lambda,U, but no positivity of M,n or the counts. The stated cap S^9+4S^5 has the correct exponents.

`SourceScoreCountOrder.sequential_score` invokes the actually executed count theorem, not an assumed I/H answer. `caller_cardinality` discharges L^4=U^2 from the original enumeration lengths L=r^Q and U=r^(2Q). This does not assert that arbitrary alphabets or arbitrary duplicate lists have those cardinalities. `integerValue_bound` uses the actual all-prefix lane bounds. Original generic averaging remains valid with list multiplicities; the original source caller supplies its own exact complete enumeration.

## Choice, candidate order and reports

`SourceChoiceOrder` generalizes physical-ID choice to order equivalence. `SourceScoreChoice` uses the same original finite labels as typed metadata while executing the actual physical score comparator. Its choose recursion first selects the original tail winner, then compares the left candidate with that winner, keeping the left candidate on <=. Thus ties and candidate ordering agree exactly with the original `MaterializedWords.choose`, including zero weights and singleton alphabets.

Every score recomputation is retained: the tail's report, the left callback, the callback on the selected tail winner, and the comparator report are all added. No memoization of repeated winning scores is assumed. `assign_refines` quantifies the comparison relation at all candidate prefixes, so the dynamic chosen-prefix induction does not assume that a desired prefix is reached. `assign_work` retains every step and requires an explicit generic callback clock/width condition; this generic theorem alone does not claim that the final actual source budget has already been proved. The separate original-input budget must discharge it.

The raw-ID order module and the typed-label source-choice module are distinct interfaces. The new caller intentionally uses the typed-label path; it does not claim that original labels, Nat loop indices or all source metadata have already become physical tape registers.

## Actual physical score call path

`SourceScorePhysicalSearch.run` acquires the original two weight words ONCE, then passes the concrete `SourceScoreCountBits.score` callback to assignment. Its clock retains weight acquisition plus the complete assignment report. Inspection of that callback confirms actual terminal/predicate execution, physical branch additions, acquired padding, physical lane additions and physical weighted multiplication/addition. Native mathematical count values occur in correctness theorems, not in the physical runtime as supplied count answers. In particular, the internal terminal premise is discharged by `terminal_original_value`; it is not left as a final source-caller oracle.

`score_value` identifies the physical denominator-one word with the cancelled integer objective. `score_valid` is unconditional because its literal denominator is one, not because of supplied Fits advice. `score_order` joins actual counts, the original cardinality identity and positive-factor cancellation. `run_refines` therefore returns the EXACT original deterministic labels rather than merely a mathematically good objective value.

`computedList` executes actual `compileAll owner factor indices terms` before physical search and retains that descriptor construction report. The public source wrapper does not accept a precompiled score-program answer. `SourceScorePhysicalCaller.computed` obtains M, terms, indices and alphabet directly from the original enumeration. Its runtime accepts neither rational x/y nor offset. `computed_refines` allows ANY proof-side shared offset; this is legitimate because only within-search comparisons matter. `producer` caches the labels once, retains that search work, and exposes the same actual `labelAt` incidence lookup. `producer_refines` identifies those returned incidence labels with the original producer; it does not transfer the old producer clock by value equality.

## Scope retained

The completed stage closes the original producer's score-data/count/comparison oracle at its documented interface. Original word labels, finite types, owner/factor/descriptor callbacks, enumeration construction and Nat control remain typed/native metadata inputs or separately tracked construction. Canonical physical weight acquisition starts from original host natural dimensions and actually builds U; those natural-control/input encoding boundaries are still explicit. This is not yet a full N-only tape-machine implementation or a whole-public primitive-bit clock theorem.

The six reviewed sources establish semantics and report retention. Their generic callback-budget theorems must still be joined to the separate actual predicate/count/search budgets for a uniform original-input work theorem. No old value equality is used to discard new count/weight/comparator work. No source score, chosen-label, count, intermediate-Fits or actual terminal-truth answer is supplied by the final original-caller runtime.
