# Independent public-parameter, schedule and enumeration review

Disposition: PASS for the exact mathematical interfaces below. Read-only review of the three sources identified by the adjacent hash JSON; no new compilation or runtime claim is inferred from this review. Parent independently ran the strict compilation gates.

## Public graph parameters

`SemiprimeMacroParameters` uses `N.size`, hence N < 2^L including powers of two. Its transform length is the least dyadic with square at least 16L; the proved quarter-radix identity, positive digit count, digit coverage/minimality and actual truncated final digit width match the compiler. The target digits reconstruct N, vanish beyond the active horizon, and every candidate x <= N satisfies the actual top-digit caps. The coefficient/carry capacity uses the physical modulus and strict integer bounds.

Crucially FFT length and Boolean variable count are distinct. `variableCount` is the cardinality of the actual subdivided edge type; L <= E <= 6400L. The actual vertex arities are bounded by `scopeBound`, with scope <= 512 E^(3/4). Thus the later schedule receives E, not the FFT length. No supplied width-coverage hypothesis is hidden in these public arithmetic conclusions.

## Actual schedule and rank

`SemiprimeScheduledCounter.parameters` is a literal constructed-counter parameter record. `packingGuard` derives the source guard from occurrence <= 2, actual incidence 2E, the displayed scope bound and its stronger integer guard. The selected-rank budget is a conclusion of constructed rows, not an input assumption. Universal-space cardinality, total rank and full literal summary-box count are charged. The graph specialization obtains ordered coordinates and occurrence two from the actual endpoint bijection. Eventual guards use E(L) tending to infinity and the proved growing-arity bound; finite exceptions remain an explicit executable fallback obligation.

The integer spectral guard is genuinely sufficient: ln(2r lambda) <= clog2(2r lambda), so using the latter in the displayed quadratic-width inequality is safe. `integer_tolerance_load` proves epsilon*(2E) <= E/2, the executable tolerance test. Its source doc calls this a Taylor budget, but it must not be substituted for the actual Taylor cutoff. The latter is q=floor(2E R/Q), precision q+1, and the separate source guard 4R <= Q gives 2E R/Q <= E/2 directly. The proof report `scheduled-proof.md` accurately calls the former an epsilon test, so there is no contradictory report claim to fix.

## Streamed inclusive menu

`SemiprimeCounterEnumeration.stream_eq_menu` requires a noduplicated variable list and gives exactly all U subset S with |S| <= q. The three branches are exclusion, S-only and S-and-U; the support budget drops precisely in the last two branches. The empty/zero-budget callback survives. `tracked_menu` proves the same value, callback count sum_{j=0}^q 2^j binomial(E,j), bounded recursion nodes and depth, without a materialized mask-family list.

The entropy theorem includes the 2^j inner choices and requires real 0 < u <= E and q <= u. For the actual counter take u=2E R/Q and q=floor(u), not precision q+1. `counter_precision_sufficient` and `counterValue_eq_original` use width floor(dR/Q)+1, so Hermite strict degree and inclusive support cutoff agree exactly. There is no off-by-one gain from replacing q+1 by q. A callback supplies its own Mobius sign; this standalone traversal does not silently add one.

## Closed versus open scope

The exact finite identities, public shapes, actual occurrence/rank bounds and callback envelope pass. Enumeration alone does not prove the whole streamed counter machine runtime: callback evaluation, rational heights/storage, source layout construction/selection, and implementation refinement must be composed with their separate ledgers. The noncomputable mathematical layout/representative constructors are not turned into cheap oracles by these theorem types. The scheduled proof itself explicitly disclaims a primitive runtime theorem and distinguishes the source Q-1 convention from the earlier Python Q-trial layout.
