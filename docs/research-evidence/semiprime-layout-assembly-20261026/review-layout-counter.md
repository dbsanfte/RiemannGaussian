# Independent semantic review: constructed layout and exact counter

**Verdict: PASS for the stated construction/count/search semantics. No hidden desired conclusion, layout oracle, summary-count oracle, wrong occurrence promise, or representative premise found.** This is a source/type-interface review, not an independent rerun of the authors' compilation/audit. It does not certify a primitive runtime or polynomial-space implementation. Reviewed source hashes are recorded in `review-layout-counter-hashes.json`; the final ConstructedCounter read includes the explicit summary Fintype, monotonicity fix, nodeRows/sample transport, search-none equivalence and query bound.

## 1. What is actually constructed

`SemiprimeSourceLayout.builtLayout` invokes the pinned source's literal `Packing.computedWords`, computed complete-bucket packing, universal rational interpolation/swap rows, singleton leftover rows, and original-owner pullback. The lists are formed by complete finite enumerations; a desired layout or locality certificate is not an input. Checked vendor interfaces/bodies: `PackingAlgorithm.computedWords`, `PackingConcrete.computedPacking(_coverage)`, `PackingTheorem.correlated_packing`, `LayoutBlocks.data`, `LayoutHeadPullback.pullback`, `LayoutRankUniversal.actual_pulled_blocks_total_rank_le`, and `LayoutRowSelection.exists_actual_row_basis`.

In particular `correlated_packing` refers to the **same computedWords** assignment, not an unrelated existential good word assignment; `searchedPacking_coverage` proves coverage for the actual computed packing. Universal row support/restoration/degree/locality are provided by the concrete source construction. Leftovers are actual identity/singleton rows; they are not silently discarded.

The quantitative `PackingGuard` inputs are original owner/factor fibre bounds, positive cardinalities/tolerance, and explicit load/head inequalities. The rank API additionally supplies public r/Q/R/spectral-width inequalities. Neither is a layout-existence, row-locality, rank, summary-count or counting-answer premise. Exact counting does not need those efficient-rank guards: arbitrary searched words still give structurally correct complete blocks plus leftover constraints.

## 2. Height chain is literal and uses B once

`SourceLayoutHeight` bounds the actual **integer constraint entries**, not every rational interpolation-row coefficient or every counter intermediate. The chain is sound:

1. source `clearedDefect_natAbs_le` bounds each literal `d*I-N` entry by `2*(8Q)^(2R)`;
2. joint-to-head and complete-block embeddings are injective, copying an entry or inserting zero (not summing all universal rows/blocks);
3. leftover singleton entries are 0 or 1 and fit the same bound;
4. only the final original-owner head-fibre pullback sums entries, over at most B original incidences for each variable.

The resulting `B*2*(8Q)^(2R)` therefore needs one factor B, not the total number of incidences or a second block factor. `headOwner_fibre_card_le` injects the restricted head fibre into the original owner fibre. It does not incorrectly replace a group size by B. Selected basis rows are **actual unrescaled integer rows**, preserving this height exactly.

The public height theorem assumes owner-bound, node positivity and interval containment only. The range-facing wrapper derives containment. No height of an already-built matrix is supplied as the final premise. This is not yet a complete bound on rational coefficient denominators or all runtime arithmetic; those are separate obligations.

## 3. Row selection, spans, signatures and representatives

`LayoutSelection.selectRows` invokes actual-row basis existence and `Classical.choice`; it does not assume that a small selected matrix has the required span/rank. The selected index cardinal is the true rational row rank and every original row is in its rational span. Integer-kernel locality survives selection in the correct direction. `LayoutCertificates` derives the needed off-group rational row-span coefficients from integer-kernel annihilation by finite common-denominator clearing and finite-dimensional duality. No modular row-span or hidden prime-field operation is substituted.

The summaries are explicit full signed integer boxes, **not the attained-signature set**: for local cardinal m and entry bound W, each coordinate has `2*m*W+1` possible values, inclusive endpoints `[-mW,mW]`. Shifting by mW, Int.toNat and readout are consistent; zero rows/empty groups remain legal. Tuple cardinal is exactly the product of these bases raised to selected ranks. The common-box bound replaces m by total variable cardinal only via monotonicity. The final source read has the explicit `Nat.mul_le_mul_*` monotonicity fix; no issue remains.

`firstRepresentative` really scans a bounded enumeration of all local Boolean assignments and returns a matching one if the fibre is nonempty. It deliberately ignores forced-prefix/Möbius bits; that matches the separation theorem, whose actual local summation applies forced bits separately. The all-false fallback is used only where no attainable fibre is promised and contributes no invalid fibre term. No representative satisfying extra forced bits is assumed.

**Resource distinction:** `Fintype.equivFin` Boolean decoding and `Classical.choice` selected-row bases are mathematical finite enumeration/selection, not yet a primitive streamed decoder or a proved polynomial-time row-selection routine. The scan is syntactically tail recursive, but its generic decode callback is not thereby proved efficient or polynomial-space. The row-span coefficients are used as proof witnesses; the counter does not need to acquire them as runtime data.

## 4. ConstructedCounter accepts the original finite-network data

`Parameters` supplies only r,Q,R,B,epsilon, range inequalities and an upper bound on actual coordinate occurrences in `Incidence = Sigma e,Fin(arity e)`. It does not require a summary budget, rank certificate, layout, representative, counter answer, occurrence exactly two or a hidden bounded-arity conclusion. Repeated coordinates inside a factor are allowed by these generic semantics; B must count all actual incidences. The macro graph can later instantiate B=2 using its ordered occurrence theorem.

The generic `problem` requires **coverage** `forall a, exists e i, coordinate e i=a`. Thus the theorem is for finite networks with all declared variables occurring, not isolated free variables without adjustment. This is an explicit natural input premise; adding constant-one unary factors for isolated variables is a separate concrete preprocessing step if needed. Macro graph edges already have two ports, so coverage follows there once the instantiation is made.

`nodeDesign` is built from the actual source rows/height and selected integer rows. The sample-node equivalence uses the same rational nodes `1,...,Q`; the latest explicit `nodeRows` transport preserves the same physical incidence and actual node, not an assumed extension of certificates to arbitrary points.

`constructed_prefix_count` has no layout/count-correctness oracle premise: it builds `Problem` from original tables, coordinates, coverage and p, then applies the already-proved exact counter. `constructed_search_sound` returns bits of one common original accepting assignment, `constructed_search_none` correctly characterizes absence of one, and `constructed_search_queries` counts at most one initial plus one per requested bit. That last theorem counts calls; it does not give their bit cost. Prefix restrictions change local predicates on the original scopes rather than introducing arbitrary global-constraint oracles.

## 5. Summary/rank claims are not smuggled into correctness

`summary_count` is an equality for the actually constructed finite Summary types; `summary_count_le` uses their literal integer box and actual totalRank. `totalRank_le` derives that rank from actual computed packing and universal rows, with explicit original-fibre/load/head/spectral guards. These are not assumptions in `Parameters` or `constructed_prefix_count`.

For the quantitative B=2, M=2*n instantiation, totalRank<=2*epsilon*M gives c<=4*epsilon*n, matching the separate source-rate condition `c*(r*lambda)<=4*n` when epsilon=1/(r*lambda). Source height then equals `4*(8Q)^(2R)`, matching `SourceLayoutRate.sourceHeight`. This mathematical substitution still needs to be instantiated into the chosen p/network in a final theorem.

The vendor construction uses stronger load/head constants than the older Python Lemma-4.7 diagnostic: `4*(B+a)*D^2 <= epsilon^2*M` and `16*Q*r^2<=n`. They must not be inferred merely from an older weaker accepted guard. The separately reviewed SourceLayoutRate states/proves the stronger actual-source guards eventually at the integer schedule; that is the proper bridge. Its natural-log spectral width and ceiling-binary schedule are explicit, with no definitional identification of the two logarithms.

## 6. Closed versus still open

Closed by the present public types/proofs: actual finite searched layout, restoration/degree/locality, actual constraint height, actual-row selection existence, integer-kernel-to-span certificate construction, finite signed summary boxes and exact cardinalities, valid unforced representatives, exact original-network prefix count, search semantics and number of counter calls. No substantive semantic correction requested.

Still open to a full executed fast factorer: deterministic primitive implementations/refinements for the finite enumeration, selected-row computation, representatives, polynomial/jet/Hermite operations; the complete bit-height/space/time proof including their representation; the concrete macro graph's vertex-entry-to-factor-count instantiation and public parameter/bitlength bridge; final composition of stronger source-rate/rank/height bounds with that actual implementation and finite fallback. Existing mathematical finite definitions are genuine constructions for semantic correctness, but must not be advertised as already the frozen Python streamed implementation or as a machine running-time theorem.

Source mutation policy: no reviewed module was edited. The final pruned height source was fully re-read at hash `a0af31d8682fd21b95d442a4f36ce2925cce924d019096d2901c3f69f222b0bf`; its unused Fintype/DecidableEq/NeZero assumptions were removed (including the final Fintype G removal from blocks_data_constraints_abs_le) and one redundant simp argument pruned, without changing the bound or construction. PASS remains unchanged; ConstructedCounter was `a08925f266e025f1099046ebb783372311a625b7627c8058762396200beb0e35`. The hash file is refreshed to this pruned source. Any subsequent formula/interface changes require a new disposition; unused-binder-only edits do not change this semantic conclusion.
