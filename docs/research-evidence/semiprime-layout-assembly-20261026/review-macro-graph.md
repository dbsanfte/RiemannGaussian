# Independent semantic review of the concrete macro graph

27 October 2026. **PASS at the actual ordered graph-structure and subdivision-count scope.** Reviewed stable `SemiprimeMacroGraph.lean` against frozen `semiprime-shared-counter-20261026/factor_network.py`. This is a semantic review, not a duplicate of the author's strict/all-declaration audit. No source was edited and no new test campaign was run.

## Signal endpoints are the actual compiler roles

The two axis equivalences are correct and deliberately different: inputIndex(j1,j2)=j1+r*j2, outputIndex(k1,k2)=k2+t*k1. Word consumers use their inverses in the correct places. Source words feed the forward first stage at inputIndex; product words feed the inverse first stage at the same input ordering; forward second-stage outputs feed point products at outputIndex; inverse outputs feed carry coefficients at outputIndex.

First-stage output signals feed their own twiddle scales, and twiddles feed second-stage input positions with j1 as the local word index. There is no accidental transposition or reuse of outputIndex for the inverse's input indexing. `wordEndpointEquiv` proves the endpoint/role bijection from these literal cases, not merely a cardinality equality.

The carry endpoints are correct at both boundaries: signal0 is produced by the initial constant vertex and read as carryPrevious0; signal k+1 is produced by carryOut k; the last signal n is read by the terminal check. Every nonterminal carry is read exactly at the next carry vertex. The physical word width is n+1 throughout, matching the actual Python allocation and its separate carry<2^n predicate.

Flag producers and consumers match the real sequential OR chain. The first digit flag feeds orPrevious0 when d>1; later digit i feeds orNew(i-1); each nonfinal OR result feeds the next orPrevious; the last feeds the final one-check. When d=1 there are no OR gates and the sole initial digit flag feeds the terminal check directly. The explicit positive-d premise prevents the otherwise invalid zero-digit terminal case. The full vertex owner map also requires d<=r*t so every digit flag belongs to a declared source word.

## Ordered local ports match unpacked code arrays

Source flags share the actual source-word vertex and appear at offset n+1 after the complete word. Padded constant sources have no flag slot. The subtype used for an optional source flag is a singleton exactly when i<d and empty otherwise; there is no extra free Boolean flag on padding words.

`LocalSlot`, `structuredPortEquiv`, and `localSlotFinEquiv` give a concrete ordering. Inputs precede outputs; within a word block the word index is major and the bit index minor. The offset lemmas agree with Python's `unpack`/Builder ordering:

- first DFT: t input words, then t output words;
- scale: one input word, then one output word;
- second DFT: r input words, then r output words;
- product: left word, right word, then output;
- carry: coefficient, previous carry, then next carry;
- OR: previous, new digit flag, output;
- source: complete word, then optional one-bit flag;
- terminal checks: their sole actual word/flag input.

The initial constant and final zero carry vertices are retained as actual word ports, not silently folded into a recurrence boundary condition.

## Genuine incidence proofs and equality subdivision

The stage rank proves producer/consumer owners differ. It is a partial-stage ranking, not a claim about Python's absolute vertex indices; independent OR and arithmetic branches may have overlapping ranks harmlessly. The resulting same-vertex scope-injectivity statement concerns actual signals and literal role ports.

After subdivision, Edge=BitSignal*Bool records producer/consumer **host halves**. A second endpoint Bool records original/equality side. These two Boolean tags are kept distinct in the definitions. Every new edge has one original vertex endpoint and one equality vertex endpoint. Equality ports are explicitly ordered false->0 and true->1.

`edge_occurrence_two` and `ordered_edge_occurrence_two` prove that each actual edge variable occurs in exactly two actual ordered local ports. The ordered-scope injection rules out duplicate variables within a vertex. Thus these properties now follow from a constructed endpoint/ordered-port map, not an unsupported graph-incidence analogy.

`graph_subdivision_count` is correct for **any** predicate on original role-port assignments: all equality predicates force the two host-half vectors equal, giving exactly one copy assignment for each original shared-signal assignment. It does not assume the desired multiplication/count equivalence. Conversely it does not yet establish that the predicate argument is the conjunction of the actual arithmetic vertex verifiers; that later semantic instantiation remains necessary.

In the following formulas n=r*t is the transform length, not the counter's Boolean-variable count `Fintype.card Edge`. The exact counts agree with the previously audited code: pre-subdivision signals `(13n+1)(n+1)+4d-2`, original vertices `7n+3(r+t)+2d+2`, twice as many edge variables after subdivision, and total local arity twice the post-subdivision edge count. The counts are now supported by concrete endpoint and ordered-port bijections.

`physicalCarryEquiv` supplies the precise zero-high-bit correspondence between n-bit active carries and n+1-bit physical words checked below2^n. This closes that finite-width bijection itself; applying it in the final graph predicate/count equivalence remains a separate composition step.

## Exact remaining gaps

No substantive structural, offset, boundary, d=1, multiplicity or scope correction is requested. The module proves actual graph wiring and ordered incidence properties. The following remain separate and must not be inferred from its cardinalities or generic subdivision predicate:

1. Define/attach the literal public-N-dependent verifier at every ordered vertex, including top-digit bit bounds, zero-padding source words, exact roots/twiddles/inverse normalizer, canonical range tests, carry guards/target digits, flags and final checks.
2. Prove that their product corresponds to the full canonical-array/integer relation, with unique extensions for all intermediate words and flags, and hence counts the original bounded integer factor pairs. The existing arithmetic/MacroBit results are ingredients, not an already stated global graph theorem.
3. Instantiate all parameters from the original N and prove d>0,d<=n, n=r*t, radix/transform capacity, the original input-bit range, dyadic balanced-axis bounds, and complete factor coverage. The current arity bound is explicit in r,t,n, not yet an all-N O(L^(3/4)) theorem.
4. Supply executable descriptions/enumerations and local predicate algorithms, with ordinary bit/space and primitive-machine bounds; connect this graph's ordered input bits to the actual-counter prefix factor decoder.

The complete structural producer/consumer graph is no longer an open assumption after this module. The outstanding graph **semantic/public-input/resource** connection is explicitly retained. No claim of a finished factoring or runtime theorem follows from this review.
