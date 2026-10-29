# Layout-constructor bridge: exact reuse map and next proofs

Read-only audit of frozen `shared_layout.py`, current `NodeCertificate`, and pinned OpenAI math commit `7ef5c0cc...`. Source/artifact hashes and strict-build availability are recorded in `layout-sourcehashes.json` (30 files). At that snapshot the independent external build was running with 1808 completed modules and zero failures. Generic modules explicitly marked compiled below were already completed; this does not claim the entire SAT endpoint build has finished.

## Main finding

There is a genuinely generic, already compiled **universal block → incidence copies → original-variable pullback** construction. Its scope and occupancy parameters are independent numeric inputs, so growing maximum scope `w=O(n^(3/4))` is allowed. It can plausibly replace the Python diagnostic layout without changing the desired rate. It is **not** the same constructor as that Python file, and the existing `exactScheduleGuard` is not by itself a proof of its stronger numerical premises. The missing work is a short sequence of explicit incidence, guard, kernel/span, and finite-enumeration adapters, not reuse of a fixed-k SAT endpoint.

All external relative paths below start at
`/tmp/semiprime-d1-audit-20261026/openai-math/lean/OAI/Algorithms/SubexponentialSAT/`.

## 1. Labels and packing: use the generic theorem, not the SAT query wrapper

**Compiled:** `SqrtLog/PackingTheorem.lean:46`, `Packing.correlated_packing`.

Input: arbitrary finite incidence type I, owner map `ivar:I→V`, factor map `factor:I→E`; finite exhaustive word alphabet, score-term and label-index enumerations; ε>0; bounds B on owner-fibre sizes and a on factor-fibre sizes. Its exact size premises are

`4(B+a)*D^2 <= ε^2*M`, `16*Q*r^2 <= n`,

where `M=card I`, `n=card V`, `D=card(UniversalType r Q 1)=r^(2Q)`.

Output: the **computed** correlated word assignment, complete uniform blocks covering at least `(1-ε)M` incidences, and every original-variable head size at most `3n/(2r)`. Neither fixed arity nor a SAT predicate occurs in this theorem. `PackingWords.mean_incidence_energy_le` (`SqrtLog/PackingWords.lean:163`) explicitly uses B and a via B+a−1; it does not replace a by a fixed constant.

**Compiled:** `SqrtLog/PackingConcrete.lean:41–90`, `computedPacking`, `computedPacking_head`, `computedPacking_slot`, `computedPacking_coverage`: explicit finite bucket scans/metadata corresponding to those words and complete blocks.

**Compiled:** `ConditionalExpectation.lean:147`, `assignWithEvaluator_le`, supplies the generic exact conditional-expectation proof from evaluator base/step equations. This does NOT by itself certify Python's analytic `score()` implementation; those evaluator equations and represented rational costs must be supplied. The generic packing implementation has its own proved evaluator (`SqrtLog/PackingProgramScores.lean`, `evaluator_eq_numerator`, etc.), distinct from the Python score formula.

**Do not use as direct frontend:** `SqrtLog/LayoutProducedHeadsQuery.lean:29` consumes a SAT-derived `Query` and `LeafParametersProgram.Guard`. The lower-level generic `correlated_packing` is the reusable interface. `SubexpLayoutConstruction.lean` builds clause/unary factor streams and is not a generic high-arity tensor constructor.

### Actual incidence adapter still needed

For our network use `I = Sigma (fun e => Fin(arity e))`, owner `(e,i)↦coordinate e i`, factor `(e,i)↦e`. Prove `card I=sum arities=2n`, factor-fibre size equals arity(e)<=w, owner-fibre size<=2, and coverage. These are properties of the actual Boolean bit graph, not consequences of the counter polynomial. Enumerate I, V⊕E, words and score terms without duplicate/missing elements. Empty factors can receive an arbitrary color; they have no incidences and contribute a scalar, but their input count must remain part of the polynomial input-size accounting.

## 2. Existing exactScheduleGuard is insufficient literally, but same schedule has ample margin

Our guard (`SemiprimeCounterTail.lean:413`) proves

`2(2+w)D^2 <= 2n`, `2Qr^2 <= n`, plus the exact Q-trial tail guard.

Source packing instead needs, for ε=1/(r*λ),

`4(2+w)D^2*(r*λ)^2 <= 2n`, `16Qr^2 <= n`.

The first inequality and second constant are NOT logical consequences of the existing guard alone. They need new eventual schedule lemmas (or stronger exact tests with finite fallback). They do hold asymptotically under the SAME actual schedule: `scheduled_dimension_square_le` proves `D^2 <= 2n^(1/64)`; w<=C n^(3/4) gives the product `O(n^(49/64) polylog(n))=o(n)`. The extra `(rλ)^2` is only polynomial in log n. Likewise Qr² is polylog n, hence `16Qr²=o(n)`. No fixed-w hypothesis is needed.

**Separate spectral conversion:** source `LayoutRankUniversal.universal_total_rank_le` uses source interval `Subexp/TailInterval.intervalStart`, centered on `(Q-1)*(r-1)/(2r)`, and requires

`32*(Q-1)*log(2/ε) <= R^2`, `r>=2`, `Q>=2`, `R>=4`, `4R<=Q`.

The Python/current guard centers an exact Q-trial tail interval. Those interval/tail statements must NOT be identified silently. The simplest source-route choice is use the source interval instead. With our actual `R=4*ceil(sqrt λ)` we have R²>=16λ; Q<=λ/(128ν), ν=ceil(log₂ λ), r<=sqrt λ, so the required width follows eventually (indeed with a large constant margin) for ε=1/(rλ). Existing `6R<=Q`, `R>=32` imply the other size conditions. This is a precise new guard-conversion proof, not an implemented lemma in the current repo.

## 3. Universal rows already have restoration, degree and exact locality

**Compiled:** `SqrtLog/LayoutUniversal.lean:89`, `LayoutUniversal.data` constructs `Layout.Data` over any commutative coefficient ring with supplied denominator and node units. It uses actual finite universal swap numerator matrices, not an abstract locality assumption.

* `LayoutScaledMatrices.sourceRow_origin` (:72) proves origin/restoration.
* `LayoutScaledMatrices.sourceRow_degree` (:77) proves degree<=R.
* `LayoutUniversal.locality` (:42) proves off-group **integer-kernel annihilation** for explicit cleared-defect constraints.
* `SubexpRowInterpolation.NodeUnits.ofField` (:57) constructs all units from distinct nonzero field nodes. Our actual rational nodes 1,...,Q satisfy those premises; the finite sample indexing equivalence must be supplied.

**Compiled:** `SqrtLog/LayoutBlocks.data` (:61) assembles complete uniform copies and identity-polynomial rows/singleton constraints on uncovered incidences.

**Compiled:** `SqrtLog/LayoutHeadPullback.pullback` (:58) transports a head-coherent incidence layout to original variables; `LayoutPullback.row_origin` (:95), `row_degree` (:105), and exact fibre-sum dot identities justify restoration, degree and locality after the literal pullback. Incidences are copies only for constructing rows: original Boolean assignments are not duplicated in the contraction.

Next adapter: derive head coherence and factor-color coherence from `computedPacking_head/slot`, then construct this data over ℚ at actual nodes. This gives our native rows and origin/degree premises without reproving the swap algebra.

## 4. Constraint rank and measurement RANGE remain controlled

**Compiled:** `SqrtLog/LayoutRankUniversal.lean:96`, `actual_pulled_blocks_total_rank_le`: from the above concrete blocks, coverage `(1-ε)M`, source width guard and head coherence, the sum of rational constraint ranks over all groups is <=`2εM`. With M=2n and ε=1/(rλ), this is `c<=4n/(rλ)`.

**Compiled:** `SqrtLog/LayoutRowSelection.lean:45`, `exists_actual_row_basis`: chooses actual integer constraint rows, with cardinality equal to rational rank and the same rational row span. `selected_bound` (:61) retains their literal original coefficient bounds. Thus **no arbitrary rational-basis denominator growth is needed**.

**Compiled explicit height:** `SqrtLog/LayoutNumeratorBridge.lean:46`, `clearedDefect_natAbs_le`, gives per-entry bound

`W0 = 2*(8Q)^(2R)`

when A<=Q and Q>=1. `LayoutBlocks.constraints` copies one such row into one block, or uses a singleton unit row. It does not sum all blocks into each measurement. After owner pullback, at most B=2 incidence entries contribute to each original coordinate, so the elementary bound is

`W <= 2*W0 = 4*(8Q)^(2R)`.

The copy/pullback coefficient bound still needs a short explicit lemma tied to the selected source constructor; it is not a rank bound masquerading as a height bound.

**Compiled:** `SqrtLog/LayoutSignatureBound.lean:20,34`, `abs_boolSignature_le` and `card_range_boolSignature_le`: a group with m variables and c integer rows bounded by W has each actual Boolean signature in `[-mW,mW]` and at most `(2mW+1)^c` signatures. The proof concerns integers, independent of modular precision.

Consequently `log₂(2nW+1)=O(log n+R log Q)=O(λ)` for SAME schedule, and the total summary enumeration exponent is `O(cλ)=O(n/r)`. Group scans cost `2^{<=3n/(2r)}`. Since `r~sqrt λ/(log λ)^2`, both fit the already targeted `O(n(log log n)^2/sqrt(log n))` exponent. Crucially W is `exp(O(R log Q))`, **not exp(Θ(D))**. The number D of universal coordinates only contributes a polynomial-size matrix/copy construction, because D²<=2n^(1/64).

There is no assertion here that these last assembled range/rate inequalities are already one compiled external theorem for our network. Their exact premises and the source height theorem needed to prove them are identified above.

## 5. Precise bridge to NodeCertificate

Our `NodeCertificate` requires: an explicit partition `A≃Sigma Local`, factor assignment, rational measurement rows, finite summaries and readout, actual readout equality, off-group **rational row-span witnesses**, and valid representatives for nonempty fibres.

The source `Layout.Data` instead supplies exact integer-kernel annihilation. This is sufficient mathematically over ℚ, but the direction is important: `LayoutExactBuckets.killsIntegerKernel_of_rational_span` proves row-span⇒kernel, NOT the converse needed for our current certificate. No converse adapter was located in the inspected generic modules. A small finite-dimensional lemma must prove integer-kernel annihilation⇒rational row-span by clearing rational-vector denominators and using matrix kernel/row-space duality. It can be applied after selecting actual integer basis rows. It must not merely assume the desired `NodeCertificate.row_span`.

Partition: use subtype groups `{v // head t v=g}` and the explicit finite-fibre equivalence. Factor assignment is the source color at t. Samples convert Fin Q to positive rational samplePoints Q. None of these changes physical scopes.

Summaries: use an explicit integer box with radius `m_g*W` for each selected row, with readout returning its signed integer coordinate in ℚ. Prove the measurement map lands in the box using `abs_boolSignature_le`. Do NOT define an opaque Fintype of attained signatures and assume it has a cheap enumeration: that would hide the enumeration cost.

Representatives: enumerate the finite Boolean assignments of each group, choose the first matching signature when it exists, and arbitrary all-zero assignment otherwise. Prove `representative_valid` by the finite search theorem. Representatives need not satisfy forced bits. The source/layout algebra does not automatically give this new `NodeCertificate` field, but the existing counter's explicit scan is precisely this construction.

## 6. Constructor representation mismatch and recommended proof order

Python `shared_layout.py` places all incidences into `h=max occupancy` PARTIAL copies, with hD<=2M, and uses integer ±1 spectral eigenbasis measurements. Source uses COMPLETE copies plus leftover identity rows, then selects bounded actual cleared-defect rows by rational rank. These are different valid layout algorithms. The compiled source theorems do not certify the literal Python constructor. A replacement implementation and comparison controls are required if root chooses the faster proof route.

Recommended next substantive proofs, in dependency order:

1. Generic original-graph incidence adapter and complete explicit enumerations.
2. Stronger source packing and spectral guard conversion for the SAME schedule; finite fallback for failures.
3. Compose `correlated_packing` → `LayoutUniversal.data` → `LayoutBlocks.data` → `LayoutHeadPullback.pullback`, retaining original row origin/degree.
4. Derive bounded integer selected measurements, rank count and literal coefficient height; supply the kernel-to-row-span adapter.
5. Construct finite summary boxes, their readouts and nonempty-fibre representatives; package actual `NodeCertificate`s at all nodes.
6. Prove cost/space of the concrete replacement constructor and scans, and connect their output arrays to the semantic data. Generic scope-list packing cost components can be reused, but the SAT/clause/unary frontend and its dense table representation are not a high-arity tensor endpoint.

This route reuses substantial generic compiled mathematics and retains the current rate. It does not supply a finished layout-constructor bridge, machine theorem or factoring exponent claim. In particular `counterValue_eq_original` and `CounterSearch.Problem` still legitimately require actual node certificates until steps 1–5 are discharged.
