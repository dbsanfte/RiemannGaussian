# Independent adversarial audit of full bit composition

27 October 2026. Read-only review of `full-bit-composition-candidate.md`, the actual source constructor/guard/search scripts, the frozen shared counter/compiler/recovery, and current Lean interfaces. No prior source or frozen packet was changed. Source hashes are in `full-bit-audit-source-hashes.json`.

## Disposition

The proposed finite algorithm has a defensible polynomial-bit implementation of every examined arithmetic and control loop. I found no new exponential acquisition hidden in its construction or contraction ledger. Two parts of the candidate proof require the concrete repairs below: the sorted selector's **partial** Gaussian scratch height, and the absolute coefficient accounting for local Boolean expansions. Neither repair changes the subexponential exponent.

This is **not** an end-to-end kernel-verified runtime theorem. The actual-loop/refinement connectors listed at the end remain real formal obligations. In particular, runtime must not be assigned to a `Classical.choose` enumeration or a mathematically defined packet coefficient. The ordinary algorithm already has explicit loops for those operations, and the mathematical loop invariants below explain how to connect them; the Lean interpreter/composition statements have not all been built.

## 1. Actual algorithm and graph, including the subdivision concern

The production source entrypoint is `/tmp/semiprime-executable-counter-20261027/source_factor_search.py`, not the older `factor_solver.factor`. It constructs the actual source layout, then imports only the frozen compiler, finite trial division and prefix-recovery functions. Its contraction closure calls the frozen `shared_counter.count` on the current local predicates, with actual layout validation and quantitative checks enabled. No diagnostic `direct_count` or supplied counting oracle is used. The uncapped mathematical algorithm has `max_dimension=None`; capped runs may return no result and are excluded from the guarantee.

There is no original/subdivided mismatch in the current numerical ledger:

* `ScheduledCounter.publicCoordinate` explicitly has `SubdividedVertex`, `subdividedArity`, `Edge`, and `orderedEdgeAt` types. Its incidence proof uses `subdividedOrderedEndpointEquiv`.
* `PublicFactorCount.public_tensor_factor_count` is the contraction of exactly the same equality-subdivided table/edge graph.
* Python `factor_network.compile`, lines 239–254, returns doubled edges and the added equality vertices. `original_vertices` and `steps` are witness-generation metadata, not the factors passed to the counter.

Thus n is the post-subdivision edge count in all three places. The ScheduledCounter comment “Original ordered graph scopes” means the scopes initially supplied to that counter, not the unsubdivided graph. No frozen edit is needed to resolve the mathematical issue.

`MacroEntryBitCheck.publicBitEntry_correct/polynomial` directly covers original vertex predicates. The added equality predicate is a two-bit comparison. The final complete-entry checker must perform the corresponding sum-type case split; its cost is the maximum of the existing polynomial checker and this constant check. This is a small remaining formal binding, not an entry-evaluation oracle.

The frozen Python compiler predicates have polynomial worst-case bit cost on **all** local words: malformed/noncanonical words are rejected before modular arithmetic; DFT roots/exponents, products, explicit normalization, carry arithmetic and target power-of-two digit extraction all involve polynomially many bits. Fermat compositeness causes no unit assumption: the transform length is a power of two and the modulus is odd, and the formal DFT/carry results already treat this ring.

Prefix restrictions are applied at the designated original endpoint of each selected doubled edge. Each gate is literally the old predicate AND an equality to the requested bit. Enforcing a fixed edge at one host is globally equivalent to enforcing it at every occurrence, as in `CounterSearch.prefixTable`, because every occurrence reads the same global edge value and Boolean 0/1 gates are idempotent. All scopes and the exact two-incidence graph remain unchanged. `check_input_coverage` verifies L distinct public P bits and actual hosts. Recovery queries only those L bits, so L+1 counter calls suffice. The ordinary-factor equivalence includes squares and either factor orientation; zero initial count correctly means no nontrivial factor.

## 2. Conditional word search: a concrete shared denominator

Let W=r^Q, D=W², and epsilon=a/b in reduced form. In `conditional_score`:

* every incidence equality-product has denominator dividing D, so every partial incidence sum does too;
* every head equality has denominator dividing r, so every partial head sum does too;
* x=epsilon*M/D and y=n/(2r).

Consequently the **same integer**

    Cscore = 4*r²*b²*D²

clears every complete score, for every partially assigned av/df table and every candidate word. Incidence sums have at most M² terms, head sums at most Qn² terms. The centering terms have the same divisibility properties. Intermediate products/additions have polynomial bit size as well; normalized Fraction operations on these bounded inputs create only a constant multiple of this size before reduction.

The function `eq` is the correct conditional probability: identical indices return one; distinct fully assigned indices return their exact equality; otherwise a whole-word match has probability 1/W and a coordinate match probability 1/r. Variable and factor label tables are independent sorts, so the product of their equality probabilities is valid even if numerical IDs coincide across sorts. Whole words, rather than partly assigned coordinates, are chosen by this Python loop.

`computed_words` tries W words at each of n+F steps, recomputing polynomially many score terms. Under the proved schedule W²=D and D²<=2*n^(1/64), so this is polynomial, including storing the alphabet, label maps, and length-(n+F+1) score history. No unrelated-denominator accumulation occurs.

## 3. Gaussian repair: completed rows versus partial scratch

`select_actual_rows` and frozen `_row_basis` maintain sorted, normalized row-echelon rows. On inserting a new pivot q before an older pivot p, the older row has zero at q (its first nonzero entry is p). The new row has eliminated every older pivot. Sorting therefore preserves row-echelon independence. It need not preserve the literal intermediate array produced by ordinary Gaussian elimination on the original rows reordered by pivot: for example, after (0,1,1), processing (1,2,3) stores (1,0,1), whereas ordinary elimination starting with the original second row has (1,2,3). This is why the candidate's tight Schur-minor sentence should not be used verbatim for every partial scratch row.

Here is a sufficient uniform repair. Suppose the input integer matrix has entries bounded by A>=1 and K=min(number of rows,width).

1. At creation, a completed new residual is the unique linear combination of its original row and the previously selected original rows that kills the existing pivot columns. The original selected pivot submatrix is invertible. Cramer's rule expresses every residual coordinate as a bordered minor divided by its determinant. Dividing by the new nonzero pivot cancels that common denominator. Therefore each **stored normalized basis row** has one common nonzero minor denominator and minor numerators, of orders at most K. The bound k!A^k gives H0=O(K*(log(A+1)+log(K+1))) bits for these integers.
2. A partially processed scratch row need not have that same minor form. After k eliminations it has a common denominator dividing its initial common denominator times the product of the k stored-row denominators. Each rank-one update has infinity-norm amplification at most 1+2^H0. Thus its denominator and numerator have O(Hinput+K*(H0+1)) bits: a conservative O(K²*(log(A+1)+log(K+1))+Hinput), still polynomial.
3. The raw multiplication/subtraction/division used by Python Fraction has at most a constant multiple of these polynomial input heights before normalization. No repeated squaring of the common denominator is needed in the proof: both scratch coordinates use the same initial denominator at each update.

This proves polynomial height for the actual sorted selector, `_row_basis`, and `_in_span`. For `_in_span`, the tested replacement-row evaluations have a known common input denominator delta, included in Hinput. Only original integer measurement rows are retained, so none of the larger Gaussian scratch heights enters the signature radii or Y.

`exact_solve` is ordinary full Gauss–Jordan elimination of an augmented integer binomial system with row swaps and no column swaps. Completed stages have the usual minor ratios; while a stage is being applied, each updated row is a product/subtraction of two such bounded rows. The matrix size is R and entries are bounded by 2^(Q+R), including the unit signed RHS, so all scratch arithmetic is polynomial-bit. The consecutive binomial-evaluation matrix is nonsingular (successive finite differences reduce it to unit triangular form); the parity solve is integral. Thus no singular or fractional-coefficient exception is being silently ignored on actual parameters.

## 4. Every remaining constructor loop is paid

The integer operator expansion visits at most sum_j 2^j choose(Q-1,j)<=3^Q terms per row. Since r>=2, 3^Q<=D. The loops over node/group/universal rows, and the D² universal-row coordinates, are therefore polynomial. Integer partial sums, even before cancellations giving the sharper final W0 bound, have polynomial bit length by the Gaussian coefficient height plus O(Q+R) bits.

Interpolation uses at most Q linear factors, integer node/difference inverses, and the spectral power-of-two denominator. Each difference/node divides Q!, so partial polynomial products and sums have shared polynomial-bit denominators. The actual common-denominator and numerator theorems in SourceRowHeight justify the completed row; the same finite-product bounds apply to the constructor's intermediate `poly_mul`, `poly_add`, and `poly_scale` prefixes.

Complete bucket assembly stores at most M incidences, with D buckets and at most M/D complete copies. Universal N/rows, interpolation caches, complete-copy maps, forms, raw constraints, selected rows, and validation matrices all have polynomially many entries. `basis_cache` is not a cache over Boolean n-variable assignments: it is produced inside the D²Q universal construction. Its size is polynomial because D is polynomial. Validation performs row-space checks, restoration/degree scans, and scope tests; it never enumerates a full tensor truth table or all global Boolean assignments.

## 5. Repair the local-expansion envelope using an explicit norm

A bare count of 2^n global Boolean assignments does not itself count the 2^arity local truth expansions. The candidate's factor delta+2P can nevertheless be justified without adding a new exponential runtime term.

Use the coefficient l1 norm on jets of precision J. A corrected input port has common denominator delta, and every numerator coefficient is bounded by P. Hence its numerator l1 norm is at most JP. Its complement has l1 norm at most delta+JP. Summing absolute values over **all** local truth choices factorizes:

    sum_eta product_ports norm(choice_eta)
      = product_ports(norm(yes)+norm(no))
      <= [delta+2JP]^arity
      <= [J*(delta+2P)]^arity       (J>=1).

Local table entries and all prefix restriction gates are 0/1. A partial truth-table sum is a subset of this absolute sum, so the same bound covers its accumulator without cancellation. A partial port product is bounded separately by the same global envelope. Truncated convolution is l1-submultiplicative, and a partial convolution coefficient is a subset of its absolute product sum. This covers every `Jets.mul` prefix, not just its output.

Across a partial set of assigned factors, used incidence count is at most M. Group subtotal prefixes have at most 2^|group| local Boolean terms. Products of such partial sums have at most 2^n assignment records because the groups partition variables; inactive groups contribute one dummy choice, not an extra 2^|group|. Factor-dependent off-group Boolean bases are allowed. The FibreAccumulatorHeight masks/record identities cover precisely this distinction.

A partial label sum adds at most Y records, and a partial signed support sum at most Cq<=3^n. Padding a used-incidence denominator to delta^M costs at most an extra delta^M. Therefore the candidate's deliberately loose envelope

    3^n * Y * 2^n * J^(F+M) * (delta+2P)^M * delta^M

is sufficient once this l1 argument is made explicit. No small final count is used to bound a large intermediate.

The Taylor-form frontend itself also has bounded prefixes: each shifted coefficient is a partial sum of at most R+1 original-row coefficients times integer binomial/power factors. `delta[0]=0` ensures that adding the Boolean constant base and the correction does not double the same coefficient budget: the base occupies only degree zero and the correction has zero degree-zero coefficient. All supports and nodes share delta.

## 6. Exact H acquisition and Hermite: mathematical loop matching versus formal execution

The actual frozen `count` does **not** acquire H by evaluating an implicit global polynomial. It explicitly builds `form_data`, then for each (S,U) builds the correction jets, scans each summary label/group fibre, invokes streamed local Boolean multilinear expansion, multiplies group subtotals, and accumulates the signed H jet. Induction on these loops identifies its values with the finite masked/grouped/native expressions in PacketHeight and FibreAccumulatorHeight. A truncated jet multiplication is correct because coefficient k<J depends only on input coefficients <=k; no lost high-degree coefficient can return to a lower degree. This supplies the ordinary-algorithm acquisition and the height argument; it is not a new oracle.

The **formal** missing step is the tracked interpreter/refinement proving that these exact array/dictionary loops have those mathematical meanings and the stated operation counts at every program location. The existing mathematical finite-record theorems describe loop prefixes but do not execute them. This connector remains open.

HermiteArrayHeight now removes any cardinal-input oracle: it executes repeated affine truncated multiplications, constructs the cardinal scalar at zero, performs cached inversion/quotient, evaluates with cached powers, and accumulates nodes while charging callback work. Its common denominator is dL*(dH*dL^J), shared by every node. It proves polynomial binary budgets for the actual scalar backend and prefixes. The frozen binomial-power cardinal builder is algebraically the same finite product; either its ordinary polynomial cost can be charged directly, or the new proven affine builder may be used as the explicit replacement backend. Neither alternative samples the global count polynomial.

## 7. Memory, control and callback qualifications

The actual shared counter retains polynomial state:

* one support S/U and generator state, one mixed-radix summary tuple, and at most r representatives;
* one Boolean local word, full representative/update vector of length n, and polynomially many active jets;
* `form_data`/correction at worst M-by-n-by-J entries, and Q retained H jets;
* fixed-category statistics counters (their integer bit lengths are logarithmic in the number of operations), and at most L+1 result-statistic dictionaries in source_factor_search.

It does not store all 2^h words, all Y labels, or fibre lists. The constructor's alphabet/universal dictionaries are polynomial-size by the D bound. Restriction descriptors accumulate at most L fixed-bit entries. Exact comparisons, dictionary/list operations, indices, copies and array allocation can therefore all be implemented by deterministic scans of a polynomial-size binary state at polynomial overhead per logical operation. A Python dictionary need not be assumed to have expected O(1) access.

The Lean representative function and finite enumerations are not automatically executable scans. A naive complete summary table would lose this polynomial-space statement. It would not defeat the subexponential **time** conclusion if its total work is charged and a fixed-power tape simulation is used, but it would change the explicit constant/time ledger. The reference Python already uses the required streaming implementation.

Arbitrary rational table callbacks are outside the bit contract: individually short, unrelated entry denominators could accumulate badly over a truth table. Native public predicates and every restricted predicate are 0/1 with the explicit polynomial entry program, so this exception does not occur here. Likewise a callback's acquisition work must be charged; array-coefficient lookup or H packet extraction is not a free scalar operation. The actual count loops above supply that work.

## 8. Total rate and all-input qualification

After the repairs, the operation ledger poly(n)*Cq*Y*2^h*2^w promotes to the same form of bit ledger using the polynomial-space scan implementation. Each factor belongs to one group, so group/fibre scans contribute a sum of at most r*2^h, never a Cartesian 2^n execution. A local extension explicitly costs poly(n)*2^w. All construction/validation, Q nodes, J width, F factors, and L+1 prefix queries are polynomial factors.

The exact displayed constant 16435 should be separately pinned to the entropy/schedule derivation; this review does not infer that numerical constant from passing backend audits. The subpower conclusion has an elementary substitute that avoids this numerical constant entirely. Put alpha=q/n, so alpha→0 by q<=4096*n*nu/sqrt(lambda). For 0<x<=1, the finite binomial generating function gives Cq<=x^(-q)*(1+2x)^n, because x^i>=x^q for i<=q. Taking x=sqrt(alpha) when q>0 yields log(Cq)/n <= -(alpha/2)log(alpha)+2sqrt(alpha)→0; q=0 gives Cq=1. The proved summary bound gives log(Y)=O(n*nu²/sqrt(lambda))=o(n), and the head bound gives h=O(n*nu²/sqrt(lambda))=o(n). Thus the needed rate follows without assuming the unreviewed value16435. Any fixed-power tape simulation multiplies constants in that exponent; it preserves o(L) but need not preserve 16435 verbatim.

Since L<=n<=6400L, w<=512L^(3/4), and nu²/sqrt(lambda)→0, all fixed polynomial overheads preserve 2^o(L)=N^o(1). The guard is a computed test, not advice. Eventual acceptance means its failures occupy only finitely many input lengths; ordinary trial division on those cases is an asymptotically constant exceptional cost. No numerical threshold has to be supplied to the algorithm. Eventually 2^(L/12)<=2^(1/12)*N^(1/12), leaving room below 1/6.

## 9. Exact remaining formal joins before a global verified runtime claim

1. **Computable enumerations:** SourceLayout is generic in finite `en`; the Python constructor has explicit lexical enumerations. ConstructedCounter.layout currently hardcodes `defaultEnumerations`, whose semantic definition uses noncomputable enumeration choices. Do not assign a machine cost to that choice. Instantiate the generic layout/counter with explicit enumerations, or prove the requisite computable refinement. No equality with a particular classical enumeration is needed for the ordinary algorithm because the source guarantees hold for every enumeration.
2. **Actual selector/exact_solve execution:** formalize the sorted selector's span/rank and polynomial scratch proof above (and the binomial Gauss–Jordan solve), or provide a proved fraction-free implementation retaining original integer rows. Passing row-space/rank theorems alone is not a paid elimination interpreter.
3. **H frontend:** connect the explicit Taylor/local-truth/partial-convolution/forced-fibre/support loops to the mathematical masked/node packets and their uniform bounds. Existing PacketHeight/FibreAccumulatorHeight cover the mathematical intermediate expressions; they are not themselves those array loops.
4. **Primitive/control composition:** RationalBits, DotBits, HermiteArrayHeight and local entry clocks still need one full interpreter/cost composition with the concrete packet/layout calls, bounded buffers, flat-table/control handling, and the chosen machine model. Do not charge H-generation or enumeration callbacks as reads.
5. **Public semantic join/restrictions:** root is constructing the source-counter-to-public-factor join. The subdivided graph types already match as explained above; add the equality-entry checker and designated-host restriction equivalence when assembling the executable public interpreter. The Python/Lean compiler-ID isomorphism is not currently a proved theorem; an explicitly encoded typed-graph implementation can instead be used, with its construction and local IDs paid.
6. **Rate theorem:** attach the exact finite menu/head/summary and schedule estimates to that same executed algorithm. The mathematical estimates and eventual guards are already available, but a final primitive-runtime theorem must quantify over the actual public execution rather than a unit-cost or abstract callback counter.

These are genuine formal correspondence/execution obligations, not a newly identified unpaid exponential mathematical operation. This review supports the repaired ordinary bit-composition argument and gives concrete invariants for closing those joins; it does not label the complete guaranteed runtime kernel-verified or the overall goal finished.

## Final refresh after root integration

Root amended the candidate with the polynomial partial-Gaussian denominator product and the explicit l1 factor accounting. I reread those amendments: they repair the two quantitative issues identified here. The remaining sentence about “reordering gives the same ordered-pivot invariant” should be read only as preserving row-echelon independence, not equality with the intermediate matrix of ordinary Gaussian elimination on reordered original rows. The explicit creation-time/minor and partial-scratch proof in §3 above is the precise invariant.

New `SemiprimeSubdividedEntry` now contains the original-checker/equality case split and its correctness/polynomial bound, closing that previously small entry binding. New `SemiprimePublicConstructedCount` provides the semantic source-counter/public ordinary-factor join; this resolves the count specification join, not the executable-enumeration or runtime refinements. New LocalPrefixHeight is also acknowledged by the amended candidate for actual masked truth subtotals/selected-port leaves. The remaining substantive formal obligations are explicit enumerations, computed elimination, complete H interpreter and primitive/control/callback cost composition, then a final execution-rate theorem.

No semiprime-success experiment or numeric factoring campaign was used for this audit. The two Python copies actually read were hash-compared with the frozen imported shared_counter/compiler and are identical.

Final doc-only reread: the candidate now explicitly limits sorting to echelon independence and replaces reliance on unpinned16435 by the finite-generating-function o(n) proof; these amendments PASS, and its reviewed source hash has been refreshed.
