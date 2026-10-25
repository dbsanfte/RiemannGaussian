# Reusable randomness in the shallow Dixon circuit proposal

Status (22 October 2026): the shallow-circuit proposal gives a valid **two-way-random-tape** sublinear-space algorithm, conditional on the proposed circuit family and its factoring analysis. It does not yet give a fresh-coin randomized source to which the OpenAI manuscript applies. I found no supplied theorem that closes that gap. This is a model restriction, not an arithmetic workspace lower bound.

## Exact circuit-to-machine statement

Let a bounded-fan-in circuit family for a verified factoring predicate have size Z, depth D, and at most R random input bits. Assume its local gate-description procedure has workspace U_S and time U_T. For fixed input N of bit length n, the circuit can be evaluated using a read-only reusable random input with

    S = O(D + log Z + log R + U_S),
    T <= 2^{O(D)} poly(D, log Z, n) U_T R.

This bound can be obtained without storing a gate identifier at every recursion level. Keep the root-to-current-node binary path (D bits), the stack of completed child values (O(D) bits), and one current gate identifier (O(log Z) bits). Reconstruct the identifier from the path whenever needed by rerunning the uniform gate procedure. Each output bit may be evaluated separately. Moving a physical two-way random-tape head to an addressed input costs at most R extra steps and O(log R) counted address bits. Consequently, if

    D + log Z + log R + U_S + log U_T = o(n),

then S=o(n) and log T=o(n). This proves the useful reusable-random-tape statement; it does not prove its fresh-coin analogue.

For the proposed Dixon parameters B=exp(n^alpha), 0<alpha<1/2, the anticipated logarithm of the trial count is O(n^(1-alpha) log n). The anticipated log-squared factor-base linear-algebra depth is O(n^(2alpha)). Both are o(n). Subject to the other circuit construction details, these estimates are compatible with the statement above.

## Why the manuscript cannot presently be applied

The OpenAI manuscript, page 2, defines the randomized machine using fresh independent fair bits. Its configuration transition system can forget past coins only because future coins are independent. An evaluator querying the same random input twice must see the same bit. Replacing the second query by a fresh bit changes its distribution (the circuit r XOR r is the elementary counterexample). Keeping an uncounted random assignment on a read-only tape changes the machine model.

The distinction is recognized explicitly in primary literature: Kinne–van Melkebeek–Shaltiel distinguish BP.L, with two-way random input, from BPL with one-way randomness; their discussion does not identify the two models. Their 2009 bounds are historical, not a claim about the current literature.

Source: https://cs.indstate.edu/~jkinne/research/KvMS.pdf (Theorem 4 and following footnote).

## A directly relevant quantitative theorem, and its missing premise

Cheng–Wu, *SC Derandomization for Regular ROBPs and Models Beyond BPL*, latest v3 (7 October 2026), Section 10.4, Corollary 6, treats a time-T, space-S machine with a two-way random tape, provided each random cell is visited at most p times. It gives additive-epsilon estimation in time

    2^{O(p(S+log(n+T)))} poly(n,T,1/epsilon).

Its workspace is O((p(S+log(n+T))+log(1/epsilon)) log(n+T)). Thus, for constant epsilon, the additional condition

    p(S+log T+log n) = o(n)

would give deterministic exp(o(n)) factoring directly, with no need to invoke the OpenAI result. Constant p suffices, as would some slowly growing p.

Source: https://arxiv.org/abs/2609.23603v3 ; local text `cheng-wu.txt`, Section 10.4, Corollary 6. The original v1 calls the corresponding result Corollary 4, Section 8.4; the OpenAI manuscript cites its constant-p specialization as Theorem 5.

Circuit depth alone supplies no such visit bound. Unfolding a depth-D circuit can revisit a random bit as many as 2^D times, and a physical head also revisits intermediate cells while moving between queries. Even an oblivious evaluation schedule is insufficient: the theorem restricts multiplicity, not merely adaptivity. The current construction establishes only p<=T, which makes the displayed deterministic-time bound useless for exp(o(n)). This is an absent upper bound, not a lower bound proving that all possible Dixon evaluations require many visits.

The same paper's oblivious-stack theorem still requires fresh/read-once random coins. An oblivious DFS recursion stack does not license a second reusable random tape; storing the sampled assignment on that stack would require a separate valid stack-access construction. Arbitrary random-bit reuse is not automatically compatible with LIFO access.

## Why three tempting repairs do not establish the premise

1. **Generate a candidate from a short stored seed.** Exact uniform sampling modulo N needs at least log_2 N random seed bits by support size. Even total variation distance delta from uniform needs support at least (1-delta)N. Therefore an o(n)-bit seed cannot reproduce the distribution used in the usual proof. A number-theoretically tailored source might nevertheless preserve factoring success; that needs a new proof. This observation is only about uniformity, not an impossibility result for tailored sources.

2. **Use a generic space-bounded PRG.** Its standard guarantee is for a source that reads fresh coins once. A two-way evaluation of a function of a fixed random assignment is exactly the missing guarantee. The fact that deterministic arithmetic on that assignment is shallow does not establish it. A generator G_N with seed k=o(n), local generation in exp(o(n)) time and o(n) space, and proven factoring success would suffice; seed enumeration alone would then already give deterministic exp(o(n)) factoring.

3. **Apply conditional expectations.** For success indicator f_N, fixing a prefix needs estimates of E[f_N(aU)] with the suffix reused consistently throughout circuit evaluation. Those are still two-way-random-input probability problems. The new fresh-coin estimator does not supply those estimates. Also, retaining an arbitrary full prefix consumes its length; implicit prefix recomputation would need its own proved time/space bounds. Conditional expectations is a reduction to an estimator here, not an implementation of that estimator.

## A precise next lemma that would finish this route

Any one of the following, with rigorous success probability, would suffice:

* A fresh-coin implementation of the fixed Dixon success predicate with S=o(n), log T=o(n), allowing the OpenAI quantitative compiler.
* A reusable-random-tape implementation with the same resources and p(S+log T+log n)=o(n), allowing Cheng–Wu directly.
* A locally evaluable o(n)-seed hitting distribution for the *whole verified-factor-output circuit*, allowing direct seed enumeration.

Preserving only the marginal chance that a residue is smooth does not establish the last item: the relation dependencies and the final nontrivial-square-congruence success must remain valid. No one of these lemmas follows solely from the shallow arithmetic and linear-algebra circuit bounds.
