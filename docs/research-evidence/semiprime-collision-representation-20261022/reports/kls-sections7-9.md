# Reading Song–Zhang v2 §§7–9: uniform closure and transferable invariants

22 October2026. Scope: substantive reading of §§7–9 (PDF pp63–138), including the starting-family/loss initialization, repeated-height profiles, finite-chain floors, and final closure. This is an applicability/quantifier review, not formal certification of the paper's entire KLS theorem or of its earlier analytic dependencies.

Source: user-supplied cached *An O(1) Bound for the KLS Constant*, Zhao Song and Xinzhi Zhang, arXiv:2610.01447v2,4Oct2026. PDF SHA256 fad3f750a121cd99f09213ea237fc71b66e97ad1699ecca1d07f74c2fd69d771. Read from the cached text/PDF in this directory. References below use the paper's own numbering, not independently certified theorems.

## What the argument actually does

Section7 first establishes a dimensional profile, not the final dimension-free bound. Gaussian observation gives the exact posterior identities (168)–(169). Before a covariance exit, the witness variance obeys F'(t)>=−2F(t). A localization time c/log(en), together with the stated covariance exit estimate, leaves a realization with controlled covariance and witness variance >1/2. Whitening that posterior transfers the curvature profile back with one fixed constant. Theorem7.1 states its constants uniformly in BOTH n and arbitrary finite inner depth r, so r can subsequently be chosen near log-star(n). This is an existential selection of a good posterior, not an algorithm producing that realization or evaluating any arithmetic zero mask.

Section8 bootstraps profiles into coefficient estimates and back. Proposition8.3 is designed to transfer a STATIC coefficient bound without continuity of the assignment that defined it. The finite-degree smoothing/approximation fixes the parameters before passing to a limit. Proposition8.1 keeps the starting depth r_Q independent of outer-round count j, but its amplitude is A_j=A_1*C_*^(j−1). Since the height termination count kappa(x) in Lemma8.26 is unbounded, a constant cost PER round is not enough for a universal final bound. The paper explicitly identifies this as the remaining loss.

The actual energy bookkeeping is stronger than separate estimates on unrelated families. Lemma8.8 initializes ONE finite starting family, with bounded prefix losses AND a matched energy budget (186) for all needed later prefixes. Lemmas8.9–8.10 reuse that same family, retain its initial loss prefix, and compare the joint accumulated losses against its budget. An existential low-loss family for each inequality separately would not justify their combination. Proposition9.23 preserves this requirement explicitly in (407), as well as the actual propagation envelope (408).

Section9 replaces the fixed outer multiplier by losses tending to zero, and prevents the worsening cutoff/depth from reintroducing an unbounded argument cost. This is the important substantive mechanism, rather than merely the phrase 'iterate log-star.'

## Uniformity as iteration depth varies

The following quantifiers are explicit in the inspected statements and are crucial to their intended closure:

1. Proposition8.3 has one transfer threshold independent of the coefficient floor H and of its assignment Z. Proposition8.24's profile constant is independent of the seed amplitude, Q, r and dimension after the seed comparison constants are fixed. Lemma8.23 bounds the whole terminal distortion product uniformly in Q and its finite terminal depth, after a common burn-in r_Q.

2. Proposition9.23 permits ANY finite ordered cap chain H_0,...,H_(N−1), with constants independent of its length N, cap amplitudes, margins, and Q. Its floor is a MAXIMUM of the cap contributions, not their sum. More importantly, its proof partitions coefficient degrees into disjoint bands and bounds their UNION by ONE stretched-exponential degree sum (409). It does not pay a fixed constant once per retained cap. The per-order bridge estimates likewise use the appropriate band rather than summing all band constants.

3. The averaged height maps in Lemma9.17 are globally1/4-Lipschitz. Their i-fold compositions W_i have Lipschitz constant4^(−i−1). Lemmas9.18–9.20 reduce FIXED-power/sum/product argument distortions to O(4^(−i)). Here 'fixed' is a real qualification: the constants may depend on those powers. The paper chooses one additive reserve after listing the finite types of powers needed; it does not authorize polynomial exponents that increase with i.

4. In Proposition9.25, alpha_i=alpha_0*2^(−i), R_i=ceil(C alpha_i^(−12)), A_(i+1)=exp(C_A alpha_i)A_i, and S_(i+1)=S_i+B2^(−i). Thus A_i and S_i are bounded by geometric series, even though their admissible starting depths R_i grow exponentially in i. The asserted profile holds for EVERY finite i and EVERY r>=R_i before a final i is selected.

5. The growing threshold is not disposed of by a naive Lipschitz argument: 4^(−i)R_i would GROW like2^(10i). Lemma9.24 first uses the fixed-power argument estimate to replace alpha_i^(−12) by an argument of order2^i, and ONLY THEN contracts it, obtaining an O(2^(−i)) cost. This order of operations is essential. It is the explicit control of the otherwise hidden depth charge.

6. In the final step9.26, for a given curvature parameter x=max(1,a^−1), choose the FINITE i=N_chi(x)+1 and r=R_i+ceil(C t(x)). Finite termination gives W_i(x)=4, while Lemma9.24 controls W_i(r). Bounded A_i,S_i then yield the claimed universal radius bound. No uniform finite i is asserted for all x. Approximation fixes each approximant's finite internal choices and passes only the already-uniform scalar inequality to the limit.

The dependency order at the end of Proposition9.25 is also stated: fix degree/moment/Green/bridge constants, then the depth/order/transfer constants, then C_R,0, C_A, B, and finally A_0. The intended point is that enlarging B,A_0 cannot retroactively change the depth or block constants. I found no explicit dependence on cap-chain length in the cited closure statements; verifying every imported analytic estimate and its domains would require a separate proof audit. In particular Section7's covariance control uses the earlier uniform quadratic-form input Lemma2.1, and Section9's block proof imports several substantial Section6–8 analytic estimates. This reading does not silently certify those dependencies.

## What transfers to exact sparse collision support

### A. One source-bearing family, one matched budget

The most useful conceptual transfer is the SAME-FAMILY constraint. Arithmetic sketches, norms, character phases, and scalar masks may each be cheap, but combining their separately obtained zeros is invalid unless they refer to the same native row and index. The paper's (407) is an appropriate design template: one acquired object should simultaneously carry retained-prefix support and a budget that accounts for every later operation. In our setting the analogue is a labelled nonnegative collision measure on actual leaves (j,i), with restriction maps or a certified lift preserving that label. It is not an unlabelled extension-field norm whose zero could come from a different conjugate component.

### B. Retain old bounds without paying once per old bound

The finite-chain argument provides a concrete way to avoid repeated overhead: retain all earlier constraints, assign disjoint parameter/degree ranges to them, and charge each underlying term once. An arithmetic analogue would partition actual exponent blocks/valuation strata and share their preprocessing, rather than run a separate long-product routine for every public twist/cap. Merely retaining a compact list of constraints does not suffice; one needs the analogue of the single sum (409), i.e. an explicit near-linear total acquisition over the disjoint ranges. Our gcd-stratum orbit correlation and product-tree zeta combination is an example of this kind of ACTUAL charge: sum_(d|m)phi(d)=m, rather than a fresh m-sized computation for each d.

### C. Summable error can preserve an integer support count, if it is acquired

The exact deficit D=sum[1−Jacobi(diff,N)^2] is a nonnegative integer <=2J on the retained order range. If a future positive coarse-graining algorithm produced a certified approximation with TOTAL absolute error <1/2, it would determine D exactly by rounding. One may allocate errors epsilon_i with sum epsilon_i<1/2 and charge the precision/verification at every level. For normalized mass D/(2J), the absolute error threshold is <1/(4J), not a dimension-free constant. Preserving a fixed fraction of TOTAL averaged mass is not enough to preserve one rare planted leaf unless positivity and labelled source retention are proved.

This is a possible architecture, not an approximate character-count algorithm supplied by the KLS theorem. Signed character cancellation has no nonnegative-loss interpretation automatically. Likewise a bounded product of analytic loss factors does not itself give an integer support count or a properly localized base-prime separator.

### D. Remove polynomial argument inflation before contraction

The fixed-power-then-contraction step in Lemma9.24 is a useful warning and a constructive target. An arithmetic recursive transform may have O(m) descriptive states but still expand target shifts or block lengths exponentially. A claimed contracting size parameter must first account for every polynomial/exponential threshold introduced by the smaller error. The needed theorem should bound the total acquired vector lengths, convolution degrees, and bit precision, not just a normalized amplitude. Any recurrence that carries O(m) states at EACH of unboundedly many rounds still has to sum their work.

## What does NOT transfer as an algorithm

The paper proves inequalities using moment/operator bounds, Gaussian conditioning, norm-attaining vectors, and finite parameter choices. It does not provide a near-linear algorithm for constructing those witnesses. Its bounded A_i and S_i are ANALYTIC amplitudes/reserves, not operation counts. R_i~2^(12i), high-order Q depending polynomially on epsilon^−1, and the long blocks used in their proofs can grow substantially. No soft-m arithmetic runtime follows from the statement that all these parameters are finite or that the final constant is universal.

Nor does uniform KLS turn the original discrete modular collision grid into a log-concave sampling space with computable normalization. Such a representation would itself have to acquire the nonnegative source mass/normalizer or exact defect; otherwise it assumes the missing query. The useful analogy is the invariant and the explicit loss accounting, not invoking the dimension-free bound as a factor-finding oracle.

## Focused takeaway for the current construction

The immediate concrete direction remains an acquired symmetry-breaking object: a fixed-array whole-local orbit equalizer or a low-rank permutation defect with a certified same-leaf source. The KLS closure suggests retaining all prior constraints on that SAME object and partitioning losses so each acquired coefficient/block is paid once. A positive arithmetic theorem would additionally need total work soft O(m), precision/error small enough to retain at least one integer leaf, and proper/saturated scalar recovery. No such theorem is proved by this analogy. This scoped reading neither asserts nor rejects the validity of the entire claimed KLS result.
