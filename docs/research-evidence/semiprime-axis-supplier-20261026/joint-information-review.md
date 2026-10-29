# Joint interval/residue HH consumer: independent theorem check

26 October 2026. Paper-only extension of the independently reviewed restricted Harvey–Hittmeir consumer. No tests, implementation, repository changes or supplier claim.

**PASS.** Weak interval information and weak residue information combine in the following actual consumer; neither input needs to identify one complete factor tag/window separately.

## Statement

Use the prepared native semiprime N=PQ, P<Q, N<=k^6, k>16, H=k², and supplied beta with both local q=beta^H orders greater than 16H. Let n|k. Supply A explicit rectangles

    (sigma_j mod n, integer 1<=L_j<=U_j<=sqrt N),
    U_j<=2L_j,

at least one of which has BOTH P=sigma_j mod n and L_j<=P<=U_j. This is a joint promise on one rectangle, not separate assertions that one interval and a different residue are correct. Put

    Delta=sum_(positive widths j) (U_j-L_j)/L_j.

Point intervals are tested directly for divisibility first. Nonunit residues modulo n are discarded; they cannot describe P. A wrong or noncovering menu returns only a verified factor or bounded FAIL, never a primality conclusion.

For every positive integer r in the source's polynomial-height range, the restricted source algorithm has initialized bit cost

    soft O(A+r*Delta+sqrt(N)/(nr)^(3/2)+1).       (1)

Integer optimization yields the upper bound

    soft O(A+Delta+1+N^(1/5)*(Delta/n)^(3/5)),     (2)

provided the requisite projected-order condition is supplied. The native sufficient regime below proves that condition directly, without a new preparation.

## Integer centres and exact endpoints

In rectangle j initialize sigma0=L_j. While sigma0<=U_j, acquire its source lattice pair and giant, then update

    sigma0_next=ceil((1+1/r)*sigma0).

Do not replace this with a noninteger continuum approximation. Every integer P in [L_j,U_j] belongs to some visited half-open bin [sigma0,sigma0_next). For integer P, membership implies P<(1+1/r)*sigma0, exactly the source hypothesis. An inclusive upper endpoint is therefore covered. The last bin may extend past U_j; those extra candidates are harmless and need not be declared promised.

If t starts are visited, successive centres grow by at least 1+1/r. Consequently t<=1+log(U_j/L_j)/log(1+1/r)<=1+2r*(U_j-L_j)/L_j. This proves the A+rDelta count, including width-one and very short intervals. Point intervals L=U contribute a direct tested integer, not a fictitious zero start. If every interval is a point, all promised work terminates in this initial scan and Delta=0 requires no division.

All rectangles share the same baby alphabet delta=beta^(n²), lambda=ceil(4sqrt(N)/(nr)^(3/2)), kappa=2lambda+1. For the true rectangle/bin, HH Proposition 3.3 and Algorithm 4.3 give the covered giant. Duplicate centres/giants are allowed: retain all labels and process all global matches, bounded by the total actual giant count. The exact quadratic recovery, including a=0 or b=0, precedes removal of matches. The primary local-collision routine then applies to the remaining giants. Literal exponent-zero matches are handled by that exact recovery, not an annihilator assumption. Thus (1) inherits the fully paid correctness proof in review-restricted-residue.md, not only its lattice descriptor.

## Computable weights with no large rational common denominator

For each positive delta_j=(U_j-L_j)/L_j choose a power of two d_j satisfying

    delta_j<=d_j<2delta_j.

Compute it by comparing integer numerator/denominator bit lengths and one shifted comparison. Since U_j-L_j>=1 and L_j<=sqrt N, delta_j>=1/sqrt N, while delta_j<=1. Thus every d_j denominator is a power of two with O(log N) exponent. Choose the largest exponent T across the menu and sum integer numerators over the common denominator 2^T. This acquires Delta_hat=sum d_j with

    Delta<=Delta_hat<2Delta.

The numerator has O(log N+log A) bits; in the native A=O(k) regime this is O(log N). Total preparation is soft A bit work. No product of the unrelated L_j denominators is formed. Direct exact construction of ceil(c*k/Delta_hat) uses this one binary denominator and integer arithmetic.

Replacing Delta by Delta_hat changes optimized bounds only by constants. For positive Delta in the native sufficient regime

    A=soft O(k), Delta<=n/k^(1/3),

take, conservatively,

    r=ceil(32k/Delta_hat).

Then nr>=16k^(4/3), hence

    lambda<=ceil(k/16), kappa<=k/8+3<k.

Also rDelta<=rDelta_hat<=32k+Delta_hat=O(k), because n<=k and Delta_hat<2n/k^(1/3). The total acquired giant count is soft k. All baby values, source lattice constructions, exact centres, exponentiations, sorting, monic polynomial construction/evaluation and collision localization are consequently soft k.

The local order guard is automatic: n² divides H, so q=(beta^(n²))^(H/n²) and ord_R(beta^(n²))>=ord_R(q)>16H at R=P,Q. No smoothness, roughness, cross-prime coprimality or new order finder is needed. Positive Delta_hat>=1/sqrt N ensures r=O(k sqrt N); in the native prepared range k<N^(1/4), this is O(N), meeting the source parameter-height condition. All lattice/exponent labels therefore remain O(log N) bits.

## Scope

The guaranteed consumer itself uses source quadratic/local-collision recovery and does not require T_ext. A separate annihilator fallback still requires its own nonzero label and once-only charge. The +Delta term in (2) is the integer-r ceiling cost; the +A term pays each rectangle even when its relative width is tiny. The degree/length of the input menu, its acquisition, and any work proving its joint coverage remain additional obligations.

This is a genuine combined-information interface: a covering set of at most soft k joint rectangles with total relative width at most n/k^(1/3) suffices for a native soft-k factor query. It does not supply those rectangles, convert arbitrary axis alias phases into factor residues, or prove a new all-semiprime factoring rate. Primary provenance is [Harvey–Hittmeir Proposition 3.3 and Algorithm 4.3](https://arxiv.org/html/2105.11105), already independently checked in this packet.
