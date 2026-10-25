# Rough quadratic-torus orders with a paid wide-exponent extraction

24 October 2026. Separate scratch followup; no integrating packet or repository file was changed. The extension is proved below. It replaces the supplier's 2-primary projection by complete removal of primes <=k and keeps the same soft-k deterministic BIT budget. The complementary-exponent splitting is a known generic-group algorithm, not a new generic order algorithm.

## 1. Input and exact output

Use `/tmp/semiprime-quadratic-ideal-20261024/torus-order-supplier.md`, SHA256 `1f3033cc85c1b6798a188daa7b7c32d702b87d2cb3401e3e1f1afe6cb3a4e9bc`, and its independent review SHA256 `f84298cac56e9f028828ab69494e408d3fbe9d288be57b7a3688b14cf7fd4de6`.

Thus N=PQ, P<Q distinct odd, N<=k^6, P,Q>16k^2, H=k^2, C=16k^2, and B=(Z/N)[tau]/(tau^2-D), with D<0 fundamental, |D|<=k/2 and Jacobi(D,N)=-1. The actual scalar beta remains available. The norm-one local groups T_p are cyclic of order p-epsilon_p, epsilon_p=(D/p). We use the synchronized character/conductor data when rebuilding the native rows, exactly as in the predecessor.

**Proved extension.** Deterministically in soft k BIT operations return a proper factor of N or an acquired norm-one W such that BOTH local orders are k-rough (every prime divisor is >k) and

    ord_P(W^H)>C,  ord_Q(W^H)>C.

These orders are odd automatically, and ord_p(W^H)=ord_p(W). No coprimality between the two primes' orders and no survival under an N+1 projection is claimed. This roughness is an additional result of the following algorithm; it must not be imputed to the previous supplier without running the changed projection/extraction.

## 2. Acquire the smooth-killing exponent and charge its width

Sieve the primes ell<=k and acquire the fully factored integer

    E=prod_(prime ell<=k) ell^[floor(log_ell(N+1))].     (1)

The exponent of each prime is found by exact integer powers/comparisons. Each prime power in (1) is at most N+1. An elementary sufficient bit bound is

    B_E=bitlength(E)=O(1+pi(k) log(N+1))
                         <=O(k log(N+1))=soft k.

No sharp prime-counting estimate is needed. A balanced integer product tree acquires E in soft B_E work. Its prime factors/exponents are retained; no factorization of N+1 is performed.

If R is any norm-one point, its local order divides p-epsilon_p<=N+1. Hence W=R^E has no local prime factor <=k: for each such ell, (1) removes its ENTIRE possible ell-primary part. It already removes the complete 2-part. Because every prime divisor of H=k^2 is <=k,

    gcd(H,ord_p(W))=1,  ord_p(W^H)=ord_p(W).            (2)

Computing R^E by binary powering costs O(B_E) constant-rank ring multiplications, hence soft k bits. The local value is allowed to become one; the actual screen and progress argument below handle that branch. No projection-survival premise is introduced.

## 3. Preserve the actual palette and ordered screen

Maintain M<k dividing BOTH p-epsilon_p, initially M=1. The predecessor's acquired palette R_a=(a+tau)/(a-tau), 1<=a<=2M+1, has actual unit denominators and pairwise unit differences. At most M entries lie in each local M-kernel. Scan the actual norms Norm(R_a^M-1): a proper gcd factors, a saturated value is discarded, and a unit selects R outside BOTH M-kernels. This costs soft M; no order screen is run for every palette member.

For that one selected R acquire W=R^E and q=W^H. Run the predecessor's actual monic baby/giant short-order screen for q through C=(4k)^2. Norm-one is essential: at BOTH split and nonsplit sides,

    Norm(q^n-1)=0 mod p iff q^n=1 in the whole B_p.

On a split side this is -(u^n-1)^2/u^n for (u,u^-1). Thus unit block norms certify both local orders>C; return W, with roughness from Section 2. A proper block/child gcd factors. Otherwise take the FIRST nonunit block and earliest-child descent. It gives an exact COMMON projected order

    ord_P(q)=ord_Q(q)=r<=C,                            (3)

including r=1. Earlier positive exponents have been excluded on BOTH sides. A saturated block alone is not used as an order.

Now the RAW point R has an actual global annihilator

    K=E H r.                                         (4)

Its complete prime factorization is acquired by merging (1), the public factors of k, and trial factorization of r<=16k^2. The latter costs at most 4k trial divisors, hence soft k. Put kappa=bitlength K; kappa=B_E+O(log N)=soft k. Every individual prime-power factor A_ell=ell^[v_ell(K)] has O(log N) bits, since its contribution from E is <=N+1 and H r is polynomially bounded in N.

K is WIDE: kappa need not be O(log N). Repeatedly powering R by K/ell independently for all primes would not meet the claimed bound. The next two sections replace precisely that operation. No wide-annihilator Burgess/beta decoder is invoked anywhere.

## 4. Known complementary-power tree: all prime-primary values in soft k

Write K=prod_(ell in S) A_ell, with coprime prime-power leaves, and w=|S|. Build a balanced product tree of these integer leaves. For a node v with subtree product D_v, maintain an actual group element

    R_v=R^(K/D_v).

At the root R_root=R. For children with products D_left,D_right, compute

    R_left = R_v^(D_right),
    R_right= R_v^(D_left).                            (5)

At a leaf this delivers

    S_ell=R^(K/A_ell),                                (6)

without acquiring w independent kappa-bit complementary exponents. The equality in (5) proves the invariant with no division in B.

At each tree depth the sibling exponents in all calls have TOTAL bit length O(kappa): the corresponding disjoint subtree products multiply to a divisor of K, and their number is also O(kappa). Binary powering therefore takes O(kappa) group multiplications per depth, O(kappa log(w+1)) overall. Integer product-tree work/storage is soft kappa. Since B has fixed rank and residues have O(log N) bits, all actual group arithmetic is soft k BIT work. This bound needs no random base or hidden group oracle.

**Primary attribution.** [Andrew V. Sutherland, Order Computations in Generic Groups, PhD thesis, MIT, 2007](https://math.mit.edu/~drew/sutherland-phd.pdf), Chapter 7, supplies the relevant established machinery. Section 7.4, Algorithm 7.3, pages 113--114, explicitly credits Celler and Leedham-Green and computes all alpha^(N/N_i) by recursive product splitting in O(log N log w) group operations. Section 7.2 treats large factored exponents; Section 7.6 gives additional fixed-base multiexponentiation options, unnecessary for this soft bound. We use the elementary complementary-power version and prove its exact ledger here. The extension below is the norm-gcd branch that extracts or separates TWO unknown local orders and plugs it into the supplier; it is not a claim to invent the generic exponent-splitting technique.

## 5. Simultaneous local valuations: one short search per primary leaf

Because the local raw orders divide K, the local order of S_ell is precisely ell^b_(ell,p), where b_(ell,p)=v_ell(ord_p(R)); all other prime components were killed by (6). Here 0<=b_(ell,p)<=a_ell=v_ell(K).

For any e in [0,a_ell] acquire S_ell^(ell^e), then compute

    g_e=gcd(Norm(S_ell^(ell^e)-1),N).

A proper g_e factors. If g_e=1, BOTH b_(ell,p)>e. If g_e=N, BOTH b_(ell,p)<=e. These implications use only the norm-one whole-identity test, and remain valid on the split side.

Binary-search the threshold, initializing lo=-1 and hi=a_ell. The upper endpoint is a known annihilator; the lower endpoint expresses the automatic inequalities b>=0. At each interior midpoint use the test above: unit sets lo=e, saturated sets hi=e, proper factors and stops. Upon termination hi=lo+1. If hi=0, both valuations are zero. Otherwise the last certified lower inequality and upper inequality force BOTH valuations to equal hi. Thus if unequal local valuations existed, some test necessarily would have returned a proper factor; no unequal-primary branch is silently identified as common.

One leaf uses O(log(a_ell+2)) tests. Every powering exponent ell^e has bit length at most O(1+a_ell log ell)=O(log A_ell). The total cost of all leaf tests is therefore

    O(sum_ell log A_ell * log(a_ell+2))
       =O(kappa log log(N+2))

constant-rank group multiplications, plus a polylogarithmic-bit gcd per test. The bound sum log A_ell=log K pays all leaves; it is NOT kappa times their number. Together with Section 4 this is soft k.

If no factor was returned, reconstruct

    d=prod_ell ell^[b_ell].                           (7)

This is the exact RAW order of R at BOTH primes, because (6) covers every prime factor of the global annihilator and every valuation was determined. Although K was wide, d divides both p-epsilon_p and hence d<=P+1<=N+1. Thus d and every partial positive product in (7) have O(log N) bits. The small size is a consequence of the proven actual-order invariant, not an assumption that the wide exponent was short.

This gives a complete deterministic factor-or-common-exact-order extraction for the raw R from the wide fully factored K, within soft k. A saturated norm at one arbitrary large exponent is not used as a prime factor witness, and no auxiliary order value is handed to the original bounded-leaf decoder.

## 6. Termination, AP escape, and total budget

Apply the same supplier continuation with this d. If d>=k, use the established exact AP factor consumer: search both di+1 and di-1 over 2<=di+epsilon<=floor(sqrt N). The smaller prime lies in one progression; all terms are below Q, so a nonunit gcd is proper. Full blocks and literal tails give exact endpoints, even when d=P+1>sqrt N. Its term count is O(sqrt N/d+1), and its baby size is O(k) because N<=k^6 and d>=k. The AP products and gcds cost soft k.

If d<k, the chosen R was outside the old M-kernel, so d does not divide M. Set M'=lcm(M,d); it still divides both full group orders and M'/M is an integer >=2. If M'>=k the AP escape applies immediately. Otherwise continue with the new M. This invariant uses only a known common divisor, not an unacquired element of order M.

There are O(log k) iterations. Their palette M values at least double, so total palette work is soft k. E and its factorization are acquired once. Each iteration pays one R^E, one actual q screen, one r factorization, one complementary-power tree and valuation extraction, each soft k. Suppressed logarithmic factors cover O(log k) repetitions. All gcds, integer products/labels, explicit inverses for palette points and AP endpoints are charged.

As a useful consistency check, any nontrivial r from (3) is itself k-rough by (2); therefore r>k and the recovered raw d>=r already triggers AP escape. Only r=1 can feed the below-k M-growth branch. This observation is not needed for the termination proof.

## 7. Native consumer and honest scope

Use the returned W in ALL actual beta-coupled native targets, retaining the synchronized conductor/tag contract. It is still norm one and its local orders divide p-chi_D(p), so the original own-hit proof and target norm identity remain valid. Reacquire all rows in soft k. RERUN the actual short unit screen for the CHANGED coupled seed z=(beta W)^H: beta can cancel a split coordinate even though W^H itself has certified large rough order. The nonsplit beta norm argument keeps that screen within soft k, returning a factor or the actual required units.

The original same-leaf norm/beta consumer remains unchanged. No coprimality between the two local torus orders, no N+1 projection, no generic additive coordinate profile and no balanced Groebner ideal are supplied here. The norm-fiber modulus and ideal constructions remain independent of W's order. The completed long query remains soft(J+sqrt(JL))=soft k^(3/2); roughness alone has not executed its terminal product or improved the factoring exponent.

## Source pin

The exact primary thesis PDF is cached as `sources/sutherland-phd.pdf`, SHA256 `5c326306358bd06f5f0ddb47fceb2b179ce29421222acde9094ef85681c0d20f`, with searchable text beside it. The integrating packet in `/tmp/semiprime-quadratic-ideal-20261024/` was not edited.
