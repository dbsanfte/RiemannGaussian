# Large-index Frobenius traces of the actual quadratic AP source

23 October 2026. Scratch research only. The 222 frozen entries and repository files are unchanged. Read the constructive frontier index, the torus-Frobenius and weighted-rational-trace reports, native multiplier closure, q-Newton contraction, twist-character algorithm audit, and composite-colour retention reports before this investigation. Smooth projection, source-preserving count/character-deficit equivalences, and the short-annihilator consumer are inherited results, not new acquisitions here.

**Result.** No all-input collision detector or nonzero global annihilator was acquired from the specified large indices. Exact Frobenius gives a useful but different relation: S_(Nk)=S_(Qk) modulo P, not S_k. N, N-1, N+1 cannot themselves be global annihilators on the surviving strong-setup branch. Standard public-exponent cleaning can make all monomials in N,N-1,N+1 act as automorphisms of both local beta groups. This preserves the original collision support and every centering correction; it does not project onto the colliding nodes. One fixed actual prepared AP instance disproves the natural proposed scalar gcd identities at these indices. The useful additional quantitative observation is that each restricted family's local collision count is <P,Q, so an exact count has no characteristic wraparound. A fast such count is a sufficient target, not an acquired constructor or a new count-oracle principle.

## 1. Exact source, index cost, and allowed weights

Use the positive-C/centered-B convention from the frozen phase-contraction report. Let r be odd prime, H=r^2, M=r^4, s=1+rt, and

    1<=C_s<H, |B_s|<=M/2,
    2s+B_s=0 modulo H,
    s^2+B_s s+C_sN=0 modulo M.

For balanced P,Q<=2r^3, the safe common cap is |sigma|<=5r. Put

    K_s,c,sigma=C_sN+c^2+B_sc-Msigma,
    Z_s,c,sigma=beta^K,
    S_k=sum Z^k.

Delete the already screened public integer-K=0 leaf, if present. Its subtraction h0 from every S_k is exact, including for the large indices below. At the true covered leaf K=(P-1)(C_sQ-c^2) is nonzero and Z=1 modulo P. All integer exponents and source labels remain the actual ones.

For a supplied integer index k, first prepare alpha=beta^k ONCE. Then the paid evaluator becomes

    S_k=(sum_sigma alpha^(-Msigma))
        *sum_s alpha^(C_sN) sum_c alpha^(c^2)(alpha^B_s)^c.

This avoids charging the bit length of k separately at every row. If b=ceil(log_2 N) and ell(k) is its explicit binary length, a conservative bound is

    soft O(r b^2 + ell(k)*b) bits,

with soft O(rb) workspace, in addition to storing the index if needed. Polynomial-size N,N±1 and fixed/polylogarithmic powers are therefore inexpensive specified indices. Even a supplied soft-r-bit smooth exponent can be prepared in soft-r total work. That observation does not make its many distinct trace indices free, nor make smooth-order coverage new.

Separable supplied weights w_s v_c u_sigma retain the same fixed-k MPE. Polynomial weights in K of bounded/polylogarithmic degree can also be handled using a bounded/polylogarithmic number of derivative/weighted MPEs and weighted geometric sums. For example K=C_sN+c^2+B_sc-Msigma gives a constant number of such terms. These operations compute weighted additive traces. A collision indicator or an arbitrary leaf-dependent weight has not thereby been acquired.

## 2. What Frobenius at the large public indices actually says

Let d_P=ord_P(beta). For every actual integer K,

    Z^(Pk)=Z^k modulo P,
    Z^(Nk)=Z^(Qk) modulo P,

because Z is an element of F_P. Summing gives

    S_(Pk)=S_k modulo P,
    S_(Nk)=S_(Qk) modulo P.

Modulo Q the analogous identities exchange P,Q. More generally S_(N^a k)=S_(Q^a k) modulo P. Thus the large public index replaces its P factor by the unknown OTHER prime's action; it is not the local identity map. The known C_sN term and cubic B_s constraint do not change this calculation.

Likewise

    S_(N-1) modulo P = sum Z^(Q-1),
    S_(N+1) modulo P = sum Z^(Q+1),
    S_(Nk)-S_k^N modulo P = S_(Qk)-S_k^Q.

The last expression is a Frobenius defect at Q evaluated in characteristic P, with no reason to vanish. At a singleton family it is identically zero modulo N regardless of whether that leaf collides: Z^(Nk)-(Z^k)^N=0. Consequently a saturated leaf of this nonlinear defect is NOT a beta-annihilator certificate and cannot invoke the inherited decoder.

There is a second exact check for the simplest candidate indices. Let D=ord_N(beta), T=P+Q. Since D divides phi(N)=N+1-T, a global annihilator N+a would imply

    D divides T+a-1.

In the balanced window, 0<T+a-1<=4r^3 for a=-1,0,1, whereas D>256r^4. Therefore beta^(N-1), beta^N, beta^(N+1) are all unequal to 1 modulo N on this branch. A proper gcd at one of these exponents can still factor N, but a guaranteed global short annihilator at these three indices is excluded by the setup's own margin.

## 3. Public cleaning and exact preservation of the AP carry

Apply the inherited exponent-cleaning mechanism to, for example,

    A=N(N^2-1), e=A^L, L=ceil(log_2 N).

This is a public O(b^2)-bit exponent. Because every local beta-order is <N, powering by e removes its entire primary part at every prime dividing A. The new local orders are divisors of the old coprime odd orders. The universal first-nonunit detector returns a proper factor, an exact common order, or certifies both new orders>B=16r^2. The common-order case is 1 by coprimality, giving the explicit short global annihilator e of the original beta and invoking the inherited extractor. On the retained branch both orders>B and are coprime to A. The usual additional q2=alpha^(r^2) detector costs soft r and preserves the stronger seed interface; it either factors or certifies its >B orders. Thus this is a paid application of inherited setup/cleaning, not a new source algorithm.

Every index k=N^a(N-1)^b(N+1)^c, for nonnegative integer a,b,c, is now coprime to both retained local orders. Consequently

    Z^k=1 modulo P iff Z=1 modulo P,

and likewise modulo Q. Large such indices preserve the original local collision set exactly. The linear defect S_(Nk)-S_k is a sum of leaf defects Z^k(Z^(k(N-1))-1). On this cleaned branch each SINGLE leaf defect vanishes exactly at a collision. However, their full-family sum is not forced to vanish by the covered leaf, and nonunit sums do not have the multiplicative parent-to-child localization implication. This route therefore still needs a proved aggregate identity, even though its individual leaves have the right support.

This also gives an exact source-specific check on modular coefficient manipulations. The AP cubic generator only specifies B modulo M; its actual lift is B=P3-Mh. Replacing the phase by its cubic lift changes a node by q^(h c), q=beta^M. At index k the correction is q^(k h c). If k is coprime to the local beta-order, this correction is 1 exactly when q^(h c) was already 1. Such large indices cannot erase an unaccounted centering carry. Likewise the identity

    C_sN+c^2+B_sc=(c+B_s/2)^2 modulo M

is an auxiliary-modulus identity; it does not determine exponents modulo the hidden d_P. Translating it into the scalar group still requires its full integer q-phase. No carry-killing consequence of N or its powers was found.

## 4. A single reproducible prepared-source diagnostic

The adjacent `check_frobenius_traces.py` and `frobenius-check.json` reproduce one fixed exact test. There is no input search, native success campaign, or inference of a runtime theorem. Public construction of all rows and traces uses only r,N,beta; the listed P,Q are used to verify the promises and true witnesses.

Take

    r=37, P=50147, Q=50459, N=2530367473, beta=4,
    d_P=25073, d_Q=25229, B=21904,
    D=632566717 >256r^4=479785216.

P,Q and d_P,d_Q are prime, P=2d_P+1, Q=2d_Q+1. Thus beta has exactly the claimed odd coprime local orders. N<=r^6, P,Q<=r^3, and gcd(D,N(N^2-1))=1, so the N/N±1 cleaning condition already holds. The trace uses every AP row, every 1<=c<r, and sigma=-5r,...,5r. Its leaf count is 494172, and its public-zero cleanup is empty by the positive-K bound.

| k | exact S_k modulo N |
|---|---:|
| 1 | 38868229 |
| N-1 | 2038247167 |
| N | 899554513 |
| N+1 | 1725649574 |
| (N-1)^2 | 98273555 |
| N^2 | 1127680563 |
| N^2-1 | 458980220 |

Every listed S_k and S_k-494172 has gcd 1 with N. So does beta^k-1 for every listed k. The natural aggregate defects also give units:

| expression | exact residue | gcd with N |
|---|---:|---:|
| S_N-S_1 | 860686284 | 1 |
| S_N-S_1^N | 1622092980 | 1 |
| S_(N-1)-S_0 | 2037752995 | 1 |
| S_(N+1)-S_2 | 1211663183 | 1 |

Nonetheless the actual own witnesses are present and nonzero: (s,c,sigma)=(593,34,34) has K=344065145128 and is a collision modulo P; (593,4,4) has K=344122349008 and is a collision modulo Q. The script independently verifies the forced relations S_P=S_1 modulo P, S_Q=S_1 modulo Q, and the two correct S_N cross-prime identities. This falsifies these particular proposed unconditional identities on the actual structured source, not all possible weighted or adaptive uses of traces.

## 5. Exact local counts: useful size refinement, still an unacquired target

Count/character-deficit locator equivalences are inherited. In particular the earlier twist-character audit already studies the exact positive deficit sum(1-Jacobi(h,N)^2) on original useful scalar differences. This section does not claim that replacing a product oracle by a count oracle is new progress. The refinement specific to this short AP family is a uniform bound preventing reduction modulo a hidden characteristic from losing a positive count.

The inherited setup implies ord_P(q),ord_Q(q)>B for q=beta^(r^4). Indeed q2=beta^(r^2) has order>B; if r^2 divided a local beta-order d, then d/r^2<r^2/16 because the other hidden prime exceeds B and N<=r^6, contradicting that q2 certificate. Thus v_r(d)<=1, and q,q2 have equal local orders. For dyadic m, equality follows immediately from the local orders being odd.

The common AP cap has length <=10r+1<B. For each fixed (s,c) there is at most one sigma giving a local collision. Hence, for every restricted Cartesian rectangle after public-zero deletion,

    0<=mu_P<=|R|*|C|<=r(r-1)<P,
    0<=mu_Q<=r(r-1)<Q.

A sufficient target would be a soft-r routine returning a residue U with

    U=mu_P modulo P, U=mu_Q modulo Q.

Then gcd(U,N)=N means neither field has a hit; a proper gcd factors N; gcd(U,N)=1 means both fields have hits. Binary restriction of rows, common multipliers, and the common sigma interval either finds a proper gcd or preserves a hit in both fields until a global leaf is reached. The clean leaf has a nonzero short K, so the inherited extractor applies. Counts cannot wrap to zero because of the displayed bound. This is a precise sufficient alternative to full-product acquisition, not an acquired oracle.

For the separate unbalanced extension with O(log N) size windows, this count argument must be applied ONE WINDOW AT A TIME. Its total row count is soft r, but summing all windows can give an r^2 log N count bound which need not be below the smallest hidden prime. O(log N) separate window queries retain the allowed budget and each window's mu<=r(r-1)<P,Q bound. Trace acquisition may still aggregate all windows; the characteristic-wrap claim does not follow for their aggregate count.

For completeness, a pointwise subgroup projector gives the exact desired count identity:

    (1/L) sum_(j=0)^(L-1) S_j = mu_P modulo P

whenever L is a multiple of d_P and P does not divide L; similarly at Q. But a supplied local order d_P immediately factors via gcd(beta^d_P-1,N), since the other nontrivial order is coprime to it. A supplied common short order-multiple already provides the global annihilator accepted by the decoder. Neither missing order information nor its long trace average has been acquired from N,N±1. The public universal multiple lcm(1,...,ceil(2r^3)) has Theta(r^3) explicit bits in this balanced window; its ordinary construction/powering is outside the soft-r ledger. The soft-r-bit small-smooth exponent is inherited and does not cover the remaining rough orders.

Averaging only along large-index powers N^j does not itself give this projector. Modulo P it averages Z^(Q^j). Even if d_P is prime and Q generates its nonzero residue group, the relevant orbit length is d_P-1 and the nonidentity sum is -1; computing that orbit average, or proving a different short identity on this actual source, is additional work. No short orbit-period or weighted projector follows from the AP cubic coefficient constraint. This identifies the precise arithmetic/aggregate input not supplied by the large-index observations, rather than an algorithmic lower bound.

## 6. Frobenius literature and scope

The original AKS manuscript, Lemma 3.1(2), printed pp.2-3, supplies the polynomial Frobenius identity used above; its algorithm's output is a primality decision. It does not assert a factor-producing transformation from one scalar power trace. [Agrawal-Kayal-Saxena, primary manuscript](https://cse.iitk.ac.in/users/manindra/algebra/primality_original.pdf).

Grantham's primary treatment, Sections 1-3 (printed pp.1-7), develops finite-field/Frobenius recurrence tests and their pseudoprimes. It supports using such relations as compositeness tests under their given polynomial hypotheses; it supplies no all-input factor locator for the present AP collision family. No claim about these exact structured traces is inferred from generic pseudoprime examples. [Grantham, Frobenius Pseudoprimes](https://arxiv.org/pdf/1903.06820).

The scalar identities and count bound above are proved directly for the actual source. No external analytic hypothesis, unverified factor oracle, whole-family query acquisition, or new factoring exponent is claimed. The next constructive target is a source-specific weighted identity that acquires the restricted local counts (or another sufficient locator) with total soft-r work; cheap access to the specified large trace indices alone has not supplied it.
