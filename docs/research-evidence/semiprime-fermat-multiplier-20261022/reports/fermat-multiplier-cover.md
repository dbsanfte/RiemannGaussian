# Fermat-quotient multiplier cover: finite construction and factoring consumer

2026-10-22. No repository edits. Let r be an odd auxiliary prime with N^(1/6)<=r=O(N^(1/6)), H=r^2, and N=PQ with P<=Q. If r divides N, its gcd supplies a factor. The COVER below is uniform in every unit integer P. The explicit small-quotient consumers below have their stated balanced-factor condition; they do not prove a sixth-rate factorizer.

## 1. Primary image theorem and an explicit finite bound

Ostafe–Shparlinski, *Pseudorandomness and Dynamics of Fermat Quotients*, SIAM J Discrete Math25(2011),50–71, [DOI](https://doi.org/10.1137/100798466), [primary arXiv PDF](https://arxiv.org/pdf/1001.1504). The arXiv v2 labels the result **Theorem10**, section3.4, pp12–14; the published numbering is3.8.

For q_r(x)=((x^(r-1)-1)/r) modr on units, its image on 0<=x<r has size at least (1+o(1))r/(logr)^2. The artificial q_r(0)=0 adds nothing because q_r(1)=0. Thus this holds for Q={q_r(c):1<=c<r}. It is uniform over primes r, without an average-case qualification.

The primary proof gives the following stronger usable FINITE statement. Put pi=pi(r-1). For each a, let n_a count primes c<r with q_r(c)=a. Their collision second moment satisfies

`sum_a n_a^2 <= pi+(r-2)`.

Indeed equal quotients imply c/d belongs to the Teichmuller kernel in (Z/r^2Z)^*, which has exactly r-1 elements. Its identity contributes pi ordered pairs. Each of its r-2 nonidentity elements contributes at most one ordered pair: two such pairs imply c1*d2=c2*d1 as integers, since both products are <r^2, and primality forces the pairs equal. Cauchy therefore yields, for r>=3,

`|Q| >= max(1, ceil(pi(r-1)^2/(pi(r-1)+r-2)))`.                  (1)

This finite lower bound needs no ineffective o(1) threshold. PNT applied to (1) gives the printed asymptotic. For r=2, Q={0} directly; the displayed fraction is0/0 and must be replaced by that separate case. The catalog construction works for r=2 with A=F_2; signed-representative identities below are stated for odd r.

The source identities used are

`q_r(xy)=q_r(x)+q_r(y) modr`,

`q_r(u+kr)=q_r(u)-k/u modr` for r not dividing u.             (2)

Repeated squaring acquires the whole q_r(c) table, image bitvector, and a representative rep[q]<r for every q in Q in soft O(r) bit work. One may use all multipliers; restricting to prime representatives also suffices by the proof of (1).

## 2. Exact greedy cover and bit complexity

Write M=|Q| and U=F_r initially. For every a define

`score(a)=#{q in Q: a-q in U}`.

Their sum is M|U|. Choose the least maximizer a, append it to A, and remove a-Q from U. Each round leaves at most (1-M/r)|U| points. Thus

`|U_after_k| <= r*exp(-kM/r)`;

For an entirely integer finite bound, let d_r be the positive integer lower bound in(1), with d_2=1, let L=ceil(r/d_r), and B=bit_length(r). Then

`|A| <= L*(B+1)`.                                          (3a)

Indeed every L-round block at least halves the residual: for 0<x=d_r/r<1, Bernoulli gives (1-x)^(-L)>=(1+x)^L>=1+L*x>=2; the case x=1 ends immediately. After B+1 blocks fewer than one point remains. This proves(3a) without floating logarithms or an ineffective threshold. Equations(1) and PNT give the asymptotic |A|=O(log^3r). The algorithm stops at U empty and its result is `A-Q=F_r`.

Every score is the cyclic convolution `(1_U*1_Q)(a)`. Here is an exact deterministic bit implementation: pack either bitvector as sum_i v_i*B^i, where B=2^b>r and b=ceil(log2(r+1)). Their ordinary integer product has coefficients <=r, so carries do not mix coefficients. Fold coefficient a+r into coefficient a to obtain the cyclic convolution. The packed integers have O(rlogr) bits; deterministic fast integer multiplication, extraction, scanning, and repacking cost soft O(r) bits per round. O(log^3r) rounds still cost soft O(r). Explicit removal costs O(M) indices per round, totaling O(rlogr). Working arrays and witness labels use soft O(r) bits.

When t is first removed, record its chosen witness

`t=a(t)-q_r(c(t))`, `c(t)=rep[a(t)-t]`.                      (3)

This acquires r witness records in the same budget. Let T_a={t:a(t)=a}. The T_a partition F_r, and c(t) is distinct within each T_a because a-t is distinct.

## 3. Small Teichmuller catalog and uniform coverage

For a in A and u=1,...,r-1, define

`s_a(u)=u+r*[u*(q_r(u)-a) modr]`, in [1,H-1].                (4)

Equation(2) gives q_r(s_a(u))=a. With tau(u)=u+r*[u*q_r(u) modr], equivalently s_a(u)=tau(u)*(1-r*a) modH. Thus S consists of exactly the disjoint q_r-fibers indexed by A:

`|S|=(r-1)|A|=soft O(r)`.

All entries and labels(a,u) are acquired in soft O(r) bit work.

For EVERY unit P, take t=q_r(P) and the recorded(a(t),c(t)). Then q_r(c(t)P)=a(t), so `c(t)P modH` belongs to S. This establishes a genuine all-input multiple coverage theorem with c<r, including exact witness functions. It does not identify the true t from N or from one catalog row.

## 4. Strongest simple balanced consumer: a linear polynomial

Assume the balanced branch P,Q<=2r^3; more generally the same estimates hold with fixed comparable-size constants. For every s in S compute

`b_s=center(-N*s^-1 modH)`,

`d_s=(N+s*b_s)/H`,

`g_s(x)=b_s*x+d_s`.                                      (5)

The numerator defining d_s is divisible by H, and |b_s|<=H/2. All row data costs soft O(r) total. If the true multiplier is c=c(t), s=cP modH and h=(cP-s)/H, then

`H*g_s(h)=N+b_s*cP=P*(Q+b_s*c)`.

Since gcd(H,P)=1, `g_s(h)=sigma*P` for an integer sigma, and

`H*sigma=Q+b_s*c`,

`|sigma| <= Q/H+(r-1)/2 < 3r` on this balanced branch.       (6)

This obtains the desired O(r) quotient interval by elementary arithmetic, without a new Gauss/LLL or successive-minima assertion. The bound in (6) is also exact for unbalanced factors; it becomes larger when Q is larger. Uniform coverage remains valid there, but this balanced radius bound must not be asserted for all sizes.

For any unit beta moduloN, Fermat now supplies

`beta^(N+b_s*c)=beta^(H*sigma) modP`.                      (7)

The giant exponent is linear in c. If the right pair(c,sigma) is found,

`Q=H*sigma-b_s*c`,                                        (8)

so a gcd/divisibility check recovers the factor directly. There is no quadratic root ambiguity.

The b_s values form another small catalog: for odd r, q_r(-1)=0, and b_s=-N/s modH implies

`q_r(b_s)=q_r(N)-q_r(s) modr`.                             (9)

Thus b_s lies in the |A| fibers q_r(N)-A. Signed centering does not alter q_r for odd r. Neither b_s nor its row is zero modulo r, so there is no zero-coefficient exception. The unresolved target family is therefore geometric in c with bases beta^(b_s) from a second structured Teichmuller catalog.

## 5. Explicit quadratic balanced refinement, also verified

For comparison, one may set a_s=1 for every row. Define

`C_s=center(s^2*N^-1 modH)`,

`b_s=center(((s^2-C_s*N)/H)*s^-1 modH)`,

`d_s=(C_s*N+H*b_s*s-s^2)/H^2`,

`g_s(x)=x^2+b_s*x+d_s`.

Then the exact cleared identity is

`H^2*g_s((D-s)/H)=D^2+(H*b_s-2s)*D+C_s*N`.                (10)

Bounds |C_s|,|b_s|<=H/2 and |d_s|<=N/(2H)+H/2+1 are immediate. At h=(cP-s)/H, 0<=h<=P/r, so balanced factors give |g_s(h)|=O(r^4). Since P divides g_s(h), sigma=g_s(h)/P is an integer of size O(r), and

`H^2*sigma=c^2*P+(H*b_s-2s)*c+C_s*Q`.

Consequently

`E_{s,c}=c^2+(H*b_s-2s)*c+C_s*N`,

`beta^(E_{s,c})=beta^(H^2*sigma) modP`.                    (11)

Also q_r(C_s)=2q_r(s)-q_r(N), so C_s lies in another |A|-fiber catalog. This is real structure, but the simpler linear relation(5)–(8) has the same balanced quotient width and avoids the chirp term entirely.

In a general acquired quadratic F_s(D)=a_sD^2+B_sD+C_sN, the exact equation is H^2sigma=a_sc^2P+B_sc+C_sQ. Thus the c-dependent Fermat exponent a_sc^2+B_sc+C_sN cannot be replaced by its value at c=1.

## 6. Witness labels restore r(r-1) pairs

The maximal immediate pruning supplied by(3) is: row s_a(u) uses only multipliers

`C_a={c(t):t in T_a}`.

Yet sum_a |C_a|=sum_a |T_a|=r. Since every a has r-1 catalog rows, the total admissible row/multiplier labels is EXACTLY

`sum_a (r-1)*|C_a| = r*(r-1)`.                            (12)

This is a direct accounting statement, not a lower bound on all shared algorithms. Explicitly acquiring the giants in(7), even with this pruning, takes soft O(r^2) operations. Matching them against O(r) baby values has the same dominant list cost, N^(1/3+o(1)) for r comparable to N^(1/6).

There is an exact bijection behind(12). Given any unit x modH, t=q_r(x) fixes c(t), and s=c(t)x modH lands in S. Conversely, given row s_a(u) and t in T_a, x=s/c(t) modH is unique and has q_r(x)=t. Thus labeled catalog points represent ALL H-r unit residues moduloH. The catalog compresses the unlabeled rows; explicitly restoring their missing multipliers expands back to every residue.

The known q_r(N)=q_r(P)+q_r(Q) couples the second factor to q_r(N)-t but leaves r possible t. Applying the cover to both factors gives compatible products automatically, rather than a selector for t. No c-selection algorithm within soft r was obtained from these labels.

## 7. Exact remaining consumer and order condition

Using the linear refinement, the unpaid simultaneous query is

`beta^(N+b_s*c)` versus `beta^(H*sigma)`,

for s=s_a(u), c in C_a, |sigma|<=O(r), with soft O(r) TOTAL work and same-label recovery through(8). For one fixed row the selected c-values form a SUBSET of a geometric progression: C_a is an arbitrary subset of [1,r), not necessarily an interval or the whole interval. Across rows the bases beta^(b_s) vary; a compact specification is not an acquired O(r)-entry target list. I did not derive a shared product/evaluation/collision procedure at that cost.

The INHERITED strong setup with m=r already supplies the necessary base and q=beta^(r^2) unit promises. Its global-order decoder is sufficient for every globally colliding linear leaf; no new local-order premise is needed. Precisely, let D=ord_N(beta)>256r^4, with D dividing phi(N). Any global equality in the linear family gives

`D | N+b_s*c-H*sigma`.

Subtracting phi(N)=N+1-(P+Q) gives

`D | P+Q-1+b_s*c-H*sigma`.

For P,Q<=2r^3, c<r, |b_s|<=r^2/2, and |sigma|<=3r, the latter integer has absolute value <8r^3<D. Hence it is zero:

`P+Q=1+H*sigma-b_s*c`.

Solve the factor-sum quadratic and verify. This applies to ANY globally colliding admissible pair, not only the private true witness. Proper local gcd leaves already return a factor. Therefore the product/gcd localization pipeline completes conditional on acquisition of the still-unpaid aggregate query. This is an application of the existing bounded global-leaf recovery in [uniform-setup-and-query-interface.md, section8](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md), not a newly proved recovery mechanism. The setup also already certifies the short q-factorial/interval units. This note does not infer additional target-to-target unit promises for the expanded family.

Optional alternative-base accounting: if a different beta is used instead of that inherited setup, `ord_P(beta^(r^2))=ord_P(beta)/gcd(ord_P(beta),r^2)`; for the quadratic version the corresponding power is r^4. Such a route must separately pay its required order promises. These formulas are not extra assumptions on the inherited linear consumer.

## 8. Validation scope

The quotient-lift signs, greedy witness coverage, and label bijection were exhaustively checked for r=3,5,7,11,13,17,19,23,29,31 over every unit residue modulo r^2. These are algebra/implementation sanity checks; the primary theorem and proofs above establish the uniform claims. They are not a native factoring coverage test or a proof of a new factoring exponent.

The established advance is the finite, deterministic soft-r whole catalog covering a multiple of EVERY factor, plus explicit balanced linear and quadratic O(r)-quotient consumers. The remaining row/multiplier processing in(12) is unpaid. No generalized impossibility or algorithmic lower bound is claimed.
