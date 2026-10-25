# Uniform short collision clocks and aggregate traces

23 October 2026. The short-index construction now covers **every surviving
semiprime, including unbalanced factors**, and one specified power trace
of this entire family can be acquired in soft O(N^(1/6)) bit work. This
extends the preceding balanced construction. It does **not** acquire a
collision detector or improve the guaranteed factoring exponent.

The [complete construction](reports/unbalanced-geometry.md) combines the
existing quotient-Gauss lattice method with the elementary AP
small-multiple cover. Its proof is reviewed independently in
[geometry review](reviews/geometry-review.md) and
[root review](reviews/root-review.md). The exact Gauss routine, small-factor
projection, simultaneous roots and saturated-leaf decoder are inherited;
they are not counted as new acquisitions.

## All-input short clocks

After the paid setup, let N=PQ<=r^6 with distinct primes P<Q, an odd
prime r=Theta(N^(1/6)), and P,Q>16r^2. Put H=r^2 and use the r rows
s=1+rt, 0<=t<r. Every P has a multiplier 1<=c<r for which cP=s mod H.
The multiplier is not supplied by the cover.

For each public size window P0=16r^2*2^j<=sqrt(N), set X=2P0/r.
The inherited exact quotient lattice and nearest lift produce integers
a,b,d with

    H^2 d-sH b+s^2 a=0 mod N,
    d^2+X^2 b^2+X^4 a^2 <= (5/2)H^2 X^2,
    |a|<r/20.

The old restriction excluding a=0 is unnecessary here. When a=0, the
shortest quotient vector has u=+N or -N, and b is a unit modulo H. This
controlled linear case is included throughout.

For the true window and multiple, h=(cP-s)/H lies in [0,X), and
g(h)=P sigma for g(Y)=aY^2+bY+d. Consequently

    |sigma| <= sqrt(30)r < 6r.

Thus O(log N) public windows, each with r descriptors, cover every
surviving input using one short signed interval [-6r,6r]. The proof does
not rely on successful examples or a hidden-factor choice of window.

Define B=Hb-2as and CN=H^2d-Hbs+as^2. Then C is a nonzero integer and

    H^2 sigma=ac^2P+Bc+CQ,
    E=ac^2+Bc+CN,
    E-H^2 sigma=(P-1)(CQ-ac^2).

The true exponent is nonzero: Q cannot divide ac^2 when a!=0 and
0<|a|,c<r<Q; the linear case uses C!=0. Every public integer-zero
candidate forces c=s, and the AP catalog allows only s=c=1, with
sigma=d. There is at most one candidate to screen per window. After
that screen, any global collision supplies a nonzero O(log N)-bit
annihilator, handled by the existing unconditional decoder.

## The information acquired cheaply

The small nonzero a coefficients admit the already paid simultaneous
root construction. It returns a factor or a purified common base beta
and row bases rho_v satisfying rho_v^(a_v)=beta, with the same large odd local
orders. Here v labels both row and size window. Include r in the
projection so that the seed clocks retain those orders. Linear rows
use rho_v=beta.

For quadratic rows, the actual nodes are

    Z_v,c,sigma = rho_v^(C_vN+B_vc-H^2 sigma) beta^(c^2).

For a specified k and common multiplier mask D, put

    P_k(T)=sum_(c in D) beta^(k c^2)T^c,
    A_v,k=sum_(sigma in I_v) rho_v^(-kH^2 sigma).

Then

    sum_(v,c,sigma) Z_v,c,sigma^k
      = sum_v A_v,k rho_v^(kC_vN) P_k(rho_v^(kB_v)).

One monic multipoint evaluation handles all these row/window points.
The linear rows use a second polynomial sum_(c in D)T^c. The actual
signed seed intervals enter division-free geometric sums; they may
differ between rows. Finally subtract the number of public-zero leaves.
No r-by-r multiplier table is constructed.

Including descriptor acquisition and legal roots, a specified k with
O(log N) bits costs soft O(r(log N)^2) bits and soft O(r log N) storage.
The O(log N) window factor is included in the soft notation. Arbitrary
descriptor restrictions and common multiplier masks remain available.
Native-tag masks are common multiplier masks since s=1 mod r.

The acquired statistic is a power sum of all the actual candidate
nodes. A covered leaf contributes 1 locally; other terms can cancel its
contribution. **One power sum is not a test for the presence of that
leaf.** Computing h<=r traces and the corresponding formal product prefix
still costs soft O(rh), not soft O(r) when h grows with r.

## What the parallel acquisition attempts establish

The separate coefficient-one AP family has an exact rank-r row-algebra
representation, with the canonical carries retained in a dense
interpolant V. The [trace-index investigation](reports/trace-index.md)
identifies the outstanding scalar norm of a quadratic-exponent product.
The natural doubling changes V to beta^(2n)V. The prepared local-order
bound proves that this shift cannot be realized by an endomorphism of
that same rank-r algebra. This excludes that particular reuse step,
not other norm algorithms. The AP-linear coordinate in this construction
is not assumed for the new variable-a Gauss rows.

An exact adjacent-window difference of h traces is acquired in
soft O(r+h). Its multiplicative form is a ratio of two overlapping
window products. Common local collisions cancel in that ratio, and a
value for one of the original window products remains missing. The
boundary identity therefore does not supply the detector.

The [large-index investigation](reports/frobenius-traces.md) tracks the
actual source under Frobenius. For example S_(Nk)=S_(Qk) mod P, with
P,Q exchanged modulo Q. It does not generally equal S_k. One exact
prepared-source diagnostic for the coefficient-one AP family rejects the
listed simple scalar-gcd proposals; its [script](implementation/check_frobenius_traces.py) and
[residues](implementation/frobenius-check.json) are retained for replay.
It is neither a coverage campaign nor an impossibility theorem for
weighted or adaptive traces.

## The next sufficient acquisition target

The direct target remains a restriction-stable soft-O(r) computation of
the cleaned product F(1), or another statistic that provably locates a
collision. An exact local collision count is one sufficient alternative.
For a single size window, each row/multiplier pair has at most one local
hit because the seed order exceeds the interval width. Hence

    0<=mu_P,mu_Q<=r(r-1)<P,Q.

A residue encoding these two counts modulo P and Q would distinguish
no hit, a one-sided hit and hits in both fields without characteristic
wraparound. Binary restrictions would then localize a useful leaf.
Run this count query separately for each size window: their combined
count is not automatically smaller than P. The O(log N) calls would
fit the budget. This sufficient interface and its character-deficit
antecedent are inherited; the per-window bound sharpens its application
here. **The required fast count has not been acquired.**

The positive result is whole-input geometry plus a whole-family
fixed-index additive computation. The main missing theorem is still
the conversion to a guaranteed detector within the same total budget.
Complete executable and Lean bit-complexity integration remains after
that mathematical acquisition step.

## Evidence and scope

[Integration review](reviews/integration-review.md) checks the boundaries
between the two families and the count/trace claims.
[Source pins](source-pins.json), [archive provenance](archive-provenance.json)
and [validation](validation.json) record the reviewed inputs and copies.
Prior frozen evidence is preserved. This checkpoint adds no Lean theorem,
broad build, commit or push. Integrity checks and finite identity checks
are not counted as a factorization-rate advance.
