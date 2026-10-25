# Root review: uniform short clocks and the remaining acquisition

23 October 2026. This is a mathematical review, not a Lean verification or
an improved factoring exponent. The new application combines the inherited
exact quotient-Gauss constructor with the elementary small-multiple cover.

## Independent geometry calculation

Let r be an odd prime of size Theta(N^(1/6)), N=PQ<=r^6, with P<Q and
both factors greater than 16r^2 after the paid prefix. Put H=r^2.
Enumerate P0=16r^2*2^j<=floor(sqrt(N)); their intervals
[P0,2P0) cover every surviving smaller factor. Set X=2P0/r, an integer.
For each s=1+rt, 0<=t<r, use the explicit quotient lattice

    (u,a) in Z^2, u+(s^2/H mod N)*a=0 mod N,
    D=s^2+H^2 X^2, F(u,a)=u^2+X^2 D a^2.

Exact Gauss reduction and the inherited nearest-line lift Hd-sb=u give

    F(u,a)<=2N X sqrt(D),
    d^2+X^2 b^2+X^4 a^2
       <=X^2 F(u,a)/D+D/4
       <=(2N/H+H^2/2)X^2
       <=(5/2)H^2 X^2.

The middle inequality uses X>=1 and 0<s<H. This calculation does not
require the old H^3<=N or HX<=2sqrt(N) assumptions. Those assumptions
served different purposes in the earlier supplied-residue application.
Here |a|<=sqrt(5/2)H/X<r/20; a=0 is allowed explicitly.

For the true P in this window, take c=P^(-1) mod r in [1,r). Then cP
mod H is one of the catalog rows and h=(cP-s)/H is an integer in (0,X).
The lattice congruence implies P divides g(h), where g(Y)=aY^2+bY+d.
Writing g(h)=P sigma, Cauchy--Schwarz gives

    |sigma|<=sqrt(15/2)HX/P<=sqrt(30)r<6r.

Thus one common signed interval [-6r,6r] suffices for every surviving
factor size. There are r rows per O(log N) public windows, acquired in
soft O(r) total bit work. This is a uniform covering family, not a
finite experimental coverage statement.

## Coefficients, trivial leaves and recovery

Set B=Hb-2as and CN=Hu+s^2a. The latter is divisible by N by construction.
Then

    G(Z)=aZ^2+BZ+CN
        =a(Z-s)^2+Hb(Z-s)+H^2d,
    H^2 sigma=ac^2P+Bc+CQ,
    E=ac^2+Bc+CN,
    E-H^2 sigma=(P-1)(CQ-ac^2).

C cannot be zero: it would force H|a, then a=0 and u=0, contrary to the
nonzero Gauss vector. If a=0, exact shortest-vector selection forces
u=+N or -N. Consequently b is a unit modulo r. If a is nonzero, a is a
unit modulo r because |a|<r. In the quadratic case, the valuation of
a(c-s)^2 is uniquely smallest whenever v_r(c-s)<2. In the linear case,
H^2|Hb(c-s) forces H|(c-s). Therefore every public integer-zero exponent
K=E-H^2 sigma has c=s mod H in either branch.

Within this catalog and multiplier interval only s=c=1 is possible.
There is at most one candidate per window, with sigma=d. Exact testing
of the multiplier mask and interval removes precisely those leaves.
The true witness is never removed: if a is nonzero, Q cannot divide
ac^2 since 0<|a|,c<r<Q; if a=0, C is nonzero. Hence CQ-ac^2 is nonzero.
Every remaining saturated leaf supplies a nonzero O(log N)-bit exponent
annihilating its prepared base, eligible for the inherited unconditional
short-annihilator decoder. No new global factor-sum premise is needed.

## Shared trace after changing the leading coefficient

All nonzero coefficients a are small. The inherited product-tree smooth
projection, collapse recovery and outside-power construction supply one
common beta and roots rho_s with rho_s^a=beta. Include r in the projection
product. On the continuing branch every rho_s has the same large odd
local orders, coprime to r and all selected nonzero a. Set rho_s=beta
for the linear rows. This uses the existing factoring-or-roots routine;
no inversion of a modulo N is interpreted as an inverse group exponent.

For the nonlinear rows the exact nodes are

    Z_s,c,sigma=rho_s^(CN+Bc-H^2 sigma)*beta^(c^2).

They retain precisely the local zero support of the Gauss leaves formed
with the purified common beta, because exponentiation by a is injective
in both projected cyclic groups. This is not a claim that purification
preserves every pre-purification hit of beta_in.
For a specified k use

    P_k(T)=sum_(c in common mask) beta^(k c^2)T^c,
    A_s,k=sum_(sigma in the actual interval) rho_s^(-k H^2 sigma),
    S_k=sum_s A_s,k*rho_s^(kCN)*P_k(rho_s^(kB)).

One monic multipoint evaluation handles all nonlinear rows and windows.
The linear rows use the second polynomial sum_c T^c with the same mask.
Row-dependent geometric weights A_s,k are computed division-free in
polylogarithmic work per row. Subtract the public-zero count. A specified
k of O(log N) bits therefore costs soft O(r(log N)^2) bits, with soft
O(r log N) storage. For h indices the acquired bound remains soft O(rh),
including suppressed bit factors. No simultaneity across k is inferred.

## Audit of the separate trace-index continuation

The positive-C, coefficient-one AP row algebra in trace-index.md is a
different family from the Gauss family above. Its linear W and dense V
must not be asserted for the new variable-a rows. The separation argument
is valid: gcd(P-1,N)=1 for the smaller P, so a gap in beta^(rN u) cannot
vanish modulo P under the large-order bound. Any nonunit gap factors N.

The exact quadratic product doubling identity changes V to beta^(2n)V.
A unital endomorphism of the split rank-r algebra would create a cycle
of at most r coordinates and force beta^(2n ell)=1 modulo P, impossible
for 1<=n<=r. This rules out that particular state-reuse mechanism only.

The boundary difference of two adjacent multiplier windows is acquired
for h traces in soft O(r+h). It is a raw-product identity; public-zero
corrections are applied separately. Common local zeros disappear in the
formal quotient, so its value at 1 cannot replace either collision query.
The universal Newton-support count describes a chosen expanded
representation, not a lower bound on all algorithms or specialized inputs.

## Scope and next constructive target

The advance is an all-input extension of the short-index geometry and
fixed-index additive trace. The rank-two Gauss engine, smooth projection,
root acquisition, monic arithmetic and decoder are inherited and credited.
This extension neither acquires F(1) nor improves the guaranteed factoring
exponent. A useful next theorem must acquire a multiplicative product, an
equivalent restricted collision count, or enough informative contracted
traces in soft O(r), with a proof of local detection and localization.

For the count formulation, retain one size window per query: at most one
sigma can hit for each row/multiplier pair because the seed order exceeds
16r^2. Then the local count is at most r(r-1)<P,Q, so it cannot vanish by
characteristic cancellation. Summing counts across all size windows is
not automatically below P; O(log N) separate window queries preserve the
desired budget. The count interface is sufficient but unacquired, and
its character-deficit predecessor is already part of the earlier work.
