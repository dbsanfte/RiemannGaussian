# Explicit short-clock coefficient catalog

23 October 2026. Root proof, not a new collision detector. This gives a
uniform, explicitly enumerable source with more structure than the previous
per-residue Gauss construction. It does not prove a sixth-rate factorizer.

## Setup and algorithm

Use the inherited paid setup with an odd prime r, N=P Q<=r^6,
16r^2<P<Q, and r=Theta(N^(1/6)). Write H=r^2 and M=H^2. For each public
window P0=16H*2^j<=sqrt(N), put

    A=floor(sqrt(N)/P0), T=floor(H/(A+1)).

Compute A by integer square root. We have 1<=A<=r/16<r. Enumerate

    1<=a<=A, 0<|C|<=T, CN=a (mod r).                    (1)

For each a, these C are one clipped arithmetic progression with stride r;
finding its endpoints does not require scanning the ambient rectangle.
There are

    J<=A(2T/r+1)<2r+A<3r                              (2)

descriptors. Also |aC|<=A floor(H/(A+1))<H.

Every pair determines exactly one s=1+r t, 0<=t<r, with CN=a s^2 mod H:

    t=((CN-a)/r)*(2a)^(-1) (mod r).                     (3)

Here a and C are units modulo r. Choose B as the centered representative
modulo M of

    -a s-CN*s^(-1).                                    (4)

All inverses in (3)-(4) are modulo explicitly known prime powers. Then

    B=-2as (mod H), a s^2+B s+CN=0 (mod M), |B|<=M/2.  (5)

The integral polynomial

    g(x)=[a(Hx+s)^2+B(Hx+s)+CN]/M

therefore has degree two, leading coefficient a, and O(log N)-bit
integer coefficients. These formulas construct the whole catalog in
soft O(r) bit work over all O(log N) windows. The canonical signed B is
part of the data; changing its lift changes the witness seed.

## Uniform coverage and the seed bound

Choose the window with P0<=P<2P0. Define the proof-only c in [1,r-1]
by cP=1 mod r, and s=cP mod H in [1,H-1]. Then s=1 mod r. Let

    alpha=s^2*N^(-1) (mod H).

The A+1 points j alpha mod H, 0<=j<=A, are distinct. Among their A+1
cyclic gaps, one has length at most floor(H/(A+1))=T. The difference
of its two labels has nonzero absolute value a<=A. Orienting the signed
gap consistently gives 0<|C|<=T with C=a alpha mod H. Consequently
CN=a s^2 mod H; its reduction modulo r is (1), and the catalog recovers
this very s in (3). This proof does not require the algorithm to know P,
c, or alpha.

Let h=(cP-s)/H>=0. Equation (5) shows M divides G(cP), where
G(Z)=aZ^2+BZ+CN. Also

    G(cP)=P[a c^2P+B c+CQ], gcd(P,M)=1.

Thus the following seed is an integer:

    M sigma=a c^2P+B c+CQ, g(h)=P sigma.                 (6)

Its three contributions satisfy

    a c^2P/M <2A P0/r^2<=2sqrt(N)/r^2<=2r,
    |B|c/M <r/2,
    |C|Q/M <=N/[r^2(A+1)P0]<sqrt(N)/r^2<=r.

The strict inequality in the last line uses (A+1)P0>sqrt(N). Hence
|sigma|<7r/2. A common interval [-4r,4r] is safe for every window.

## Collision and recovery interface

For each descriptor form

    K(c,sigma)=a c^2+B c+CN-M sigma.

At the covered leaf, (6) gives the exact identity

    K=(P-1)(CQ-a c^2).                                  (7)

This integer is nonzero: otherwise the prime Q divides a c^2 although
0<a,c<r<Q. Its bit length is O(log N). The inherited prepared-base
and legal-coefficient-root procedure includes r in its smooth projection
and supplies rho_a^a=beta with the same large odd local orders, coprime
to r and to every leading coefficient in the catalog,
so rho_a^K=1 mod P. Any acquired
nonzero global leaf has the inherited unconditional short-annihilator
decoder. These are inherited consumers, not new algorithms in this note.

A public K=0 must be removed before treating a saturated leaf as a useful
annihilator. Taylor's exact identity is

    G(c)=G(s)+(2as+B)(c-s)+a(c-s)^2,

with M|G(s) and H|(2as+B). If the r-adic valuation of c-s were 0 or 1,
the last term would have strictly smaller valuation than the other two
terms, namely 0 or 2. Since a is a unit modulo r, M|G(c) therefore
implies H|(c-s). The ranges c in [1,r-1] and s in [1,H-1] force
c=s, hence c=s=1. For each descriptor at most one sigma is then possible.
There can be MANY such descriptors in this catalog, unlike the previous
one-row-per-s family. Scanning all O(r) descriptors and deleting the
individual public-zero leaves remains soft O(r). It does not delete the
true leaf because of (7).

Alternatively, the public large-input guard N>5r^5 excludes every K=0
in the safe seed interval: |a c^2+B c-M sigma|<5r^5, while |CN|>=N.
For a fixed upper bound r<=4 N^(1/6), the complementary range has
N<=(5120)^6. This is a finite-range fallback, not an exponent advance.

## Exact ratio information and what remains to acquire

At the true witness, reduce (6) modulo c. Since both M and Q are units
modulo c,

    gcd(c,sigma)=gcd(c,C),
    denominator(sigma/c)=c/gcd(c,C).                     (8)

Changing B to B+kM adds k to sigma/c and leaves this denominator fixed.
Thus merely recentering B cannot put every witness into a small menu of
rational values. This statement alone is not a lower bound on a new
N-dependent selector.

A supplied small common menu R of reduced fractions u/v is useful:
solve v g(h)-u(Hh+s)=0 for every row/menu entry, and test gcd(N,Hh+s)
at each integer root in its window. C!=0 ensures that no tested
polynomial is identically zero. At the covered root, Hh+s=cP<N, so
the gcd is proper. This costs soft O(r*|R|), but no all-input small
menu has been constructed. In particular the zero-ratio case is a
restricted consumer, not a universal acquisition theorem.

For one specified exponent k, the full additive node trace still has
the inherited monic multipoint evaluator after sharing rho_a among
rows with the same a. This source organization does not by itself
compute a product, a local collision count, or a factor.

For one window, after local order>16r^2 preparation, each row/multiplier
has at most one seed hit, since the seed interval has length 8r+1 and
M is coprime to the local order. Consequently the local labeled hit
count is at most J(r-1)<3r^2<P,Q. This validates count recovery IF the
count is acquired; it does not acquire it.

The main open operation is the whole structured-family collision query
in soft O(r), including every row, multiplier and seed. A proof of
coverage, additional traces, or the supplied-menu consumer does not close
that acquisition gap.
