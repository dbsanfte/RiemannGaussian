# Exact phase-kernel HNF and its small correlated scalar screen

26 October 2026. Scratch derivation from `common-character.md`,
`phase-index.md`, and the actual Gauss Cartesian input. No tests or
repository edits. The new paid operation here is a whole-colour
kernel-generator screen with only O(log k) distinct q-starts. It is
not by itself a complete cover. Section 6 COMPLETES a uniform cover
using O(sqrt k) multiples and an initialized longer clock, at soft
O(k+N^(1/4)), which misses the target. Earlier sections distinguish
the smaller short-clock screen from this completion. No old
long-clock generator cover is presented as a new step.

## 1. Kernel arithmetic simplifies from quadratic to linear slope

Let k=2*3^e, H=k^2, j a unit representative in [1,k), and

    g=gcd(j-1,k), n=k/g,
    Lambda_j={(a,b):a*j^2=b*N mod k},
    chi_j(a,b)=(j-1)(b*N*jinv-a) mod H.

Here jinv is an inverse modulo H. The exact kernel is

    Gamma_j=ker(chi_j|Lambda_j)
           =n*{(alpha,beta):alpha*j=beta*N mod k}.       (1)

Thus put c_j=[N*jinv]_k. A particularly simple HNF basis is

    v1=(nk,0), v2=(n*c_j,n).                            (2)

Its determinant is k*n^2, so its index in Lambda_j is n^2, exactly
the phase-image index already proved in `phase-index.md`.

For completeness, inclusion in (1) follows directly. If
alpha*j=beta*N mod k, then

    n*(alpha*j^2-beta*N)=n*beta*N*(j-1) mod k =0,
    chi_j(n*alpha,n*beta)
       =n*(j-1)*(beta*N*jinv-alpha)=0 mod H,

because n*(j-1) is a multiple of k. Both lattices have index n^2
in Lambda_j by the existing exact image theorem, proving equality.
This argument includes j=1: g=k,n=1 and Lambda_1 already has zero
phase character. It avoids any division by j-1 or modulus-one
inverse. All HNF data are acquired in soft k total bit operations.

## 2. Canonical labels collapse to very few actual q-nodes

For a kernel vector use its canonical lambda in [0,H). Because its
phase vanishes, its actual integer label E=a+bN+lambda is the least
multiple of H not smaller than a+bN:

    E/H=ceil((a+bN)/H).                                 (3)

The canonical phase is also a legitimate conic phase: the lattice
condition makes (aj-bNjinv)^2 divisible by H, whence
lambda^2=4abN mod H. We do not assert that these augmented HNF
vectors satisfy the old |ab|<k row bound. Their individual nonzero
short beta labels have the licensed general annihilator decoder.

For (2), since g>=2, equation (3) gives

    E(v1)=H,
    E(v2)=H*C_j,   C_j=ceil((N+c_j)/(k*g)).               (4)

Hence the canonical generator nodes are exactly q and q^C_j.
For a fixed g, 0<=c_j<k, so the C_j lie in an interval of width
less than 1/g. They take at most TWO consecutive integer values.
The possible g are 2*3^t, 0<=t<=e. Thus only O(log k) distinct
nontrivial canonical generator starts occur across ALL colours.
Their acquisition needs no roots, hidden orders, discrete logs,
or extension rings. One may enumerate the actual colours in soft k
and deduplicate the acquired pairs (g,C_j); all integers have
O(log N) bits. The at-most-two claim does not presume every possible
ceiling value is attained.

## 3. Execute the correlated generator screen

For every actually attained C_j evaluate

    product_(h=0..4k)(1-q^(C_j-h)).                     (5)

If C_j lies in this interval, omit that single literal-zero index
BEFORE evaluation, splitting into at most two strings. Every retained
factor has nonzero integer beta label H*(C_j-h), with O(log N)
bits. The inherited monic, division-free geometric backend, using
O(log k) starts and clock length O(k), evaluates and localizes this
screen within soft O(k), including acquisition and at most one
terminating T_ext. Its arithmetic evaluation alone is bounded by
soft O(log k+sqrt(k log k)); colour acquisition remains soft k.
No inverse of a rejected or merely nonzero factor is used.

The v1=q strings contribute nothing useful: after omitting h=1,
all their other factors are units, since 0<|1-h|<=4k and both local
q orders exceed 16H. This is an exact actual-node fact, rather than
a generic failure example. A nonunit from (5), on the other hand,
is useful: a proper gcd returns a factor; if saturated, its own
nonzero short beta label feeds the licensed extractor. The screen
may therefore be run as a valid extra prepass. It is not proved to
return a factor on every continuing semiprime.

## 4. Exact remaining coverage condition at the true colour

Take j=P mod k. Then c=c_j=[Q]_k. Let

    D=k*g, C=ceil((N+c)/D), delta=D*C-N-c, 0<=delta<D.

The canonical phase of v2 is n*delta. Its stationary integer index
is exactly

    I=(c*P+Q+delta)/D,
    C-I=((P-1)/g)*((Q-c)/k).                           (6)

Integrality follows either from the actual stationary phase theorem
or directly from c=Q mod k and P=j mod k. No roughening premise is
needed here: q=beta^H, and g divides both H and P-1. Thus
q^((P-1)/g)=beta^((H/g)*(P-1))=1 modulo P by Fermat, so the local
q order r_P divides (P-1)/g. Consequently C=I mod r_P, as required.

A useful hit in (5) at this colour therefore requires the additional
arithmetic condition

    exists h in [0,4k]: r_P divides I-h,
    equivalently r_P divides C-h.                     (7)

The complete Gauss-box coverage theorem gives a short index for a
DIFFERENCE of many stationary points; it does not bound the single
HNF index (6) by 4k or place its residue in that interval. In
particular (6) retains cP+Q rather than a reduced cancellation
between coefficients. Other colours' C values may accidentally
supply a useful hit, but that would need its own coverage theorem;
it is not implied by the true-colour stationary calculation.

Here is a strictly conditional arithmetic illustration of the gap,
not an existence claim or an all-colour counterexample. If the true
colour has g=2, c<=k-5, Q<=2P and r_P=(P-1)/2, then (6) gives

    I>Q/(2k)>8k,
    I<((k-5)P+2P+2k)/(2k)<(P-1)/2=r_P.

Thus the true-colour second generator has no short-clock hit. This
uses the actual PQ equation and allowed local-order branch; it says
nothing about the other colours' screen or how often those extra
conditions are realized. No numerical examples or prime-distribution
hypothesis are used to promote it to a uniform failure theorem.

## 5. Why shared generator nodes do not yet evaluate kernel witnesses

An inner-lattice vector has alpha=k*t+c_j*b, beta=b. In the HNF
basis its UNWRAPPED label is

    H*(t+C_j*b).

So integer combinations have exactly acquired nodes q^(t+C_j*b).
Canonicalizing that vector independently changes the label by an
integer multiple of H, which changes the finite physical clock.
Its carry must be retained, just as in `common-character.md`.

The small list of C_j therefore does not acquire the finite sets of
t+C_j*b arising from the actual transported Gauss difference boxes,
or their interval unions. The generator-unit result from (5) cannot
be extended to those combinations by multiplying or cancelling
nonunit factors. This is the precise uninitialized support remaining
in this attempted cover, rather than an assertion that shared q
coordinates can never help.

## Interim outcome and concrete next arithmetic obligation

The exact kernel is an N-dependent LINEAR-slope lattice, and its
canonical HNF generators collapse to O(log k) actual q-starts. The
resulting whole-family screen is fully initialized and paid within
soft k, with correct literal-zero deletion and T_ext accounting.
At this short clock no complete coverage has been obtained. Section 6
subsequently supplies complete coverage at a worse paid rate; no
full-query gain is obtained.

A genuinely stronger next lemma would have to show that either the
small acquired starts satisfy (7) somewhere, OR that the actual
short Gauss witness combinations t+C_j*b can be covered by soft-k
acquired clock intervals with their source carries. The exact
HNF normalization alone proves neither alternative. This is a
specific remaining native arithmetic condition, not a proposed
hypothetical generic square/discrete-log oracle.

## 6. Completed uniform cover using the correlated starts (subsequent step)

The generator screen can in fact be completed WITHOUT acquiring a
separate kernel Gauss vector or a factor-scale grid. Its fully paid
rate is soft N^(1/4), so this is an initialized cover comparison,
not the requested sixth-exponent improvement. This section updates
the earlier outcome: complete coverage is obtained after enlarging
the generator combinations and their clock as follows.

Choose integer bounds

    D0=ceil(sqrt(2kN)),
    V=ceil(sqrt(2k))+1,
    T=ceil(D0/(16kH))+V,
    W_g=ceil(2D0/(kg))+ceil(T/g)+V.                     (8)

All bounds are publicly computable by integer square roots and
integer division. For every actually attained pair (g,C), acquire
starts q^(C*b), -V<=b<=V, and evaluate

    product_(b=-V..V) product_(h=-W_g..W_g)
                    (1-q^(C*b-h)),                    (9)

OMITTING each literal index h=C*b when it lies in the interval.
Do not divide out its numerical zero. Each omission splits one
interval into at most two; signed clocks are represented by a unit
start shift and positive common q clock. The b=0 start is allowed,
but its h=0 factor is omitted. Every other included leaf has its
own nonzero O(log N)-bit beta label H*(C*b-h).

Here is a uniform all-semiprime coverage proof. At the true colour
consider the INNER index-k lattice

    alpha*P=beta*N mod k,

weighted by (P,Q). Its Euclidean covolume is kN. The usual two-
dimensional reduced-basis bound supplies a nonzero (a,b) with

    sqrt((aP)^2+(bQ)^2) <= sqrt(2kN/sqrt(3)) <= D0.

This vector is used ONLY in the existence proof. Its unknown
coordinates need not be acquired. Since Q>=sqrt(N), P>16H, and
c=[Q]_k, writing a=k*t+c*b gives

    |b|<=D0/Q<=V,
    |t|<=|a|/k+|b|<=D0/(16kH)+V<=T.

Take n=k/g and the kernel vector w=n(a,b). Use the UNWRAPPED HNF
phase t*lambda1+b*lambda2, where

    lambda1=H-H/g,
    lambda2=n*delta,
    delta=kg*C-N-c, 0<=delta<kg.

Its exact exponent is H*(t+C*b). The stationary integer index is

    I=[n*(aP+bQ)+t*lambda1+b*lambda2]/H.

Subtracting t gives

    I-t=(aP+bQ)/(kg)-t/g+b*delta/(kg),
    |I-t|<=sqrt(2)*D0/(kg)+T/g+V<=W_g.                 (10)

Thus the actually enumerated leaf b,h=I-t vanishes modulo P.
Its integer beta label is

    H*(C*b-h)=(P-1)*n*(bQ-a) !=0.                     (11)

Indeed |a|<=D0/P<Q, because D0<N under the standing N>256H^2
branch. If b!=0 the Q term dominates, and if b=0 then a!=0.
Consequently the guaranteed hit is NOT one of the omitted literal
indices. This also proves that the b=0 branch is safe: its true
h is nonzero, even though the artificial h=0 leaf was removed.
No short-clock/order comparison or extra coprimality assumption is
needed for (10)-(11). The Fermat difference proves the local hit
directly. Additional order aliases are harmless decodable leaves.

For each fixed g there are at most two C values. Hence (9) has
O(V log k)=soft O(sqrt k) acquired starts, O(log k) length groups,
and common clock q. Start powering uses O(log N)-bit exponents;
all whole-family acquisition, including identifying attained C
values, is soft O(k). The inherited division-free monic engine
and prefix localization give

    soft O(k + sum_g sqrt(V*W_g) + T_ext)
      = soft O(k + N^(1/4)).                           (12)

In particular V=O(sqrt k), T=O(sqrt k) from N<=k^6, and
W_g=O(sqrt(N)/(g*sqrt k)+sqrt k). The g sum is geometric over
2*3^t, so its evaluation contribution is
soft O(N^(1/4)+sqrt k), dominated by small g. For N near k^6
this is k^(3/2), worse than the original k^(5/4) backend. We do
not claim an optimality statement for this construction.

The scalar (9) is guaranteed nonunit, not necessarily globally
zero. Prefix nonunit/gcd localization identifies a pair (g,C),
then b, then h, with only logarithmic overhead. A proper gcd
finishes; a saturated leaf supplies the explicit short nonzero
label (11), or its own H*(C*b-h), to T_ext once. No original
Gauss-box incidence or old |ab|<k row needs to be reconstructed.

This is the requested completed covered algorithm for the very
small correlated HNF-generator family: combine O(sqrt k) multiples
of those generators with a publicly bounded clock. It removes
unpaid finite support and hidden factor scales from that proposal,
but the resulting clock is too long for the target rate. A better
choice of correlated finite domains or a contraction of (9) remains
open; the constant number of HNF nodes alone is insufficient to
assert the target improvement.

## 7. Universal g0=2 compression: one colour-independent covered query

The parent's refinement is valid and removes even the attained-colour
and g lists from the completed algorithm. Put n0=k/2. Since every
actual g is even, n0 is an integer multiple of k/g. Therefore

    n0*{(a,b):a*j=b*N mod k} subset ker chi_j

for EVERY odd unit colour, including j=1. We intentionally use this
universal sublattice rather than claiming it is the exact kernel.
Its HNF generators n0(k,0), n0(c_j,1) have canonical labels

    H, H*C_j,   C_j=ceil((N+c_j)/(2k)).

Set C=ceil(N/(2k)). Since 0<=c_j<k, write

    C_j=C+epsilon_j, epsilon_j in {0,1}.

With D0,V,T from (8), define

    W=ceil(D0/k)+ceil(T/2)+2V = W_2+V.                 (13)

The SINGLE colour-independent finite target is

    Z=product_(b=-V..V) product_(h=-W..W, h!=C*b)
                             (1-q^(C*b-h)).           (14)

The exclusion h!=C*b is imposed only when that integer lies in the
clock interval. It is a direct literal-label omission, not numerical
division. Thus (14) is a two-GP product with its literal incidences
removed; it contains no colour parameter, phase extraction, Gauss
basis, list of C_j, or auxiliary root of unity.

To prove coverage choose the true j and the same unknown reduced
inner-lattice vector (a,b) as in Section 6. Write a=k*t+c_j*b.
Use the universal HNF phases, namely lambda1=H/2 and
lambda2=(k/2)*(2k*C_j-N-c_j). The stationary integer I then obeys

    |I-t|<=W_2.

Take h=(I-t)-epsilon_j*b. Since |b|<=V, it lies in [-W,W], and

    H*(C*b-h)
       =H*(t+C_j*b-I)
       =(P-1)*(k/2)*(bQ-a) !=0.                       (15)

Therefore this leaf is included in (14), not omitted, and vanishes
modulo P. This proves nonunit coverage for ALL semiprimes in the
stated native hard branch. The epsilon clock shift preserves the
original Fermat gap EXACTLY; it is not an equality only modulo an
unknown order. A negative b or h changes nothing in this argument.
The b=0 origin issue is treated exactly as in Section 6: omit only
h=0; the guaranteed leaf is nonliteral by (15).

There are O(sqrt k) acquired starts q^(C*b), and clock length
W=O(sqrt(N/k)+sqrt k). All quantities have O(log N)-bit descriptions.
The inherited monic division-free joint backend, signed-clock
shifting and direct interval splits give

    soft O(sqrt k + sqrt(V*W) + T_ext)
        =soft O(sqrt k + N^(1/4) + T_ext)
        <=soft O(k+N^(1/4)).                          (16)

No soft-k colour enumeration is needed for THIS query. Nonunit
prefix localization over b and then h finds a leaf; its proper gcd
factors N, or its own nonzero short integer label H*(C*b-h) feeds
T_ext once. The scalar need only be nonunit; a global-zero-only
oracle is not asserted sufficient for the localization.

This is a completed constructive compression of the Section 6
cover into one common-base finite product. Its N^(1/4) readout is
still too expensive for the intended N^(1/6) goal and, in the hard
regime, worse than the existing native long-query backend. No new
factoring exponent or novelty claim is attached to it. The positive
content is the fully initialized colour-independent query and its
exact original-annihilator decoding, not a target-rate improvement.
