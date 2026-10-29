# Uniform short-shift coverage from weighted stationary rectangles

26 October 2026. Parent derivation following the Christoffel-word probe.
This removes the balanced-factor restriction from the dense-box coverage
idea. It does NOT acquire the resulting collective scalar cheaply and does
not improve the complete factoring exponent. The trade-off is explicit:
soft-k public rectangle descriptions represent soft-k-squared row
incidences and guarantee a nonliteral same-field edge at an integer shift
between 0 and 6k. This is a new coverage construction for an enlarged
family, not a coverage theorem for a small subset of the old family.

## 1. Prepared inputs and public construction

Use the inherited prepared branch N=P Q, P<=Q, H=k^2, k>16,
N<=k^6, P,Q>16H, gcd(N,k)=1. The original unit base beta and
q=beta^H have their inherited order and factor-recovery guarantees.
All scales and integer labels below have O(log N) bits.

For each public unit colour 1<=j<k and each power of two B<=k, put

    A=ceil(2k^2/B),
    S_(j,B)={(a,b): 0<=a<A, 0<=b<B, a*j^2=b*N mod k}.

Each rectangle is an auxiliary row family. It is NOT subject to the old
|ab|<k admission rule, and is not silently inserted into that catalogue.
Its coverage and its leaf decoder are established below independently.

For each point choose the canonical stationary phase

    lambda_j(a,b)=[-a*j-b*N*jinv]_H,
    E_j(a,b)=a+b*N+lambda_j(a,b),

where jinv is an inverse modulo H and brackets denote the least
nonnegative residue. The existing stationary phase identity applies to
every point of Lambda_j, independently of the old low-product cutoff.
Indeed, write P=j+k*t. Modulo H, P^(-1)=jinv-k*t*jinv^2; thus
aP+bN/P-(a*j+bN*jinv)=k*t*(a-bN*jinv^2)=0 mod H
by the lattice condition. This proves integrality of the true-colour
index used below.

Apply the public cell filter A<=H/g, where g=gcd(j-1,k). Its
coverage and exact literal-edge meaning are proved in section 4 below.
Also include the transpose of each retained cell, with (a,b) replaced
by (b,a) and the same canonical phase.

There are O(k log k) public (j,B) descriptions. They, theta_j=j^2/N mod k,
and all rectangle dimensions can be acquired in soft O(k) bit operations.
An explicit description is not the explicit list of its points or nodes.

## 2. Each rectangle has between k and 3k points

For each fixed b there is exactly one residue class for a modulo k.
Consequently its number of representatives in 0<=a<A is either
floor(A/k) or ceil(A/k). Let n=|S_(j,B)|. Then

    n >= B floor(A/k) >= B(A/k-1) >= 2k-B >= k.

For the upper bound, A<2k^2/B+1 gives

    n <= B ceil(A/k) < 2k+B/k+B <= 3k+1.

Since n is integral, n<=3k. This count is independent of colour and does
not require a generic-position or distributional premise. In particular,
the explicit incidence lists have Theta(k^2 log k) entries across colours
and scales. That is a cost for this materialized construction; it is not
a lower bound for all compressed evaluations or all deduplicated lists.

## 3. A public scale guarantees a shift at most 6k

For the actual smaller factor define, for this proof only,

    rho=k*sqrt(P/Q)=k*P/sqrt(N).

The prepared bounds give 16<rho<=k. Some enumerated power of two B
satisfies rho/2<B<=rho. Choose that scale and the true colour j=P mod k.
Every point then has an integer stationary index

    I_(a,b)=(aP+bQ+lambda_j(a,b))/H >= 0,
    beta^E=q^I mod P.

Using A-1<2k^2/B, b<B and lambda<H,

    I < 2P/B + BQ/H + 1
      < 5*sqrt(N)/k + 1
      <= 5k^2+1.

Sort the n>=k integer indices with multiplicity for the existence proof.
If two coincide, their difference is zero. Otherwise an adjacent gap is
at most (max I-min I)/(n-1), hence strictly less than

    (5k^2+1)/(k-1) < 6k                 (k>16).

Thus two distinct rectangle points u,v have an integer difference

    s=I_v-I_u, 0<=s<=6k,
    q^s beta^E_u=beta^E_v mod P.          (1)

No sorting algorithm or index oracle is assumed: the unknown indices are
used only to prove coverage. This is an all-prepared-semiprime statement,
including unbalanced factors. It strengthens the balanced square-box
pigeonhole observation in christoffel-products.md by choosing public
weighted rectangles.

## 4. Every guaranteed edge is nonliteral and recoverable

For Delta a=a_v-a_u and Delta b=b_v-b_u, stationarity gives exactly

    E_v-E_u-Hs=(P-1)*(Delta b*Q-Delta a).   (2)

Since B>=1, A<=2k^2, so |Delta a|<2k^2<Q. If Delta b!=0, the
second factor cannot vanish. If Delta b=0, distinct points have
Delta a!=0. Thus (2) is nonzero for the pair in (1).

The two integer labels are also distinct. For Delta b=0 they have the
same b and phases satisfying the fixed-colour rule; even if one initially
worries about cancellation between Delta a and Delta lambda, equality of
E would imply q^s=1 locally. For 0<s<=6k this contradicts the prepared
order bound; for s=0 it contradicts (2). Alternatively one can retain
all point metadata and let the general literal-label routine decide
duplicates; the guaranteed pair is never a literal duplicate.

A proper gcd of q^s beta^E_u-beta^E_v with N gives a factor. If this
equality saturates globally, (2) supplies a nonzero O(log N)-bit beta
annihilator, so the inherited extractor applies. Its cost is
T_ext=soft O(N^(31/192)), charged at most once before termination.
The s=0 case uses the usual node-separation test on distinct labels;
it is not the tautological comparison of a node with itself.

The zero vector (0,0) has E=I=0. It causes no unconditional self-edge
in this predicate: edges always use distinct points and, for a factor
return, a nonzero integer gap. It may be one endpoint of a useful edge.
No whole-row deletion based on the original physical window is applied
to this auxiliary construction.

### A public filter removes every literal edge, preserving coverage

For a cell of colour j put g=gcd(j-1,k). Retain it only if A<=H/g.
If two points have different b, their label difference has magnitude
at least N-(A-1)-(H-1)>N-3H>6kH. If they have the same b,
Delta a is a multiple of k, and

    E_v-E_u = Delta a*(1-j) mod H.

Divisibility by H would require |Delta a|>=H/g for nonzero Delta a.
That is impossible when A<=H/g. Thus EVERY distinct-point edge of a
retained cell has a nonzero integer gap for 0<=s<=6k, including s=0.
In particular all its integer labels are distinct.

The filter has an exact converse for the original rectangle: if A>H/g,
both (0,0) and (H/g,0) are present. The latter has E=H, creating a
literal shift-one edge from the origin. This is why an unfiltered
resultant would contain a tautological zero.

The good cell in section 3 always passes the filter. For j=P mod k,
g=gcd(P-1,k). Since q^((P-1)/g)=1 mod P, the high-order premise gives

    g < P/(16H) <= rho/16.

The chosen B>rho/2 therefore satisfies B>8g. Consequently
A=ceil(2H/B)<=H/g, as H/g is integral. This is a public arithmetic
filter, not an unknown-factor test performed by the algorithm.

### Transposition gives the same shift at the other prime

For every retained rectangle include its transpose with phases retained.
The colour changes to N*jinv mod k, and the phase rule agrees modulo H.
If H I=aP+bQ+lambda, its transposed row (b,a,lambda) has the SAME
physical index at Q. The two guaranteed endpoints thus give a
same-field edge at the SAME shift s at Q as well as at P.

Distinct original points cannot have the same a: otherwise the lattice
condition forces k to divide Delta b, while |Delta b|<B<=k. Therefore
any two distinct transposed points have different coefficients of N.
Their label gap has magnitude at least N-k-H>6kH, so no transposed
cell introduces a literal edge in the specified shift range.

The exact collective predicate can now be the bare finite product

    Z = product_(retained cells and transposes)
        product_(s=0)^(6k)
        product_(distinct ordered points u,v in that cell)
             (q^s beta^E_u-beta^E_v).                 (4)

It is globally zero modulo N for every prepared semiprime. Every one
of its leaves has a nonzero short integer exponent gap. Diagonal
self-pairs are excluded; pairs from different cells are NOT inserted.
There is no optional division or unknown literal-edge mask in (4).
This defines a valid complete coverage and recovery query. Its value
or local-zero predicate is still not acquired at the target cost.

## 5. Exact implicit form and unpaid acquisition

The geometry has a short description. For fixed b, the permitted a's
form one arithmetic progression of step k in the rectangle. With the
unwrapped character

    U_j=beta^(1-j), V_j=beta^[N*(1-jinv)],

the node is NOT automatically U_j^a V_j^b. If

    t_(a,b)=floor((-a*j-b*N*jinv)/H),

then its actual canonical node is

    beta^E=U_j^a V_j^b q^(-t_(a,b)).       (3)

The carry is explicit for a supplied point. Any implicit Christoffel,
Beatty, rational-tangle or generating-function product must keep it.
The rectangle's finite endpoints, public cell filter and exclusion of
diagonal self-pairs must also be retained. The unmasked word-product algorithm alone does not
evaluate the resulting collective edge predicate.

The enlarged construction trades the old soft-k explicit rows and
O(k^(3/2)) index horizon for soft-k rectangle descriptors, soft-k-squared
implicit row incidences, and O(k) guaranteed edge shifts. Materializing
the latter incidences already exceeds the target soft-k budget. No
compressed joint query, amortized per-colour algorithm, or stronger
general lower bound is supplied here.

The concrete constructive target is a soft-O(k) factor-or-no-nonliteral-
edge query for these supplied rectangle descriptions and shifts [0,6k],
including (3), the public cell filter, diagonal exclusion, and recovery.
A sufficient localization contract asks for the same query on prefixes
of the public cell list and prefixes of the shift interval, with scalar
gcd/nonunit status rather than only a global equality-to-zero bit. Two binary
searches select one cell and one shift in logarithmically many calls.
Only then materialize that cell's O(k) nodes and use the paid
supplied-shift/separation consumer in soft O(k+T_ext). Every leaf is
nonliteral by the filter and transpose proofs, so the original gap
consumer applies. A fast value for the full product alone would need
this localization cost justified as well. Coverage for that target is
now proved. Its acquisition and the full desired bit
complexity remain open. The existing complete query rate is unchanged.
