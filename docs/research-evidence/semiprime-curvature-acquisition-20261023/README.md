# Collision acquisition: linear reindexing and quadratic carries

23 October 2026. **No improved factoring exponent or whole-family soft-O(m)
collision query is proved here.** This note corrects the interpretation of
the preceding small-multiple cover and records the exact information that
must survive a quadratic contraction. The goal remains a classical,
deterministic worst-case soft-O(N^(1/6)) factorizer, followed by complete
executable and Lean bit-cost integration.

## What the linear cover actually does

The [Fermat-quotient constructor](../semiprime-fermat-multiplier-20261022/README.md)
and its bit bound remain valid. However, existence of an O(r)-size catalog
covering a small multiple of every unit modulo r² is already elementary:
take S={1+rt:0<=t<r} and choose c=P^(-1) modulo r in [1,r). Then cP is in S
modulo r². This is an existential multiplier for an unknown P, not a public
way to select it. The earlier construction's distinctive feature is its
quotient-layer structure and witness table, not the existence of a uniform
small-multiple cover. That novelty qualification supersedes any stronger
reading of the preceding checkpoint; its frozen files are preserved.

For the Fermat construction put H=r² and b_s=center(-N/s mod H). Its selected
(s,c) pairs biject all units modulo H by s/c. Hence their residues b_s c
also biject all units. For every integer interval I, the aligned triples

    (s,c,sigma) with T=H sigma-b_s c in I

are in bijection with all T in I for which r does not divide T. Moreover,

    beta^(N+b_s c)-beta^(H sigma)
      = beta^(b_s c) (beta^N-beta^T).

The product over the triples is therefore a unit times the ordinary long
geometric product over these T. On a whole number of H-blocks the unit
exponent is exactly zero: each quotient layer is closed under s -> -s,
b_(-s)=-b_s, and sum_(s,c) b_s c=0. In particular the positive interval
1<=T<=2r³ gives exact equality of the two forward-oriented products. It
contains 2r³-2r² leaves. At the genuine factor witness T=Q, Fermat's theorem
already gives beta^N=beta^Q modulo P.

Thus the linear consumer reindexes the full cofactor interval; the cover
does not thin that search. The [complete proof](reports/interval-reindexing.md)
retains signed endpoints, multiplicities, inverse labels and restrictions.
An arbitrary row/multiplier box need not become an interval in T, and an
oracle for boxes does not automatically supply the aligned interval query.

The inherited geometric-product method costs soft O(r^(3/2)) on an interval
of this length. Removing multiples of r costs soft O(r), with a gcd guard
before division. A proper gcd factors N; a saturated leaf uses the paid
strong-order decoder P+Q=T+1. This is an existing quarter-rate consumer,
not an improvement over the project's one-fifth baseline. It is also **not
a general lower bound** against faster ring algorithms or factor-only
queries. The [primary-literature ledger](reports/multibase-literature.md)
keeps the degree and dimension costs explicit.

The [dyadic cover](reports/dyadic-cover.md) makes the same point with even
simpler arithmetic. For m=2^k, k>=2, the homomorphism
q(x)=(x^(m/2)-1)/(2m) modulo m/2 has kernel x=+1 or -1 modulo 2m. Small odd
multipliers are a complete set of quotient representatives. The resulting
two arithmetic progressions, with every carry retained, enumerate all odd
T in a candidate interval. Their geometric nodes have different m/2-th
powers, so they cannot be substituted for the conjugates in one cyclic
norm fiber. The [Teichmuller audit](reports/teich-norm.md) gives the analogous
moving-power correction for the odd-prime construction.

## Quadratic transport retains a private digit

Use the explicit quadratic catalog row

    G_s(Z)=Z²+B_s Z+C_s N,
    C_s=center(s²/N mod r²), B_s=r² b_s-2s,

with b_s chosen so that G_s(s)=0 modulo r⁴. For cP=s modulo r²,

    r⁴ sigma=c² P+B_s c+C_s Q.

In the balanced regime P,Q<=2r³ this gives |sigma|=O(r). Let j=s/c modulo r,
and let a_j, ell_j be the original canonical native coefficients. Set

    kappa=(c²-a_j C_s)/r,
    lambda=(B_s c-ell_j C_s)/r,
    nu=(kappa j+lambda)/r.

All three are integers. At P=j+ru and native seed
I=(a_j P+Q+ell_j)/r², the exact identity is

    r² sigma=C_s I+kappa u+nu.

The short sigma interval therefore does not turn into a short native I
interval by division by C_s: the unknown next digit u remains in a
potentially large cancellation. This does not introduce a new independent
unknown; it specifies the arithmetic the shared query must process.

The [transport proof](reports/quadratic-transport.md) also pays simultaneous
C_s-roots and an r-root using the inherited smooth projection and
outside-product method, with factor recovery on collapse. After this legal
normalization the same local zero support is represented by

    eta_j = rho_s^(r³ sigma-D_s,j),
    D_s,j=(c²+B_s c-C_s delta_j)/r, c=[s/j]_r.

There are r native targets and soft O(r) root bases, but D_s,j still has
r² indexed phases. The roots themselves do not acquire their contracted
query. Nor may C_s be replaced freely by a factorized modular lift:
replacing it by C_s+r² k changes the true clock by

    r²(sigma'-sigma)=Delta b*c+kQ.

The private kQ contribution and any enlarged seed interval must be paid.

## Returning to the original curvature

For a native unit tag j modulo m, let u_j=j^(-1) modulo m², and keep the
canonical coefficient a_j=[N j^(-2)]_m<m. Define the public lift defect
h_j=(a_j-N u_j²)/m modulo m. The literal target exponent satisfies

    E_j=N+delta_j
       =N(1-u_j)²+m(1-j)h_j modulo m².

This gives a quadratic phase with its exact coefficient-lift correction.
Replacing a_j by the full m² representative removes that correction but
can enlarge the true seed interval from O(m²) to O(m³). The useful target
is therefore a shared computation retaining the actual mask and the
canonical coefficient bound.

The already-paid sparse dyadic norm handles a single shift and a supplied
fixed weight. It does not automatically supply the varying mask, the long
seed product, or restriction-safe factor localization. Subsequent work in
this packet tests explicit recurrences for those missing data. An identity
or a compact descriptor is not counted as an acquired collision query.

## A closed dyadic row recursion

The [canonical-mask calculation](reports/canonical-lift-recursion.md)
sharpens the earlier half-tag transport. At m=2n, write j=r+epsilon*n and
a_m=a_n+eta*n, where epsilon,eta are bits. Then eta=h_n(r) modulo 2 is
public and is the same for both upper tags. With the actual centered
coefficients,

    kappa=(2b_m-b_n-2a_m*epsilon-eta*r)/n in {-7,...,2},
    E_m(j)=E_n(r)+n*eta*(1-r)+n²*kappa.

The residual phase is therefore linear in the lower tag. A slope parameter
lambda closes exactly under lambda'=2lambda+eta. Simultaneously a seed
stride/phase pair (A,theta) updates to

    A'=4A, theta'=4theta-kappa+2lambda*epsilon.

These formulas retain the original seed index and every integer carry.
All row records and target-polynomial updates cost soft O(m) per level;
that target polynomial was already affordable. After t levels, the
2^t possible slopes times the lower rank m/2^t still have total size m.
This count is compatible with the desired bound and is not an obstruction.

What remains unpaid is the long product for those states. Packing a phase
theta into one fixed tangent weight supplies q^theta, whereas its kth
moment needs q^(theta*k). Absorbing it into the base of the norm fixes that
identity but inserts the interpolated phase polynomial repeatedly. The
available rank-p, width-D support envelope then has O(p*(1+D)) slots,
rather than the tangent's O(p+D). With only D=O(p) available, this attempt
does not certify soft-linear work. This is a cost of the inspected
representation, not a lower bound against a better contraction. An
embedding of the actual scalar targets into the sparse norm is also
required; the row congruence alone does not provide it.

## One full-family power trace is acquired

The elementary AP catalog has a useful additional property: since every
s is 1 modulo r, the native tag j corresponds to the same multiplier
c=j^(-1) modulo r in every row. Common multiplier restrictions therefore
also implement native-tag restrictions.

For supplied row and multiplier subsets and a common sigma interval, set

    Z_s,c,sigma=beta^(c²+B_s c+C_s N-r⁴ sigma),
    P_k(X)=sum_c beta^(k c²) X^c,
    A_k=sum_sigma beta^(-k r⁴ sigma).

The exact aggregate power trace is

    S_k=sum_(s,c,sigma) Z_s,c,sigma^k
       =A_k * sum_s beta^(k C_s N) P_k(beta^(k B_s)).

The [shared evaluator](reports/phase-contraction.md) constructs one
degree-<r polynomial and evaluates it at O(r) points by monic multipoint
evaluation. The seed sum uses division-free geometric doubling. Repeated
points and composite-ring zero divisors are permitted. For one specified
k of O(log N) bits, a conservative bound is soft O(r*(log N)²) bit work
and soft O(r*log N) workspace. No r² phase matrix is formed.

This acquires an additive statistic of the whole family. For
F(z)=product(1-z Z_s,c,sigma), h traces supply F modulo z^(h+1) using
formal exponentiation, at the currently proved cost soft O(rh), with
logarithmic N factors understood. For h<=r all needed small denominators
are units on the prepared branch. The multiplicative detector F(1)
remains unacquired. A trace or truncated prefix can cancel or miss a local
zero; neither is substituted for the detector. The missing step is a
shared contraction of the trace-index direction or a direct product
algorithm, including localization.

The [AP coefficient analysis](reports/ap-catalog.md) proves a separate
soft-O(r) resultant for the part depending only on C_s and sigma. Its
native phase beta^(c²+B_s c) still depends on both labels. The coefficient
formulas expose both centering carries. The trace report uses an
alternative positive-C, centered-B convention for its cubic generators;
the trace and zero-screen formulas work under either convention. The
finite |sigma|<4r bound is proved for the AP report's centered-C rows.

## Recovery and public zero cleanup are already affordable

For any quadratic leaf with global equality, the public integer
K=C_s N+c²+B_s c-r⁴ sigma is a global annihilator. If K is nonzero it has
O(log N) bits, so the inherited unconditional unbalanced short-annihilator
extractor costs soft O(N^(31/192)), within the current budget. Unlike the
linear interval query, this argument does not require the stronger
quadratic exponent to fit below the global order. The decoder is an
inherited primitive, not an acquisition advance.

K=0 must be removed because it is a tautological equality. Put y=c-s.
The row identity gives

    K=y²+r² b_s y+r⁴(d_s-sigma).

If v_r(y)<2, the first summand has uniquely smallest valuation. Therefore
K=0 forces c=s modulo r², hence c=s<r for the canonical representatives.
An O(r) scan tests at most one candidate per row. In the elementary AP
catalog only s=c=1 is possible. Its sigma is d_s, which is checked against
the actual interval. The count h0 of deleted leaves is thus acquired
cheaply, and the clean trace is S_k-h0. At the true covered leaf,
K=(P-1)(C_s Q-c²) is nonzero because Q>16r² and C_s is a nonzero integer;
cleanup preserves coverage.

The original scalar query and its new quadratic variants consequently
still need acquisition, not additional global-leaf recovery. The
independent reviews and archive validation below distinguish these
proved algebraic refinements from the unproved sixth-rate bound.

## Review and preservation

The [independent algebra review](reviews/independent-review.md) checks the
lift recurrences, carry signs, support envelope, trace and zero cleanup.
The [second review](reviews/powertrace-review.md) separately checks the AP
and cubic generators, four dyadic branches, composite-ring evaluation,
restriction scope and bit bounds. A total-precision qualifier was added
to the moment-batching statement: O(m) total requested moments across
the partition are affordable, not O(m) moments separately for each mask.

The second review also derives a useful consequence of the inherited
setup: for prime r, beta^(r⁴) has the same large local orders as
beta^(r²). Both hidden primes are less than r⁴/16; a local beta-order
divisible by r² would contradict the certified beta^(r²) order bound.
Thus for nonempty |I|<=10r+1 and k<=r the geometric sum A_k is a unit.
This permits optional normalization of the uncleaned S_k to giant-only
moments; the known h0 cleanup must still be retained. It supplies no
detector. Empty intervals are handled separately.

[Validation](validation.json), [copy provenance](archive-provenance.json)
and [source fingerprints](source-pins.json) record what was checked.
All 208 previous frozen entries are preserved. The reports' finite
checks corroborate algebraic identities; they are neither factorization
coverage evidence nor measurements proving the complexity bounds.
No new Lean theorem, broad build, commit or push is included.
