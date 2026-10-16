# Complete Euclidean intermediates: all original linear-center windows miss on an actual infinite family

Classical arithmetic proof, 2026-10-08. Joint investigation of
/root and /root/mask_arithmetic_review. All previously frozen sources,
audits and reports remain read only. This report extends the preceding
square-root-box obstruction to the COMPLETE actual Euclidean source,
including every intermediate vector with coordinates as large as m-1.
It proves failure of the specified paid whole-family acquisition channel,
not a lower bound for arbitrary factorization or arbitrary centers.

## 1. Exact source and new theorem

Let N=P*Q be a balanced distinct-prime input, and let m be the literal
least prime at least ceil(N^(1/6)), namely publicRowModulus N. For each
unit tag 1<=j<m, take ALL vectors emitted by publicPairs N m j:

    euclidPairs(m, (N*j^(-2) mod m), 0, 1, false).

Here the displayed slope is the exact representative of quotientSlope
modulo m; the inverse is the actual public Bezout inverse. The literal
source retains every current Euclidean vector and every intermediate
division vector. For each emitted signed pair (a,t), apply exactly

    D=(t*N-a*j^2)/m,
    b=centered(m,-publicInverse(m,j)*D), c=(D+j*b)/m,
    t*N=m^2*c-j*m*b+a*j^2.                              (E1)

Write ell=m*b-2*a*j and delta=a+ell. The actual original target is
gamma^(t*N+delta), and alpha=gamma^(m^2). For a fixed C>0 retain EVERY
original integer index in the two literal rectangle windows

    |i-publicShift(N,m,j,a,b,t)|<=C*m,
    |i-reflectedShift(N,m,j,a,b,t)|<=C*m,                (E2)

and optionally in BOTH applicable additional windows

    |i-(2*sqrt(a*t*N)+ell)/m^2|<=C*m       if a>0,
    |i-ell/m^2|<=C*m                     if a<0.        (E3)

Rounding the real centers in (E3) by a bounded amount is harmless.
Targets and indices are transported together; (E2)-(E3) always refer
to the ORIGINAL index and full N-dependent source lift.

**Theorem.** Infinitely many actual balanced distinct-prime inputs,
with the literal selector, actual longBase2 route and its actual gamma,
have

    gcd(N,gamma^(t*N+delta)-gamma^(m^2*i))=1            (E4)

for EVERY actual public Euclidean current/intermediate row, EVERY
index in (E2)-(E3), and BOTH hidden-field orientations. The factors can
also be required to have distinct tags modulo m. No advised order,
prime-field toy input, GRH or unpublished prime-density premise is used.

The whole-family source and scalar norm in these linear windows are
paid soft O(m) classically. The theorem therefore defeats a complete
source-faithful acquisition with that cost; constructing a matrix or
more backend identities cannot recover a nonexistent local collision.
The result also holds for every width W<=C*m*(log m)^B with fixed
C,B>=0, as proved in Section 9.1 below.

Two new counting steps are essential. A universal SET of all possible
Euclidean rays across all nonzero slopes has soft O(m) members and is
independent of the full input. Partitioning each P-fixed selector strip
into width-m^2 boxes removes the former weighted-height/gap-squared loss.
For own tags, count admissible P intervals separately for each ray,
instead of seeking a uniform short-height bound for the whole source.

## 2. Authoritative source and published actual supply

The preceding centered audit was revalidated read only: all 479 source,
107 selected Mathlib and 48 artifact pins match. Its SHA256 is
de11da69ec0086d3cd8ba1c982a32e06f05cb3b4fdbb520c4056c004ba18da03.
The source formulas and native finite hit/uniqueness contracts are the
same ones used by the frozen full-height-centered report.

Put M=X^(1/3), kappa=677/1000 and theta=21/40. The published
[Kurlberg--Pomerance Lemma 19 and its cited large-divisor input](https://www.impan.pl/shop/en/publication/transaction/download/product/82225)
give Omega(X/log X) primes in a fixed multiplicative bin in [cX,X]
whose P-1 has a prime divisor R_P>P^kappa. The bin can have ratio <=3/2,
so all ordered pairs are balanced. Write

    P-1=v_P*R_P,
    1<=v_P<=V=O(M^(3-3*kappa))=O(M^.969).              (E5)

The large divisor is unique and has exponent one. Removing base-2
orders that omit R_P costs O(V^2/log X) individual primes, by the
logarithm of product_(r<=V)(2^r-1), or the same primary paper's
order-omission argument. Remove diagonal and cross-period pairs at cost
O(X+X^(2-kappa)), ensuring R_P!=R_Q, R_P does not divide Q-1 and
R_Q does not divide P-1. The retained actual ordered-pair supply is

    Omega(M^6/log^2 M).                               (E6)

The literal public projected base is

    gamma=(2^(N-1))^((m!)^ceil(log_2(N+1))) mod N,

with staged public powering available. Its two EXACT local orders on
this supply are R_P and R_Q: the factorial power kills each cofactor
v, while R>m and the cross-period exclusions preserve the large prime
through both public projections. The preserved route proofs give the
actual longBase2 outcome; these hidden primes and periods are proof-side
counting facts, never algorithm input. Eventually, uniformly,

    m is comparable to M, v_P,v_Q<m, R_P,R_Q>16*m^2,
    P,P-1,Q,Q-1 are units modulo m^2.                 (E7)

For example m cannot divide P-1=v_P R_P because m is prime and
v_P<m<R_P. The source denominators below will also be units.

For mminus the preceding prime and g=m-mminus, the LITERAL selector is

    mminus^6<P*Q<=m^6.                                (E8)

At fixed P in [cX,X], the possible Q form a strip of length O(m^2*g).
It contains O(m*g+1) integers in any prescribed class modulo m.
Consecutive selector gaps telescope:

    sum_m(g+1)=O(M).                                  (E9)

[Baker--Harman--Pintz, Theorem 1](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf)
gives g=O(M^theta). Apply the backward prime interval at x=m-1 to
avoid selecting m itself. Hence

    sum_m g^2=O(M^(1+theta)).                         (E10)

All cofactor/prime counts below allow integer P or Q wherever stated.
No prime distribution inside the selector strips or residue classes is
needed. The published inputs and actual route are the previously frozen
ones; this turn adds arithmetic counting rather than an analytic premise.

## 3. One universal soft-linear Euclidean ray SET

For a nonzero slope lambda in {1,...,m-1}, define its exact coordinate
list euclidPairs(m,lambda,0,1,false). Let C_m be the SET union of these
lists, with repeated coordinate pairs removed. It depends only on m.
Every actual row at every tag and every coprime full input has its
signed pair (a,t) in C_m, since the actual slope is nonzero modulo m.

Here is a direct derivation of the cardinal bound from the authoritative
native complete source budget; no new generic lattice count is assumed.
Choose any nonresidue eta modulo the odd prime m. In the two public
inputs N=1 and N=eta, the slopes N/j^2 as j scans units cover respectively
the two square classes of all nonzero slopes. Thus EVERY lambda is a
slope of one of those two literal public inputs. The native theorem
publicPackets_length_le includes every intermediate and both rectangle
centers and bounds its length by 8*m*(floor(log_2 m)+1)^2 for each N.
Dropping centers divides the coordinate occurrence count by two; taking
a SET union and dropping duplicates can only decrease it. Consequently

    |C_m|<=8*m*(floor(log_2 m)+1)^2=soft O(m).           (E11)

The nonresidue is only a catalog-existence/counting witness. It does
not select a factor or supply an actual input to the factoring algorithm.
Equivalently the source's determinant/quotient charges prove this bound
across all slopes using a unique linear slope fiber rather than the
at-most-two quadratic tag fiber. No construction of the charge envelope
is required.

Every catalog ray satisfies

    0<|a|<m, 1<=t<m.                                  (E12)

Indeed each division frame has r0>r>0,y>0,x>=0 and r0*y+r*x=m.
The current ray has |a|=r<m and t=y<m. Each intermediate k with
1<=k<floor(r0/r) has |a|=r0-k*r>0,t=x+k*y>0 and

    |a|*y+r*t=m,

which bounds both coordinates strictly below m. Because m is prime,
a and t are units modulo m^2. These bounds retain the ACTUAL largest
intermediate coordinates; this is not a square-root truncation.

Since C_m is a SET, three elementary dyadic weighted bounds will be
used. For any fixed C1>0,

    sum_((a,t) in C_m, 0<a<=C1*t) t^(-1/2)=soft O(m^(3/4)),
    sum_((a,t) in C_m, 0<|a|<=C1*t) t^(-1)=soft O(m^(1/2)),
    sum_((a,t) in C_m) (|a|+t)^(-1)=soft O(m^(1/2)).     (E13)

For the first two sums, t in [T,2T) and |a|<=C1*t give at most O(T^2)
distinct integer pairs, as well as at most |C_m|. Summing
min(O(T^2),soft O(m))*T^(-s) over dyadic T and splitting at sqrt(m),
with logarithms absorbed, gives exponents 1-s/2 for s=1/2 and s=1.
The third sum uses U=|a|+t in [T,2T), with the same O(T^2) envelope
and s=1. These estimates would not be justified by an occurrence
multiset with arbitrary repetitions; the set convention is essential.

## 4. Literal centers and exact local hit kernel

Let

    A=(1+1/sqrt(2))/2, B=(1+sqrt(2))/2,
    A*B=(4+3*sqrt(2))/8>1.                             (E14)

For BOTH signs of a the original public rectangle midpoint satisfies

    m^2*publicShift=ell+(A*a+B*t)*sqrt N+O(m^2+|a|+t),

and reflectedShift swaps A and B. The source floor square roots and
integer midpoint division contribute exactly the displayed error.
The other centers have beta=2*sqrt(a*t) for a>0 and beta=0 for a<0.
Thus every chosen index has

    |m^2*i-ell-beta*sqrt N|<=C0*m^3, |beta|=O(m),        (E15)

where beta depends only on (a,t,center type), not on j,b,c or N.
The centered b has canceled only after the target and index have both
been transported; the original quotient relation still retains it.

In the P field an actual original collision is exactly

    t*Q+delta-m^2*i=K*R_P, K an integer.                (E16)

Combining (E15)-(E16) gives

    |K*R_P-(t*Q+a-beta*sqrt(P*Q))|<=C0*m^3,
    |K|=O(v*m).                                       (E17)

The cleared hit polynomial and ACTUAL source elimination are

    F(P)=K*P^2-(K+v*delta)*P-v*t*N=0 mod m^2,
    F(P)=(K+v*a)*P*(P-1)-v*a*(P-j)^2-v*m*b*(P-j)
         modulo m^2.                                  (E18)

The complete integer identity also retains the discarded -v*m^2*c.
The authoritative finite Lean leaf already proves this exact identity.
For fixed P,m,a,t,v,K the reduction modulo m is a quadratic in j with
unit leading coefficient -v*a, so it gives at most TWO tags.
At every false tag j!=P mod m, the coefficient of b after canceling m
is a unit; b modulo m is unique. The original quotient relation fixes
the entire N modulo m^2, hence ONE Q class modulo m^2. The native
false_tag_input_state_unique proves these cancellations with their
explicit coprime gates and without any derivative/Hensel premise.
They cover every false repeated-root branch as well as simple roots.

## 5. Width-m-squared subboxes price EVERY false hit

At fixed actual P,m partition the selector Q strip into half-open
subboxes of length at most m^2. There are O(g+1) of them. For each
catalog ray and center define the real function

    Phi(Q)=(t*Q+a-beta*sqrt(P*Q))/R_P.

On the balanced range, (E12) and |beta|=O(m) give

    |Phi'(Q)|=|t-(beta/2)*sqrt(P/Q)|/R_P
             =O(m/R_P)=O(v/m^2).                      (E19)

Thus Phi varies by O(v) within ONE subbox. The error in (E17), divided
by R_P, is also O(m^3/R_P)=O(v). Consequently each subbox has an
interval containing only O(v) possible integer K, INDEPENDENT of
j,b,c and the two-digit public state. Each K yields at most two tags;
each false tag gives one Q class modulo m^2, containing at most one
integer in a half-open width-m^2 subbox. The endpoint convention can
also be relaxed at a constant cost.

For fixed m,v, there are O(X/v) integers P in [cX,X] with P=1 modulo v.
This upper bound applies to the actual prime/order subset. Catalog size,
subbox count, K count and state uniqueness give

    false pairs at fixed m,v
      <=soft O((X/v)*m*(g+1)*v)=soft O(X*m*(g+1)).      (E20)

The cofactor v cancels. Sum v<=V and sum_m(g+1)=O(M):

    ALL false-hit pairs in either field=soft O(V*M^5)
      =soft O(M^(5969/1000))=soft O(M^5.969).           (E21)

This replaces the old whole-strip bound that charged both a large
K variation and O(g+1) representatives of its residue class. After
subdivision, the class has only one representative; charging that
second gap factor would double-count strip length. No average-prime-gap
estimate or unproved source/phase equidistribution is needed.

## 6. EVERY own-tag hit is the exact forced index

If j=P modulo m, (E18) becomes (K+v*a)*P*(P-1)=0 modulo m^2.
Both P and P-1 are units. Hence m^2 divides K+v*a. By (E17),

    |K+v*a|=O(V*m)=O(M^1.969)=o(m^2),

so the integer multiple must vanish: K=-v*a. Substitute this into
(E16), using v*R_P=P-1, to get the EXACT original index equation

    m^2*i=a*P+t*Q+ell.                                (E22)

No other local alias remains at the own tag, despite the full unbounded
Euclidean weights. Its inclusion in a chosen window is now real
weighted-sum geometry. The legal true-tag relation is

    a*P=t*Q modulo m,                                 (E23)

which fixes one Q class modulo m, since 1<=t<m.

## 7. Own stationary and cancellation hits: reverse the ray/P count

For a positive stationary ray, (E15) and (E22) imply

    (sqrt(a*P)-sqrt(t*Q))^2<=C2*m^3,
    |sqrt(a/t)-sqrt(rho)|<=C3/sqrt(t), rho=Q/P.          (E24)

Balanced rho lies in [1/2,2], so necessarily a<=C4*t for a FIXED C4.
For each fixed catalog ray, its admissible rho form an interval of
width O(t^(-1/2)); this follows by squaring the interval in (E24), whose
center sqrt(a/t) is now uniformly bounded.

Freeze rho0=m^6/P^2. By literal selection, |rho-rho0|=O(g/m), so the
admissible rho0 interval has width O(t^(-1/2)+g/m). On the fixed balanced
scale, P->rho0 is monotone with derivative comparable to 1/X. Therefore
the number of admissible INTEGER P in [cX,X] for this one ray is

    O(X*(t^(-1/2)+g/m)+1).                            (E25)

This reverses the former counting order: neither a vector frozen across
inputs nor a universal small-height promise for Euclid is required.
Each such P has only O(m*g+1) possible Q in its true-tag class (E23).
Using the first weighted sum (E13) and the catalog cardinality,

    own stationary pairs at fixed m
      =soft O((m*g+1)*(X*m^(3/4)+X*g+m)).              (E26)

Sum the selector gaps (E9)-(E10), with X=M^3:

    ALL own stationary pairs
      =soft O(M^(23/4)+M^(4+1+theta))
      =soft O(M^5.75+M^5.525).                        (E27)

For a=-a0<0 the cancellation center yields |a0-rho*t|<=C5. Then
a0<=C6*t and the rho interval has width O(t^(-1)). The second weighted
sum (E13) changes m^(3/4) in (E26) to m^(1/2), giving

    ALL own negative-cancellation pairs
      =soft O(M^5.5+M^5.525).                         (E28)

All +1 integer-endpoint terms are smaller: for example catalog-size
times (m*g+1) summed in m is soft O(M^3). Both hidden-field
orientations are counted by the same argument, with rho in [1/2,2].

## 8. Own rectangle hits: the AB>1 discriminant gap

For the literal public center, (E15) and (E22), divided by sqrt(N),
give for u=P/sqrt(N) in a fixed positive compact interval

    |f(u)|<=C7,
    f(u)=a*(u-A)+t*(1/u-B).                            (E29)

ReflectedShift swaps A and B. Put U=|a|+t, and freeze u0=P/m^3.
Literal selection gives |u-u0|=O(g/m), so a necessary frozen condition
is |f(u0)|<=E, where E=C8*(1+U*g/m).

For a>0 set

    Delta=(A*a+B*t)^2-4*a*t.

The matrix of this quadratic form has positive leading principal minor
A^2 and determinant 4*(A*B-1)>0. Thus Delta>=c8*(a+t)^2 for a FIXED
positive c8. The reflected form has the same positive-definite gate.
The exact derivative identity is

    (u*f'(u))^2=(A*a+B*t+f(u))^2-4*a*t.               (E30)

Since g/m=o(1), for all sufficiently large U the frozen level band
|f(u0)|<=E has |f'(u0)|>=c9*U: the perturbation from Delta in (E30)
is O(U*E+E^2), and E/U=O(1/U+g/m) is smaller than a fixed discriminant
gap. f''(u)=2*t/u^3>0, so the level band has at most TWO components.
Each has length O(E/U)=O(U^(-1)+g/m). The finitely many rays with U
below the fixed threshold satisfy the same P-count upper bound after
enlarging its fixed constant.

For a<0 the derivative f'(u)=a-t/u^2 has absolute value >=c10*U
everywhere on the compact interval. The band is monotone and has the
same length bound, without a discriminant argument. The same reasoning
applies to the reflected constants. Since P=m^3*u0, each fixed ray
therefore admits at most

    O(X*(U^(-1)+g/m)+1)                               (E31)

integer P. There is no exceptional real-ratio exclusion around a
coefficient zero: the discriminant/derivative argument controls those
positions directly and uniformly.

Combine (E31) with (E23), the third weighted sum (E13), and (E9)-(E10):

    ALL own rectangle pairs, BOTH literal centers
      =soft O(M^5.5+M^5.525).                         (E32)

The strict AB>1 inequality is the arithmetic reason that positive-ray
near-zero bands remain transverse at full source height.

## 9. Actual infinite ALL-hit absence and the paid norm it defeats

Summing both fields and all center types, (E21), (E27), (E28) and (E32)
give the complete hit-containing actual-pair loss

    soft O(M^5.969+M^5.75+M^5.525)
      =soft O(M^5.969)=o(M^6/log^2 M).                 (E33)

Remove these pairs from (E6). Positive actual mass survives at unbounded
scales. Same-tag pairs can separately be removed at cost O(M^5), by one
Q class modulo m and (E9); no thin same-tag supply is intersected.
Every remaining actual input satisfies (E4) for ALL actual source
packets and ALL original indices in ALL four stated windows. On both
fields each residual is nonzero, so it is a unit modulo the actual
squarefree N. This proves the theorem, including every false-row alias.

The whole-family norm route is concretely paid. The existing complete
source budget gives soft O(m) emitted rows with both rectangle centers;
adding the two applicable extra centers multiplies the count by a
constant. Euclidean frames, public inverse tags, exact lifts and integer
centers require soft O(m) classical bit work at log(N)=O(log m).
Alternatively the known exact frame recurrences generate target phases
incrementally; no matrix is constructed. The original source is generated
from full N, rather than substituting the universal catalog's two proof
inputs for the actual rows.

For each integer center w_l, transport the actual target to

    y_l=gamma^(t_l*N+delta_l-m^2*w_l).

For common I={-L,...,L}, L=ceil(Cm)+2, the exact residual is

    gamma^(t_l*N+delta_l)-alpha^(w_l+h)
      =alpha^w_l*(y_l-alpha^h).                       (E34)

Build the monic target polynomial F(T)=product_l(T-y_l), of degree
soft O(m), evaluate it at the O(m) points alpha^h, and multiply:

    B=product_(h in I) F(alpha^h)
      =(-1)^(R*|I|)*product_l product_(h in I)(y_l-alpha^h),
      R=number of retained centered targets.          (E35)

Fast product trees and multipoint evaluation divide only by monic
polynomials and work over Z/N without nonunit inversions. The work is
soft O(m) ring operations, or soft O(m*log N) bits, hence soft O(m) in
the standard N^(1/6) convention. Target unit powers, common baby powers,
and the public gamma projection add only soft O(m) bit work. Deterministic
Euclidean arithmetic and sorted lists suffice; no expected hashing,
hidden order, private factor, or interpolation through a nonunit is used.

On the actual infinite counterfamily every B in (E35) is a unit and
gcd(N,B)=1. All corresponding row norms are units too. This is a paid
acquisition with a rigorously false coverage contract, not a failure
merely to price source construction.

### 9.1. Fixed polylogarithmic width padding at the COMPLETE source

All source coordinates are already fully retained in (E12); no further
height padding is needed or claimed. Allow the windows to have width
W<=C*m*(log m)^B for fixed C,B, and put E=1+W/m=soft O(1).
The error in (E15) becomes O(E*m^3). In each width-m^2 Q subbox, the
K interval contains O(v*E) integers; the derivative variation remains
O(v). Thus (E21) is multiplied only by E. The global bound becomes
|K|=O(v*(m+E))=O(v*m), so own-tag integer forcing (E22) still holds.

For positive stationary own tags the squared defect is now O(E).
Consequently a<=C*(t+E) and the rho interval has width

    O(sqrt(E)/sqrt(t)+E/t).

The required weighted catalog estimates, with this enlarged cone, are

    sum t^(-1/2)=soft O(m^(3/4)+E*m^(1/4)),
    sum t^(-1)=soft O(m^(1/2)+E).                      (E36)

To prove them, split dyadic t at sqrt(m). Below that split, the distinct
integer-pair envelope is O(T^2+E*T); above it use the soft O(m) catalog
bound. For exponent 1/2 the low terms sum to O(m^(3/4)+E*m^(1/4));
for exponent 1 the E contribution is O(E*log m). The upper tail gives
respectively soft O(m^(3/4)) and soft O(m^(1/2)).

Multiplying (E36) by sqrt(E) and E respectively still gives soft
O(m^(3/4)); the +g/m term uses the same catalog cardinality. Hence
the positive stationary bound remains (E27) up to logarithms. Negative
cancellation has |a0-rho*t|<=C*E, the same cone and rho width O(E/t),
so (E28) is unchanged up to logarithms.

For rectangles, the level tolerance in (E29) becomes O(E). Rays with
U<=C*E number only O(E^2), and permitting every P for those rays costs
soft O(M^5), using their one Q class modulo m and (E9). For larger U,
the frozen band has tolerance O(E+U*g/m), and the discriminant argument
gives derivative >=c*U once the fixed threshold C*E is large enough.
The admissible P intervals have length O(X*(E/U+g/m)), plus a constant
integer endpoint count. The third estimate (E13) makes their weighted
sum soft O(sqrt(m)); thus (E32) also remains valid up to logarithms.

These bounds prove (E33) for every fixed polylogarithmic width padding.
For the paid norm use L=ceil(W)+2 in (E34)-(E35); both the number of
target factors and common evaluation points remain soft O(m). The
arithmetic failure therefore persists throughout this padded complete
Euclidean-source acquisition contract.

## 10. Exact scope and remaining frontier

The result includes the FULL native actual public Euclidean source,
all convergents and intermediate division slots, both signs, original
centered lifts, literal m, all false tags, arbitrary full-N adaptive
selection/reordering/subsets within that source, and both hidden fields.
All actual coordinate sizes up to m-1 are covered. Finite products and
certified-unit multiplicative cancellations among these residuals remain
units. A true quadratic root in these original windows would imply the
same actual collision, so exact per-row quadratic extraction cannot
restore covered factor information there.

The universal catalog is the precise source restriction. The complete
height-m coordinate BOX has Theta(m^2) distinct rays and is NOT covered
by the soft-linear catalog argument. Arbitrary legal rays not emitted
by actual Euclid, polynomially wider windows, arbitrary new centers,
new additive pivots, companion differences and source-specialized
implicit scalar queries remain outside this theorem. The source-specific
carry-correction channel under parallel investigation needs its own
long-interval acquisition and coverage proof.

The preceding native hit leaf proves finite hit identities, two-tag
roots and false carry/state uniqueness. The fresh finite universal-ray
leaf proves nine source theorems with two computable finite catalog
definitions, including the two-input slope cover and the bound
|C_m|<=16*m*(floor(log_2 m)+1)^2. This checked bound is slightly looser
than the classical constant 8 in (E11), which additionally divides the
two-center packet occurrence count by two; both give the same soft-linear
catalog bound. The catalog constructors supply no factorization runtime.
This full asymptotic theorem and paid norm cost remain classical; no
published analytic assertion was imported as a Lean axiom. This closes
one further concrete full-source acquisition route and does not prove a
guaranteed one-sixth factorization algorithm, the all-input bit-time/memory
composition, or a general factoring no-go.
