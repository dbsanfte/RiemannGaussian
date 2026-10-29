# Retrospective hybrid: uniform factor tags from torus first variations

26 October 2026. This addresses the user's request to revisit earlier
representations against the weaker information requirement. The successful
handoff is arithmetic provenance plus a weaker observable plus the restricted
lattice consumer. **The observable has not been acquired in soft O(K).**
This is a uniform acquisition target, not a complete faster factorer.

Two versions are useful. The existing short weighted family tolerates
multiple hits after separating content classes. A pair of explicit monic
families gives a simpler first-order target with no hit-count search. The
latter is developed completely below. Neither imports a QRH orientation
promise or asserts that a scalar-clock alias labels a factor.

## 1. Keep the actual torus preparation and modulus

Use the old symmetric prepared torus branch, with modulus denoted K to
distinguish it from the current pure 3-power scalar modulus:

    N=P Q, P<Q, N<=K^6, K~N^(1/6), H=K^2, P,Q>16H.

Its previously paid discriminant D has Jacobi(D,N)=-1. In
`B=(Z/N)[tau]/(tau^2-D)`, let W be the supplied norm-one unit, beta the
supplied scalar unit, pi=beta*W and barpi=beta/W. The scalar and torus
orders are odd, K-rough and greater than 16H at both primes. The actual
coupled short-order screen supplies unit differences for q=pi^H through
16H or already returns a factor.

At the unique nonsplit prime R, which can be P or Q, the beta and W
orders divide R-1 and R+1 and are coprime. Therefore

    ord_R(pi)>256H^2,
    pi^R=barpi, barpi^N=pi^(N/R).

The scalar base used by HH is beta, not pi. Its projected order guard
holds because q_s=beta^H has both orders greater than 16H. For every
n|K, q_s=(beta^(n^2))^(H/n^2). Thus the new HH proof extends verbatim
to this conductor-aware K; it did not require K to have only factors 2,3.

All of this preparation is prior credit from the journal's
[complete signed-weight construction](/home/dbsanfte/riemann/formal/docs/semiprime-factorisation-investigation.md:43815).
Its discriminant scan already uses the unconditional composite-character
Burgess/Lau–Wu bound below the sixth exponent. Rechecking
[Pollack Theorem 1.1](https://arxiv.org/html/1508.05035) and
[Lau–Wu Theorem 1](https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf)
does not constitute a new discriminant supplier. The known conductor and
the actual preparation costs remain in the ledger.

## 2. Two nonaxis monic families supply uniform unique-hit provenance

For each unit j in [1,K), acquire both coefficient pairs

    A: b=1, a=[N*j^(-2)]_K,
    B: a=1, b=[j^2*N^(-1)]_K.

All displayed nonconstant coefficients lie in [1,K); every a is a unit
modulo K. In either family a*j^2=b*N mod K. Define actual integers

    D_j=(a*j^2-b*N)/K,
    t_j=[D_j*j^(-1)]_K,
    ell_j=[-2a*j+K*t_j]_H, centred in [-H/2,H/2),
    y_j=pi^(ell_j)*barpi^(a+b*N).

For f_j(X)=aX^2+ell_j X+bN, direct substitution gives
`f_j(j)=0 mod H` and `f'_j(j)=0 mod K`. These are the actual phases;
neither the old character-dependent plus roots nor an assumed swapped
sign is substituted. The two root lists cost soft O(K).

Family A is the good family if the nonsplit prime is P. Family B is
good if it is Q. In the good family, EVERY row satisfies, for R the
nonsplit prime and S=N/R,

    0<T_j=aR+bS<=K*P+Q<17H^2/16.

Here P<=sqrt N<=K^3 and Q=N/P<K^4/16. At the own tag j=R mod K,
`I=(T_j+ell_j)/H` is an integer. Positivity and the displayed bounds
place it in [0,2H]. Frobenius gives y_j=pi^(T_j+ell_j), so the row
hits q^I. This proves coverage on one of the two families for EVERY
prepared input, with no knowledge of which family is good.

Conversely, any good-family hit y_j=q^i, 0<=i<=2H, implies

    ord_R(pi) divides T_j+ell_j-H*i.

The integer on the right has magnitude less than 4H^2, hence is zero.
Consequently f_j(R)=0 mod H. Write x=R-j. The same polynomial is

    f_j(R)=a*x^2+K*c*x+K^2*d

for integers c,d. If a prime l dividing K had v_l(x)<v_l(K), then,
because a is a unit, the first term would have uniquely lowest valuation.
This contradicts divisibility by K^2. Thus K divides R-j: ONLY the
actual unit tag can hit. The q-order guard and interval length<16H
then give ONLY ONE hit index for that tag.

This restores a uniform unique-hit promise by changing the monic family
in the larger-nonsplit case. The old smaller-nonsplit theorem alone did
not authorize that step. It is a combination of existing signed-row
arithmetic and the complementary monic choice, not new point preparation
and not a faster query evaluation.

## 3. Only two first-order coefficients are needed

Choose any public n|K with n>=K^(1/3), and set w_j=[j]_n. For each
of the two families define the finite marked product

    Z(delta,Y)=product_(j unit mod K, 0<=i<=2H)
                 (1-y_j/q^i + delta*(1-Y*w_j)).

Ask for just the two actual values in B

    V=[delta] Z(delta,0),
    U=-[delta*Y] Z(delta,Y).

At the good nonsplit prime the unique hit contributes
`delta*(1-Y*r)`, r=R mod n. Every other leaf has nonzero constant term.
Thus the local first slice is `A*(1-Y*r)`, A nonzero, and

    V=A != 0, U=A*r.

This holds regardless of the behavior at the other prime. It needs no
full hit polynomial, identified row, collision index, higher Hasse depth,
or unique hit at both primes. One of the two pairs is guaranteed to have
this one-prime property. The other pair may be arbitrary, provided its
acquisition attempt has a bounded cost.

### Paid validation and recovery

Compute gcd(N,Norm(V)). A proper gcd factors. If it is N, this attempt
may fail; that outcome cannot occur for the good pair. Otherwise invert V
using its unit norm and write U/V=A0+B0*tau. At the good prime B0=0.
A proper gcd(N,B0) factors; gcd 1 rejects this attempt; gcd N makes
the ratio globally a base scalar A0.

For 0<=r<n compute gcd(N,A0-r). A proper gcd factors. A global zero
gives a candidate r which, on the good attempt, is the actual residue of
the nonsplit factor. Keep only unit r mod n. The scan costs soft O(n),
at most soft O(K). Complement it by N/r mod n and apply the restricted
HH consumer; it handles either factor. There are only two family attempts,
so all validation, candidates and HH recovery remain soft O(K).

No denominator is inverted before its norm is certified. A wrong pair
can return only a checked factor, a bounded candidate list or failure.
The good pair ensures the joint attempt succeeds if both pairs are
actually supplied. No generic beta-annihilator extractor is required.

## 4. What acquisition still costs

These first-order values can be computed by the existing product engine
over `B[delta,Y]/(delta^2,Y^2)`, a constant-rank algebra. Each marked
leaf is a known unit prefactor times an ordinary geometric-clock leaf:

    1-z+delta*(1-Yw)
      =(1+delta*(1-Yw))
         *(1-z/(1+delta*(1-Yw))).

Its inverse and row prefactors are explicit in the truncated algebra.
The initialized baseline therefore costs

    soft O(K+sqrt(K*H))=soft O(K^(3/2)),

with constant precision overhead. This is slower than the best existing
short weighted complete query, soft K^(5/4). We retain that better
algorithm; the monic version is a potentially easier weak-output target,
not an algorithmic speedup or a reason to replace the current factorer.

The exact clock-endpoint recurrence cancels the entire interior
`delta*(1-Y*r)` factor. Its cheap boundary values do not supply U/V.
The retrospective found no already acquired old coefficient or moment
that equals these two first-order values. A new ratio/first-variation
algorithm is still necessary to finish this hybrid at soft O(K).

## 5. Shorter-clock alternative: content sectors, including axes

The existing weighted Gauss family has h=O(K^(3/2)), at most K rows
per public factor bin, and exact-integer hit provenance at the nonsplit
prime in its correct bin. In a nonaxis row let

    g=gcd(a,K)=gcd(b,K), n_g=K/g.

Its Gauss bound gives |ab|<=K/sqrt(3), so g<=sqrt K. The valuation
argument with a possibly nonunit proves every hit satisfies
R=j mod n_g. Thus ALL hits in one content sector have the SAME tag r.
Marking by w_j=[j]_(n_g) gives first local slice A(1-Yr)^d, and the
two values `V=d*[Y^0]slice`, `U=-[Y]slice` again have ratio r.
There is at most one hit per row, so d<=K<R, making d a unit at the
good prime. This is genuinely a many-hit consumer.

Axes are not a gap in THIS torus family. A shortest axis vector is
(+/-K,0) or (0,+/-K). Its exact phase gives respectively

    f_j(R)=+/-K*R*(R-j) mod H,
    f_j(R)=+/-K*N*(1-R/j) mod H.

Since R,N,j are units modulo K, an exact hit forces R=j mod K.
The axis sector has at most one good-field hit and uses the full tag.
This argument depends on the torus's exact-integer provenance; it does
NOT relabel accidental hits of the scalar axis product as factor tags.

Across content sectors, scan each weak pair through its n_g possible
tags. The total is at most K*sum_(g|K)(1/g)<=K*(1+log K), plus the
axis scan. Lift each returned residue to its g residues modulo K.
Over the bins the total palette is at most

    O(log N)*(1+sqrt K*tau(K)).

For example the elementary uniform divisor bound
tau(K)<=C_epsilon*K^epsilon with epsilon=1/12, and log N=O(log K),
bound this by C*K^(2/3) with a fixed constant C. A single shared HH
call at n=K, with its fixed interval constant increased by C, therefore
costs soft O(K). There is no separate full HH call for every false sector.
At least one correct-bin sector supplies a true factor tag if its weak
pair is acquired. This removes both the unique-hit and smaller-prime
orientation requirements from this sector-based output target.

The cost to acquire ALL those first-slice pairs is still additional.
The existing finite-jet algorithm pays the whole query and its precision
overhead; the improved decoder does not eliminate that payment. This
version keeps the shorter clock but has a harder leading-slice request.
The two-monic version has a longer clock but requests only first order.
That tradeoff, proved for uniform coverage, is the substantive result of
the retrospective. Neither version yet meets the whole-family acquisition
milestone.
