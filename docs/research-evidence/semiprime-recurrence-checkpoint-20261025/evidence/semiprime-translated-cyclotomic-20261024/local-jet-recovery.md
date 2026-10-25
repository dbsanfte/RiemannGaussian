# One supplied native local raw jet suffices for soft-m recovery

24 October 2026. Conditional positive strengthening, not a rate advance. No repository changes, examples or backend claim. The raw jet is a strictly stronger UNACQUIRED input; the theorem below does not construct it from a reduced translated row and does not acquire/process all rows in soft m.

## Actual source pins

Paths below are in /home/dbsanfte/riemann/formal/docs/research-evidence/ unless absolute.

| Source | SHA-256 | Used contract |
|---|---|---|
| semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md | 4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46 | prepared original beta, actual native rows/offsets, own collision, bounded global-leaf recovery |
| semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md | a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be | optional nonzero short-annihilator fallback, soft N^(31/192) bits |
| semiprime-cyclotomic-row-cancellation-20261016/README.md | 992e31ea5ece408e448dba91771a1616228b4629668552960c15311c9aafad6e | sigma-row definition and original own-tag Frobenius identity |
| /tmp/semiprime-translated-cyclotomic-20261024/literature-and-exponent.md | a5aec97ae267a4d1b242aa38a09bd52176c895a52cf18d43f6a2d9b155928ac5 | actual raw g² lift extraction and natural mixed-lift failure |

These actual bytes were read and hashed. No new source theorem is presumed compiled into Lean.

## Precise stronger-input contract

Use N=P Q, distinct odd primes, the original prepared beta, prime m and d=m² from the pinned setup. In particular N<=m⁶, N>256m⁴, both primes exceed 16m², beta has odd local orders >16m², coprime local orders and global order >256m⁴. Keep the ORIGINAL beta, actual row label j, and integer a_j, ell_j, delta_j=a_j+ell_j with -3d<=delta_j<=d. Let L=2m²+2; then L<P,Q.

Set g=X^m-1, A=(Z/NZ)[X]/g, u=beta+X. A single acquired polynomial H_j of degree <2m is supplied modulo g². Its reduction f_j modulo g is promised to be the ACTUAL translated row

    T_j=u^ell_j*(sigma_j u)^a_j*sigma_(j^-1)(u^N)

as a global element of A. This is a unit. In addition promise that for ONE unknown prime factor P of N and ONE unknown I in [0,L),

    H_j=u^(dI) modulo (P,g²),                         (1)

and that this is the ORIGINAL native own pair j=P modulo m,

    dI=a_j P+Q+ell_j.                                (2)

Neither P nor I is supplied to the algorithm; j is supplied and promised to have this property. The second promise is essential for reusing the original beta recovery channel. An equivalent weaker recovery contract may replace (2) by the explicit same-prime original collision

    beta^(N+delta_j-dI)=1 modulo P,

with its retained bounded native metadata and positive nonzero short exponent. Merely promising (1) for an arbitrary translated row or arbitrary algebra exponent, without that original-beta connection, does NOT suffice for the final recovery below.

The algorithm may return a factor early through a guarded scalar inversion. Outside these promises no claimed fast success guarantee applies. In particular this is not an oracle to identify an own row among all j.

## Step 1: acquire a local scalar index jet

Acquire u inverse by the explicit beta^m+1 certificate. It is a unit by the prepared local order screen (also by odd local order), so only a certified scalar inverse is needed. A known unit modulo g has a unit lift modulo g² as well.

One may acquire f_j inverse explicitly, avoiding arbitrary quotient-algebra pivots: compute u^N and u^-N, u^ell_j and u^-ell_j, and the corresponding positive/negative powers of sigma_j u, then apply the coefficient permutation sigma_(j^-1). Their product gives T_j and its inverse in soft m residue work for this ONE row. Comparing f_j to T_j is a paid O(m)-coefficient check. Alternatively guarded polynomial Euclidean inversion with final verification is lawful. All exponent lengths are O(log N); logarithmic powering factors are suppressed, not omitted.

Differentiate any representative of H_j and reduce modulo g. This is well defined: changing H_j by g²V changes H_j' by a multiple of g. Acquire

    w=d^-1*u*(H_j' mod g)*f_j^-1 mod g.               (3)

Every polynomial in this operation has degree O(m), so the work is soft m. By (1), modulo P it equals I*1. Write its canonical representative as

    w=s+sum_(r=1)^(m-1) w_r X^r.

Compute D=gcd(N,w_1,...,w_(m-1)). All nonconstant coefficients are divisible by P. Thus on the promise D is either a proper factor or N; D=1 is excluded. A proper D immediately factors N. If D=N, w is globally scalar and

    s=I modulo P.                                   (4)

Choose the canonical integer representative 0<=s<N. No translated q-order or scalar-image order has been used.

## Step 2: acquire and localize one scalar interval product

Compute

    V=product_(i=0)^(L-1)(s-i) modulo N.              (5)

This is genuinely acquired in soft sqrt L=soft m: choose b near sqrt L, build the monic B_b(X)=product_(r=0)^(b-1)(X-r), evaluate it by monic MPE at the explicit complete-block starts s-bt, multiply the values, and include the final short block. Only O(b+L/b) polynomial coefficients/points are acquired. No difference s-i or evaluation-point difference is inverted.

By (4), V is divisible by P. A proper gcd(V,N) factors. If it is N, split the public index interval. At each split compute child products by the same initialized constructor. Return a proper child gcd if found; otherwise retain a saturated child (a product of units cannot be saturated). Descend to a leaf. Costs along a path are soft sum_k sqrt(L/2^k)=soft sqrt L, including recomputation and gcds. No factor values or leaf index are free.

At a saturated leaf, s-i=0 modulo N for some acquired i in [0,L). Since 0<=s<N and 0<=i<L<N, the literal difference lies strictly between -N and N, so s=i as integers. Combining (4) with i,I<P gives i=I. This is interval uniqueness modulo P, not uniqueness of powers of translated q. A different Q-side interval root can only cause an earlier proper-factor split or the same globally saturated leaf.

## Step 3: retain original beta recovery at the recovered index

Use the original integer offset and recovered i to acquire

    K=N+delta_j-d*i,
    v=beta^K-1 modulo N.

The native identity (2) gives K=(P-1)(Q-a_j)>0. More generally the uniform retained bounds prove positivity for every original bounded row/index: K>=N-3d-d(L-1)>0 from N>256m⁴. Its binary length is O(log N). By the retained original collision promise and i=I, v is divisible by P. A proper gcd(v,N) factors N.

If gcd(v,N)=N, this is a GLOBAL ORIGINAL-beta bounded native leaf. Apply section 8 of the pinned uniform interface: with global beta order D_beta>256m⁴ and factor-sum bound P+Q<16m²+1+m⁴/16, divisibility forces

    P+Q=1+d*i-delta_j.

Acquire this integer, take the exact square root of its square minus 4N and recover/verify the two factors. This costs polylog N. It works for any original globally colliding bounded canonical leaf; no translated collision decoder is asserted.

Alternatively beta^K=1 with positive O(log N)-bit K satisfies the separately pinned short-annihilator theorem for the ORIGINAL beta, whose odd local orders exceed 16m². Its soft N^(31/192) bit cost is within soft m. No factorization of K or order of beta is supplied. This is an optional inherited fallback, not an annihilator-acquisition oracle.

## Complete ledger and limitation

| Operation | Paid cost | Guarantee/output |
|---|---:|---|
| Read one degree-2m H_j, retained row metadata | soft m | stronger supplied jet input |
| u inverse, one actual row and inverse | soft m residue arithmetic | explicit algebra units |
| Differentiate H_j, acquire w | soft m residue arithmetic | w=I modulo P |
| Gcd of all nonconstant coefficients | soft(m log N) bits | proper factor or globally scalar s |
| Scalar interval product and saturated descent | soft sqrt L=soft m residue arithmetic | proper factor or exact original I |
| Original beta leaf and bounded global decoder | polylog N bits | proper factor |
| Optional original-beta short annihilator | soft N^(31/192) bits | proper factor |

All residue operations at this precision cost soft log N bits, so the one-row conditional theorem costs soft(m log N) bits, customarily soft m on the sixth-root scale. It assumes no local/global order for q_cyc=u^(m²), beta+1 or beta^m+1. A LOCAL raw jet and its original-native connection suffice; a global raw-power equality is unnecessary.

The missing input is precisely the exponent-bearing local first-order jet (1). The natural mixed lift in literature-and-exponent.md fails (1) uniformly on its own prime by the unit discrepancy Q/u. The cheap etale lift has zero normal derivative. Neither initializes this theorem. Supplying or processing all m rows separately costs at least soft m² with the present construction, and the theorem does not select the promised own row. Thus this conditional positive recovery closes the factor-witness objection for one supplied native local jet, but yields no new whole-query or all-semiprime factoring exponent.

### Whole-family scalar interval acquisition is still unpaid at soft m

Even granting the O(m) scalar constants s_j as already acquired in soft m, the local promise is only s_j=I modulo one hidden prime for the successful row. It does not turn these into globally known bounded integers I_j. Searching all supplied scalars against [0,L) therefore asks for

    product_j product_(i<L)(s_j-i).

The initialized additive many-target constructor builds a common length-b factorial polynomial and evaluates it at J*ceil(L/b) explicit shifted row starts, plus paid tails. Its cost is soft(b+JL/b+J), optimized to soft(J+sqrt(JL))=soft m^(3/2) at J~m,L~m². Thus even free shared scalar acquisition would leave an old whole-family interval-product bottleneck unless an additional shared operation or selector were supplied. Actual global raw powers would reveal global bounded indices cheaply through their jets, but that is a stronger, uninitialized promise. The local-jet theorem above is not by itself a new sufficient soft-m whole-query interface.
