# A paid non-parity digit-mask linear form for q-Pochhammer coefficients

24 October 2026. Separate scratch mini-task. Positive result: ONE explicitly specified coefficient mask from one fixed Schönhage tensor leaf is acquired in soft sqrt(b), including all starts, when its radix dimension is of order b and the native short q-differences are units. For that fixed mask, all consecutive geometric giant-clock arguments cost soft(sqrt(b)+R). An explicit first non-parity mask has an even shorter formula. This does not acquire all leaf encodings, outer row sums, requested output box sums, or the full factoring query.

## 1. Exact input and the actual digit masks

Let A be R=Z/N or the acquired constant-rank quadratic algebra over R. A ring multiplication costs a constant number of residue operations. The supplied q is a unit, and every 1-q^r, 1<=r<=b, is an ACTUALLY certified unit. This is the native short-difference contract for b<=C; it is not deduced from a characteristic-zero point. All inversions below are only of those proved unit products. In the native application b and the radix dimension D are polynomially bounded in N, so digit/exponent metadata have O(log N) bits; outside that regime their actual bit lengths must also be charged. For the quadratic algebra, a unit inverse is acquired by its explicit norm and conjugation, with the scalar gcd/extended gcd paid.

Set

    P_b(X)=product_(i=0)^(b-1)(1-q^i X)=sum_(a=0)^b c_a X^a,
    f(n)=product_(r=1)^n (1-q^r), f(0)=1.

The coefficient identity is

    c_a=(-1)^a q^[a(a-1)/2] f(b)/[f(a)f(b-a)].       (1)

It is the q-binomial polynomial identity, with its denominators now explicit acquired units. No division by c_a or by a final mask value is required.

The task's actual inner masks, communicated from the checked Schönhage section2.2 encoding, have the following form. Flatten p11,p12,p21,p22 to digit basis e0,e1,e2,e3. A LEFT tensor digit is one singleton e_d or one of -(e0+e2), -(e1+e3); other listed slots are zero. A RIGHT digit is one singleton or -(e0+e1), -(e2+e3); other listed slots are zero. Fix ONE tensor leaf Q of m such digit choices. Its coefficient weight is

    w(a)=product_(s=0)^(m-1) w_(s,digit_s(a)),

with radix4 digits. Every nonzero digit support has size one or two. Thus the actual support

    S_Q={0<=a<=b : all required digit entries are nonzero}

has t<=2^m elements. This is an exact branching count, not an assumption of low Fourier support or of digit tensor rank for c_a. If any digit is zero, the leaf is zero and is returned immediately.

The radix dimension D=4^m must hold every requested coefficient index. If D=Theta(b+1), then t<=sqrt(D)=O(sqrt(b+1)). A missing boundary coefficient at a=D must NOT be discarded: either choose enough digits for b+1 indices, or handle that boundary separately with its actual weight. Choosing the smallest radix dimension at least b+1 changes the size only by a constant factor. If an encoding instead fixes D much larger than b, the proved bound is soft(sqrt b+t+m), not automatically soft sqrt b.

Enumerate S_Q by the actual at-most-two digit branches from the MOST significant digit, carrying its known sign/weight and pruning a prefix when its least feasible completion exceeds b. The interval cutoff leaves only one boundary path, so this uses O(m(t+1)) elementary branch work, soft(t+m) in the native logarithmic-digit regime (in particular D=Theta(b+1)). For these particular masks all pair entries have the same minus sign, so the sign on the supported indices is the fixed (-1)^(number of pair digits); the algorithm may also simply multiply the actual weights at cost O(tm). No Pochhammer coefficients have been factorized by their digits.

## 2. Acquired batch-prefix lemma, proved over the ring

For ANY explicitly requested T indices n_l in [0,b], all f(n_l) can be acquired in

    soft(sqrt(b+1)+T)

ring/bit work, with usual log N and log b factors. The following construction pays all starts and does not need a hidden field or an arbitrary-prefix oracle. Bounded b<=2 is handled directly.

Choose d as the smallest power of two at least sqrt(b+1). For b>=3 it satisfies d<=b and sqrt(b+1)<=d<2sqrt(b+1). Define actual short polynomials

    B_h(Y)=product_(r=1)^h(1-q^r Y),
    B_(a+h)(Y)=B_a(Y)*B_h(q^aY).                    (2)

Starting from B_1=1-qY, acquire and store every dyadic B_(2^s) through h=d. Polynomial multiplication and coefficient scaling in (2) cost soft d in total, because their sizes form a geometric sequence. Their aggregate stored coefficients also cost O(d). All required q powers have O(log b)-bit exponents and are computed, not supplied as evaluation oracles.

Let G=floor(b/d). Acquire the actual G points q^(dg), 0<=g<G, by a power walk. Monic multipoint evaluation of the ONE degree-d B_d gives all full-block values

    U_g=B_d(q^(dg))=product_(r=1)^d(1-q^(dg+r)).

Compute all prefix products A_g=product_(h<g)U_h for 0<=g<=G. Then A_g=f(dg). This costs soft(d+G)=soft sqrt b. Include q^(dG) if needed for selected last-block starts. Monic evaluation divisors do not require distinct target points or inverses of values.

For each requested n=dg+r, 0<=r<d, partition its residual interval of r factors into dyadic blocks by the binary digits of r. A block of length 2^s starting after offset o contributes the ACTUAL value

    B_(2^s)(q^(dg+o)).                              (3)

All starts dg+o are explicit integers in [0,b], computed with each request's labels; each factor index used by that block is <=n<=b. At each size 2^s there are at most T requested values (3). Acquire their q powers, then perform ONE monic MPE of the stored B_(2^s) at all these actual points, costing soft(2^s+T). Summing over s<log2 d gives soft(d+T), with the logarithmic factor on T suppressed. Multiplying each requested residual's values and its acquired A_g yields f(n).

This proof includes the potentially unaligned tails: they are not T independent length-d scans. It also includes all full-block prefix products, the entire dyadic short-polynomial table and O(T log b) actual tail starts. Repeated requested indices/starts are harmless and can be deduplicated, but no such deduplication is needed for the cost.

No division is used anywhere in this prefix lemma. It remains an exact value algorithm even if a factor vanishes. The separate promised short-unit guard makes its outputs units for the coefficient use in (1). A saturated auxiliary f(b) would not itself be an original collision witness if that guard were absent; no new decoder is being assigned to it.

## 3. Execute ONE full masked linear form in soft sqrt b

The desired actual leaf form is

    L_Q(x)=sum_(a=0)^b c_a x^a w(a).

Acquire the requested prefix-index set

    {b} union {a,b-a : a in S_Q}.                   (4)

It has at most2t+1 entries, including zero and repeats. Apply Section2's initialized prefix algorithm; its cost is soft(sqrt b+t). All denominator products in (1) are units by the supplied guard; compute their inverses by actual fixed-rank arithmetic. Acquire the scalar powers q^[a(a-1)/2] and x^a by binary powering for every a in S_Q, at soft t additional cost. x may be zero or a nonunit: no inverse of x is used. The exponents have O(log(b+1)) bits, and the a=0 term is handled as x^0=1.

Compute every selected coefficient by (1), multiply its actual x power and digit weight, and sum. The total is

    soft(sqrt b+t+m),

hence soft sqrt b for a fixed-leaf tensor dimension D=Theta(b+1). Only O(sqrt b) short-polynomial coefficients and the t requested c_a are acquired. No degree-b coefficient vector, no field interpolation pivot and no low-rank digit decomposition of the Gaussian-binomial coefficient tensor is assumed.

This is a complete evaluation of the specified mask, including zero outputs. Its unit divisions precede the final linear combination; a zero/nonunit output is returned as a value and is not divided away. This is a standalone linear-form primitive. No claim is made that its zero is an original row/index factoring witness without the separate correct reduction.

The construction uses standard product trees, monic MPE and block doubling, with its full ring-safe initialization proved here. It is consistent with the batch-index q-holonomic viewpoint, but does not depend on importing a field theorem or omitting its requested starts.

## 4. The first explicit non-parity mask

Take m>=2. Set the LOW radix4 digit to the left singleton e0, the next digit to the actual left column-pair mask -(e0+e2), and every higher digit to e0. The supported coefficient indices are EXACTLY a=0 and a=8, each with weight -1. This is not a global parity filter: higher even indices outside that actual leaf are excluded too.

For b>=8 the exact value is

    L_Q(x)=-1-c_8 x^8,
    c_8=q^28 * product_(r=0)^7(1-q^(b-r))
                    / product_(r=1)^8(1-q^r).       (5)

For b<8 it is just -1. The first coefficient is c0=1; the sign and q exponent in c8 follow from (1). All eight denominator factors are certified units. Acquire q^b by binary powering and the eight indicated numerator factors, compute the eight-factor denominator and its actual inverse, then x^8. This is O(log(b+1)) ring operations plus a constant number of fixed-rank inversions, with no b-coefficient expansion. At b=8, (5) correctly gives the leading coefficient q^28.

One can instead take both lowest digits to the left pair mask -(e0+e2) and all higher digits to e0. Its support is {0,2,8,10} with positive weight. The same constant-many coefficient formula computes that first two-free-bit non-parity form in O(log b); this is another symbolic specialization of the proved algorithm, not numerical evidence for a generic tensor-rank claim.

The general fixed-Q result of Section3 is proved by support enumeration and the batch-prefix lemma, not extrapolated from (5).

## 5. For ONE fixed mask, batch the actual geometric giant clock too

There is an additional initialized primitive. Suppose the required arguments are the ACTUAL consecutive giant clock

    x_g=x0*Q^g, 0<=g<R,

where Q is supplied (in the native cut Q=q^(-b), x0=1; q inverse is a certified unit). After acquiring the t selected coefficients once, set

    d_a=w(a)c_a x0^a, lambda_a=Q^a.

All d_a and lambda_a cost soft t. Define the formal generating series

    sum_(g>=0)L_Q(x0 Q^g) T^g
       =sum_(a in S_Q) d_a/(1-lambda_a T).           (6)

Acquire its numerator and denominator by an actual fraction product tree: leaves (d_a,1-lambda_a T); merge (N1,D1),(N2,D2) as

    (N1 D2+N2 D1, D1 D2).

The aggregate coefficient work is soft t. The final denominator has constant coefficient one even if some lambda values coincide. Acquire its inverse series through T^(R-1), multiply by the numerator and return ALL R requested clock values. This costs soft(t+R), by the standard constant-one series inversion circuit. Repeated clock bases, cancellations and zero d_a cause no unit-pivot issue. No eigenvalue/Vandermonde inverse or missing starting amplitude is used.

Together with Sections2--3, ONE fixed mask at all R consecutive giant arguments costs

    soft(sqrt b+t+m+R),

or soft(sqrt b+R) in the stated tensor dimension. R output values and their complete coefficient/series initialization are explicitly charged. This is not a theorem for R arbitrarily distant requested clock indices without paying their own evaluation method.

For the mask (5), this reduces to the concrete two-base sequence

    L_Q(x0 Q^g)=-1-c_8 x0^8 (Q^8)^g.

Its two starts, constant-order recurrence or direct power walk are actual. No higher-position mask is claimed to have that same fixed order; the general initialized denominator in (6) can have degree t.

## 6. Exact boundary of this positive result

Parity-only combinations P_b(x)+/-P_b(-x) were already known. This result handles the actual non-parity singleton/pair DIGIT masks of one fixed tensor leaf by their sparse support, without assuming the q-binomial coefficient tensor factors like a pure geometric coefficient tensor. Arbitrary weights on all four digits may have support of order b, in which case the proved budget becomes soft b. A higher-position periodic bit mask can also have growing Fourier support; the constant-cost parity identity is not a justification for it.

The output here is ONE fixed-Q coefficient form, or its explicitly sized consecutive giant-clock list. It does not acquire every Q simultaneously. Taking a union of requested support sets may grow to b coefficients, and the corresponding cost must then be paid. Outer row-band sums can mix many different Q and shifted coefficient indices; requested output boxes and the product of native row/seed factors are separate nonlinear contractions. No bound for those operations is supplied merely by (4) or (6).

| Actual operation | Paid work | Delivered object |
|---|---:|---|
| One fixed leaf support/weights | soft(t+m) | actual t<=2^m supported indices |
| All dyadic short B polynomials and full-block starts/prefixes | soft sqrt b | acquired coefficient vectors and prefix products |
| T arbitrary requested factorial prefixes | soft(sqrt b+T) | actual f(n_l), including unaligned tails |
| All c_a, a in one leaf support, and L_Q(x) | soft(sqrt b+t+m) | exact non-parity masked value, zero safe |
| First mask (5) | O(log b) ring work | actual two-coefficient form |
| ONE fixed mask on R consecutive giant arguments | soft(sqrt b+t+m+R) | every returned clock value, starts included |
| All leaf encodings, outer sums, box sums or terminal norm | NOT acquired here | no whole-query/factoring bound claimed |

This is a positive initialized sub-b coefficient-mask primitive in the stated sparse-leaf regime. Whether the larger implicit tensor encoding uses few enough of these forms and can contract its required outputs with the original zero-safe factoring witness remains an unfinished separate task.
