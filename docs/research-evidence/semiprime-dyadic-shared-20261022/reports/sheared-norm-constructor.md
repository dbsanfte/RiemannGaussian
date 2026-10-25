# Deterministic known-support construction of sheared cyclic norms

This is an actual near-linear constructor for ONE shifted norm denominator. It does not acquire all affine weighted numerators or the collision query.

Let the scalar ring be Z/NZ with a PUBLIC unit eta whose order modulo EVERY prime divisor of N exceeds 16m². The prepared gamma may be used as eta. Let p be a power of two with p<=m. For any integer s (including negative s), define the Laurent-polynomial norm

 Q_p(Y,z)=Norm_(X^p=Y)[(X+gamma)²−z*t²*X^s*(1+gamma X)²].       (1)

Its exact symbolic representation can be acquired in soft O(p) bit work. An optional z-prefix can only reduce the cost. Exponent metadata uses O(log N) bits in the native regime; coefficient arithmetic is modulo N.

## Support invariant

In the coefficient z^j of the product over all p conjugates, j factors contribute the X^s term. The remaining polynomial factors each have X-degree at most two. Thus all X exponents lie between s*j and s*j+2p. Norm invariance forces the surviving X exponents to be multiples of p. Therefore

 Q_p(Y,z)=sum_(j=0)^p sum_(e integer, s*j/p<=e<=s*j/p+2) c_(j,e) z^j Y^e.  (2)

There are at most THREE possible e per j, including zero coefficients. This remains valid over the composite ring: it follows equivalently from the explicit dyadic norm recurrence below, so no root extraction or cancellation by a nonunit is used.

## Graeffe recurrence and Laurent normalization

Start Q_1(X,z)=(X+gamma)²−z*t²*X^s*(1+gamma X)². Given Q_p(X,z), form Q_p(X,z)Q_p(−X,z); keep the even powers of X and replace X² by Y. This gives Q_(2p)(Y,z).

At a multiplication stage p<=m/2, let a=floor(s/p), r=s−a*p, so 0<=r<p even if s is negative. Normalize each monomial z^j X^e by storing exponent e−a*j; this is the integral shear Z=z*X^a. By (2), the stored X exponent is between (r/p)j and (r/p)j+2, hence is NONNEGATIVE and at most j+2.

The conjugated factor Q_p(−X,z) in this SAME normalization is obtained by multiplying coefficient (j,e_stored) by (−1)^(e_stored+a*j). This explicitly retains the parity of the removed Laurent shear. Multiplication produces z-degree at most 2p, and stored X exponents satisfying

 (r/p)j<=e_stored<=(r/p)j+4.                            (3)

Thus a KNOWN candidate output support has at most 5(2p+1) monomials. No unknown sparse interpolation support is being guessed. After recovering these coefficients, translate e_actual=e_stored+a*j. Odd e_actual coefficients cancel identically by conjugation; retain the even ones and set e_new=e_actual/2. This exactly reinstates the Laurent exponents required for (2) at 2p. They may again be negative; the next stage independently renormalizes them.

## Safe Kronecker span at EVERY product

Before the parity filter, encode a normalized monomial z^j X^e by exponent

 E=j+L*e,  L=2p+1.

Because 0<=j<=2p, this encoding is injective on the entire candidate support, including all product terms. From (3), e<=j+4<=2p+4, so

 0<=E<=2p+(2p+1)(2p+4)=4p²+12p+4
       <=m²+6m+4<=5m²,                               (4)

for m>=2 and p<=m/2. Thus the span of ALL exponents participating in any multiplication is at most 5m², strictly below the assumed local order 16m². The initial Laurent shear and the post-filter Laurent output do not enlarge this bound: only normalized exponents enter interpolation; their removed shifts are exact integer metadata. One may simply use the full bound (4) even if a prefix truncation is requested.

## Known-support sparse multiplication over Z/NZ

Let S be the candidate support (3), encoded by its distinct E values; T=|S|=O(p). Put alpha_E=eta^E. These nodes are units and every pairwise difference is a unit: a nonunit difference would imply eta^(E−E')=1 modulo a prime divisor, contradicting 0<|E−E'|<=5m²<its order.

To multiply two sparse polynomials whose product support is contained in S:

1. Evaluate each encoded input at eta^i for i=0,...,T−1. These values are the power sums sum_E c_E alpha_E^i. They are computed in soft O(T) using product-tree rational summation sum_E c_E/(1−alpha_E*z), followed by series expansion to precision z^T. Missing input monomials have coefficient zero. This is the standard transposed-Vandermonde operation, not evaluation in time proportional to the ambient exponent span.
2. Multiply the two value sequences pointwise. They are the first T moments of the UNKNOWN product coefficients on the KNOWN support S.
3. Recover coefficients by an explicit inverse transposed Vandermonde. Let D(z)=product_E(1−alpha_E z), and M(z) be the degree<T moment prefix. Form P(z)=D(z)M(z) mod z^T. Then P=sum_E c_E product_(E'!=E)(1−alpha_(E')z), so

 c_E=P(alpha_E^(-1))/product_(E'!=E)(1−alpha_(E')/alpha_E).

Fast multipoint evaluation computes all numerators and denominator derivative values in soft O(T). Every denominator is a checked/proved unit. Product-tree construction, series inversion with D(0)=1, and multipoint evaluation require no field factorization. The recovery denominators may be inverted in a batch with a unit product, or by individual fast extended gcd calls within the same soft bound.

No restriction on eta^(E*i) beyond modular arithmetic is required: Vandermonde invertibility depends on the NODE exponent differences E−E', whose span is bounded by (4). All large powers are reduced modulo N and have logarithmic exponent bit size.

## Total construction cost and limitations

Each Graeffe stage costs soft O(p). The p values double, so their sum is O(m). The complete Q_m, or any desired prefix, is therefore acquired in soft O(m) bit work and O(m) coefficient/exponent storage. Its sheared support has O(m) entries, even when its ordinary rectangular bidegree suggests quadratic size.

This proves a genuine arithmetic advance over dense expansion. It does NOT say that m different shifted norms cost soft O(m): they have different s and must be shared or prefix-truncated with a separate total-branch proof. Nor does norm construction supply the linearized weighted numerator. The open contraction requires the affine numerator branches and their coefficient modulations; those remain explicitly outside this theorem.

## Addendum: a fixed spatial numerator is also constructed near-linearly

Let U(X) be a supplied polynomial of degree L<=2m, independent of z. Work over dual numbers epsilon²=0 and construct

 Norm_(X^p=Y)[F(X,z)+epsilon U(X)] = Q_p+epsilon V_p,
 F=(X+gamma)²−z*t² X^s(1+gamma X)².

There is exactly one U insertion in each tangent term. In coefficient z^j, its total original X exponent lies in

 [s*j, s*j+2(p−1)+L].

After division by p, tangent support therefore has width <=2+L/p and only O(p+L) candidate monomials. The dual-number Graeffe recurrence is

 Q_(2p)=even_X[Q_p(X)Q_p(−X)],
 V_(2p)=even_X[V_p(X)Q_p(−X)+Q_p(X)V_p(−X)],

with exponents halved after the even filter. The same integral shear floor(s/p) is used for BOTH coordinates, and the same actual-exponent parity rule applies.

At a product stage the tangent normalized exponent is at most j+4+ceil(L/p), with 0<=j<=2p. Using E=j+(2p+1)e gives

 E<=4p²+12p+4+(2p+1)ceil(L/p)
   <=4p²+14p+5+(2+1/p)L
   <=m²+13m+5<=10m²<16m²

for m>=2, p<=m/2 and L<=2m. Thus the existing prepared separation cap also pays the tangent products. Candidate tangent support has O(p+L) slots; evaluation/interpolation handles each of the two cross-products in that bound. Summing geometric p and the repeated L term over log m levels gives soft O(m+L) total work. The input direction U is supplied ONCE, not regenerated per output coefficient.

The ratio V_p/Q_p is the relative trace of U/F. At Y=1 and p=m, choosing U=B(X)g(X) gives the fixed-weight power-trace generating function for f(X)/g(X), where F=g−z f. The proof extends without change to g,f supported in two fixed-width intervals separated by an arbitrary integer shift s. In particular monomial shifts of the degree-one rational base have a paid fixed-weight trace constructor independent of the ambient dense degree of that shift.

This does NOT yet pay a varying direction U_a, nor does it identify the coefficient-index-folded B weights with a single fixed U. The sufficient all-branch accounting would require acquired directions with a bounded SUM of their sizes, including their modulation/twiddle dependence; that supply is not assumed here.
