# Rational Frobenius source and three concrete query mechanisms

Status: a paid simplification of the entire native source, plus two explicit transform candidates. No near-linear collision evaluator is proved here. All identities are in the actual scalar-coefficient algebra, not a hidden-field oracle.

## Contract and a simpler source

Let R=Z/NZ, A=R[X]/(X^m−1), m odd, gcd(N,m)=1, bar=rho_{−1}, rho_j(X)=X^j for j a unit modulo m. Let gamma have odd local orders >16m² and let t²=gamma be public. This is available by initially squaring the prepared odd-order base; its orders and any recovered original integer annihilator are preserved. Put

 W=t(1+gamma X)/(X+gamma),  Q_W=W^(m²).

Both binomials are units: their algebra norms are 1+gamma^m, a scalar unit because an odd-order local element cannot equal −1. In particular the inverse of 1+gamma X is the geometric polynomial sum_{r=0}^{m−1}(−gamma X)^r/(1+gamma^m). The analogous inverse of X+gamma is equally explicit. Preparation, checking the scalar denominator, and forming all coefficients cost soft O(m) ring work, including O(log N)-bit exponent and gcd charges. No Gaussian sums or hidden fields are used. W bar(W)=gamma.

Write the canonical row as a=N j^(−2) mod m, ell=mb−2aj, E=N+a+ell, with the integer centered-b definition retained. Define

 Z_j=W^ell (rho_j W)^a rho_{j^(−1)}(W^N).

At the true tag j=P mod m, coefficient Frobenius gives rho_j W=W^P and rho_{j^(−1)}(W^N)=W^Q in the WHOLE algebra modulo P. Therefore Z_j=Q_W^I whenever ell+aP+Q=m²I, exactly the original native integer relation. Norm gives Z_j bar(Z_j)=gamma^E.

The root's proposed V=t(1+gamma X)/(1+gamma X^(−1)) equals XW. Since ell+aj+N j^(−1)=0 mod m, EVERY corrected Z_j is unchanged on replacing V by W. Also V^(m²)=W^(m²). Thus the complete native query, not merely its hidden-prime coverage, has this degree-one rational presentation. All integer carries in ell and I remain present.

Recovery remains paired. For f=Z_j−Q_W^i and G=gamma^E−gamma^(m²i),
 G=bar(Z_j)f+Q_W^i bar(f),
so (f,bar(f))=(f,G). A single cyclotomic component hit does not establish this paired ideal condition or an original scalar annihilator. Whole-algebra source coverage does establish a valid hit, but a controller must retain that distinction.

## Mechanism 1: public Cayley dilation

Set R0=W/t, C=(X−1)/(X+1), lambda=(gamma−1)/(gamma+1). Then

 (R0−1)/(R0+1)=lambda C,
 R0=(1+lambda C)/(1−lambda C).

Here X+1, gamma+1, X+gamma, and R0+1 are units: R0+1=(gamma+1)(X+1)/(X+gamma). Also gamma−1 is a unit by the prepared order promise. All coordinate changes are therefore paid soft O(m), with no unsafe Cayley denominator. This is a genuine separable coordinate for the SOURCE: the rational base is a scalar dilation of the public Cayley coordinate.

Define the rational multiple-angle map B_n(c)=((1+c)^n−(1−c)^n)/((1+c)^n+(1−c)^n), interpreted projectively if a displayed denominator is not a unit. Then rho_j C=B_j(C), whereas the Cayley coordinate of R0^a is B_a(lambda C). The native row mixes these two operations, and B_a(lambda C) need not equal lambda B_a(C). Consequently source separation does not automatically separate the weighted row. A sufficient new evaluator would batch the actual carried mixed products defining Z_j against the geometric powers Q_W^i, retaining paired support, in soft O(m) total. The coordinate identity supplies its inputs in that budget; it does not supply that evaluator. Intermediate B_n denominators must be kept projectively or checked, since the initial safe denominator argument does not prove safety at arbitrary powers.

## Mechanism 2: Möbius-conjugated Dickson action

Put Y=X+X^(−1), and M(Y)=((1+gamma²)Y+4gamma)/(gamma Y+1+gamma²). Direct calculation gives

 R0+R0^(−1)=M(Y),
 R0−R0^(−1)=(gamma²−1)(X−X^(−1))/(gamma Y+1+gamma²).

The denominator is the unit (1+gamma X)(X+gamma)/X. The determinant of M is (gamma²−1)², also a unit. Thus M is an invertible projective coordinate change on the relevant trace locus. The fixed subalgebra A^bar has dimension (m+1)/2 and can be represented by symmetric coefficient pairs in soft O(m).

For Dickson polynomials D_0=2,D_1=s,D_(n+2)=sD_(n+1)−aD_n, the universal identity D_n(u+a/u,a)=u^n+(a/u)^n holds over any commutative ring for unit u. Hence

 rho_j Y=D_j(Y,1),
 Tr_bar(rho_j W)=t M(D_j(Y,1)),
 Tr_bar(W^n)=t^n D_n(M(Y),1).

The automorphism action on S=M(Y) is therefore M composed with D_j composed with M^(−1), while power action is D_n on S. This gives a concrete simultaneous conjugated-Dickson transform target. Binary Dickson evaluation at one represented algebra element costs soft O(m log n); evaluating every weighted native row this way still costs soft O(m²), and does not establish the desired soft O(m) bound. The obstruction here is an explicit mixed-action batching operation, not lack of a trace representation.

Trace alone also loses orientation. For norm-one u,v, equal traces imply (u−v)(u−v^(−1))=0 componentwise. It gives an OR of direct/inverse matches, whereas original recovery demands conjugate-paired support. In the actual rows even the scalar norms can differ. A sufficient trace algorithm must output paired characteristic-polynomial equality or combine trace information with the original scalar norm condition; equality of a single compressed trace is insufficient.

## Mechanism 3: monomial eigenline boundary and rational deformation

The completely separable source W0=tX^c has W0 bar(W0)=gamma. The same native congruence cancels every X exponent, giving Z_j=t^E and Q_W0=t^(m²). Thus monomial sources solve the entire carrier query syntactically but return precisely the original scalar long query. The rational W above is a degree-one deformation of that boundary with nontrivial Frobenius action, while preserving its scalar norm and source coverage. This identifies a concrete design requirement: a usable rational deformation must admit a batched mixed automorphism/power transform, rather than only fast exponentiation of a single torus point. No universal factoring gain follows from the monomial specialization.

## Literature and duplication audit

The repo already studies scalar Dickson recurrences around journal2687 and journal3609, and bounded rational seed changes around journal29093. This note does not claim those as new. The new paid statement is the exact V=XW cancellation in every native corrected row, and the resulting safe Cayley dilation/Möbius trace coordinate for an automorphism-based WHOLE-algebra Frobenius source.

Rubin–Silverberg, *Compression in Finite Fields and Torus-Based Cryptography*, author PDF https://www.math.uci.edu/~asilverb/bibliography/tbc.pdf, §9 (PDF pp15–16), explicitly distinguishes quotient-torus compression from group multiplication: exponentiation descends to conjugacy classes, multiplication generally does not. Their known-finite-field compression theorems do not supply the mixed native transform over R. PDF SHA256 e819b5c59e40993e3ad53b892af5107220219957b209b82ed995692fed26708d.

Pain, *A derivation of Dickson polynomials using the Cayley-Hamilton theorem*, arXiv:2406.07322v2, https://arxiv.org/abs/2406.07322v2, equations (29)–(31), gives the recurrence and u+a/u identity used above. Although stated there over complex numbers, these are integral polynomial identities and the commutative-ring instance follows by the displayed recurrence, without division by n. PDF SHA256 63325ab0228fc61cf5a5b6ba69010e14a531054859a243c0dcc745d4bbe915de.

All preparation is soft O(m) bit operations with the usual O(log N) factors suppressed, assuming polynomially bounded native exponents and m. A full m-coefficient algebra multiplication is soft O(m), not one scalar operation. No theorem in these sources turns J~m distinct mixed native rows into a constant number of such operations. The exact remaining constructive target is that mixed-action batch with paired support and localization, not an additional source/order lemma.

## Addendum: all antipodal aggregates survive for arbitrary W

These identities need only W bar(W)=gamma, not Gauss amplitudes. For odd prime m, take canonical j=1,...,m−1, a_j in {1,...,m−1}, and centered b_j. Then a_(m−j)=a_j and b_j+b_(m−j)−2a_j is divisible by m. Define the EXACT integer s_j=(2a_j−b_j−b_(m−j))/m. Centered bounds imply s_j in {0,1,2}. Therefore ell_j+ell_(m−j)=−m²s_j, including the actual wrap.

Because rho_j(W)rho_(−j)(W)=gamma and the inverse tags are antipodal,

 Z_j Z_(m−j)=gamma^(N+a_j) Q_W^(−s_j).

Take one representative j from every antipodal pair, h=(m−1)/2, A=sum a_j, S=sum s_j. Then

 product_(j unit) Z_j = gamma^(Nh+A) Q_W^(−S).

All scalar sums and the displayed aggregate are paid soft O(m), including O(log N)-bit exponentiation costs. This does not acquire individual Z_j or their differences with seeds.

For A_j:=W^j/(rho_j W), using the CANONICAL positive integer j rather than a residue exponent,

 A_j A_(m−j)=W^m/gamma,
 product_(j unit) A_j^(a_j)=(W^m/gamma)^A.

Thus the normalized weighted antipodal aggregate also requires no Gauss construction. These formulas preserve the whole-algebra source, norms and same-leaf recovery identity above.

One may select m as the first odd prime at least u=ceil(N^(1/6)) by a sieve through 2u (with the finite smallest input handled directly); Bertrand supplies this range for u>1. Individual gcd screening of m against N returns a proper factor if encountered; a saturated equality N=m is a finite/primality case, not a unit assumption. Retained prepared inputs with P,Q>16m² satisfy gcd(m,N)=1 automatically. The existing integer native bounds apply using N<=m^6: the true quotient index remains below 4m² for retained P<=Q. No auxiliary ell is required for W. This selector supplies a prime row modulus; the KMP automorphism wrapper additionally takes a checked public primitive root. Deterministically enumerating candidates and testing primitivity is a separate supply cost and is not silently included in the KMP API.
