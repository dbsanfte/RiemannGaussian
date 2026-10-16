# A small Toeplitz resultant exists, but its entries are the long remainder in another basis

2026-10-15. Exact positive algebraic interface and a scoped acquisition diagnosis. No nearlinear actual-source evaluator or general circuit lower bound is claimed.

## 1. The J by J identity, with signs and scaling

Let R be any commutative ring, z_1,...,z_J units, L>=J-1, and F(t) any polynomial of degree at most L. Define

 D(t)=product_j(1-t/z_j),
 F(t)/D(t)=sum_(n>=0) a_n t^n,
 M_(i,j)=a_(L-i+j), 1<=i,j<=J.

The series exists over R because D(0)=1. Then

 det M = product_j z_j^(-L) F(z_j).                 (1)

For F=P_L(t;q), the original product S=product_j P_L(z_j;q) is therefore

 S=(product_j z_j)^L det M.

Only 2J-1 distinct Toeplitz entries are needed, indexed from L-J+1 to L+J-1. This is a genuine small determinant, not a J+L Sylvester matrix.

Here is a direct sign check and proof. Work first in the rational-function field of independent x_j=1/z_j and coefficients of F. Partial fractions give, for n>=L-J+1,

 a_n=sum_r d_r x_r^n,
 d_r=F(1/x_r)/product_(s!=r)(1-x_s/x_r).

Thus M factors into matrices (x_r^(J-i)), diagonal entries d_r x_r^(L-J+1), and (x_r^(j-1)). The two Vandermonde determinants and the product of denominators cancel with the same sign, giving product_r x_r^L F(1/x_r). Both sides of (1) are polynomial identities over the integers in the coefficients of F and x_j, so specialization proves (1) over every R, including repeated nodes and zero divisors. No numerical Vandermonde inversion is licensed by this generic proof.

This is the rectangular supersymmetric Jacobi--Trudi resultant identity. Its name does not provide the entries for free.

## 2. J of those entries already recover every wanted row value

Put n0=L-J+1 and form the length-J tail polynomial

 A(t)=sum_(k=0)^(J-1) a_(n0+k)t^k,
 K(t)=D(t)A(t) mod t^J.                            (2)

Then K has degree<J and satisfies the exact polynomial identity

 F(t)-D(t)sum_(r=0)^(n0-1)a_r t^r=t^n0 K(t).       (3)

For n0=0 the prefix sum is empty. To prove (3), subtract the series prefix from F/D. The remaining series starts at degree n0. Multiplication by D produces a polynomial of degree<=L; after removing t^n0 its degree is at most L-n0=J-1. Its first J coefficients are precisely (2).

Evaluating (3) at any original target gives

 F(z_j)=z_j^n0 K(z_j).                             (4)

Consequently only J consecutive tail entries, all included in M, recover ALL original row values in soft O(J) ring operations beyond their acquisition: multiply truncated polynomials, monic multipoint-evaluate K, and compute z_j^n0 by O(J log(L+1)) unit powering. Repeated nodes and nonunit differences cause no problem. Monic remainder trees do not divide by target differences. Bit cost modulo N is soft O(J log N) for polynomial-size L; storage is soft O(J) residues. No row value is inverted.

Thus a nearlinear acquisition theorem for these Toeplitz entries would genuinely solve the original whole-batch problem. Treating the entries as already selected q-coefficients is circular: they are coefficients of F/D, not F. For J=1 the single entry is already a_L=z_1^(-L)F(z_1), the complete scalar query rather than one selected coefficient of F.

This is an exact interface equivalence with the polynomial remainder, not a complexity lower bound. Since D(0)=1, t is invertible modulo D. Its leading coefficient is also a unit because every z_j is a unit. Given F mod D, compute

 K=t^(-n0)F mod D

by binary powering/modular polynomial arithmetic, then recover the selected tail via A=K/D mod t^J. Conversely (3) gives F mod D=t^n0 K mod D. Both conversions cost soft O(J log(L+1)) operations. The tail is therefore exactly the original quotient-algebra remainder in a shifted coordinate basis.

An unrestricted converse from row VALUES to this tail is not asserted for repeated nodes or nonunit differences: interpolation then needs confluent data or another contract. In the actual source, one may first publicly deduplicate equal integer offsets delta_j. Distinct offsets in a span of 4m^2 give unit target differences because their nonzero differences are smaller than both local orders. The deduplicated nodes therefore admit ring-safe fast interpolation, and the reverse conversion from their complete value list also costs soft O(J) plus powering. Original multiplicities are kept separately when forming S. This source-specific observation is not needed for the unconditional implication (4).

## 3. Why short convolution and the dual determinant do not yet pay the entries

Writing 1/D=sum_(r>=0) h_r t^r gives

 a_n=sum_(k=0)^min(n,L) c_k h_(n-k), F=sum c_k t^k.

The h_r obey a known order-J recurrence, but n near L still denotes a long inner product. It is not a convolution of only J selected c_k with coefficients of D. The exact short convolution D*A in (2) is cheap AFTER the tail has been acquired; it does not acquire it. Selected common-stream q-binomial values or their jets provide c_k, not these long recurrence-filtered combinations.

Swapping the two alphabets gives the dual rectangular determinant of dimension L, with coefficients of D/P_L rather than P_L/D. Those coefficients are short convolutions of D with the reciprocal-q-factorial sequence

 [t^n]1/P_L(t;q) = product_(r=1)^n(1-q^(L+r-1))/(1-q^r).

But the explicit L by L Toeplitz representation has Theta(L) distinct nonnegative generator indices, extending to L+J-1, in the regime L>>J. Reading/acquiring that complete generator list loses the target. This is only an explicit-representation charge; a compressed determinant algorithm using the recurrence could still be useful. On the retained actual source all exponents needed here stay below the local orders, so unit denominators are not the obstruction. No claim is made that scalar evaluation must expand the generator list.

Even after the small matrix's entries are known, a fast determinant algorithm over Z/N needs its own ring-safe pivot/factor/saturation contract. This report does not silently transfer a field Toeplitz solver through collision-induced nonunit minors. The acquisition issue in section 2 remains even if determinant evaluation is granted for free.

## 4. q-shifting does not turn the missing entries into selected coefficients

For F=P_L and A_series=F/D,

 (1-t)D(qt)A_series(qt)=(1-q^L t)D(t)A_series(t).

If D=sum_(r=0)^J d_r t^r and a_n=0 for n<0, its coefficient relation is

 (q^n-1)sum_(r=0)^J d_r a_(n-r)
 +(q^L-q^(n-1))sum_(r=0)^J d_r a_(n-1-r)=0.

This is an explicit order-(J+1) q-recurrence for the desired entries. It is the original first-order coefficient recurrence composed with the reciprocal-D filter, whose state depends on the J targets. Likewise, H(qX)-q^J H(X) lowers the degree of a monic H by canceling its leading term, but does not by itself supply the filtered tail or F mod H. No softly linear propagation of this growing-state recurrence was obtained. Matrix size or order is not claimed to imply an operation lower bound; an implicit structured propagation algorithm remains a live possibility.

## 5. Primary provenance and outcome

Moens--Van der Jeugt, A Determinantal Formula for Supersymmetric Schur Polynomials, Journal of Algebraic Combinatorics 17 (2003), 283--307, section 1 equations (1.6)--(1.7), records supersymmetric complete functions and Jacobi--Trudi conventions. Their plus-sign y convention becomes the difference-alphabet convention here by y->-y. The new identity is proved directly above to fix signs and ensure arbitrary-ring specialization; no field algorithm or root separation theorem is imported from that paper. Primary PDF mirror: https://www.kurims.kyoto-u.ac.jp/EMIS/journals/JACO/Volume17_3/l66lh57578211177.fulltext.pdf . The primary institutional bibliography https://biblio.ugent.be/publication/208757 was freshly opened and confirms authors, venue and pages. Search-indexed primary text exposed the cited conventions, but direct PDF downloads from the ETH/Kyoto mirrors returned 404/403; no saved/full-PDF inspection is claimed. Inherited interface/source hashes and this retrieval scope are listed in manifest.json.

The positive outcome is a truly O(J)-generator determinant and a ring-safe reduction from its tail entries to all row products. The tempting claim that its entries are cheaply selected coefficients is false as an input contract: acquiring them is equivalent to the original remainder computation. This does not rule out a new algorithm for precisely that tail or a different determinant whose entries really are paid. No actual-source soft O(m) query has been obtained here.
