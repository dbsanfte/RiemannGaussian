# Rational filtering through q-integration: exact identities and the unpaid interface

2026-10-15. No soft O(J+sqrt L) tail algorithm was obtained. This audit gives a concrete exact failure of rational Jackson integration of the filter's logarithmic derivative, plus the precise formal-series and partial-fraction interfaces. It does not rule out additive algorithms, remainder acquisition, or selected-tail algorithms in general.

Let F(t)=P_L(t;q), D(t)=prod_{j=1}^J(1-t/z_j), and A(t)=F(t)/D(t)=sum a_n t^n. The actual branch has units q,z_j, local prime orders R_P,R_Q>L, z_j in the corresponding q-subgroups, J~m, L~m², and hidden characteristics P,Q~m³. Equal source offsets may be deduplicated first; then target differences are units because their nonzero exponent differences have size <=4m² below both orders. No orders or factors are supplied to an algorithm.

## 1. The logarithmic-derivative route is exact but not sparse in known coefficients

Writing p_r=sum_j z_j^(-r), direct formal differentiation yields

 t A'(t)/A(t)=sum_{r>=1} b_r t^r,
 b_r=p_r-(1-q^(Lr))/(1-q^r),
 n a_n=sum_{r=1}^n b_r a_(n-r).                         (1)

For 1<=r,n<=L the displayed denominators and n are units on the retained branch. The geometric-root contribution is cheap per r; the p_r are the power sums of D and form a degree-J rational recurrence stream. Equation (1) is therefore valid over Z/N with its promised units. But it consumes preceding FILTERED a_n and the p_r stream, not O(J) selected coefficients of F. Generating the whole prefix by fast formal logarithm/exponential costs soft O(L+J) ring work and O(L) output/storage if materialized. That is a valid paid algorithm, but not the sought soft O(J+sqrt L). No lower bound is inferred for an implicit selected-index implementation.

## 2. A specific rational q-antiderivative does not exist on the actual source

In either hidden field K, let q have exact order R, let sigma B(t)=B(qt), and define Tr(B)=sum_{h=0}^{R-1} sigma^h B. Since R divides |K|-1 it is invertible in K. Every rational sigma-difference has trace zero.

Every target satisfies z_j^R=1. Consequently the exact rational-function norm identity is

 prod_{h=0}^{R-1} D(q^h t)=(1-t^R)^J.

Taking logarithmic derivatives, which commute with sigma, gives

 Tr(t D'(t)/D(t))=-JR t^R/(1-t^R).                   (2)

Here J<R and J<P, so the right side is nonzero. Thus NO rational B in K(t), with any allowed poles or degrees, solves

 B(qt)-B(t)=t D'(t)/D(t).                            (3)

The same calculation for F gives norm(F)=(1-t^R)^L and hence

 Tr(t A'(t)/A(t))=-(L-J)R t^R/(1-t^R).              (4)

For the actual L>J and L-J<P this too is nonzero. Thus the analogous rational q-integration of the entire filtered logarithmic derivative also fails. These are actual-source statements using subgroup membership, not a generic denominator-degree argument. They concern the ordinary scalar sigma-difference operator on rational functions; they do not reprove or assume the earlier weighted-adjoint certificate theorem.

This obstruction does NOT prevent rational Hermite reduction with a remainder. In fact set g=tD'/D and g0=-Jt/(1-t). Their traces agree, so g-g0 has a rational antiderivative. Explicitly, for any trace-zero h,

 B=(1/R) sum_{r=0}^{R-1} r sigma^r h

satisfies (sigma-1)B=h. This formula uses the unknown R and up to R orbit terms, and is not the target algorithm. It shows why (2) must not be marketed as failure of every q-reduction: a universal residual can absorb the trace. Acquiring a suitably compressed primitive and its needed boundary values remains unpaid.

Formal Jackson integration around t=0 is also possible to precision H<R:

 [t^r]B = [t^r]g/(q^r-1), 1<=r<=H.

These denominators are units on the actual branch. The rational nonexistence theorem therefore does not exclude formal jets. It also does not turn the high-index tail into a bounded jet at an arbitrary unit point; a new paid conversion would be required.

## 3. Partial fractions and Padé do not supply free boundary coefficients

After source deduplication, ordinary partial fractions are ring-safe and, beyond the polynomial quotient of F/D, have residues

 F(z_j)/prod_{k!=j}(1-z_j/z_k).

The denominator factors are units, but the numerator is exactly the desired row value. Thus this PARTICULAR direct partial-fraction acquisition route presupposes the query. Equivalently the filtered tail gives F mod D and all rows by the exact selected-determinant report, while the actual unit-difference promise gives interpolation in the opposite direction. No claim is made that every partial-fraction or Padé-based algorithm must acquire residues this way. Padé reconstruction from enough known a_n can recover a rational function, but here a_n near L is the missing input; reconstructing D from its already supplied coefficients does not acquire the numerator remainder.

## 4. Primary q-Lagrange formulas: what their inputs actually are

Dennis Stanton, Recent Results for the q-Lagrange Inversion Formula, author-hosted PDF https://www-users.cse.umn.edu/~stant001/PAPERS/qlagr.pdf, was downloaded and its full extracted text inspected. Section 3, equations (3.1)--(3.9), discusses q-inversion via shifted products and the roofing operator r*(x)=prod_{h>=0} r(x q^(-h)); Theorem 4 gives a residue formula involving that transformed series. This supplies a formal change of basis, not an arithmetic theorem acquiring selected high coefficients of an arbitrary F/D in soft O(J+sqrt L). Its formal coefficients are rational functions of q; at finite-order specialization one must explicitly ensure every denominator needed at the requested precision is a unit. Below R this is possible for the usual 1-q^r factors; an unqualified infinite roofing product is not a finite-field/composite-ring value.

Section 4, condition (4.3) and Theorem 6, assumes a family r_k with D_q r_k=[k]_q rho(x) r_k for one common rho. It does not assert that an arbitrary supplied degree-J D is such a family with paid coefficient/residue extraction. Assigning D to r_1 and invoking the theorem does not provide the rest of the family or those residue coefficients. The explicit nonzero cyclic trace in (2) is one warning against replacing these formal conventions by an unrestricted rational q-antiderivative on the actual finite-order branch.

Ira Gessel, Lagrange Inversion (2016), https://arxiv.org/abs/1609.05988, is a primary-author survey of ordinary one-variable inversion, not a new q-tail arithmetic algorithm. Its coefficient ring is an integral domain containing the rationals (section 2). Any application over Z/N must instead prove a finite identity and charge/check its integer denominators. No selected-index arithmetic guarantee applicable to this rational filter was identified in either source.

The old q-rational reduction literature's infinite shift-coprimality assumptions were already audited in the frozen rational-query bundle; they are not counted as new evidence here. No short q-Chu transformation, cyclic-dilog singularity audit, generic state-size lower bound, backend build or numerical experiment was repeated.

## Outcome

The positive formal identities (1) and the trace-zero residual primitive are completely costed at their stated interfaces. The new scoped obstruction is (3), including arbitrary rational poles, on the actual subgroup family. The missing nearlinear operation remains acquisition of the filtered tail or an equivalent restriction-stable additive observable. No public O(J)-selected-coefficient reduction across one or polylogarithmically many paid common streams was found.
