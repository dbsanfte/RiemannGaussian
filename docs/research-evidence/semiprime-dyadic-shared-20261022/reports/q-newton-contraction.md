# q-Newton contraction on the original target quotient

2026-10-22. Constructive basis attempt following the sheared-norm primitive. Original scalar beta,q and native integer offsets are retained. No frozen files changed.

Let Y be any acquired restricted native target set, J=|Y|, and F(X)=product_(y in Y)(X−y). For a common interval [a,a+L), one can first replace y by q^(−a)y and account for the unit q^(aJL). Thus write a=0 below. Empty sets/intervals return1.

## A genuinely sparse acquired q-dilation

Define B_0=1 and B_k(X)=product_(0<=i<k)(X−q^i). Factor matching gives

 B_k(qX)=q^k B_k(X)+q^k(q^(k−1)−q^(−1))B_(k−1)(X), k>=1.     (1)

Thus q-dilation in the Newton basis is bidiagonal, not merely an implicit dense Vandermonde conjugation. All J diagonal/off-diagonal entries are acquired in soft O(J). Because all q-node differences in this range are units, the coefficients f_k in

 F(X)=B_J(X)+sum_(k<J) f_k B_k(X)

are acquired by fast Newton-basis conversion/product-tree interpolation in soft O(J) bit operations (ordinary logarithmic factors suppressed). Target polynomial construction and source rescaling are paid. These are valid actual original-ring operations, not roots-of-unity substitutions.

In the degree<J representative space, multiplication C by X has the explicit form

 C B_k=B_(k+1)+q^k B_k, k<J−1,
 C B_(J−1)=−sum_(k<J)f_k B_k+q^(J−1)B_(J−1).              (2)

Both C and the bidiagonal D from (1) therefore have soft O(J) actions and acquired O(J) data. In this precise basis the q-Weyl boundary is a SINGLE acquired column:

 DC−qCD=w e_(J−1)^T,
 w=q^J F(X)−F(qX), represented in degree<J.                (3)

To verify (3), it vanishes on degrees<=J−2. On monic B_(J−1), the two polynomial reductions subtract F(qX) and q^J F(X), respectively. Leading coefficients cancel, so w has degree<J. This sign and normalization do not use inverse target differences or cross differences.

## Applying it to the query

The required scalar is det B_L(C)=product_y B_L(y), with the conventional resultant sign fixed by this displayed identity. Its complete matrix recurrence is

 M_0=I, M_(k+1)=(C−q^k I)M_k.                             (4)

Equation (4) is an exact computable representation of the ORIGINAL query, including zero divisors, not a companion norm of a substituted base. It has only O(J) acquired operator data, but performing L updates is not a near-linear algorithm. A determinant of its final matrix has not been supplied by the sparse actions alone.

There is an exact finite q-boundary identity on this same matrix:

 (C−q^(L−1)I) B_L(qC)=q^L(C−q^(−1)I)B_L(C).             (5)

This is cleared polynomial factor matching and holds even when any matrix/factor is singular. It must not be solved by inverting a cross factor. Taking determinants gives the corresponding exact endpoint relation, whose initial value remains det B_L(C). Hence (5) transports the query but does not itself determine it.

The tempting useful contraction would combine the rank-one q-Weyl defect (3) with (5), turning the unknown scalar determinant into O(J) acquired boundary data. The unresolved term is NOT a basis-conversion cost: it is the propagated correction when q-dilation crosses reduction modulo F. Explicitly, for any polynomial P=QF+R,

 P(qX) mod F = R(qX) mod F + Q(qX)F(qX) mod F.             (6)

The quotient Q varies with the full long polynomial or intermediate update. The new basis makes D cheap but does not erase the second term. For native F, no identity making that correction a unit multiplier, fixed low-rank determinant update, or paid telescoping term has been derived. Formula (3) is consistent with the older paid-q-pencil boundary; it is not claimed as an independent solution of that older mixed-diagonal problem.

## Actual acquisition bound and next concrete theorem

Paid: O(J) target polynomial and Newton coefficients; sparse C,D,w; O(m) q/endpoint powers; row restriction and seed-origin unit scaling. This is soft O(m) bits, and all data depend on the true beta powers including centered carries.

One can complete the query with the established block product/MPE algorithm in soft O(J+sqrt(JL)), recovering the known soft O(m^(3/2)) bound. The new bidiagonal basis alone does not improve that completion. No full-degree or rank lower bound is asserted.

A positive next theorem would be an algorithm computing det B_L(C) for the **acquired native f_k**, using the one-column defect (3) and the exact endpoint recurrence (5), with total soft O(J+sqrt L) residue-bit work, while allowing singular C−q^i. A proof that only operates on invertible C−q^i would exclude the desired source. A proof for arbitrary supplied F would be stronger; this pass has not found the required native cancellation in the propagated term (6).

Conclusion: q-Newton coordinates do restore genuinely sparse dilation and a paid one-column correction on the actual target quotient. They supply an exact compact operator representation of the original query, but not the scalar determinant contraction. This is a constructive operation and a precise remaining term, not a claim that the representation itself achieves the sixth-rate goal.
