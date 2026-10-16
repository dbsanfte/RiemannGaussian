# Sparse forcing does not yet acquire the quotient tail

2026-10-16. Focused unsuccessful algorithm attempt. No improved acquisition algorithm or stronger canonical pole theorem is proved here. The useful exact calculation is a unit-ended coefficient recurrence before multiplication by the sparse block forcing; the obstacle is transferring it through that multiplication.

Let F(t)=prod_(i<L)(1-q^i t), alpha=q^(1-L), Dhat(x)=prod_j(1-z_j x), K(Y)=prod_j(1-z_j^B Y), Ehat=K(x^B)/Dhat(x). Write

 A(x)=F(alpha x)/Dhat(x)=sum a_n x^n,
 P(x)=Ehat(x)F(alpha x)=K(x^B)A(x).

Here J<=B<2J, M=J(B-1)<=L, and the actual hidden-field q order exceeds L+M. A is interpreted as a formal power series at zero; Dhat(0)=1. This definition does not assume its coefficients have been acquired.

## Exact small-order recurrence

The q-factorial equation yields

 (1-alpha x)Dhat(qx)A(qx)=(1-qx)Dhat(x)A(x).       (1)

Put U(x)=(1-alpha x)Dhat(qx), V(x)=(1-qx)Dhat(x), with coefficients U_r,V_r, r=0,...,J+1. Then for n>=1,

 (q^n-1)a_n + sum_(r=1)^(J+1)(q^(n-r)U_r-V_r)a_(n-r)=0,       (2)

where negative indices mean zero. Both U_0 and V_0 equal one. If d_J is the leading coefficient of Dhat, the trailing coefficient in (2) is

 q^(n-J-1)U_(J+1)-V_(J+1)=d_J q(1-q^(n-L-1)).    (3)

For 1<=n<=L, the forward pivot q^n-1 and the trailing pivot (3) are nonzero in each actual field, and units over the composite ring under the inherited unit-power promise. Thus there are no J+1 consecutive zero coefficients of A in the prefix a_0,...,a_L. Indeed such a zero window ending at n<=L propagates backwards via (3) until it contradicts a_0=1. This argument is fieldwise; it does not assert that every surviving coefficient is a unit modulo N.

The recurrence construction requires only the supplied degree-J Dhat, q,alpha. Its coefficients cost softly O(J) ring operations. Direct propagation to index M costs O(JM) operations and O(J) coefficient state, plus the required unit inversions (which can be batched or checked factor-aware). In the regime M=Theta(JB), B=Theta(J), this direct propagation costs O(J^3), not the target softly O(J). The recurrence is not being offered as a competing algorithm to the existing generic bound. Any faster high-index recurrence algorithm must charge its growing dimension and setup.

## Where the intended pole-density transfer fails

The canonical rational-index residues are proportional to p_0,...,p_(M-1), the first M coefficients of P. But

 p_n=sum_(h=0)^floor(n/B) k_h a_(n-Bh),  K(Y)=sum k_h Y^h.       (4)

A nonzero a_n can cancel against the other terms in (4). The no-zero-run theorem for A therefore does not prove the analogous statement for P or Omega(JB) nonzero residues. There is no argument here that actual-source cancellation occurs or is impossible; the proposed implication is simply missing.

Eliminating A gives the exact equation

 U(x)K(x^B)P(qx)=V(x)K(q^B x^B)P(x).             (5)

The polynomial multipliers now have degree JB+J+1. Their sparse-block product descriptions are inexpensive to state, but (5) no longer has the short scalar coefficient window used in the preceding proof. Treating its entire shifted coefficient state as freely supplied would reintroduce the missing tail. This is a limitation of this attempted proof/algorithm, not a complexity lower bound for sparse recurrences.

The same issue affects a symbolic O(J)-term presentation of the canonical rational-index function obtained by partial fractions of 1/D: each term remains a long truncated basic-hypergeometric sum. Counting these terms is not a construction/evaluation algorithm. No efficient evaluation of those sums is supplied here, and no lower bound against such an evaluation is claimed.

## Consequence and scope

The previous uniform Omega(J) genuine-pole theorem remains the proved bound. It allows an O(J)-size rational representation and does not imply an operation lower bound. This investigation has not proved Omega(JB) poles on the actual catalog or acquired an O(J)-size representation with a paid fast evaluator.

Likewise, acquiring b_i=w(z_i)H(qz_i)G(qz_i), F=r+HG, is still the original payload: the already paid softly O(J) inverse converts b to all F(z_i), and applying the paid operator converts the values back to b. Neither (1) nor sparse K makes b available for free. A different q-Ore representative, finite-grid correction, or compact inhomogeneous forcing remains possible.

Arithmetic costs above count operations on O(log N)-bit ring elements; multiplication-based soft bounds carry the corresponding bit-multiplication cost. All unit requirements are explicit. No new factoring exponent, acquisition theorem, experiment, repository change or build is claimed.
