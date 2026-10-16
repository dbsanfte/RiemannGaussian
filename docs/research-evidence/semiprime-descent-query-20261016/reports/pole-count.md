# A uniform actual pole count for the negative-index mask contraction

2026-10-16. New rigorous result: the canonical rational coefficient-index function for the dyadic mask has at least ceil((J-1)/2) genuine poles in EACH actual hidden field. The proof uses a unit q-binomial minor and block-support counting, not generic nonvanishing. It does not acquire the query or exclude all representatives modulo q-Ore syzygies.

## 1. The rational function and theorem

Let K be a field, q a unit of order R, J>=2, and B dyadic with

 J<=B<2J,  JB<=L,  M=J(B-1),  R>L+M.

More generally it suffices that 1-q^a is nonzero for 1<=a<=L+M. Let arbitrary z_1,...,z_J be units; distinctness or subgroup membership is NOT needed in this theorem. Define

 F(t)=P_L(t;q)=sum_(a=0)^L c_a t^a,
 D(t)=prod_j(1-t/z_j),
 D_B(Y)=prod_j(1-Y/z_j^B),
 E(t)=D_B(t^B)/D(t)=sum_(h=0)^M e_h t^h.

This quotient is a polynomial, with e_0=1 and unit leading coefficient e_M. Put R_0(X)=1 and, for h>=1,

 R_(-h)(X)=q^h prod_(a=0)^(h-1)(X-q^a)
                    /prod_(a=1)^h(X-q^(L+a)),
 mathcal_R(X)=sum_(h=0)^M e_h R_(-h)(X).             (1)

The finite poles available to (1) are the M distinct simple points beta_t=q^(L+t), 1<=t<=M. At least

 ceil((J-1)/2)                                      (2)

of them are genuine poles after all cancellations.

This holds separately in both retained actual hidden fields, uniformly for the supplied unit targets. For the canonical source J=m-1, choose B as the least dyadic integer >=J. Then B<2J and JB<2J^2<2m^2<=L for the original long window L>=2m^2+2. Also L<=4m^2 and M<2m^2, so L+M<6m^2<R_local under the inherited R_local>16m^2 promise. Thus (2) is Omega(m) on actual inputs, with no new deletion or random/generic assumption.

## 2. Connection with the original coefficient contraction

For 0<=a<=L, every c_a is nonzero. Backward coefficient recurrence gives

 c_(a-h)/c_a=R_(-h)(q^a),

using c_(a-h)=0 when h>a. In that case the numerator in (1) contains q^a-q^a and its denominator is still nonzero. Consequently

 [t^a](F E)=c_a mathcal_R(q^a),  0<=a<=L.           (3)

In particular the relevant low Cartier-channel coefficients are samples of this rational index function. Formula(3) is not asserted as a division by c_a for a>L, where c_a vanishes and (1) develops its poles.

Let alpha=q^(1-L). At beta_t, write rho_t=Res R_(-t), a nonzero scalar. For u>=0 the regular ratio of R_(-(t+u)) to R_(-t), evaluated at beta_t, is

 prod_(r=0)^(u-1)(1-q^(L-r))/(q^L(1-q^(-r-1)))
     =q^u(q^(-L);q)_u/(q;q)_u=alpha^u c_u.

Thus

 Res_(X=beta_t) mathcal_R
    =rho_t sum_(u=0)^(M-t)e_(t+u)c_u alpha^u.      (4)

Every rho_t is nonzero: its numerator and other denominator differences use only nonzero powers with absolute exponent at most L+M. The reversal identity

 c_(L-u)=c_L alpha^u c_u

also shows that (4) is rho_t/c_L times [t^(L+t)]F(t)E(t). Therefore genuine poles are exactly the nonzero high-tail coefficients of FE, up to nonzero normalizations. The next argument bounds that support without assuming its individual coefficients are units.

## 3. Reverse the mask and expose sparse forcing

Let d_J and e_M be the leading coefficients of D and E, and define constant-one reversals

 Dhat(x)=x^J D(1/x)/d_J=prod_j(1-z_j x),
 Ehat(x)=x^M E(1/x)/e_M,
 Khat(Y)=prod_j(1-z_j^B Y).

The norm-complement identity gives

 Dhat(x)Ehat(x)=Khat(x^B).

Set

 P(x)=Ehat(x)F(alpha x)=sum p_n x^n,
 Q(x)=Dhat(x)P(x)=Khat(x^B)F(alpha x)=sum Q_n x^n.

Equation(4) becomes Res_(beta_t)mathcal_R=rho_t e_M p_(M-t). It remains to show that at least ceil((J-1)/2) of p_0,...,p_(M-1) are nonzero.

Write Khat(Y)=sum_(a=0)^J k_a Y^a, with k_0=1, and f_n=alpha^n c_n. In each of the J-1 complete blocks h=0,...,J-2, consider the first h+1 coefficients

 Q_(Bh+i)=sum_(a=0)^h k_a f_(B(h-a)+i), 0<=i<=h.  (5)

All these indices are below M. The square coefficient matrix in (5) is invertible. Therefore these h+1 values cannot all vanish: that would force all k_a, including k_0=1, to vanish. Each of those J-1 blocks contains at least one nonzero Q coefficient.

## 4. Unit-minor proof, including the exponent ranges

The scalar factors alpha^(B(h-a)+i) in (5) are nonzero row/column factors, so consider the matrix c_(Ba+i), 0<=a,i<=h, reversing rows if needed. Put r=h+1, X_a=q^(Ba), and

 V(X)=prod_(s=1)^(r-1)(1-q^s X),
 p_i^basis(X)=prod_(s=0)^(i-1)(q^L-q^s X)
                   *prod_(s=i)^(r-2)(1-q^(s+1)X).

Its evaluation factorization is

 c_(Ba+i)=c_(Ba) p_i^basis(X_a)/V(X_a).

The seeds c_(Ba) and V(X_a) are nonzero: Ba+i<=B(J-2)+J-2<JB<=L. The X_a have distinct unit differences because their exponent differences are at most B(J-2)<L. At eta_k=q^(L-k), k=0,...,r-1, the cleared basis evaluation is triangular, with diagonal

 (q^L)^k prod_(u=1)^k(1-q^(-u))
          *prod_(u=1)^(r-1-k)(1-q^(L+u)).

Every factor and the eta Vandermonde determinant are nonzero; the largest additional exponent is L+r-1<=L+J-2<=L+M. Hence the basis coefficient matrix and its evaluation at X_a are invertible. This proves the required minor without a generic-specialization argument.

Over Z/N with the same unit-power promise, all these determinants are UNITS, and the forcing vector in (5) cannot vanish after reducing to either hidden field. Different blocks may have different nonzero coefficients in the two fields; no claim that each counted coefficient is a unit modulo N is needed.

## 5. From forced blocks to many residues

Since deg Dhat=J, a nonzero coefficient p_u can contribute to Q only at indices in [u,u+J]. As J<=B, this interval meets at most TWO blocks of width B. For Q indices below M only p_u with u<M can contribute. The J-1 blocks known to contain a nonzero Q coefficient must therefore be covered by the support intervals of p_0,...,p_(M-1). If there are s such nonzero coefficients, J-1<=2s. Equations(4)--(5) prove (2).

This support argument avoids a conjectural no-long-zero-run theorem and any assumption about the coefficients of the supplied D or E other than the normalized leading/constant coefficients.

## 6. Exact scope for the q-syzygy investigation

The result excludes an EXACT rational-identity compression of mathcal_R into only polylog(m) simple-pole terms, or into a representation whose TOTAL allowed finite pole count is polylog(m). It is an actual pole-count obstruction to that bounded-pole ansatz. It is not a bound on the number of long q-factorial streams: one succinct denominator can encode many poles and may be cheap to evaluate. Pole count alone never implies an arithmetic-operation lower bound. In particular an O(J)-size rational index representation is entirely compatible with this Omega(J) pole count and could fit the desired soft O(m) clock if its construction and evaluation were paid. No superlinear bound is obtained.

Nor does it exclude the requested q-Ore escape. A different representative modulo the actual phase q-relations may alter the rational index function, move poles between shifted terms or retain a boundary remainder. Equality only at the required finite q^a samples is weaker than the rational identity in (1), and can have a polynomial interpolant with no finite poles. Acquiring such a representative/interpolant with the original collision semantics is still unpaid. The proof does not transfer its pole lower bound through an unproved equivalence of those contracts.

No nearlinear whole-family coefficient tail, mixed diagonal, collision locator or factor-selective observable has been acquired here. The new substantive result is the uniform Omega(m) genuine-pole bound and its self-contained unit-minor/block-support proof, with the limits above. No backend generation, repository edit, build or numerical experiment was performed.
