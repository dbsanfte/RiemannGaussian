# The normalized Sylvester spectral check is paid; its collision implication remains open

2026-10-16. Exact positive factor-or-unit-check primitive and actual endpoint facts. No whole collision query, all-row spectral implication, or new asymptotic counterfamily theorem is established here.

## Exact determinant and its acquisition

Use H(t)=t^J+sum_(k<J)h_k t^k, h_J=1, the row companion M=U-e_last h^T, D_q=diag(q^s), a=q^L, and

    L_X=(I-aM)-X D_q(I-M).

The normalized right operator in coefficient coordinates is R_coef=D_q(I-M)(I-aM)^(-1), on the branch delta=det(I-aM) unit. The orientation matters: D_q multiplies on the LEFT of I-M. Direct determinant expansion gives

 phi(X)=det L_X
   =sum_(k=0)^J h_k product_(s<k)(1-Xq^s)
                         product_(k<=s<J)(a-Xq^s).       (1)

For clarity, before the last companion row, L_X is upper bidiagonal with diagonal A_s=1-Xq^s and superdiagonal -B_s=-(a-Xq^s). Its last-row companion correction is B_(J-1)h^T. The cofactor sign cancels the sign of its J-1-k superdiagonal entries, so all h_k terms in (1) have the displayed positive signs. In particular

    phi(0)=a^J H(a^(-1))=product_j(1-a z_j)=delta.

The FULL polynomial phi is acquired in soft O(J) arithmetic, not by J independent determinants. Use the split rational-Newton expression

    phi=(product_s B_s) [h_0+(A_0/B_0)(h_1+...+(A_(J-1)/B_(J-1))h_J)...].

Balanced multiplication of the upper-triangular polynomial matrices [[A_s,h_s B_s],[0,B_s]] gives its numerator directly. No B_s(X) or spectral value is inverted. Thus zeros of B_s at queried X create no missing branch. H itself is acquired by the already paid target product tree. Monic multipoint evaluation at T arbitrary supplied X values adds soft O(J+T), with repeats allowed. Powers X_n=q^(Jn) have the ordinary absorbed logarithmic cost. For T=Theta(L/J) in the balanced regime, all phi(X_n), their individual gcds with N, and delta are therefore paid in soft O(J+L/J) work and storage, with the usual modular log N bit factor.

## What the spectral test certifies

On delta-unit and X_n-unit branches,

 det(X_n^(-1)I-R_coef)=phi(X_n)/(delta X_n^J).    (2)

Indeed I-X R_coef=L_X(I-aM)^(-1). Therefore the diagonal-left Sylvester map A P-P R_coef, A=diag(X_n^(-1)), is invertible over Z/N exactly when every phi(X_n) is a unit: its rows are independent square systems with those unit determinants. This is a cheap exact uniqueness CHECK, not a claimed cheap acquisition of the original mixed diagonal or an arbitrary Sylvester solution table.

A proper gcd from delta or any phi(X_n) is an immediate factor. A saturated gcd N does not yield an inverse and is not resolved by this report. If all tested values are units, the check certifies spectral disjointness/uniqueness in both hidden fields; it does not certify absence of the original forced collision. Thus the result is a paid factor-or-uniqueness diagnostic on its stated branches, not a complete factor-or-query algorithm.

## Actual source endpoint tests are always units

These facts hold on the actual retained family, where J<=m-1, L>=J, and every 1-q^r through L is a unit. They do not use generic specialization.

At the first complete-block point X_0=1, every term k>=1 in (1) contains A_0=0, so

    phi(1)=h_0 product_(s=0)^(J-1)(q^L-q^s).

This is a UNIT modulo N: h_0 is a signed product of supplied units and the remaining exponents L-s lie in [1,L]. Nevertheless the native long query still has its guaranteed collision. Hence that actual first spectral test cannot detect the forced hit.

If J divides L+1 and L>=J, the last complete-block point is X_*=q^(L+1-J). Here B_(J-1)=0, so every term k<J vanishes and

    phi(X_*)=product_(s=0)^(J-1)(1-q^(L+1-J+s)),

again a unit. This is an endpoint fact, not a statement that all interior spectral tests are units, nor an infinite family satisfying the divisibility condition.

For interior X=q^v, with 1<=v and v+J-1<=L, the exact sum can also be written

 phi(q^v)=product_(s<J)(q^L-q^(v+s))
             *sum_(k=0)^J h_k q^(-Lk)
                          (q^v;q)_k/(q^(v-L);q)_k,

when all displayed denominator factors are nonzero. At boundary zero factors use (1) instead. This exhibits a linear q-Newton functional of the COEFFICIENTS of H; it is not an individual row product or a product of such row values. No actual-source theorem relating its interior zero support to F(z_j)=0 has been proved here. In particular no actual-family all-interior-unit claim follows from the endpoint calculations.

## Why full-orbit monodromy is not a free compressed identity

In a hidden field with q of order R and a=q^L, the rational operator

    U_a f(t)=[(1-t)/(1-a t)]f(qt)

obeys U_a^R=I on K(t): the R rational multipliers telescope because multiplication by a permutes the full q orbit. This is a genuine formal rational-function identity.

It does not automatically descend to K[t]/H. The nonempty target root set has J<R elements, so it is not invariant under q; otherwise it would contain a full R-element orbit. Thus the ideal (H) is not preserved by q-shifting. Thus the q-shift itself does not descend to this quotient, and the full-orbit rational-function proof cannot simply be replayed after interpolation. A weighted operator can accidentally preserve an ideal through a zero of its numerator even when q-shift alone does not; weighted descent and admissibility of ALL intermediate denominators would have to be checked separately. No identity R_coef^R=I or orbit-factorization of its characteristic polynomial follows from the rational monodromy alone. This is a limit of that inference, not proof that every compressed monodromy identity or spectral algorithm is impossible.

## Outcome

The formerly unspecified spectral uniqueness check is inexpensive on the delta-unit branch and can return a factor when a tested determinant has proper gcd. It does not yet connect interior resonances to the guaranteed original collisions, handle saturated branches, or give the required whole-query observable. No further theorem or counterfamily is claimed to fill that gap. The source-specific positive question remains open; the general acquisition clock is unchanged.
