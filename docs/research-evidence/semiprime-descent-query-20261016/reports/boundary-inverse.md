# The normalized boundary equation has a paid inverse

2026-10-16. Constructive clarification of the weighted-descent obstruction. Solving its linear equation is inexpensive; acquiring its forcing vector remains the missing query. No complete acquisition theorem is claimed.

Let H(t)=t^J+sum_(k<J)h_k t^k have distinct unit nodes with unit pairwise differences. Let M=U-e_last h^T be its row-coefficient companion, D_q=diag(q^s), a=q^L, and assume J<=L and every 1-q^r through L is a unit. On the additional delta=det(I-aM) unit branch put

    R=D_q(I-M)(I-aM)^(-1),
    L_1=(I-aM)-D_q(I-M).

Then I-R=L_1(I-aM)^(-1). The following gives a formal linear solver for L_1 in O(J) ring work and storage, including parameter-only batch inversion.

Write A_s=1-q^s and B_s=a-q^s, 0<=s<J. Each B_s=q^s(q^(L-s)-1) is a unit, as is h_0. The first J-1 rows of L_1 x=y are

    A_s x_s-B_s x_(s+1)=y_s, 0<=s<J-1.

Since A_0=0, for J>=2 compute x_1=-y_0/B_0, then x_(s+1)=(A_s x_s-y_s)/B_s for 1<=s<J-1. These determine x_1,...,x_(J-1) without x_0. The final row is

    A_(J-1)x_(J-1)+B_(J-1) sum_(k<J)h_k x_k=y_(J-1).

It determines x_0 by division by the unit B_(J-1)h_0. For J=1 the equation is simply B_0 h_0 x_0=y_0. Thus there is no division by the zero A_0 or by any unknown row value. All scalar powers and inversions have the usual absorbed logarithmic bit cost.

It follows that (I-R)^(-1)=(I-aM)L_1^(-1) has the same O(J) action cost. Formal transposition gives its inverse transpose with the same clock. In the original node-value coordinates, U_H=diag((1-z_i)/(1-a z_i))Q, with Q the interpolation q-shift. If W_(s,i)=z_i^s, then U_H=W^T R^T W^(-T). Consequently

    (I-U_H)^(-1)=W^T (I-R)^(-T) W^(-T).

The two Vandermonde/interpolation maps have softly O(J) actions on the stated unit-difference branch. The entire inverse, setup, transpose and usual soft log N bit factor are therefore paid. This includes actual retained inputs satisfying the delta-unit branch, not arbitrary saturated denominator branches.

For F=P_L, write F=r+H G and f=(F(z_i)). The weighted-descent report proves the exact equation

    (I-U_H)f=(w(z_i)H(qz_i)G(qz_i))_i, w=(1-t)/(1-a t).

The displayed inverse makes the two vectors interconvertible in softly O(J) once either is supplied. Its right side contains the unknown quotient G; this note does not acquire it. Universal boundary-rank arguments do not prove that this particular forcing vector is dense or hard. Special q-binomial syzygies, pole-bearing gauges and other factor-selective observables remain possible. This is a clarification of the missing arithmetic payload, not another purported proof of the whole-family bound.
