# Normalizing the paid block pencil gives a paid quasiseparable operator

2026-10-16. A positive conditional operator check; no query/diagonal algorithm.

Use the row-value convention W_(s,j)=z_j^s, Q_row=W^-1 D_q W, D_q=diag(q^s), and Z=diag(z_j). Let H(t)=t^J+sum_(s<J)h_s t^s, h=(h_s), a=q^L, and assume distinct unit nodes with unit differences. In coefficient coordinates,

 M=W Z W^-1=U-e_last h^T,

where U has ones on its superdiagonal. Thus M is the row-coefficient multiplication-by-t companion. Set

 G=(I-aU)^-1=sum_(r=0)^(J-1)a^r U^r,
 delta=det(I-aM)=prod_j(1-a z_j)=1+a h^T G e_last.

All identities hold over Z/N. On the additional branch where delta is a unit, Sherman--Morrison gives

 (I-aM)^-1=G-a(G e_last)(h^T G)/delta.             (1)

No field pivot is used. A proper gcd(N,delta) factors N; gcd N is not an inverse. This note asserts no inexpensive way to resolve a saturated branch.

The normalized right operator R=Q_row(I-Z)(I-aZ)^-1 has coefficient representation

 W R W^-1
 =D_q [a^-1 I+(1-a^-1)
           (G-a(G e_last)(h^T G)/delta)].         (2)

Indeed (I-M)(I-aM)^-1=a^-1 I+(1-a^-1)(I-aM)^-1. The supplied a is a unit.

Every strict off-diagonal submatrix of the upper geometric matrix G has rank at most one. Equation(1) adds one outer product, so (2) has quasiseparable rank at most two, also over either hidden field. Explicit generators, H, delta, geometric vectors and row/column scalings are acquired in soft O(J) ring work/storage. Applying G uses geometric prefix/suffix sums; h^T G is one convolution or triangular recurrence. Thus actions and transpose actions have the same paid bound. Only the stated unit inverses and public powers are needed.

Right-multiplying the reviewed block pencil by (I-aZ)^-1 gives M_block-X M_block R=rank-at-most-two. Since X is a diagonal of supplied q powers, it is invertible; left multiplication by X^-1 rewrites this as a Sylvester equation X^-1 M_block-M_block R=low rank. Spectral disjointness/uniqueness for that equation is NOT established here. Nor does this normalization supply the original mixed diagonal, its compatible ordinary commutator, or the formal determinant deformation. It resolves a paid operator-structure prerequisite, while the substantive query remains open.
