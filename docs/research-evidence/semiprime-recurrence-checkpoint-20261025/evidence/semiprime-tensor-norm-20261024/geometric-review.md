# Independent geometric transport review

2026-10-24. PASS for final `geometric-generator.md`, SHA256
`8ff92a623b50d8698b34260ab01216f3d17ad89c26c5a88831561d3602aa581a`.
The final version corrects a raw-polynomial versus quotient-scaling
ambiguity in the Bezout inverse update. No other correction is needed.

The two grids q^(s*b) and q^(s*b+1) have unit cross-differences: the
integer 1+s*(b-c) is nonzero for s>=2 and lies within the stated short
order guard. Lagrange evaluation therefore gives the displayed scaled
Cauchy matrix with all denominators certified. Its acquired diagonals,
actions and inverses cost soft t. The first Schur-complement numerator
is exactly (x_b-x_0)*(y_0-y_c); the displayed two diagonal update factors
and their signs are correct. Det(S_q) is the product of its diagonal
coefficient-scaling entries, q^(t*(t-1)/2).

If f*g=r+P*h as raw polynomials, scaling that identity before reduction
gives S_q(r)=S_q(f)*S_q(g)-d_q*S_q(h). Here h has degree at most t-2,
so this use of S_q has the required degree bound. The element d_q is
a unit because all its CRT values are products of the cross-grid units.
Multiplication by d_q and coefficient scaling are invertible linear
maps; they do not discard the missing quotient. For f=Y^(t-1), monic
division sends the t-1 free coefficients of g in span(Y,...,Y^(t-1))
triangularly, with unit diagonal, onto every quotient of degree <=t-2.
Thus the stated rank-(t-1) defect submodule is proved for this operator.
It is not asserted as a lower bound for the native scalar-norm problem.

The commutator S_q*M_Y-q*M_Y*S_q=-d_q*e_top^T follows by removing the
single leading multiple of P from Y*g. Telescoping its kth power gives
the reported degree-J polynomial commutator. Its column space has the
stated J-vector spanning set, and an action costs soft(J+t) using actual
polynomial multiplication and reduction. This upper rank bound does
not assert maximal rank on native inputs or a fast determinant algorithm.

The actual first slice F(y_b) is acquired by MPE. Nonunit values refer
to original bounded seed indices and can be localized through the
original row polynomial. On the unit branch, CRT interpolation supplies
v, and the raw identity F*v+P*h=1 supplies an acquired h of degree <=J-1.
The valid next identity is

    F(qY)*S_q(v)=1-d_q*(h(qY) mod P).

Raw h(qY) is essential when J-1>=t. Scaling h mod P would lose another
quotient carry. The final report states this distinction explicitly and
charges the raw scaling/reduction in soft(J+t). A zero of its auxiliary
right side can come from S_q(v), so its saturated norm is correctly
handled by reacquiring the actual F(q*y_b) slice rather than invoking
an original-leaf decoder for an unrelated pivot.

The Q=q^s shift has one value-coordinate boundary because it overlaps
t-1 of the original nodes. Its norm recurrence is an exact division-free
product identity. The first old/new boundary lists cost soft(J+s), and
their indices are <st+s<=3m^2+3<4m^2, so the original bounded decoder is
available. The report retains the missing initial slice norm and does
not use this recurrence as an initialized fast endpoint algorithm.

The completed K-valued product acquires each of s states in soft(J+t),
then norms its supplied final residue in soft t. This proves the stated
soft s(J+t) cost even at collisions. The existing global blocking bound
soft(J+sqrt(J*st)) remains better. There is no free rank-t operation,
unlicensed cross-collision inverse, hidden field oracle, or claimed
whole-family exponent improvement in the reviewed report.
