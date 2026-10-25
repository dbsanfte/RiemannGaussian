
## Paired Cauchy contraction and a whole-family determinant obstruction, 2026-10-24

The preceding fast coefficient action has now been converted into an
ACTUALLY acquired Cauchy factorization, and the proposed scalar determinant
replacement has been tested on the full covered family. That replacement
fails: its full matrices have UNIT determinants even though the original
coverage theorem guarantees a nonunit among their requested diagonals.
This is a uniform obstruction to that particular acquisition route,
not a factoring lower bound. The original covered query still costs
soft(J+sqrt(JL))=soft k^(3/2); the target soft k and the full one-sixth
bit/Lean theorem remain open.

Use the paid prepared branch, including actual rough beta and W cleaning,
rebuilt targets and seed screen, unit-separated retained targets,
J=Theta(k), J<=k, L=2k^2+2, and q=z with all 1-q^s through C=16k^2
certified units. Native block arguments are q^a/V_j, with original
row/interval labels and known unit factors retained. No encoded pivot
or auxiliary sum replaces the original bounded-leaf consumer.

**The Cauchy inputs are acquired.** For
P_b(Y)=sum c_nY^n=prod_(i<b)(1-q^iY), choose balanced width d and use
regular coefficient rows n=d*rho with n+d<=b. Put

    A0=S-q^b I, B0=(qS-I)diag(q^s),
    U_rho=q^(d*rho), lambda_s=q^(b-s),
    g_rho=c_(d*rho+d-1)*(q^(d*rho+d-1)-q^b),
    h_t=q^(-bt)*(q^(b+1);q)_t/(q;q)_t, 0<=t<d.

With W the lower Toeplitz matrix of h, the exact generalized eigenbasis
identity is A0 W=B0 W diag(lambda). Consequently E=B0 W, and

    C_reg=diag(g) K diag(eta) E^(-1),
    K_(rho,s)=1/(lambda_s-U_rho), eta_s=h_(d-1-s).

All cross exponents b-s-d*rho lie in [1,b]. All h constants, inverse
Toeplitz coefficients, B0 inverse prefix sums, g entries and the remaining
at most d tail coefficients cost soft sqrt b. The broader existing q
screen really covers h's factors through b+d-1. Thus this is an acquired
ring-safe Cauchy representation, not a field diagonalization oracle.
All native target evaluations of the removed tail cost soft(d+J).
The remaining paired bilinear expression still changes both vectors
at every target.

**The transformed forcing cancels at exactly the required points.**
For the FULL padded matrix define

    G(X,Y)=sum_(rho,r)c_(d*rho+r)X^rhoY^r,
    G0(X)=sum_rho c_(d*rho)X^rho,
    g(X)=sum_rho c_(d*rho+d-1)
                         *(q^(d*rho+d-1)-q^b)X^rho.

The adjacent coefficient identity proves, including the final row,

    G0(X)-G0(q^d X)=-X*g(X),
    (1-q^bY)G(X,Y)-(1-Y)G(q^dX,qY)=(Y^d-X)g(X).

The rank-two forcing vectors for G(y_i^d,y_j) are actually acquired
in soft(sqrt b+J) by MPE of G0/g at the real y_i^d nodes. On i=j,
this forcing vanishes identically and the equation reduces to
(1-q^b y)P_b(y)=(1-y)P_b(qy). It supplies a shift relation, not an
amplitude on each native q-orbit. It remains a cleared equation at
collisions; no zero or nonunit endpoint is divided away.

A transverse derivative was executed as well. T(Y)=partial_X G(Y^d,Y)
has acquired forcing and coefficient start T(0)=c_d, with

    (1-q^bY)T(Y)-q^d(1-Y)T(qY)=-g(Y^d),
    [Y^m]T(Y)=(floor(m/d)+1)c_(d+m).

Its exact degree is b-d with unit leading coefficient in the prepared
range. Full coefficient propagation is legal but costs soft b. Its
native values and the recovery of P_b(y) from them are not made free
by the short forcing or known coefficient start. This is a scoped
failed completion, not a degree-based lower bound on every algorithm.

**A full determinant loses the collision signal uniformly.** Take
nontrivial J>=2, d=J, b=J^2-1, and the FULL square coefficient matrix C_b.
The bounded/direct branch can handle J<2. In C_b E the last row is zero
except at its final entry -q^(J-1)c_b, which is a unit. Its upper-left
(J-1)-square block is the Cauchy matrix above with unit row/column
weights and unit node/cross differences. Therefore det(C_b) is a unit.

For any valid length-b window starting at a, put y_j=q^a/V_j. Their
pairwise differences are units. The actual rough preparation implies
every component ratio y_i/y_j has k-rough order. Raising to J<=k
preserves the difference masks, so y_i^J-y_j^J are also units. Hence
both ordinary Vandermonde matrices in

    M_a=V(y^J) C_b V(y)^t

have unit determinants, and det(M_a) is a unit. Its j-th diagonal,
however, is exactly P_b(y_j), the required original block value up to
its known unit factor.

Cover [0,L) by full windows starting at 0,b,...,(floor(L/b)-1)b,
and add the full final window starting at L-b when necessary. Every
window lies inside the original interval; the final overlap is allowed
for zero detection. Since J=Theta(k), the number of windows is bounded
independently of N. Original coverage guarantees a nonunit among the
P_b(y_j) diagonals of these windows, while EVERY det(M_a) remains a
unit. Thus replacing the covered query by these full determinants fails
on every continuing prepared input. This argument needs no successful
examples or hypothetical generic matrix.

The corresponding bordered Schur determinant also produces det(M_a),
not product_j(M_a)_(j,j). Removing its off-diagonal cycle contributions
would require additional acquired information; the Cauchy determinant
formula does not perform that removal.

**The small Schur correction was actually computed.** The square C
inverse is acquired through its Cauchy block and last unit pivot; native
Vandermonde interpolation is lawful by the proved separation. Therefore
the shifted full matrices K_s=G((q^s y_i)^d,q^s y_j) have paid soft-J
inverse actions even when an internal desired diagonal is nonunit.
Their rank-two update gives an actual 2-by-2 Schur correction. After
checking its ORIGINAL endpoint factors and acquiring their unit inverses,
its determinant is exactly

    q^nu * F(q^s)/F(q^(b+s)),
    F(X)=prod_j(X-V_j), nu=J(J^2-1)/2

in the first window. Both F endpoints are already cheap degree-J
polynomial evaluations. The next doubled update is also executed: its
4-by-4 correction is the corresponding two-slice endpoint ratio.
All endpoints used in these tests stay within the original interval;
any nonunit there goes to the original leaf consumer, never to division.

For a general length-r doubling, the retained diagonal matrices are
exactly diag_j P_r(q^s/V_j) and diag_j P_r(q^(b+s)/V_j). At r=b the
first is the original collection we needed to acquire. Describing the
low-rank correction does not supply these multiplying diagonals.
Multiplying the short identities across b shifts would give only a ratio
between two long products; acquiring that ratio is still a long operation.
Literal endpoint expansion costs soft k^2; the old block balance still
gives soft k^1.5.

**The checked structured-algebra theorems do not supply the missing
paired output.** The actual Cauchy factor has displacement rank one.
Applying [Bostan--Jeannerod--Mouilleron--Schost, Theorem 1.2](https://cs.uwaterloo.ca/~eschost/publications/BoJeMoSc17.pdf)
to J supplied right sides costs soft(J sqrt b), including their entries
and full outputs. For the literal attempted Vandermonde/operator
matching, the defect columns evaluate X^rho(X-q^(d*rho)); on separated
nodes their first min(number_of_rows,J)-1 columns are independent over
each local field. That particular defect therefore has growing rank.
This does not rule out another operator or a cancellation in the full
sandwich.

Using equal outer spectra presents a different issue: their commutator
annihilates all diagonal matrices. In [Olshevsky, Theorems 7.5--7.6](https://www2.math.uconn.edu/~olshevsky/papers/piv2.pdf),
the kernel parameters which become the diagonal are explicitly supplied
inputs. No theorem inspected here acquires those parameters from the
short off-diagonal generators. All normal-form and basis changes above
retain this distinction.

Proofs, exact primary applications and independent reviews are in
`/tmp/semiprime-paired-contraction-20261024/`. The original monic block/MPE
algorithm and original saturated-norm consumer remain a complete safe
completion at soft k^1.5. The outstanding constructive task is to acquire
the simultaneous paired diagonal, or a direct zero-safe product of it,
using more information than the tested full determinant or off-diagonal
forcing. No whole-family exponent improvement is claimed.
