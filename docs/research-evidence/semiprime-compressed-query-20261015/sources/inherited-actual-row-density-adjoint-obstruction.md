# Most complete long-query rows are units, and actual adjoint reduction retains linearly many sectors

2026-10-15. New classical actual-source counting and adjoint argument.
No nearlinear evaluator, Lean theorem, or general scalar lower bound.

## Inherited source and statement

Use the SAME original order-qualified prime-pair supply N=P Q,
P,Q=Theta(M^3), of mass Omega(M^6/log^2 M), before the further frozen
observation deletions. At each allowed candidate prime m=Theta(M),
K_*=O(M^.020), the actual projected gamma has exact prime local orders
R_P>P^.677 and R_Q>Q^.677. In particular R_P,R_Q>16m^2 eventually.
The frozen supply also has P,P-1,Q,Q-1 units modulo m^2.
The menu-selector envelope and telescope are

    (m-G_m)^6<N<=m^6,
    sum_m(G_m+1)=O(K_* M),  G_m=o(m).

These are inherited hypotheses, not newly proved analytic inputs or
algorithmically supplied orders. Put d=m^2, q=gamma^d, and J=m-1.
For tags 1<=j<m, retain the ACTUAL full-input lift

    a_j = N j^(-2) mod m,  1<=a_j<m,
    I_j = j^(-1) mod m,
    D_j = (N-a_j j^2)/m,
    b_j = centered(m,-I_j D_j),
    delta_j = a_j+m b_j-2a_j j,  -3d<=delta_j<=d,
    z_j = gamma^(-N-delta_j).

Let 1<=L<=4m^2. A row hits in the P field when
P_L(z_j;q)=prod_(i<L)(1-z_j q^i)=0 there. The conclusions below hold
simultaneously for every L in this range by counting the maximum range.

The total number of labelled P- or Q-field row-hit incidences
(N,m,field,j) across the original supply and whole candidate menu is

    O(K_* M^6.969).                                      (1)

Delete inputs for which ANY one candidate/field has at least M^.997
hit rows. Their number is

    O(K_* M^(6.969-.997))=O(M^5.992).                    (2)

After union with all frozen soft O(M^5.994) deletions and the new short-
shift O(M^5.993) deletion, Omega(M^6/log^2 M) inputs survive. At each
candidate m, at least

    J-2M^.997 = m-o(m)

COMPLETE row products are units in Z/N. The full rectangle still has its
existing forced collision; this result asserts collision sparsity, not
failure of the original coverage theorem. Counts (1),(2) are incidence
and input-exception bounds, NOT acquisition times.

## Count multipliers rather than individual long indices

Fix an admissible P and candidate m, and put R=R_P. Divide its possible
Q selector strip into O(G_m+1) half-open boxes of width at most d.
Fix a box starting at Q_0. Since P=1 mod R, a hit is equivalent to

    Q+delta_j-d i=k R,  0<=i<4m^2,  k an integer.         (3)

Across this WHOLE box, all tags, and every permitted i, the left side
lies in one interval of length O(m^4), because delta spans only 4d.
Therefore all possible k lie in a COMMON interval containing at most

    O(m^4/R+1)=O(M^1.969)

integers. Here R>=c M^2.031. The interval may depend on P,m and the
box, which are already fixed. There is no extra index or tag factor in
this multiplier count.

Fix one such k. Reducing (3) modulo m and using N=P Q=a_j j^2 mod m
gives

    a_j A_j=P k R mod m,
    A_j=j^2-2Pj+P mod m.                                (4)

For A_j nonzero this fixes at most one canonical a_j and hence one Q
class modulo m. Consider two qualifying Q,Q' with the same j,a_j,k.
The exact lift implies

    m(b_j(Q)-b_j(Q'))=-I_j P(Q-Q') mod m^2.

Subtract (3) modulo m^2. The possibly DIFFERENT i values disappear,
giving

    (1-P I_j)(Q-Q')=0 mod m^2.                          (5)

If j is not P mod m, the coefficient is a unit, so Q=Q' mod m^2.
A half-open width-d box contains at most one such integer Q.

The polynomial A_j is monic quadratic, so has at most two zero tags.
At each of those, allow every one of the m-1 canonical slopes a_j;
each fixed slope again gives at most one Q by (5). These tags are false:
at the own tag j=P mod m, A_j=P(1-P) is nonzero because P,P-1 are
units modulo m. Thus the exceptional tags cost O(m), in total per k.

At the unique own tag j=P mod m, equation (4) fixes one slope and one
Q class modulo m. Do not apply the unit argument to (5) there. Retain
all at most m+1 integers from that class in the box, for O(m) more.

Consequently a fixed k permits O(m) (Q,j) row-hit incidences. A fixed
Q,j,k determines i in (3), so it does not add a multiplicity. Also
R>4m^2 and gcd(R,d)=1 ensure at most one allowed i for each Q,j.
Thus the entire box contributes O(M^2.969) row hits.

There are O(M^3) possible integer P values. Summing their boxes and
the candidate menu yields

    O(M^3 M^2.969 sum_m(G_m+1))
      =O(K_* M^6.969).

Swapping P,Q costs a factor two. If an input has M^.997 or more hit
rows at even one candidate/field, it contributes at least that many
incidences. Dividing the joint incidence bound proves (2), with no
second menu factor. Unite deletions on the original qualified supply.

The earlier O(K_*M^6.969) projected PAIR-collision estimate concerned
centered q=1 current targets and proved distinct/simple root support.
This proof instead counts FULL first-current ROW hits across all
indices 0<=i<4m^2. That earlier pair estimate is not used to infer (1).

## A finite-ring summation functional

This section is self-contained over R=Z/N. Write the polynomial
q-binomial coefficients as

    P_L(Z;q)=sum_(k=0)^L c_k Z^k.

They obey the division-free identity

    (1-q^(k+1))c_(k+1)=(q^L-q^k)c_k.

Define c_k=0 outside 0<=k<=L, u=gamma^(-N-3d), and f_k=u^k c_k
on that interval, zero elsewhere. For EVERY integer k,

    (1-q^(k+1)) f_(k+1)=u(q^L-q^k)f_k.                (6)

At k=-1 the left coefficient is zero; at k=L the right coefficient
is zero. These boundary checks are essential. No coefficient or
collision residual is inverted.

On finite Laurent polynomials A=R[x,x^(-1)], set sigma(p)(x)=p(gamma x)
and define

    L_op=(1-q x^d)sigma-u(q^L-x^d),
    L_op^*p=sigma^(-1)((1-q x^d)p)-u(q^L-x^d)p.

The R-linear functional

    Lambda(p)=sum_(k=0)^L f_k p(gamma^k)

annihilates EVERY L_op^*p. Indeed, shifting a finite sum gives

    Lambda(L_op^*p)
      =sum_(k in Z) [(1-q^(k+1))f_(k+1)
                     -u(q^L-q^k)f_k]p(gamma^k)=0.

The use of all integers in this equality introduces no infinite sum:
f has finite support. Equation (6) kills every summand.

Put e_j=3d-delta_j. Then

    Lambda(x^e_j)=sum_k c_k(u gamma^e_j)^k
                 =P_L(z_j;q).                         (7)

If a complete row product is nonzero, its monomial class is NONZERO
in A/im(L_op^*). In particular this holds for every unit row on the
retained family from (2). No characteristic-zero or indeterminate-
gamma hypothesis is involved.

## Actual residue sectors cannot all disappear

For every integer e, exactly

    L_op^*(x^e)=(gamma^(-e)-u q^L)x^e
                +(u-gamma^(-e))x^(e+d).                (8)

Thus L_op^* preserves the direct decomposition of finite Laurent
polynomials by exponents modulo d. Its image and quotient decompose
by those same sectors, even over a ring with zero divisors.

The source low-digit equation

    delta_j j^2=N(1-2j) mod m

implies that each low digit c has at most two tags: c j^2+2Nj-N is
a nonzero polynomial of degree at most two over F_m. Consequently
each residue sector e_j mod d has at most two tags as well.

On the family from (2), the unit rows therefore occupy at least

    (J-2M^.997)/2 = Omega(m)

sectors. In the formal independent weights w_j, the polynomial
E(x)=sum_j w_j x^e_j has a NONZERO class in each such sector of
A[w]/im(L_op^*), extending the operator coefficientwise in the weights.
The coefficient of any unit-row weight is already a nonzero monomial
class by (7); another formal weight cannot cancel it.

Hence an endpoint-only finite-Laurent adjoint reduction cannot remove
the weighted remainder on these ACTUAL finite-ring source instances.
Finite-order coefficient zeros do not evade this functional argument.
It strengthens the separate generic residue-sector obstruction; no
transfer of a characteristic-zero theorem is being assumed.

## What remains possible

This is a rigorous obstruction to a specified endpoint-only finite-
Laurent certificate route. It does not prove that the surviving sector
sums cost more than soft O(m) to acquire together. Retaining a sparse
Omega(m)-sector remainder is compatible with the desired budget if a
new implicit evaluator handles it. Rational certificates with poles,
other operators, noncyclic functions, nonlinear cancellation, and
norm-only algorithms remain outside this proof.

No all-semiprime acquisition bound follows from collision sparsity;
the full query must still locate or aggregate the few colliding rows.
The guaranteed one-sixth factorization algorithm and its Lean bit-
complexity proof remain open.
