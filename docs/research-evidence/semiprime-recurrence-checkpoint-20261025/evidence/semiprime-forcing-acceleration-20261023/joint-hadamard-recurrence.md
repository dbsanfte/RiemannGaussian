# Joint dyadic corrections and reciprocal-kernel adjoint test

23 October 2026. Scratch only. **The whole dyadic hierarchy telescopes
to two commutator terms; no paid query improvement follows yet.** This
is a bounded recurrence calculation with the actual matrix retained.
No columns of S were acquired, no examples were used, and no generic
complexity lower bound is claimed.

## Acquired setting

Use the legal padded square overquery and acquired operators of
`/tmp/semiprime-one-shot-construction-20261023/recurrence-design.md`,
SHA256 `ccf5ea70118db47e8e6f01a3360a6d0161e41f34c6065e1537b931cdd6f9b718`.
Here B is dyadic, y_i=z_i^B, Y=diag(y_i), Z=diag(z_i), and

    S D1-K S Q D0=U=[Y,xi*1^t],
    D0=I-Z, D1=I-q^(L*) Z, L*=B²-1.

All operators, their actions/transposes, and xi are acquired in soft B.
The prior endpoint guards either factor, decode a bounded global leaf,
or make D0,D1 units. Internal z,y differences are units. The legal
overquery preserves the original covered leaf, and its extra leaves
retain the prior <17H² versus >256H² recovery margin. These facts are
inputs here, not new acquisitions.

Write [A,B]=AB-BA and

    E1=QZ-q^(-1)ZQ,
    E_B=QY-q^(-B)YQ.

The first defect has an acquired rank-one generator. The second has
fast actions and the exact kernel

    (E_B)_(i,j)=q^(-B)*h_z(q*z_j)/h_z'(z_i)
                       *Sigma_B(z_i,q*z_j),
    Sigma_B(u,v)=sum_(s=0)^(B-1) u^s v^(B-1-s),
    h_z(t)=product_i(t-z_i).

## 1. Execute the symbolic hierarchy jointly

Set X_h=diag(z_i^(2^h)) and define the Hadamard operator

    T_h(M)_(i,j)=M_(i,j)/(z_i^(2^h)+(q*z_j)^(2^h)).

Every denominator is a certified unit: both terms lie in a common
odd-order subgroup, so their quotient cannot be -1 in either field.
The T_h commute. Their product T, h=0,...,log2 B-1, therefore divides
by Sigma_B(z_i,q*z_j).

Define polynomial operators

    A_s(M)=q^s M Z^s-Z^s M.

Dyadic factorization proves A_B=A_1*T^(-1), hence

    T A_B=A_1.                                      (1)

This uses no inverse of A_1 or A_B. It remains valid at the known
q-adjacencies, where their individual entry multipliers vanish.
Ordinary matrix multiplication gives the exact Leibniz identity

    A_s(SM)=S A_s(M)+[S,Z^s]M.                       (2)

Since E_B=q^(-B)A_B(Q), equations (1)--(2) give

    T(S E_B)=S T(E_B)+q^(-B)[S,Z]Q
                         -q^(-B)T([S,Y]Q),
    T(E_B)=q^(1-B)E1.                               (3)

This is the promised joint update: it has TWO aggregate commutator
terms instead of recursively expanding correction branches. All
intermediate lower-power commutators have telescoped. Neither side
has acquired unknown diagonal data as a generator.

What (3) does not do is evaluate T([S,Y]Q). Fast actions for S,Q and
[S,Y] give fast actions for their ordinary product, not for its Hadamard
transform. Expanding the commutators in (3) without another operation
just recovers (1)--(2); it supplies no new row-value equations.

There is a useful paid limited implementation. For an explicitly
supplied rank-k matrix M, T(M) has soft(kB) actions: away from the known
overlaps its kernel is

    1/Sigma_B(z_i,q*z_j)
       =(q*z_j-z_i)/(q^B*y_j-y_i).

These are two Cauchy sums per generator. At q*z_j=z_i insert the exact
value 1/(B*z_i^(B-1)) using the regular-part Cauchy formula. Overlaps
are publicly determined by the literal offset relation; all other
cross differences are units by the prepared odd-order and offset-span
promises. Thus no unknown collision denominator is inverted. This
implementation does not give a bounded rank-k representation for the
product [S,Y]Q appearing in (3).

## 2. Heterogeneous diagonal displacement: a viable denominator, a residual

The choice mu_i=z_i, nu_j=q*z_j makes the desired displacement

    Delta*=Z S-q S Z,
    (Delta*)_(i,i)=(1-q)z_i S_(i,i).                 (4)

The diagonal multiplier is an acquired unit, so an acquired short
generator for Delta* would directly give all rows. This avoids the
same-spectrum diagonal division issue.

Put Eleft=ZK-q^(-1)KZ. Directly commuting the FULL matrix equation gives

    Delta* D1-q^(-1)K Delta* QD0
      = ZU-qUZ+Eleft S QD0-q K S E1 D0.             (5)

The first and last terms have acquired constant-rank generators.
With h_y(t)=prod_i(t-y_i), Lagrange interpolation gives

    (Eleft)_(i,j)=q^(-1)*h_y(q^B*y_i)/h_y'(y_j)
                              /Sigma_B(q*z_i,z_j).  (6)

The denominator is a unit even at q*z_i=z_j. Thus Eleft is a concrete
inverse-dyadic-Cauchy kernel with paid actions, not an unknown diagonal
named as a generator. Equation (5) leaves Eleft S QD0 and the solution
of the generalized Stein equation to acquire; it is not yet a short
generator for Delta* itself.

The natural Vandermonde gauges diagonalize the interpolation shifts,
but the desired native diagonal then becomes a mixed product again.
Cheap actions of such a gauge and its inverse do not by themselves
recover that diagonal. No alternate gauge with both properties was
constructed in this attempt.

## 3. Reciprocal kernels: retain the middle S exactly

Equations (6) and the E_B kernel have reciprocal factors:

    (Eleft)_(i,j)*(E_B)_(j,i)=alpha_i*beta_j,
    alpha_i=q^(-B-1) h_y(q^B*y_i) h_z(q*z_i),
    beta_j=1/(h_y'(y_j)h_z'(z_j)).                  (7)

Consequently diag(Eleft diag(w) E_B)=alpha*(sum_j beta_j w_j)
is acquired in soft B. This cancellation is exact, including zero
numerator rows; it must not be extended by erasing a middle S.

For r_i(t)=Sigma_B(q*z_i,t), b_j=1/h_y'(y_j), and c_k=1/h_z'(z_k),
the actual middle-matrix expression is

    diag(Eleft S E_B)_i
      =alpha_i*(b/r_i(z))^t S*(c*r_i(z)).            (8)

All displayed divisions are by units. Splitting

    r_i(v)/r_i(u)
      =1+(v-u)*r_i[u,v]/r_i(u)

with the polynomial divided difference r_i[u,v] gives one paid common
scalar b^t S c plus a correction contracting [S,Z] against the
divided-difference kernel. Thus (8) is not the rank-one answer in (7).
Obtaining its B bilinear forms independently would cost soft B²; this
report does not do that, or claim that cost is necessary for a joint
algorithm.

For an explicit adjoint test, use the trace pairing tr(XS) and set

    L*(X)=D1 X-QD0 X K,
    X_w=E_B diag(w) Eleft,
    R_w=D1 X_w-QD0 X_w K-diag(w).

All X_w actions are paid, and tr(X_w U) costs soft B since U has rank
two. Cyclicity gives the exact residual identity

    sum_i w_i S_(i,i)=tr(X_w U)-tr(S R_w).           (9)

The reciprocal-kernel cancellation does not show R_w=0 or acquire its
last contraction. Reverse differentiation of the cheap first term
would give diag(Eleft U E_B), not the requested diag S.
Likewise an outer Hadamard mask can be moved out of a weighted trace
as an explicit diagonal weight, but that still leaves a trace of an
ordinary product with S. Cyclicity does not remove that middle matrix.

## Outcome and ledger

All acquired ordinary matrix operators above have soft-B construction/action
costs. Hadamard masks have only the separately stated supplied-rank-k
Cauchy-action guarantee. The joint symbolic recurrence (3) uses a constant number of
operator products plus T, represented by log B commuting masks; no
exponential correction tree is needed. The limited rank-k Cauchy action
is also executable at the stated cost. Neither fact pays the product
Hadamard contraction in (3), the residual in (5), or tr(S R_w) in (9).

These are concrete remaining operations for a new joint recurrence,
not supplied-data oracles advertised as an improvement. No verified
algorithm below the existing soft B^(3/2) query bound was found in this
bounded pass. There is no claim against future joint contractions,
other heterogeneous gauges, or deterministic factoring generally.

No tracked/frozen edits, independent S-column acquisition, numerical
examples, experiments, new literature transfer or backend expansion.
