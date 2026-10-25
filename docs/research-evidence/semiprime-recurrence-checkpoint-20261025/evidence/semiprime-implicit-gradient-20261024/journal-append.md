
## Exact gradient/product transfer and a native tag readout, 2026-10-24

The complete acquired query still costs soft k^(3/2). This pass identifies
an exact relation between the new gradient outputs and the scalar product,
including its native shift contract, and a different gradient target that
returns a small row tag. Neither supplies soft-k acquisition. The separate
known fifth-bound factorizer and the open one-sixth/full executable Lean
bit-cost objective remain unchanged.

Reviewed sources in `/tmp/semiprime-implicit-gradient-20261024`:

- `gradient-product.md`: `8ef791e4c8beb245a8fee233deea946c2322f62cf9935985fc042185bda73894`.
- `native-orbit-blocks.md`: `a6ab972dd085669e3c322a5031597fd441821d43945b4fee62e97b3f2a818e15`.
- `uniform-query-transfer.md`: `ff4dd5abb31116f23652c6c81e9509006e8c5bdfdbd69b057279ec81f9d88b0d`.
- `cauchy-contraction.md`: `cc91bc1edc9534368081749933e980daa1ec04b6aea2b750366481741bc8bc70`.

### Two exact gradient calls recover the scalar product

For E(F)=prod_(i<L)F(q^i) and the preceding unweighted outputs
T_s(F)=sum_(i<L)q^(si)prod_(r!=i)F(q^r), put
F_q(X)=F(qX), a=F(1), b=F(q^L). There is the exact identity

    (q^L-1)E(F)=a[q T_1(F_q)-T_0(F_q)]
                              +b[T_0(F)-T_1(F)].       (1)

Prove it over the universal coefficient ring by taking the u and v
coefficients of

    (F(1)+u+v) E((F+u+vX)_q)
       =(F(q^L)+u+v q^L) E(F+u+vX).

Subtract the resulting two equations. No hit factor or product is canceled
or inverted. Only the actual guarded unit q^L-1 is inverted in (1), so it
works through all zero patterns and over the quadratic composite algebra.
For monic input supply F_tilde=q^(-J)F(qX), acquired in soft J; then
T_s(F_q)=q^[J(L-1)]T_s(F_tilde). The exponent is L-1, not L.
All boundary evaluations, q powers and scaling cost soft J.

The exact-output and shift-closure requirements matter. A routine returning
only a successful ratio on the original native points need not return these
two actual gradient values, or work for roots V_j/q. A uniform exact routine
with the stated one-shift closure would acquire E at the same asymptotic
clock as its two calls. This is an interface reduction, not a lower bound.
Conversely an actual division-free product circuit can be run in the
rank-three square-zero algebra to acquire both gradients with constant
overhead. General circuits require certified unit divisors and a valid
identity on the independent coefficient deformation; a scalar algorithm
correct only on the native set cannot automatically be differentiated
off that set. The old Baur--Strassen attribution is preserved; elementary
square-zero arithmetic supplies the actual ring argument here.

For the smaller-nonsplit native MINUS family, one common q-shift has a paid
interior-hit certificate. At a putative hit index i, the coprime odd local
orders give R=r_beta*r_W>256H² dividing
K_i=a_j P+Q+ell_j-Hi. Actual repaired bounds give

    0<K_0<3H²,
    -3H²-13H/2<K_L<-15H²/16-3H/2<0,
    L=3H+2.

Both magnitudes are below R. Thus neither endpoint 0 nor L is a hit at
that field. The actual soft-J screens of F(1),F(q^L) return a proper
factor or units, never saturation on the good orientation. The shifted
family has the same unique hit at I-1, with original label map i->i+1.
Wrong orientations may decline after guarded boundary tests. No outside
index L is silently assigned to the original interval decoder. The QRH
condition on supplying a good orientation remains explicit.

### The stronger uniform interface needs no orientation selection

There is a separate conditional algorithmic implication. Suppose a product
routine returns a verified factor or EXACT E(F_S) in soft(|S|+sqrt L)
for the original FULL both-colour family and its selected polynomial
subfamilies, with no unique-hit assumption. The existing full-family
coverage already guarantees a nonunit norm, whichever prime is nonsplit.
Acquire the subproduct tree in soft J. A proper norm gcd factors. At a
saturated node query ONE child: descend into it if saturated, or into the
other child if its norm is a unit. Norm multiplicativity preserves the
saturated invariant. At a leaf use the original row/index locator and
its authoritative consumer. The path costs

    soft(sum_d J/2^d+sqrt L*log(J+1))=soft k.

Every polynomial, query, gcd and original witness is paid. The strong
exact-gradient interface, through every zero pattern and one monic shift
of each such subfamily, supplies this product routine by (1); it needs no
boundary inverses. This route would NOT require the later QRH orientation
palette for coverage. It is an implication from a STILL MISSING fast
algorithm, not an unconditional sixth-root algorithm already achieved.
The weaker native unique-hit-only route retains its separate condition.
Current actual acquisition soft(|S|+sqrt(|S|L)) still gives soft k^(3/2)
after the same descent. Full executable/Lean bit composition remains open.

### A different sufficient gradient can return the row tag directly

For actual separated roots V_j and arbitrary public labels w_j, acquire
in soft J by a balanced weighted product tree

    H_w(X)=-sum_j w_j prod_(l!=j)(X-V_l),
    H_1(X)=-F'(X).

No root-difference inverse is required for construction. Let D_w,D_1 be
the resultant directional sums with H_w(q^i),H_1(q^i) replacing the weights
in T_s. At the promised unique hit I belonging to j*, the denominator
D_1 is nonzero at the smaller nonsplit field and D_w/D_1=w_j* there.
Choose the canonical tag w_j=j in[1,k). The output is a SMALL TAG,
not the group root and not a claimed Bezout cofactor.

Classify D_1 and, on its unit branch, write alpha=D_w/D_1=alpha0+alpha1*tau.
Its P-side value lies in the base field, so gcd(alpha1,N) is proper or N.
A proper gcd factors; N proves alpha is the global scalar z=alpha0.
Acquire and localize prod_(1<=j<k)(z-j) using integer blocking in
soft sqrt k. At a leaf a proper gcd factors; gcd N identifies the actual
integer tag j because both canonical representatives lie in[0,N). Query
that ONE stored original row at cost soft sqrt L. Wrong labels have
explicit bounded failure branches. This consumer costs soft k on all
labels and preserves the original witness requirements.

The actual acquisition starts at (A,D_1,D_w)=(1,0,0) with matrix
[[F,0,0],[H_1,F,0],[H_w,0,F]], of degree J. All its coefficients are paid.
The same explicit block algorithm still costs soft sqrt(JL). Interpolation
of arbitrary labels is a general primitive, not an additional arithmetic
consequence of the following native involution.

### Execute the native negative-inverse pairing with all carries

The map h=[-N/j]_k preserves the minus colour. Antipode and N-inversion
j->N/j each flip it; ORDINARY inversion j->j^-1 already preserves it.
For actual repaired A=a'_j, B=a'_h define the integers
d=(AB-1)/k, r=(h+Aj)/k, L_j=b'_h+B b'_j-2Br. Then exactly

    ell_h+B ell_j=k L_j,
    V_h V_j^B=pi^(k L_j) barpi^[(B+1)(N+1)+kd].

All carries have logarithmic bit metadata and are acquired in soft k.
Writing L_j=k t_j+l_j retains BOTH q^t_j and pi^(k l_j); the varying
barpi power is also retained. Since B may exceed k, its prime factors
are not automatically coprime to the k-rough orders. No powered support
equivalence is inferred.

For a two-cycle there are explicit integer-half centres K and Z with
V_j=KZ,V_h=K/Z, giving

    (q^i-V_j)(q^i-V_h)
       =K q^i[q^i/K+K/q^i-(Z+Z^-1)].

These centres still vary by pair; no common seed start has been acquired.
Fixed tags j²=-N mod k number at most16 only for the original controlled
modulus, and polylogarithmically many under the orientation palette.
Their original interval queries cost soft k in total; remove them only
after their products are actually certified units. Arbitrary quadratic
grouping also gives degree-(J-2) pair-label directions, so grouping alone
is not a faster acquisition method. The diagonal F retains degree J.

### Test the Cauchy symmetrizer with its actual correction

Use m=k, R=3k, ell=mR-1=3H-1. The prefix
P_ell(T)=prod_(n<ell)(1-q^nT) has the FULL coefficient rectangle
C_(rho,s)=c_(m rho+s); the THREE remaining original factors
n=ell,ell+1,ell+2 are actually acquired and retain original index consumers.
The paid C/C^t circuits and selected coefficients come from the earlier
exact q-binomial construction, without emitting Theta(k²) entries.
For y_j=V_j^-1 and X_j=y_j^m, the true matrix is V_X C V_Y^t and its
matched diagonal is P_ell(y_j).

The acquired eigenbasis E gives D=C E with displacement
D Lambda-U D=g eta^t, U_rho=q^(m rho), Lambda_s=q^(ell-s).
All cross differences are guarded units except the last corner; there
g_(R-1)=0 and the actual entry is d_star=-q^(m-1)c_ell. Retain this
known corner rather than divide by the zero cross difference.

Acquire Gamma(Z)=prod_rho(Z-U_rho), its symmetric q-grid Vandermonde V,
and H=Bez(Gamma,1), H_(r,s)=gamma_(r+s+1). For the lower companion M,
V M=U V, H M^t=M H and H=V^-1 diag(Gamma'(U)) V^-1.
All these maps, their needed inverses and their generators have actual
soft-k actions. They are not interchangeable identities. The MODIFIED
J-by-m object S_corr=V_X H V D has the acquired rank-two displacement

    diag(X) S_corr-S_corr Lambda=a_X r^t-p_X eta^t,
    a_X=Gamma(X), r^t=1^t D, p_X=V_X H V g.

Its chosen diagonal entries are actually acquired in soft k. A zero
X_j-Lambda_j uses the derivative of the polynomial numerator; a nonunit
is classified, never blindly inverted. This is not the desired native
diagonal of V_X C V_Y^t. Restoring the inverse requires
D_new=V^-1 H^-1 D=diag(Gamma'(U)^-1)V D, whose displacement contains

    diag(Gamma'(U)^-1)[U,V]D.

Its ordinary actions are paid; its matched contraction is the retained
middle-transform problem. Removing this correction changes the output.

The proposed further q-binomial cancellation was executed on the actual
symbols. Let a=q^(1-ell), c_top=c_ell, J_R,J_m be reversal matrices and
D_R=diag(a^(m rho)), D_m=diag(a^(m-1-s)). Then

    H^-1 C=c_top D_R T_Psi^-1 C J_m D_m,
    Psi(z)=prod_(rho<R)(1-q^[m(rho+ell-1)]z),

where T_Psi is the constant-one lower Toeplitz multiplication operator.
The reciprocal twist is essential. Psi(T^m) and P_ell(T) have exactly
the single common factor 1-q^(ell-1)T in every component: at an original
root q^-n, k-roughness removes the mth power, then the short q guard
forces rho=0,n=ell-1. This does not cancel the full long product.

There is an exact TRUE two-transform representation. Put
W=P_ell/Psi(T^m) mod T^(ell+1), and retain the polynomial E_tail in

    Psi(T^m) W(T)=P_ell(T)+T^(ell+1)E_tail(T).

The reshape of W is Qmat=T_Psi^-1 C. The reshape of E_tail is the
upper Toeplitz tail with entries psi_(R+rho-sigma) applied to Qmat.
Both transforms and transposes have actual soft-k actions; their
coefficients are not all emitted. The exact original values satisfy

    P_ell(y_j)=Psi(y_j^m) W_biv(y_j^m,y_j)
                 -y_j^(ell+1) E_biv(y_j^m,y_j).

Both scalar weight arrays are acquired in soft k by degree-R MPE and
powering, without inversions. The two PAIRED values remain unacquired.
Deleting the tail at unit y_j would be invalid. The transformed short
row pencil also has an acquired generator, but still requires the same
paired endpoint contraction. Thus the attempted difference of transforms
has all ordinary actions and weights supplied, while the whole query
retains its old soft k^(3/2) completion.

The pass changes the exact useful interfaces and records an executed
symmetry/cancellation attempt, not the exponent. It supplies no new
backend formalization or sample campaign. All prior prefixes, all270
frozen evidence entries and concurrent RH work are preserved.
