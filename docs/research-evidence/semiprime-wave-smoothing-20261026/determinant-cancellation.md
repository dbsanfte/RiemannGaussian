# Determinant cancellation, cofactors, and a finite selected-residue analogue

26 October 2026. Requested read-only study of OpenAI, *Local smoothing for the Euclidean wave equation*, dated25October2026, supplied59-page PDF [paper.pdf](/tmp/semiprime-wave-smoothing-20261026/paper.pdf) and layout text [paper.txt](/tmp/semiprime-wave-smoothing-20261026/paper.txt). References below use PRINTED page numbers. This note studies §§3–4 and AppendixD; it does not independently certify the paper's analytic main theorems or resume the paused factoring goal. No PDE estimate is counted as an arithmetic algorithm.

**Useful transfer:** cancel a full determinant by constructing a compatible potential/energy whose variation produces exactly that determinant; rank-one backgrounds lower the degree of that construction. The rank-one homotopy identity can actually be evaluated on our acquired mixed operators in soft J. But the potential required to turn the physical selected residue into a boundary flux still contains an unacquired Cauchy solve. The distinction is explicit below.

## 1. What the paper cancels, precisely

Lemma3.2, equations(3.5)–(3.8), printedpp.11–12, supplies the Moore-determinant identities

C(A):H=partial_t det(A+tH)|_0,
det(A+t vv*)=det A+t v*C(A)v,
v*C(A)v=det(A restricted to v-perp).

They apply polynomially even when the full Hessian is singular/indefinite. Positivity and the matrix order are separate real/quaternionic assertions, not needed for those polynomial identities. The rank-one update identity can be checked directly by determinant multilinearity: at most one column can come from vv*. In a commutative ordinary-matrix analogue it is det(A+tuv^t)=det A+t v^t adj(A)u, with no inverse of A.

Lemma3.3, equation(3.12), printedp.13, says Hessian cofactors have divergence-free columns. Its proof is more informative than a generic adjugate formula: polarize the cofactor, test rank-one Hessian symbols g_jg_j*, observe their mixed cofactor kills every g_j, then test exponential inputs to conclude a polynomial differential identity. This is a COMPATIBILITY statement about a Hessian field, not every supplied matrix field.

Equations(3.10), (3.13), (3.14), printedpp.12–13, then give divergence form, Green's identity and the boundary compression formula. If u vanishes on r=0, H(u) restricted to the normal-orthogonal subspace equals rho H(r) there. By the compression/cofactor identity, the normal cofactor flux uses only that compression; it does not need u's second normal derivative. This boundary geometry is a substantive part of the cancellation.

In §4.2 the potential is NOT explicit data. It is the Dirichlet solution

D_u=H_fib(B0+u)>0, det D_u=lambda mu, u|boundary=0,       (4.8), p.15.

The conserved current A is orthogonal to the rank-one background B=H(B0). The full Hessian has scalar Schur complement sigma, so equations(4.9)–(4.10), p.16, give

A:H(u)=A:Sigma+lambda^-1 det H(B0+u).

The full determinant has no sign. The segment energy

E_z(u)=lambda^-1 integral_fiber u integral_0^1 det D_(theta u) dtheta,
X0=integral_fiber (-u)mu,                              (4.11), p.16,

is chosen so that Proposition4.2, equations(4.12)–(4.13), pp.16–17, yields

Delta_z X0 = boundaryflux - integral A:Sigma
                         -lambda^-1 integral det H(B0+u),
Delta_z E_z(u)=+lambda^-1 integral det H(B0+u).

The determinant cancels in the SUM. Cofactor divergence and a common null line make the energy's own lateral boundary coefficient vanish. Neither the sign of the full determinant nor a pointwise inverse of it is used. However both u and the energy derived from u must already have been constructed.

The rank-one background also makes det D_(theta u) have only TWO theta monomials. Lemma4.3, equation(4.14), pp.17–18, compares the resulting energy with X0. Its bounds use real positivity, Dirichlet sign and integration by parts. They do not imply a zero/nonunit algorithm over Z/N.

## 2. Independent small-matrix checks, including AppendixD

The ordinary symmetric subcase suffices to check the relevant algebra without importing quaternionic positivity. Let

B=diag(0,beta,0), H=[[a,b,c],[b,d,e],[c,e,f]], beta a unit.

Then the coefficient of lambda in det(H+lambda B) is

D_B(H)=beta(af-c²).

Its gradient matrix is

M=[[beta f,0,-beta c],[0,0,0],[-beta c,0,beta a]],

so M:H=2D_B(H) and M_TT=beta f. For a true Hessian H(u) and constant beta, the nonzero column divergences cancel by equality of mixed third derivatives. These directly verify the homogeneity and linearized-density mechanism in AppendixD, printedp.48.

If A is supported on the (T,y) plane, write its nonzero block as alpha. Impose alpha00=beta f, exactly the disk-equation density relation. Direct expansion gives

A:H-D_B(H)=beta(c+alpha01/beta)²+det(alpha)/beta.       (F1)

This independently checks AppendixD's completed-square formula, printedp.49. Over a real positive semidefinite alpha it is nonnegative; over our composite algebra it is only an exact identity with the explicitly required unit beta. No modular inequality follows.

AppendixD equation(D.1), p.48, makes the auxiliary PDE linear:

L_B u=C(B_fib):H_fib(u)=mu,

which after spatial Fourier transform becomes a disk Dirichlet Laplacian minus a nonnegative potential. Its existence/smooth parameter dependence still require solving that equation. The resulting energy is one half of X0, and the divergence/completed-square calculation yields (D.2), p.49. The dimensional degree drop is useful, but “linear” does not mean the solution or its boundary flux is acquired at input size.

## 3. Execute the rank-one homotopy on native operators

For ANY ordinary n-by-n matrix D over a commutative ring and supplied u,v,

det(theta D+(1-theta)uv^t)
 =theta^n det D+theta^(n-1)(1-theta) v^t adj(D)u.

If n,n+1 are units, polynomial coefficient integration gives

integral_0^1 det(theta D+(1-theta)uv^t)dtheta
 =det D/(n+1)+v^t adj(D)u/[n(n+1)].                 (F2)

This is the exact two-term segment mechanism in Lemma4.3, expressed without positivity. For n<=J, prepared primes>16H make the integer denominators safe; no arbitrary high-dimensional integral denominator is assumed invertible.

A circular application would take D=diag(W_h(T_j)), where W_h(X)=prod_(i<h)(X-q^i). Its full determinant equals the physical long leaf product times the known unit (-1)^(Jh) q^(Jh(h-1)/2), since each physical factor is 1-T_j q^-i. This unit is acquired by short-exponent powering. With rank-one background 1*w^t, the second term is the weighted sum of diagonal cofactors. At a unique good zero this gives a valid weak row-index pair for w=1 and w_j=j, but BOTH cofactor scalars remain unacquired. This regularizer is at the row-product level; it is not numerically the original physical leaf delta. The rank-one identity by itself does not pay those cofactor values.

There is a NONCIRCULAR application to the already acquired higher-Macdonald matrix

A=diag(R_i)M,
R_i=q^h(T_i-q^-1)/(T_i-q^(h-1)).

Its determinant is the paid unit q^(J(J-1)/2) product_i R_i. Its inverse action is paid in soft J: apply diag(R_i^-1), then inverse polynomial q-shift interpolation M^-1. The latter evaluates the interpolating polynomial at q^-1 T_i and needs no inverses of qT_i-T_j. Thus for any fixed supplied u,v, v^t adj(A)u=det(A) v^t A^-1u is ACTUALLY acquired in soft J, as is the ENTIRE energy(F2). Endpoint and row-separation gates remain exactly those of the frozen higher-Macdonald report.

A second actual test uses D=I-M. With l_j=L_j(0), P0=1*l^t and

kappa=product_(k=1)^(J-1)(1-q^k),

one has adj(I-M)=kappa P0. Choosing u=w,v=l gives cofactor kappa l^t w, and (F2) is kappa l^t w/[J(J+1)]. All are paid short interpolation/endpoint quantities. For u=1 this is the known endpoint projector normalization. No unknown clock-intersection mode is selected.

These are actual acquired homotopy energies, not symbolic determinant descriptions. Their matrices are generally nonsymmetric; we use the ordinary commutative determinant identity, not the PDE's positive Moore-Hessian estimate. If a symmetric Hessian example is required, the constant block matrix [[0,A],[A^t,0]] is the Hessian of the formal quadratic x^t Ay, evaluable from A-actions. Its compatibility is cheap, but it remains a regular known operator, not the singular W_h gauge. Neither construction supplies the physical selector merely by changing the name of its cofactor.

## 4. Exact finite Piola bridge: distinguish divergence from flux

In TWO grid directions let Delta_x,Delta_y be commuting forward differences and set

H=[[Delta_x²u,Delta_xDelta_yu],[Delta_xDelta_yu,Delta_y²u]].

Because its cofactor is LINEAR, forward column divergence of cof(H) is EXACTLY zero. For example Delta_x Delta_y²u-Delta_y Delta_xDelta_yu=0. This is a legitimate discrete counterpart of Lemma3.3 in the planar linearized case. For dimensions>=3 the nonlinear cofactor needs shifted-product bookkeeping; no unrestricted discrete Piola theorem is imported.

Even in dimension2, ordinary continuum flux contraction does not transfer unchanged: forward differences obey a shifted Leibniz rule. Put a=Delta_xu, b=Delta_yu and edge flux

Phi_x=a Delta_y b, Phi_y=-a Delta_x b.

Then the EXACT boundary-summable identity is

Delta_x Phi_x+Delta_y Phi_y
 =Delta_x a * S_x Delta_y b-Delta_y a * S_y Delta_x b. (F3)

This is an edge-shifted minor. It is not the unshifted det H. For the symbolic polynomial u=x²y² their constant coefficients already differ (-3 versus -1). Hence one may use a shifted edge-minor potential and exact boundary telescoping, or use adjoint/staggered differences; one may not silently apply the continuum product rule to our q-clock.

This identifies an actual possible design constraint for a new norm representation: the desired density must be realized as a COMPATIBLE shifted minor, and its potential/edge values must be acquired. Merely assigning arbitrary diagonal leaf values to a “Hessian” does not ensure those conditions.

## 5. Construct a finite linear Dirichlet analogue and charge it

Here is a completely explicit analogue of AppendixD. Put

f_i(delta)=p(q^(i-1))/(F(q^(i-1))+delta), 1<=i<=h,

where p=F' or H_w supplies the useful pair. Solve on a path

2u_i-u_(i-1)-u_(i+1)=f_i, u_0=u_(h+1)=0.             (F4)

The Dirichlet matrix is supplied and invertible: its determinant is h+1, a prepared unit. Its Green function is

G_ij=min(i,j)(h+1-max(i,j))/(h+1).

Summing(F4), or exact discrete Green's identity, gives the BOUNDARY FLUX

u_1+u_h=sum_i f_i,
u_1=sum_j(h+1-j)f_j/(h+1),
u_h=sum_j j f_j/(h+1).                              (F5)

At the unique good clock hit I, write A=p(q^I). The two boundary residues are (h-I)A/(h+1) and (I+1)A/(h+1). Their sum is A, nonzero for p=F'; the right/sum ratio gives (I+1)/(h+1). With the two p choices, the total flux ratio gives the actual hit row mark. This is a useful exact potential-to-boundary selector formulation.

But acquiring u_1,u_h is precisely acquiring the displayed index-weighted Cauchy sums. The simple inverse Green kernel is NOT a supplied potential. Direct source evaluation and prefix sums cost soft(J+h); no field inverse of a colliding source is allowed. A safe constant-rank completion at the retained bound is explicit: write d_i=F(q^i)+delta, p_i=p(q^i) and propagate

P'=d_i P,
Q'=d_i(P+Q),
V'=d_i V+p_i P,
U'=d_i U+p_i(P+Q),

from (P,Q,V,U)=(1,0,0,0). Then Q_i=iP_i,
V_h=P_h sum_i p_i/d_i,
U_h=P_h sum_i(i+1)p_i/d_i.

The transfer is a fixed4-by-4 polynomial matrix of degree O(J) in q^i, over a fixed delta jet. Its geometric blocks cost soft(Js+h/s), optimized at soft(J+sqrt(Jh)). At the good singleton V_h(0) is a nonzero cofactor times p(q^I), and U_h(0)/V_h(0)=I+1. Norm/coordinate gates precede inversion; wrong-bin saturation declines rather than invoking an additive annihilator decoder. Thus even a fully executed potential/flux analogue retains the old acquisition cost. No h-entry source vector is pretended acquired in soft J.

There IS a genuinely cheap comparison case: if the source is the REGULAR sequence f_i=F(q^(i-1)) rather than its reciprocal, the two sums in(F5) are finite geometric sums and first index moments, computable from the J coefficients in soft J (the r=0 coefficient uses ordinary integer sums). That potential has been acquired, but no singular leaf residue has been introduced. Turning the physical density into a reciprocal, zero-indicator or singular inverse is an additional operation. The real paper can use positivity/comparison to turn a regular known wave density into quantitative depth information; a composite ring supplies no corresponding ordering or maximum principle.

## 6. Prior match and the narrowly useful handoff

The rank-one determinant/cofactor algebra matches the frozen packed-residue/packed-source.md and ward-cavity-contraction.md (rank-two Ward cancellation, paid unit normalizer, rank-one reset and cofactor amplitudes). The acquired A/M example matches separated-selector/higher-macdonald.md and geometric-contraction/singular-pairing.md's known endpoint projectors. The selected finite boundary flux matches earlier q-Pearson/marked Cauchy sources. Those matches retain their prior credit.

What this paper adds to the design vocabulary is the role of COMPATIBILITY: a cofactor is divergence-free because it comes from a Hessian; a null boundary compression suppresses one flux; a segment potential cancels the full determinant without inverting it. AppendixD shows that a rank-one background can lower an auxiliary determinant equation to a linear one. The finite tests above show both a paid compatible regular energy and a compatible singular Dirichlet problem whose RHS/flux acquisition is still the long query.

A substantive transfer would construct, from the short native inputs, a compatible finite potential with an ACQUIRED mixed-cofactor density and a boundary flux provably equal to the useful selected residue, while avoiding the unacquired Cauchy RHS in(F4) or the singular W_h gauge in(F2). No such algorithm is claimed here. PDE existence, positivity and norm estimates do not pay the potential, and the exact identities alone do not establish an exponent gain.
