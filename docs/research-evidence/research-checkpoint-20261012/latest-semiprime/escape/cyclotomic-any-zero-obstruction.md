# Public cyclic carriers cannot linearly restore the row zero union

2026-10-08. Classical arithmetic by /root/long_norm_escape, with /root's
independent linear-kernel argument. This report uses the frozen Hensel
supply but does not alter it. No repository or earlier artifact is edited.
It gives an actual-family obstruction to precisely stated ANY-zero repair
contracts, and an exact source-specific carrier that escapes those contracts.
It is not an arbitrary scalar circuit lower bound or a factoring clock.

## 1. The repair being tested

The preceding mask norm detected ALL coefficient zeros at a hidden prime,
whereas the original residual product detects ANY coefficient zero.
A natural repair seeks selectors e_j in a public cyclotomic algebra and
uses L(w)=sum_j w_j*e_j. Mutually orthogonal idempotents summing to one, with every selector
nonzero in each hidden field, would make the norm zero whenever any
selected residual w_j is zero.

A more general proposed repair chooses arbitrary public algebra elements
v_j and uses a homogeneous linear map L(w)=sum_j w_j*v_j. No orthogonality,
interpolation formula or hidden-factor oracle is assumed. The required
semantics at a hidden field are:

    ANY w_j=0 implies Norm(L(w))=0 for EVERY tuple w,
    some all-nonzero tuple has Norm(L(w))!=0.        (A1)

The second condition excludes a locally identically-zero query. An exact
ANY test has both conditions automatically. A weaker one-way test must
justify that nondegeneracy separately. The theorem also treats affine
payloads for the actual common-baby residual curve, and bounded-degree
nonlinear payloads on that curve.

On a further majority subset of the SAME actual semiprime supply, every
candidate auxiliary prime m has ord_m(P),ord_m(Q)>M^.96. Each of the four
public carriers

    F_p[T]/Phi_m(T),       F_p[T]/Phi_(m^2)(T),
    F_p[T]/(T^m-1),        F_p[T]/(T^(m^2)-1)        (A2)

then has only O(M^.04) simple field factors. Consequently none can satisfy
(A1) for J=Omega(m) independently supplied rows. Nor can a nondegenerate
affine payload preserve ANY over the complete actual common-baby axis:
it has at most O(M^.04) base-field zeros. A degree-D nonlinear payload
needs D=Omega(M^.96) to cover Omega(m) distinct actual targets.

These assertions concern the specified carrier and payload contracts.
A source-specific split carrier, a different scalar query or an implicit
algorithm with no such contract remains open.

## 2. A stronger simultaneous auxiliary-order deletion

Use the registered squarefree input supply N=P*Q from the Hensel/Fourier
audit, with X=M^3, balanced P,Q in a fixed X-scale interval, and
Omega(M^6/log^2 M) surviving ordered prime pairs. The prior joint bad-pair
loss is soft O(M^5.994). The actual projected gamma has exact distinct
prime local orders R_P,R_Q, larger than 3*m^2 at every allowed modulus.

Put B=ceil(N^(1/6)). The menu consists of the first
K(N)<=B^.020 primes m>=B. The fixed dyadic envelope K_*=O(M^.020)
and predecessor gap G_m obey the already reviewed facts

    p_(-K_*)(m)^6<N<=m^6,
    m=Theta(M),
    sum_m(G_m+1)=O(K_* M).                          (A3)

At fixed P,m the selector implication confines Q to only
O(m^2*(G_m+1)) integer candidates. Summing may include every prime in one
fixed M-scale interval, an overcount of the actual adaptive menu.

Let F=ceil(M^.96). Delete an input whenever either hidden prime p has
f_p=ord_m(p)<=F at ANY allowed candidate m. The possible orders divide
m-1. The number of such nonzero residue classes modulo m is at most

    sum_(d|m-1,d<=F) d <= F*tau(m-1).               (A4)

Indeed a class of order d is a root of X^d-1, which has at most d roots
in F_m. This counts all possible orders without a quadratic F^2 union.
No distribution theorem for primitive roots is being assumed.

For every fixed epsilon>0, the elementary bound tau(n)<=C_epsilon*n^epsilon
holds. One proof factors n into prime powers. For primes p>=2^(1/epsilon),
a+1<=2^a<=p^(epsilon*a). For the finitely many smaller primes,
sup_(a>=0)(a+1)*p^(-epsilon*a) is finite. Multiplying these finitely many
constants proves the uniform divisor bound. Use epsilon=.01 in (A4).

Each residue class has O(X/m+1)=O(M^2) integer representatives in the
factor bin. Thus the exceptional p count at fixed m is O(M^2*F*M^.01).
Combining with the Q strip in (A3), and both factor orientations, gives

    bad pairs <= O(M^4*F*M^.01*sum_m(G_m+1))
              = O(K_* M^5*F*M^.01)
              = O(M^5.990).                       (A5)

This deletion is directly from the SAME original supply. It has no seed
multiplier and permits full-input adaptive choice within the prime menu.
It is dominated by the prior soft M^5.994 loss, so the retained family
still has Omega(M^6/log^2 M) actual inputs. At every candidate m, both
f_P and f_Q exceed F. In general this argument works with F=M^delta
whenever delta+.020+epsilon<1; the displayed .96/.01 choice leaves a
strict margin while preserving the old dominant loss exponent.

The prior non-Teichmuller condition p^(m-1)!=1 mod m^2 is retained. It
implies ord_(m^2)(p)=m*f_p. No old proof bytes or density premise changes.

## 3. What the public cyclic algebras contain

Fix either retained hidden prime p. Since p!=m, every polynomial in (A2)
is separable. Frobenius sends a root zeta to zeta^p. All primitive mth
roots have Frobenius orbit length f_p, and all primitive m^2 roots have
length m*f_p. Each orbit contributes one simple finite field factor.
Thus, writing t=(m-1)/f_p, the respective numbers of factors are

    Phi_m: t,       Phi_(m^2): t,
    T^m-1: 1+t,     T^(m^2)-1: 1+2*t.              (A6)

The last two counts separate roots of orders 1, m and m^2. The algebras
are products of fields; there are no hidden nilpotents in these carriers.
From (A5), t=O(M^.04). The full algebra dimensions can be m or m^2;
those dimensions do not provide that many independent selector slots.

In a product A_p=product_(s=1)^t E_s of finite fields, an idempotent is
zero or one in each field component. Nonzero pairwise orthogonal
idempotents have disjoint nonempty component supports. Hence there are
at most t of them. An injective unital R-algebra embedding R^J into a
public cyclic carrier would induce the same J nonzero orthogonal
selectors in each hidden field, so J<=t is necessary. On the retained
family this cannot hold for J=Omega(m).

## 4. Every nondegenerate homogeneous linear merger needs J components

Here is the stronger field theorem, independent of idempotents. Let
A_p=product_(s=1)^t E_s, with t<p, and L:F_p^J->A_p be linear. Assume (A1).
Write L_s for its component maps. Since the norm is the product of the
field norms, its zero set is precisely the union of kernels ker(L_s).
The nonzero-norm assignment in (A1) makes EVERY component map nonzero.

For coordinate j let H_j={w:w_j=0}. By (A1), H_j is covered by those t
kernels. If no kernel contains H_j, its intersection with every kernel
is a proper subspace of H_j. For J>=2 each such intersection has at most
p^(J-2) points, whereas H_j has p^(J-1) points. Since t<p, their union
cannot cover H_j. Thus some kernel contains H_j. A nonzero linear map
whose kernel contains the codimension-one hyperplane H_j has kernel
EXACTLY H_j. Distinct j require distinct components. Therefore

    t>=J.                                         (A7)

For J=1 the assertion t>=1 is immediate for a nonzero finite algebra.
No restriction J<p or converse zero-union hypothesis was needed.

In (A2), p=Theta(M^3) and the total component count is O(M^.04), so t<p
and (A7) excludes J=Omega(m). This conclusion applies to arbitrary public
coefficients, not just the old graph mask. Coefficients may depend on the
complete input N and source family; that does not change the local count.

If only the first line of (A1) is imposed with J>t, the norm must instead
be identically zero as a function of the local input tuple. This is LOCAL
source blindness. It need not mean gcd N globally: the other CRT field
could behave differently. A source-independent local separator might
itself reveal a proper factor and would need its own acquisition and
coverage proof. That possibility is not excluded here. A genuine exact
ANY representation must have a nonzero all-unit baseline in both fields.

## 5. The actual common-baby curve and bounded nonlinear repairs

The tuple of common-baby residuals is w_j(x)=Y_j-x, not an arbitrary
independent vector. The source-specific curve therefore requires a
separate argument. Any homogeneous linear merger has payload

    L(w(x))=A-x*B,
    A=sum_j Y_j*v_j, B=sum_j v_j.                  (A8)

A fixed affine offset only changes A. In component E_s, A_s-x*B_s=0 has
at most one solution x in F_p, unless A_s=B_s=0 and the entire norm is
identically zero locally. Consequently a nondegenerate affine norm has
at most t distinct base-field zeros.

More generally let V(X) in A_p[X] have degree at most D. If its norm is
nonzero at even one x in F_p, every component polynomial V_s is nonzero.
Each has at most D roots in F_p, so

    #base-field zeros of Norm(V(x)) <= t*D.         (A9)

This uses the individual extension-field components, rather than charging
the much larger degree of their total norm polynomial.

The registered actual original q=1 group and its specified top-bit
subgroup have d=Omega(m) distinct targets in EACH hidden field. The
row-dependently normalized first-current collection is independently
injective. For any such collection, a representation preserving every
individual target collision over the complete common-baby axis has at
least d local zeros. By (A9), it therefore needs

    D>=d/t=Omega(M^.96).                           (A10)

In particular affine or bounded-polylogarithmic-degree payloads fail.
On the actual prime-period supply, alpha=gamma^(m^2) generates the same
local cyclic group as gamma. Every target Y_j is a power of gamma, so
all those d targets occur somewhere on a complete period baby axis.
Because R_p>d, an exact ANY test also has a nonzero baseline on that axis.
This is a source-faithful complete-axis obstruction in each hidden field.

No claim is made that a length-L=Theta(m^2) baby prefix contains d actual
targets: that intersection is the unfinished arithmetic coverage question.
For a particular bounded prefix, (A9) rules out a degree-D repair only if
more than t*D distinct target hits are independently proved inside it.
Variable row-specific baby origins are not replaced by a common x here.
The theorem is not a bound on arbitrary nonlinear scalar circuits: a
payload can compute a high-degree polynomial implicitly or use another
algebra or observation altogether.

## 6. A faithful positive carrier, with the long scalar still unpaid

There is an exact algebra that preserves the common-baby ANY predicate.
For any public target list Y_1,...,Y_J over R=Z/N, form

    H_Y(U)=product_j(U-Y_j), A_Y=R[U]/H_Y(U).

For EVERY x in R, with no primality, distinctness or inverses assumed,

    Norm_(A_Y/R)(U-x)=product_j(Y_j-x)=(-1)^J H_Y(x). (A11)

In the basis 1,U,...,U^(J-1), multiplication by U is the companion matrix
of monic H_Y. Its characteristic polynomial is H_Y by expansion of the
companion determinant. Thus det(C-xI)=(-1)^J H_Y(x), proving (A11) over
any commutative ring, including repeated roots and zero divisors.
This is a repair of the collision predicate, rather than the old ALL mask.

A public balanced product tree acquires H_Y in soft O(J*logN) bit time.
For each polynomial multiplication, lift residues to [0,N), pack them in
power-of-two digits wider than log2(degree*N^2), multiply the resulting
integers, unpack without coefficient carries, and reduce modulo N. The
packed bit size is O(degree*(logN+log degree)); logarithmically many tree
levels preserve the soft bound. The required fast integer multiplication
is the unconditional binary algorithm of
[Harvey--van der Hoeven](https://annals.math.princeton.edu/2021/193-2/p04),
whose official primary statement was verified online on 2026-10-08.
For actual first-current source targets this is a soft O(m) carrier
acquisition. It does not acquire all long residuals. If all pairwise target
differences are units, public Lagrange idempotents also give an exact
arbitrary-weight linear embedding into A_Y; their explicit dense J-by-J
coefficient array is not furnished for free. The common residual payload
U-x already needs no interpolation or such array.

Unlike the public cyclic carriers, A_Y is built from the actual targets.
In a hidden field it has the needed source root factors, with repeated
factors allowed. It is outside (A6)--(A10), not a contradiction to them.
The still-unpaid common-baby long query is exactly

    product_(i<L) H_Y(u*rho^i),                    (A12)

up to the known sign (-1)^(J*L). A whole-family soft O(m) evaluator of
(A12), its variable-origin analogues and the full source cocycle has not
been proved. Moving from the old mask to (A11) preserves ANY but does not
by itself remove the long scalar acquisition cost.

A free coefficient-field extension can create more cyclotomic selectors.
If its degree is h, a primitive orbit of length n splits into gcd(n,h)
orbits after extension. Thus t components become at most t*h components;
J independent selectors require h>=J/t=Omega(M^.96). Full splitting needs
f_p|h for Phi_m and m*f_p|h for Phi_(m^2). A contract materializing J field
entries as dense h-coordinate vectors then has Omega(J*h) base-field
output coordinates. This is an explicit representation charge only;
sparse field data, implicit extensions and arbitrary circuits are not
ruled out. No N-only extension construction is being granted as paid.

All new counts and carrier assertions here are classical. No Lean source,
backend validation, frozen report or metadata is changed. Proper recovery,
prime squares/nonunits/saturation, the complete all-semiprime bit clock
and peak-memory proof remain open. The guaranteed sixth-rate goal is
active and unproved.
