# Universal two-GP query: executed shear, residue filter and spectral-dual specialization

26 October 2026. Scratch only; no tests, campaign, code or repository edits.
Read universal kernel-cover Section 7, the hybrid Cauchy-core audit,
and the current protected `semiprime-string-theory-research-proposal.md`.
The proposal was read without modification.

**Result.** The exact two-GP query has a paid old soft N^(1/4)
readout and a smaller b=0 screen. The tested Euclidean shear preserves
its separated finite blocks; completing the sheared clock adds a huge
new interval. A concrete first factor-congruence coarse-residue filter
is completely unselective on the 3-primary residue component. Both
principal specializations DO supply an exact small determinant with
cheap internal Vandermonde normalization, but its row scalars remain
the original disjoint finite q-products. The inspected spectral-duality
sources retain their block determinants and Fock normalization factors;
no initialized replacement for those row scalars was obtained. These
are scoped executed candidates, not general lower bounds.

## 1. Actual query, symmetry and fully paid baseline

Use the integer bounds of kernel-cover Section 7:
C=ceil(N/(2k)), V=O(sqrt k), W=O(sqrt(N/k)+sqrt k), q=beta^H,
H=k^2, with the exact supplied formulas for ceilings. The target is

    Z=product_(|b|<=V, |h|<=W, h!=Cb)(1-q^(Cb-h)).      (1)

Each literal index is omitted BEFORE specialization. Every retained
zero has a nonzero O(log N)-bit beta label H*(Cb-h). The universal
Gauss proof guarantees a local hit; nonunit/gcd cell/row/clock prefixes
suffice for localization. Exact-global-zero alone is not promised.
T_ext is paid once on a saturated terminating branch.

Pair (b,h) with (-b,-h). Since 1-q^(-e)=-q^(-e)(1-q^e),
(1) has the same nonunit and, for squarefree N, zero predicates as

    A0 * Phi,
    A0=product_(h=1)^W(1-q^h),
    Phi=product_(b=1)^V product_(h=-W)^W(1-q^(Cb-h)).  (2)

In the hard branch the public parameters satisfy C>W; this may also
be checked directly. Thus Phi has no literal factors. A0 is acquired
and localized in soft sqrt W, a valid smaller optional branch. On
its unit result Phi retains the guaranteed hit. This is a direct
finite symmetry fold, not numerical division of a collision.

The existing joint geometric backend evaluates Phi using V starts
q^(Cb) and one clock of length 2W+1. Its complete cost is

    soft(V+sqrt(VW)+T_ext)=soft(N^(1/4)+k).

Signed prefixes and the direct literal deletion in (1) remain legal.
This is an initialized algorithm, not a new exponent claim.

## 2. Execute the strongest elementary Euclidean shear

Set L=2W+1, C=dL+r, 0<=r<L. Write h=-W+t, 0<=t<L.
The exact exponent is

    Cb-h = rb+W-(t-dLb).                              (3)

Thus reducing the large coefficient C to r transports each original
clock to the ACTUAL interval [-dLb,L-1-dLb]. Their spacing is dL;
when d>=1 they do not overlap except possibly at endpoints. Keeping
them as blocks preserves the original V*L factor mass and starts.
The inherited evaluator still gives the baseline above, not a
length-L common window with the smaller coefficient r.

Filling a common clock envelope instead gives length
L+dL(V-1)=Theta(CV) in the present C>>W regime. Such an overcover is
safe only after deleting every literal exponent zero and retaining the
new nonzero-label decoder. It is a genuine overcover, not an equality.
One can then stop at the old sqrt N order/factorial prefix and factor
in soft N^(1/4); evaluating the enormous full envelope is unnecessary
for factorization. It does not yield a new soft-k prefix supplier.
A repeated continued-fraction shear must keep these finite blocks and
its new end boundaries; small Euclidean coefficients alone do not
acquire their scalar product. This conclusion only charges this
explicit transported-block implementation.

The arithmetic identity 2kC=N+d0, 0<=d0<2k, likewise gives exactly

    2k(Cb-h)=Nb+d0*b-2k*h.

IF an additional, paid roughening/coprimality certificate is available,
raising by 2k preserves local zero patterns. That certificate is NOT
assumed on the actual scalar branch here. Without it only the forward
implication is automatic: an old hit remains a powered hit, and extra
powered hits may occur. For a coverage-only factoring overset those
extra hits are still decodable by their OWN nonzero short labels
2kH*(Cb-h), after literal Cb=h is omitted; they do not establish
equality of the original prefix bits. Replacing q^N by its acquired
value changes neither the number of b starts nor the h clock. It
supplies no free reduction modulo an unknown order or inversion of
N-powering.

## 3. Execute a natural coarse-residue filter using PQ=N

Here is an actual native arithmetic test, rather than an arbitrary
root example. Fix a colour j=2 mod3, and inner kernel coefficients

    a=k*t+c*b, c=[N*jinv]_k,
    d0=2kC-N, delta0=d0-c.

The true physical hit associated to these coefficients satisfies

    2k*h=aP+bQ-k*t+b*delta0.                          (4)

Test whether public factor congruences modulo 2k^2 restrict h mod k
before finding P. Parameterize compatible factor residues by

    P_z=j+k*z,
    Q_z=N/P_z mod(2k^2).

They are units; choose any integer representative of Q_z. Equation
(4) defines h_z modulo k because its numerator is divisible by 2k,
and changing Q_z by 2k^2 changes h_z by a multiple of k.
Let R=k/2=3^e and use jinv modulo 2k^2. The exact inverse expansion is

    Q_z=Q_0-k*z*N*jinv^2+k^2*z^2*N*jinv^3 mod(2k^2).

Consequently

    h_z=h_0+u*z mod R,
    u=(a-b*N*jinv^2)/2 mod R.                         (5)

The quadratic term is a multiple of R. The integer numerator defining
u is even because the inner lattice gives a=b mod2. For 3 not dividing
b, the same lattice gives

    a-b*N*jinv^2 = b*N*jinv^2*(j-1) mod3,

which is nonzero. Hence u is a 3-unit and (5) is a BIJECTION on R.
This specific public congruence mask therefore retains EVERY 3-primary
coarse h residue. It cannot supply the hoped-for factor-k reduction
by that criterion, even with the true colour given.

Scope matters: the compatible modular pairs are not asserted to be
actual prime factors of this N. This is not an actual-semiprime
coverage impossibility theorem. It pinpoints exactly what this
first congruence-only filter omits: global factor/integer information
beyond PQ=N modulo 2k^2. A stronger correlated prime-specific test
could still discard candidates safely.

## 4. Package E on the ACTUAL two principal alphabets

After the A0 branch of (2), set

    J=V, M=2W+1, p=q^C, r=q, z=q^(C-W),
    x_i=p^i (0<=i<J), y_j=r^j (0<=j<M).

Then the exact finite rectangular amplitude is

    Phi=product_(i<J,j<M)(1-z*x_i*y_j).                (6)

Thus both alphabets really ARE principal GP specializations; unlike
an arbitrary native row list this extra structure is acquired.
The dual Cauchy formula in proposal Section 3 applies directly:

    Phi=sum_(lambda subset(M^J))(-z)^|lambda|
                  s_lambda(1,p,...,p^(J-1))
                  s_(lambda')(1,r,...,r^(M-1)).       (7)

It is a finite integral polynomial identity. No infinite topological
partition function is assumed evaluated and no hook denominator is
silently inverted.

An exact small determinant is particularly explicit. Put

    B(T)=product_(j=0)^(M-1)(1-z*T*r^j).

The bialternant identity gives

    det_(i,a)[x_i^a*B(x_i)]
                   =Phi*det_(i,a)[x_i^a], 0<=a<J.     (8)

A paid short-label order screen on p=q^C gives a factor or an adequate
short order guard. The Vandermonde denominator then involves only
p^s-1 for 0<s<J and is a certified unit. Its entire numerical value,
if wanted, is acquired in soft J by short powers and the product
formula with multiplicities. Thus the SMALL determinant's internal
normalization and both GP alphabets are genuinely paid.

The remaining initialized-entry question is now literal:

    B(x_i)=(z*p^i;r)_M
           =(q^(C-W+C*i);q)_(2W+1).                  (9)

These are disjoint distant blocks at the arithmetic parameter, exactly
the rows of Phi. Acquiring them jointly has the already paid baseline
soft(J+sqrt(JM)). The adjacent row ratio, if formally written, changes
the Pochhammer start by C, not by 1; clearing it retains the two
length-M blocks (or longer length-C endpoint products). It is not
an initialized short unit transfer. Formula (8) is an executed entry
map with a precisely unacquired diagonal, not a claim that every
possible spectral dual must have these entries.

Individual low-degree principal Schur/complete functions can be cheap
via finite q-binomial formulas, but (7) needs general rectangle
partitions. Replacing it by those low-degree boundary entries has no
proved identity with (6). Hook/principal normalization factors whose
exponents range beyond the native short guard need their own unit
or cleared-polynomial treatment; they cannot be assumed harmless.

## 5. Exact primary-source duality scope

[Marshakov--Semenyakin, 1905.09921](https://arxiv.org/pdf/1905.09921),
Section 3.1, explicitly implements rank/site exchange by permuting
factors in the rectangular Kasteleyn tensor space. Equations (3.15)-
(3.18) retain det(C_1...C_N) and the corresponding dual block factor;
equation (3.19) gives their nonconstant Casimir ratio. Thus its
small monodromy determinant is NOT an unnormalized replacement for
the common Kasteleyn determinant. Applying that theorem to (6)
requires a specific Kasteleyn/Lax parameter map and acquisition of
both retained prefactors; the paper does not identify the row
scalars (9) with cheap boundary entries. The exact finite parameter
map (6)-(9) above is what has been constructed here, rather than
claiming an unproved spin-chain map.

[Awata et al., 1608.05351](https://arxiv.org/pdf/1608.05351), Section
2.1 equation (13), states that the unrefined source specialization
t=q degenerates the generalized Macdonald states into Schur products
and makes its R-matrix proportional to identity. It does not give a
new interacting finite contraction of (7). Section 2.3 equations
(44)-(46) retain the nontrivial normalization N_AB and finite
Nekrasov factors G_AB. Its Fock/partition-labelled intertwiners and
SL(2,Z) automorphism are not a theorem that a rank/site exchange
initializes (9) over Z/NZ. In the refined case the source parameters,
normalization units and specialization through singularities would
all need checking; arithmetic q is not an auxiliary root of unity.

These sources support a genuine possible new representation, but no
finite arithmetic scalar algorithm is imported just from the words
spectral duality or principal specialization. This is stronger than
the earlier arbitrary-alphabet diagnostic: both actual alphabets and
the cheap short Vandermonde normalization have now been specialized,
leaving (9) as the explicit missing scalar input.

## Outcome

The completed guaranteed query and all auxiliary branches remain at
soft(k+N^(1/4)); the smaller A0 branch costs soft(sqrt W+T_ext).
No soft-k scalar, prefix predicate or coarse-residue supplier has been
obtained. The useful next target is a NEW initialized determinant or
vertex-state contraction for (6) whose coefficients avoid (9), or a
stronger global arithmetic restriction than the completely unselective
mask (5). All finite endpoints, literal omissions and once-only
T_ext remain explicit. None of the candidate failures is a general
runtime or factoring lower bound.

## 6. Executed unbalanced-Schur rectangle and paid unit boundary

The parent's sharper specialization has a genuinely initialized finite
boundary core and an O(r)-factor unit gate. A full ordinary q-prefix
through n-1 is NOT needed. The following replaces the earlier,
unnecessarily expensive denominator-screening version of this section.

Write the positive block as

    Zpos=product_(b=0)^(r-1) product_(t=1)^s
                               (1-q^(A+C*b+t)),
    r=V, s=2W+1, A=C-W-1>0, n=r+s.

Choose the partition with r nonzero parts

    lambda_i=A+(C-1)*(r-i), 1<=i<=r,
    lambda_i=0, r<i<=n.

Its Weyl principal-specialization cross-block factors are EXACTLY
Zpos: lambda_i-lambda_j+j-i=A+C(r-i)+(j-r) for i<=r<j.
Define

    V_d(q)=product_(a=1)^(d-1)(1-q^a)^(d-a),
    V_r(p)=product_(a=1)^(r-1)(1-p^a)^(r-a), p=q^C,
    D_n=(q;q)_(n-1), n(lambda)=sum_i(i-1)*lambda_i.

The finite CLEARED Weyl identity is

    s_lambda(1,q,...,q^(n-1))*V_n(q)
       =q^n(lambda)*Zpos*V_r(p)*V_s(q).              (10)

No factor in this identity is assumed invertible. In particular n
can exceed the original order guard, and D_n can be a nonunit.

### Execute the cleared small determinant

For the r-by-r Jacobi--Trudi matrix put

    d_ij=lambda_i-i+j=A+C*(r-i)-r+j,
    H_ij=(q^(d_ij+1);q)_(n-1).

The Gaussian-polynomial identity gives, as a POLYNOMIAL identity,

    D_n*h_(d_ij)(1,q,...,q^(n-1))=H_ij,
    det H=D_n^r*s_lambda(1,q,...,q^(n-1)).           (11)

All d_ij are positive here. Equation (11) remains valid at a nonunit
or zero D_n; it is not a numerical division formula for h_d.

For b=r-i put Z_i=product_(t=1)^s(1-q^(A+C*b+t)).
The numerator intervals in each row have the exact common intersection
[A+Cb+1,A+Cb+s], so direct factor multiplication proves

    H=diag(Z_1,...,Z_r)*U,

    U_ij=product_(t=-r+j+1)^0(1-q^(A+C*b+t))
          *product_(t=1)^(j-1)(1-q^(A+C*b+s+t)),
    det H=Zpos*det U.                              (12)

Empty products are one. Each U entry has r-1 endpoint factors,
r-j on the left and j-1 on the right. Across all rows only O(r^2)
ACTUAL short-power factors and entries are needed. Prefix/suffix
products initialize the complete array in soft O(r^2)=soft O(k),
with no factor inversion and no long clock scan.

### Cancel the determinant normalization FORMALLY, before specialization

Combining the universal identities (10)-(12) first over an
indeterminate q gives

    det U=q^n(lambda)*V_r(p)*D_n^r*V_s(q)/V_n(q).

This expression has an exact cancellation of powers. For 1<=d<s
the exponent r+(s-d)-(n-d) is zero; at d=s it is zero; and at
d=s+t, 1<=t<r, the remaining exponent is t. Consequently the
actual final identity is the division-free polynomial identity

    det U=q^n(lambda)*V_r(p)
                    *product_(t=1)^(r-1)(1-q^(s+t))^t.   (13)

It holds after specialization in EVERY ring. No numerical unit
assumption on D_n or V_n was used in cancelling the formal expression.
For r=2 it reads exactly

    det U=q^A*(1-p)*(1-q^(s+1)).

Thus the whole boundary determinant, not just its entries, is
acquired in soft O(r) from (13), including its monomial. The
exponent n(lambda) and all factor exponents have O(log N) bits.

Its unit status requires checking only the O(r) factors

    1-q^(C*d), 1<=d<r,
    1-q^(s+t), 1<=t<r.

Acquire their powers and products directly. A nonunit localizes to
one of these factors and yields either a proper gcd or its explicit
nonzero short beta label H*C*d or H*(s+t), feeding T_ext once.
On continuation ALL are certified units and det U is a known unit.
This costs soft O(r+T_ext), without the above-budget full-prefix
screen and without a speculative hook-denominator inverse.

### Exact hybrid handoff and remaining input

On the unit-boundary branch the CLEARED determinant det H has the
same zero/nonunit predicate as Zpos, by (12). This is a meaningful
new finite boundary specialization: the O(k)-entry boundary core,
its scalar determinant and its legal recovery branches are ALL paid.
The full Schur value need not have the same predicate if D_n is a
nonunit, and (11) does not license recovering it by division.

The unacquired diagonal in (12) consists EXACTLY of the r original
length-s products Z_i. A known invertible U does not initialize H's
linear action or singularity bit: multiplication by U cannot recover
unknown Z_i from boundary data. Row division by Z_i would be illegal
at the desired collision. A direct determinant algorithm for H still
needs a new initialized entry/action map avoiding those products.

This is an executed, compatible principal-Schur/topological-vertex
handoff, stronger than an arbitrary-alphabet formal analogy. It gives
a particularly precise next question: acquire the singularity or
coarse-hit bit of the CLEARED matrix H from its implicit diagonal
and the paid invertible U, at target cost. No such operation follows
from Jacobi--Trudi or the exact boundary determinant (13). The best
paid complete readout remains soft(r+sqrt(rs))=soft(N^(1/4)), plus
once-only T_ext. No norm acceleration or sixth-exponent claim is made.
