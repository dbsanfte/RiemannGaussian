# Collision representations, character positivity and rational traces

22 October 2026. The user requested a broader literature search, a reading
of arXiv:2610.01447v2, and constructive attempts to find a representation
that makes the covered collision query affordable. Three Sol 6.1 agents
and root review produced the results below. The target remains an actual,
restriction-stable query in soft O(m), with J approximately m and L
approximately m². **That query has not been proved.**

This packet contains a deterministic linear-size orbit matcher, a simpler
rational Frobenius source, a soft-linear algorithm for fixed-weight power
traces, and an exact positive character representation of the original
scalar collision support. Their precise interfaces matter: none alone
provides the native varying-weight contraction or its long-index search.
No improved worst-case factoring exponent, new Lean theorem or full
factor-engine implementation is claimed.

## Deterministic orbit matching is acquired

For two explicit coefficient arrays A,B, run ordinary KMP string matching,
replacing every symbol comparison by gcd(a-b,N). A proper gcd returns a
factor. Otherwise gcd=N means equality in both hidden fields and gcd=1
means inequality in both. This applies to prefix-table construction as
well as searching. Therefore, until a factor is found, the entire adaptive
comparison transcript is simultaneously valid in both fields.

For equal-length arrays of length d, search B in A+A[:-1]. In at most 6d
gcd comparisons, the procedure either factors N or returns the exact same
complete cyclic occurrence set in both fields. Different local matching
sets must expose a factor. Neither random hashing nor sparse differences
are required. A common match is a match certificate; recovering a factor
from a common native match still requires its original leaf metadata and
decoder.

For prime m, indexing nonzero coefficients by a public primitive root
turns the automorphisms rho_j(X)=X^j into cyclic shifts. The coefficient
at zero is screened separately. Public indexing and root supply fit soft
O(m). This gives a genuine near-linear consumer for actually acquired
arrays, not for an unexpanded row/index family.

The [proof and reference implementation](implementation/kmp/README.md)
use the classical [Knuth--Morris--Pratt algorithm](https://www.cs.jhu.edu/~misha/Spring23/Knuth77.pdf).
Root independently reviewed the code and replayed all five test groups.
The tests use independent naive local occurrence oracles, including late
differences, different local matching shifts, repeated arrays, prefix-table
factor discovery and the automorphism orientation. They are implementation
controls, not empirical evidence of native-family coverage.

## A rational Frobenius source retains the cheap aggregates

In A=(Z/N)[X]/(X^m-1), let bar=rho_-1 and use the prepared public t with
t²=gamma. Put

    W=t(1+gamma X)/(X+gamma), Q_W=W^(m²).

The denominator norm is 1+gamma^m, a unit under the retained odd local
orders. W*bar(W)=gamma. Its coefficients, inverse and fixed powers are
acquired in soft O(m). This alternative source needs no auxiliary Gauss
sum or auxiliary prime. The row modulus can again be the first odd prime
at least ceil(N^(1/6)), with its standard paid sieve and individual gcd
screen. This is a choice for the new source; earlier frozen selector
results are unchanged.

Retain the canonical integer row a_j, ell_j, E_j and define

    Z_j=W^ell_j * (rho_j W)^a_j * rho_(j^-1)(W^N).

At the true tag j=P mod m, Frobenius gives Z_j=Q_W^I in the WHOLE local
algebra, using the existing exact relation m²I=a_j P+Q+ell_j. Its norm is
gamma^E_j, so a same-leaf paired hit returns the original scalar recovery
condition. A single component hit does not suffice.

The acquired antipodal products are not peculiar to Gauss sums. For any
unit W with W*bar(W)=gamma,

    Z_j Z_-j=gamma^(N+a_j) Q_W^(-s_j), s_j in {0,1,2}.

Thus all pair products still use three shared vectors and scalar
descriptors, and the whole product is one vector. The rational source also
has a safe Cayley coordinate and a degree-one Mobius trace coordinate.
These simplify the algebra while preserving every integer carry. See the
[source and aggregate proof](reports/torus-frobenius.md).

For any ONE acquired B, the comparison B=rho_j W clears to

    (X^j+gamma)(B-rho_j W)
      =(gamma B-t)+X^j(B-t gamma).

It is therefore exactly cyclic matching of two acquired arrays, and KMP
pays the entire family. With B=W^N, however, the true Frobenius relation
has an additional Q-th power. The covered native equation instead asks
for B=rho_j(A_(j,I)), where

    A_(j,I)=W^(m²I-ell_j) (rho_j W)^(-a_j).

Acquiring this variable family is still open. The
[constructive orbit investigation](reports/orbit-representation.md)
does not replace it by a fixed array without proof.

## An entire fixed-weight rational trace sequence is acquired

For arbitrary ONE explicit packed B and R=W/X, all m scalars

    Tr_A(B R^a), 0<=a<m,

are acquired in soft O(m), including every cyclic character component.
This improves the available power-piece calculation beyond unweighted
norms or traces. The algorithm works for odd composite m as well when
the stated units are retained.

Its generating function is Tr_A(B/(1-zR)). With

    g=X(X+gamma), h=g-zt(1+gamma X),
    U=Bg mod h, l=1-X^m mod h,

the exact formula is

    Tr_A(B/(1-zR))
      =m*t^-1*(U_0/z)+m*[X](U X^(m-1) l^-1 mod h).

The large cyclic-algebra computation has become arithmetic in a quadratic
algebra over short scalar power series. A balanced evaluation tree
acquires the two coefficients of U in soft O(m); the quotient is never
materialized. The division by z is an exact coefficient shift, so U is
retained modulo z^(m+1). The scalar norm inverted in the second term has
unit constant coefficient 1+gamma^m. No hidden-field root, discriminant
inverse or generic polynomial inversion is assumed.

The [algorithm and proof](reports/weighted-rational-trace.md) and
[independent review](reviews/independent-trace-review.md) give the complete
degree, precision and bit accounting. This is a paper-level algorithm
using fast polynomial arithmetic; no Python runtime bound is certified.

The quadratic row relation pays an actual native selected coefficient:
[X^(N mod m)]rho_(j²)(W^a_j)=CT((W/X)^a_j). But multiplying by B=W^N
changes the required sequence to

    H_a=CT(rho_(a/b)(B) R^a), b=N mod m.

The weight now varies with a. The full corrected row also retains its
ell_j-dependent factor. Applying the fixed-weight theorem separately to
all weights costs too much. The varying-weight diagonal and the remaining
factor must be acquired or eliminated before this becomes a collision
query. Equality of traces is not promoted to whole-algebra equality.

For the special weight B=W^N, the
[varying-diagonal investigation](reports/varying-weight-diagonal.md)
proves a symmetric two-parameter expression and exact cofactor reciprocity.
It also gives a carry-aware Euclidean reduction, whose correction remains
a nonconstant packed weight. A short, actually acquired decomposition
into automorphism eigenvectors would make the varying diagonal affordable;
no such decomposition of W^N is currently proved. The inspected fast
power-series composition theorem works modulo a precision variable and
does not by itself compute this cyclic diagonal.

The [special-power follow-up](reports/special-power-diagonal.md) supplies
an exact doubling recurrence for its integrands. With
D_2=R^2/rho_2(R) and the one acquired vector C=D_2^N,

    T_(2a-m*kappa)=T_a^2 / rho_(a/b)(C) * R^(-m*kappa).

D_2 is a fixed degree-four rational function. The recurrence retains its
integer carry, and acquiring C costs soft O(m). Its scalar constant terms
do not yet close under that recurrence. The
[rational-power recognition attempt](reports/rational-power-recognition.md)
also retains the wrap terms: low-order lifts of W^N are determined by its
cyclic representative, so an ordinary derivative of that representative
does not reveal the unknown cofactor exponent.

## A dyadic choice gives genuine rational norm recursion

The rational source permits the new choice m=2^k at the required scale.
The [independent native-interface audit](reports/dyadic-native-interface.md)
proves canonical coverage, the original index bounds and decoder, and
exact even-modulus residue palettes. Center b in [-m/2,m/2), keep odd tags,
and use the actual midpoint carry. The former inverse-of-4 square formula
is replaced by parity palettes when b is odd and a completed-square
formula using the integer b/2 when b is even. Four unit squareclasses and
two parity classes suffice for a menu of total size O(m).

The new constructive feature is exact rational-family closure:

    W_(gamma,t)(X) W_(gamma,t)(-X)
      = W_(gamma^2,gamma)(-X^2).

For m>=4 this is a relative norm into a cyclic algebra of half the rank.
The same identity holds for R=W/X. All fixed norm bases across the tower
are acquired in soft O(m). The even-modulus denominator becomes
1-gamma^m, a unit under the retained odd local orders; the terminal rank
two step has the actual specialization -X^2=-1. Earlier odd-modulus
statements are not silently reused with their old signs.

The [additive contraction investigation](reports/dyadic-cyclic-contraction.md)
gives the exact two-branch parity recurrence and a rational 2-by-2 transfer
matrix. It keeps the original integer powers, high/low exponent bands and
the native seed stride. A shared contraction of those changing weights
has not been derived. Norms of unit targets alone cannot supply it:

    Norm(T-s)=Norm(T)-s*Tr_relative(T)+s^2

already contains the missing additive term for a scalar seed. Thus the
dyadic choice supplies a real recursive representation to pursue, not a
completed collision test or an improvement from changing selectors alone.

An [independent coordinate check](reports/dyadic-tower-coordinates.md)
keeps a safe homogeneous pair throughout. A global Cayley division by
the even coordinate of B is invalid: W(1)=t and W(-1)=-t force that
coordinate to vanish at the public component Y=1 when N is odd. The
homogeneous form retains exactly the additive mixed term needed by the
collision test, without assuming a square-root branch or a unit chart.

## The requested paper led to an exact positive character representation

The exact requested version of Song--Zhang,
[An O(1) Bound for the KLS Constant](https://arxiv.org/pdf/2610.01447v2),
claims a dimension-independent Poincare/Cheeger bound for isotropic
log-concave real measures. The team read its substantive sections 1--9 and
references in parallel. This was an applicability assessment, not an
independent certification of the claimed breakthrough.

The relevant ideas are exact defect accounting, retaining one labelled
object through refinements, and controlling accumulated losses across a
whole block. A convex relaxation alone did not supply a rounding-mass
proof for the factor point. We instead constructed the following exact
positive representation, without using the KLS claim as a theorem input.

Let chi be the public Jacobi symbol modulo N, including zero at nonunits.
For scalar a,b define

    K(a,b)=sum_(t mod N) chi(t+a) chi(t+b),
    W_char(a,b)=K(a,b)^2-1.

An elementary prime-field correlation and CRT show W_char>=0, with strict
positivity EXACTLY when a-b is a nonunit. Hence

    E(Y,S)=sum_(a in Y,b in S) W_char(a,b)

is an exact additive, restriction-stable detector of original scalar
collision support. It keeps the same leaf and admits binary localization
and the existing proper/saturated recovery. No hidden local character or
zero projector is an input.

This representation still has a large contraction. Its public tensor
features are Phi_a(t,u)=chi(t+a)chi(u+a), and

    E=<sum_a Phi_a, sum_b Phi_b>-|Y||S|.

For geometric seeds there is an exact constant-cost boundary update along
a supplied simultaneous q-orbit of (t,u). A startup sum must still be
acquired. The retained prime lower bounds also give a public positive
decision gap, but neither amplification nor KLS pays an estimator with
the necessary error and total work. No efficient full contraction has
been proved. See the [construction and exact remaining query](reports/kls-representation.md)
and the [paper assessment](reports/arxiv-2610-01447-v2.md).

The [contraction follow-up](reports/character-contraction.md) reduces this
positive detector to a one-variable multiplicative convolution, since
all scalar targets and seeds are units. It gives an exact endpoint
difference equation and a proof-side character spectrum. Computing even
one particular complete Jacobi Fourier coefficient would recover P+Q
and factor N, so that coefficient is an alternate acquisition target,
not available Fourier metadata. Its computation and the required orbit
startup sums remain open.

## Literature, validation and remaining work

The broader search also examined real/modular stationary lattices,
modular hyperbola actions, elliptic butterflies, finite-algebra symmetry
breaking, torus compression and finite Weil transforms. The reports retain
their actual hypotheses and input costs. An arbitrary-unit quadratic
chirp transform is affordable; replacing its exact integer carries by
root-of-unity phases is not justified. These are candidate mechanisms and
scoped results, not general lower bounds.

Reports are copied verbatim from the research scratch directories.
Source URLs, versions and cached fingerprints are recorded in
source-pins.json; full external papers are not copied. The previous six
packets' 114 manifest entries were verified unchanged. No broad Lean
build, commit or push was performed for this research slice.

The active goal remains **find and prove a near-linear collision query**.
The new consumers, positive support representation and fixed-weight trace
algorithm narrow the constructive task. The native varying-weight/long
index acquisition, complete bit/controller proof and formal composition
remain open.
