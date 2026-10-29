# Independent review: rational certificates after two endpoint strips

26 October 2026. Read the complete rational-certificate report and the
frozen first-5J initial-chart source. No examples, tests, source edits,
research code or repository changes.

**Scoped PASS on the theorem for an admissible specialized rational
function.** Add an explicit admissibility paragraph for a certificate
initially written over the quotient/composite coefficient algebra.
The pole and endpoint arguments otherwise check, including finite
q order and finite characteristic.

## 1. Nonzero poles and finite-orbit endpoint orientation

At z=beta/rho, a pole of R(rho*z) forces a pole of R(z) unless
beta=rho*A=rho^(h+1). At z=beta, a pole of R(z) forces a pole at
rho*beta unless beta=rho^(-1). These exceptional points are distinct
because h+1<D. A coefficient zero can reduce a pole's order by one,
but cannot create a different support endpoint; if it does not remove
the pole entirely, further propagation is required.

Every nonzero multiplicative rho orbit has exactly D points, even
over the algebraic closure in positive characteristic. On an orbit
other than <rho>, neither exception occurs, so the entire orbit is
occupied. On <rho>, the interval h+1,...,D-1 has nonexceptional
internal edges in BOTH directions. A pole at any index0,...,h
propagates FORWARD to h+1; a pole already in the long arc propagates
to both ends. Thus the arc contains at least D-h-1 DISTINCT poles.
Their positive multiplicities only increase denominator degree.
No ordering of complex arguments, analytic convergence or non-root-
of-unity hypothesis is being used.

Hence a reduced denominator of degree<=5J indeed excludes every
nonzero finite pole in the native range D>256H^2, h=2H+1, J<=K.
The proof permits fully occupied or higher-multiplicity orbits and
does not accidentally discard those alternatives.

## 2. Zero pole, polynomial and constant cases

A pole of order m at zero has actual nonzero Laurent leading
coefficient c in the GOOD FIELD. Comparing lowest terms gives
`(x*A*rho^(-m)-1)c=0`. With x=rho^(-I) this is
rho^(h-I-m)=1. For m<=5J and 0<=I<h, the exponent is strictly
between -D and D, so m=h-I as an integer.

When zero is regular and there are no other finite poles, a reduced
rational function is polynomial. The constant equations imply
x*(1-rho*A)=0, impossible since x and1-rho^(h+1) are units.
For positive specialized degree d, the actual nonzero leading field
coefficient gives rho^(d-I-1)=1. With d<=5J the exponent range
again forces d=I+1. Globally nonzero leading coefficients are not
substituted for specialized nonzero field coefficients.

Finite characteristic causes no missing integer-factor condition:
these comparisons use Laurent coefficients and powers, not derivative
multiplicities or factorial division.

## 3. Endpoint screens and decoder are actually paid

The two strips are original indices [0,5J) and [h-5J,h). They
are disjoint for the hard K>16 range and cost O(J) explicit nodes,
including the far start obtained by short binary powering. For
`f(X)=product_j(1-y_j X)` the precise evaluation nodes are
X=rho^i=q^(-i). Monic evaluation-tree divisors require no unsafe
point-difference inverse; degree-J MPE at10J nodes costs soft J.

At a localized global original leaf, taking norms gives the scalar
annihilator2E with E=ell+a+bN-Hi. Since a,b>=1 and i<=2H,
E>=N+1-H/2-2H^2>0 from N>256H^2. The label is short and nonzero,
even on the wrong family. If a saturated norm does not give a whole
global point zero, the nonsplit field forces its coordinates to
vanish there and a proper coordinate gcd is available. The once-only
T_ext charge is correct; additive certificate zeros are not decoded.
Use |ell|<=H/2 if avoiding the unnecessary strict centered-endpoint
convention; positivity has a huge margin either way.

Unit continuation therefore implies 5J<=I<h-5J. The pole-at-zero
alternative needs m=h-I>=5J+1; the polynomial alternative needs
d=I+1>=5J+1. This proves the stated exclusion with no off-by-one gap.

## 4. Required admissibility clarification

For an expression P(z)/Q(z) initially supplied over B[X]/F, it is NOT
enough that Q is globally a nonzero polynomial. It must define a
rational function after good-field AND hit-root specialization.
Explicitly require that, after lawful cancellation/choice of an
admissible representative, the denominator specializes to a NONZERO
polynomial, and reduce numerator/denominator over that field before
measuring the two degree bounds.

If P and Q both specialize to the zero polynomial, the displayed
0/0 object is not a rational solution at that component. It cannot
be used for the finite endpoint algorithm without a separately proved
regularization. The local theorem does not exclude such singular
representations or a regularization whose resulting degrees exceed
5J. Conversely, whenever an admissible reduced local rational solution
with the stated degrees exists, the reviewed pole theorem rules it
out. Adding this paragraph makes the global-to-local scope explicit
rather than silently treating a vanished denominator as invertible.

## 5. Scope and finite telescoping

With only a zero pole, both nonzero endpoints1 andrho^(h+1) are
regular, so c_(h+1)=0 implies the genuine finite telescoping value
-R(1). With the long nonzero pole arc, rho^(h+1) is itself a pole;
zero times an undefined endpoint cannot be discarded without another
regularization. The report correctly retains that distinction.

This excludes only bounded reduced numerator/denominator solutions of
the PARTICULAR universal rational identity in z. It supplies no bound
against matrix/sparse/high-degree certificates, finite-grid identities,
projective readouts, or scalar/norm algorithms without that certificate.
No mathematical correction beyond the explicit admissible-specialization
qualification is needed.

## 6. Checked stronger necessary-support statement for arbitrary row values

The root's final strengthening is valid and needs only the ORIGINAL
short guard, not nonsplit unique-hit provenance. Work in ANY local
field/component, let theta be an arbitrary supplied unit row value,
and put L=5J. Its local q order D>16H implies D-h-1>L in the native
K>16 range. The nonzero-pole arc proof above is independent of theta
except for its being a unit, so degree(denominator)<=L excludes it.

If there is a zero pole of order1<=m<=L, the same lowest coefficient
comparison gives

    theta*A*rho^(-m)=1,
    theta=rho^(m-h)=q^(h-m),

which is membership in the LAST L original clock positions. With no
finite poles, a nonconstant polynomial of degree1<=d<=L instead
requires

    rho-theta*rho^d=0,
    theta=rho^(1-d)=q^(d-1),

membership in the FIRST L positions. Constants remain impossible.
These are exact field equalities, not degree congruences requiring a
known hidden I; no specialized q-index or large-order advice is used.
The degree and short-range assumptions ensure all named positions
are within the original h clock.

Thus an admissible reduced rational certificate of numerator and
denominator degrees<=L forces endpoint-strip membership for ANY row.
The two unit endpoint screens exclude that membership simultaneously
for every supplied row and every local component. Consequently such
certificates are excluded on all rows after unit continuation, not only
on the good hit. The original good-hit theorem is a valid corollary.

Admissibility remains essential: a polynomial identity obtained by
clearing P/Q with Q specializing IDENTICALLY ZERO does not produce a
rational solution. This theorem neither rejects an independently
acquired singular-denominator locator nor treats its zeros as supplied
membership data. If such a strategy is proposed, its denominator,
zero interpretation and acquisition must be audited separately.
The necessary-support theorem is about this small rational certificate,
not a general rational algorithm or joint-norm complexity lower bound.

## 7. Parameterized extension checked by the q-holonomic reviewer

The final root extension to any chosen 1<=L<=H is correct. Both endpoint strips are disjoint subsets of the original clock; MPE and leaf localization cost soft(J+L), with the same positive original scalar label and once-only terminating T_ext. The local short guard D>16H implies D-h-1>L. Zero-pole and polynomial resonances force exactly the last and first L indices respectively, so admissible reduced rational degrees<=L are excluded after unit continuation on every row component. A prespecified L=soft O(J), subject to L<=H, remains target-budget preparation. This parameterizes the same narrow certificate obstruction; it is not a lower bound for other algorithms. No tests or source changes outside scratch were made.
