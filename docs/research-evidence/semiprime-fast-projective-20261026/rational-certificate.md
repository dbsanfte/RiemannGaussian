# Rational q-Gosper certificates after two paid endpoint strips

26 October 2026. Root's strengthening, independently proved below. Paper only; no tests, new research, implementation or repository changes.

**PASS.** After screening the first and last 5J original clock indices, no-factor continuation rules out an **admissibly specialized** rational certificate with both reduced numerator and denominator degrees at most 5J for the exact coefficient-side q-Gosper equation. Sections 1–5 prove the original good-hit corollary. Section 6 strengthens it to every supplied row in every local component, using only the actual short-order guard. This is a bound for that certificate ansatz, not a general scalar/circuit/algorithm lower bound or an exclusion of matrix certificates and different finite identities.

## 1. Actual equation and local parameters

Use the prepared good two-monic family. Let rho=q^-1, h=2H+1, H=K², J<=K, and D=ord_R(rho)>256H² at the nonsplit prime R. At the unique hit, the row root is x=theta=rho^(-I), 0<=I<h. Set A=rho^h. The certificate equation is the exact rational-function identity

    x(A-z) R(rho*z) - (1-rho*z) R(z)=1-rho*z.       (1)

It arises from c_t=a_t x^t and c_(t+1)/c_t=x(A-rho^t)/(1-rho^(t+1)). All finite denominators through t=h are certified native short units. Work over the good field, and over its algebraic closure when counting poles. The proof neither acquires D nor invokes a characteristic-zero summation theorem.

## 2. Nonzero finite poles require a long orbit arc

Let beta!=0 be a finite pole of R.

* At z=beta/rho, R(rho z) has a pole. Unless beta=rho*A=rho^(h+1), its coefficient x(A-z) is nonzero, so cancellation against the other term requires R to have a pole at beta/rho. Thus poles propagate backward except at beta=rho^(h+1).
* At z=beta, R(z) has a pole. Unless beta=rho^-1, its coefficient 1-rho*z is nonzero, so R(rho z) must have a pole there, forcing a pole at rho*beta. Thus poles propagate forward except at beta=rho^-1.

A simple coefficient zero can lower a pole order by one at an exceptional endpoint; it cannot furnish a different support endpoint. Higher orders can force additional propagation and only strengthen the lower bound below. At nonexceptional edges the pole orders must in fact agree, since a unique larger principal part could not cancel.

Every nonzero rho-orbit has exactly D points, in arbitrary characteristic. An orbit other than <rho> contains neither exceptional point, so any pole fills all D points. On <rho>, write the points as rho^s, s modulo D. Any nonempty pole support must contain the full arc

    rho^(h+1), rho^(h+2), ..., rho^(D-1),

of length D-h-1. To see this, propagation links all consecutive points inside this arc in both directions. Any pole outside the arc (indices 0,...,h) propagates forward into it; a pole already on it propagates to both its endpoints. A fully occupied orbit is harmless to this argument and has even more poles.

Thus a rational R with a nonzero finite pole has reduced denominator degree at least D-h-1. In our regime D-h-1>5J. Consequently degree(den R)<=5J excludes ALL nonzero finite poles, without assuming that R's denominator splits over the good field itself.

## 3. The pole at zero and polynomial alternative

If R has a pole of order m>=1 at zero, write R(z)=c z^(-m)+higher powers, c!=0. The lowest Laurent coefficient in (1) is

    (x*A*rho^(-m)-1)c=0,

so

    rho^(h-I-m)=1.                               (2)

For 0<m<=5J<D and 1<=h-I<=h<D, the exponent lies strictly between -D and D, hence m=h-I. This is a necessary condition, independent of behavior at infinity.

If zero is regular and there are no nonzero finite poles, R is a polynomial. A constant solution is impossible: its constant and linear equations imply x*(rho*A-1)=0, whereas x and 1-rho^(h+1) are units. Thus its degree d>=1. The z^(d+1) coefficient in (1) gives

    rho-x*rho^d=0, so d=I+1 mod D.                (3)

For d<=5J, the native ranges force d=I+1 as an integer. Finite characteristic does not alter (2) or (3); these compare actual nonzero Laurent/polynomial leading coefficients.

## 4. Both endpoint strips are actually acquired and legally decoded

Acquire f(X)=product_j(1-y_j X) as before. Monic MPE evaluates it at the 10J clock points with original indices

    0<=i<5J,       h-5J<=i<h.

For K>16 these strips are disjoint and inside the original clock. All start powers and endpoints have O(log N)-bit labels. One degree-J polynomial evaluated at O(J) explicitly acquired nodes costs soft J. No point-difference inverse is needed; the original short-unit range also proves node distinctness.

Classify any nonunit f value by norm and then original row leaves. A proper norm/coordinate gcd factors. If an original leaf is globally zero, y_j=q^i, taking norms supplies

    beta^(2E)=1,
    E=ell_j+a_j+b_j*N-H*i.

For E in either full monic family, a_j,b_j>=1, |ell_j|<H/2 and i<=h-1=2H, so

    E >= N+1-H/2-2H² > N-2H²-H/2 > 0.

The last inequality follows from the actual hard branch N>256H². This is a nonzero O(log N)-bit scalar label, valid even for the unpromised family. The inherited extractor is paid at most once on this terminating branch. No additive certificate/state zero is assigned an original-leaf label.

If the strip screen returns no factor, all those f values are global units. For the promised good family its unique hit therefore satisfies

    5J <= I < h-5J.                              (4)

Continuing work is soft J; a terminating saturated original-leaf branch costs soft(J+T_ext)<=soft K. The screen does not assert that either strip must contain a hit.

## 5. Degree conclusion and endpoint legality

Suppose (1) had a rational solution with both reduced numerator and denominator degrees <=5J on the good family after no-factor continuation.

1. Section 2 excludes nonzero finite poles.
2. A zero pole would have order m=h-I>=5J+1 by (4), contradicting the denominator bound.
3. With no finite poles R is polynomial, and (3),(4) require d=I+1>=5J+1, contradicting the numerator bound.

Therefore no such rational certificate exists. This sharpens the prior polynomial-certificate test by handling denominators, using a genuine paid last-strip acquisition rather than a hypothetical far-boundary promise.

If a rational solution has its only possible finite pole at zero, its values at z=1 and z=rho^(h+1) are finite since both points are nonzero. Then the standard finite telescoping equation is lawful locally: c_(h+1)=0 and a finite endpoint R(rho^(h+1)) give sum_(t=0)^h c_t=-R(1). A certificate with the long nonzero pole arc instead includes the exceptional endpoint rho^(h+1), so that zero-times-pole boundary cannot simply be discarded; it requires separate regularization. No finite-ring instruction to invert an uncertified rational denominator is inferred from these local facts.

**Scope.** This excludes degree-<=5J rational solutions of the particular universal-in-z equation (1) on the actual no-factor continuation. It does not exclude higher-degree sparse certificates, a finite-grid-only identity, another term normalization with its correction paid, matrix/approximant constructions, or an algorithm evaluating the projective tag without an expanded certificate. The full factoring goal and scalar acquisition target remain open.


## 6. Stronger necessary endpoint support, with admissible specialization

Root's final strengthening was independently checked in [review-rational-certificate.md §6](review-rational-certificate.md). It does not require theta to be the actual hit, nonsplit provenance or the stronger product order.

Work in ANY local field/component of the supplied quadratic algebra. Let theta be any supplied unit row value, L=5J, A=rho^h, and D=ord(rho). The actual coupled short-unit screen proves D>16H in each component, so

    D-h-1 > L

for h=2H+1, J<=K and K>16. Suppose an admissible rational function R=P/Q solves

    theta*(A-z)*R(rho z)-(1-rho z)*R(z)=1-rho z,

with reduced local numerator and denominator degrees at most L. The nonzero finite-pole proof in §2 is independent of theta except its being a unit. It excludes all those poles. A zero pole of order 1<=m<=L forces the EXACT field equality

    theta*A*rho^(-m)=1,
    theta=rho^(m-h)=q^(h-m),

which belongs to the LAST L original clock positions. With no finite poles R is polynomial; a constant is impossible by 1-rho^(h+1) being a unit, and a degree 1<=d<=L forces

    rho-theta*rho^d=0,
    theta=rho^(1-d)=q^(d-1),

which belongs to the FIRST L positions. These are necessary membership equalities, not a converse existence theorem. Neither a hidden index nor an acquired local order is used.

The paid unit strip screens exclude those equalities simultaneously for **every supplied row and every local component**. Therefore after unit continuation there is no such admissible bounded-degree rational solution on any row component, rather than only on the good hit.

### Explicit global-to-local admissibility

A quotient-valued rational certificate represented by polynomials P(z),Q(z) can be specialized to a row component only if its denominator specializes to a **nonzero polynomial** there. Reduce the resulting local rational function before measuring its two degree bounds. Specialization cannot increase the supplied degrees, but a zero polynomial denominator is not an invertible rational function and cannot be silently specialized.

In particular, a cleared identity whose P and Q both become zero polynomials gives 0=0, not a rational certificate or an endpoint readout at that component. If a separate regularization constructs an admissible local function, the theorem applies only to its actual resulting degrees. An independently acquired singular denominator might instead be proposed as a locator; its coefficient acquisition, zero interpretation, factor provenance and final contraction must be proved and charged separately. The necessary-support theorem does not supply that locator, a free partial norm or a factor from an arbitrary denominator zero.

Thus the all-component statement excludes small **admissible universal-in-z rational certificates** of this exact equation after the two paid screens. It does not reject singular representations merely by clearing their denominators, and does not imply a lower bound against finite-grid, sparse/high-degree, matrix, projective or other norm algorithms.

## 7. Parameterized endpoint-screen corollary

The constant 5 is unnecessary. Fix ANY public degree budget

    1<=L<=H=(h-1)/2.

Evaluate f at original clock indices 0,...,L-1 and h-L,...,h-1. These two strips are disjoint, remain inside the original clock, and all their nodes are acquired from the supplied q. Monic MPE costs soft(J+L), including powers and values. A nonunit evaluation is localized to one original row at an additional soft J cost and has exactly the positive label E>N-2H²-H/2 from §4. Thus the operation returns a verified factor in soft(J+L+T_ext) or certifies all these values units in soft(J+L); the terminating extractor is charged once.

For every local component the actual guard D>16H gives

    D-h-1>14H-2>L,

with the strict conclusion valid also at H=1 (the native branch has much larger H). The proof in §6 now applies verbatim with this L: a rational certificate with reduced numerator/denominator degrees <=L has no nonzero finite poles; a zero pole of order m<=L forces theta=q^(h-m) into the last strip; a polynomial degree d<=L forces theta=q^(d-1) into the first. Constants are impossible. Unit continuation excludes both necessary supports for every row component.

Hence after this paid screen there is no admissibly specialized degree-<=L rational solution of the exact universal-in-z certificate equation. In particular any **prespecified** soft-J degree budget (with L<=H) can be screened within soft J, or soft K including a terminating extractor. This removes a fixed-5J limitation of this certificate test. It does not exclude higher-degree implicit/sparse certificates, singular-denominator locators with independently paid semantics, matrix/finite-grid identities or other scalar algorithms, nor prove a general computational lower bound.
