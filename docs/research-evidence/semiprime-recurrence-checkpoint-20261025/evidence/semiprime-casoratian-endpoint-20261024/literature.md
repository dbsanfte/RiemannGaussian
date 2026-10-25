# Short q-difference equation versus an acquired finite endpoint

24 October 2026. Scratch mathematical audit. The executed rational-solution/contiguity candidate below does not improve the covered whole-family cost soft sqrt(JL). A recent primary infinite-product identity also supplies no exact finite-ring endpoint algorithm. This is a conclusion about these candidates, not a lower bound on the requested acquisition.

## Actual input and attempted initialized scalar solver

Pin the supplied finite class transport:
`/tmp/semiprime-quadratic-class-query-20261024/class-transport.md`, SHA256 `f813dc08c143a108758bd4a286bc601ded2a854b3a5c5bdb4693fc2695fca360`.
The preceding finite Casoratian audit is `literature.md` in that folder, SHA256 `5aa07471d0d2c514b62eff39c1b5f77eb247632cc15c0907eef82dff32f6bea4`; its acquired short normalizers are not long amplitudes.

There are M=J/r classes, J=O(k), k=d r^3, m=d r^2, H=k^2; r need not be Theta(k^(1/3)). Actual inverse arguments are

    Y_h=C D^h E^(h^2), 0<=h<r,
    P_L(Y)=prod_(0<=i<L)(1-q^i Y), L<4H,
    Z(X)=prod_h P_L(X D^h E^(h^2)), wanted Z(C).

All arguments are units, and original row/carry labels are attached. Here E^(r^2)=q^a for an acquired signed integer a, but D retains its mixed barpi factor. Define the genuinely supplied polynomial

    A(X)=prod_h(1-D^h E^(h^2) X).

Generating its r roots and coefficients costs soft r per class, soft J overall. The finite product satisfies

    A(X) Z(qX)=A(q^L X) Z(X), Z(0)=1.            (1)

No quotient through A or Z is used. Its degree is exactly rL with unit leading coefficient, even when roots collide. This is an order-one equation with degree-r coefficients, not a fixed-degree endpoint problem.

A concrete proposed execution is: use a rational q-difference solver on (1), select the normalized polynomial solution, then evaluate it at C. Over a characteristic-zero field with q not a root of unity the degree test is explicit. Comparing leading terms gives q^n=q^(rL), hence n=rL. Write A=sum a_t X^t, Z=sum z_n X^n. Coefficient reconstruction is

    (q^n-1) z_n = sum_(1<=t<=min(r,n))
                     a_t (q^(Lt)-q^(n-t)) z_(n-t).       (2)

The germ starts at z_0=1. Thus this candidate has a fully specified start, not an unknown native amplitude. Acquiring s coefficients by (2) costs O(rs) arithmetic operations and needs q^n-1 units for 1<=n<s. At s=rL+1 the literal recurrence costs O(r^2 L) per class, plus O(rL) evaluation; the full family costs O(JrL). Fast dense product construction can instead obtain Z in soft(rL) per class, but then pays soft(JL) overall. Neither reconstruction is the desired implicit evaluation.

There is an additional native specialization issue: the actual q guard ends at 16H, while rL may exceed it. Equation (2) is therefore not a lawful full coefficient algorithm under the given promise. One may construct the dense product division-free instead; one may not silently invert all q^n-1. Finite q also does not inherit the characteristic-zero uniqueness argument for normalized rational solutions: polynomial q-invariants can occur beyond the guarded range. These observations leave the actual known finite product well defined.

For completeness, an actually initialized coefficient-degree-r baby/giant evaluation of one class costs soft(sqrt(rL)+r). Running it separately for M classes costs soft(J sqrt(L/r)+J), which at L~k^2 is soft(k^2/sqrt(r)), worse than the existing joint degree-J query. Joint blocking uses degree Jb and O(L/b) giant targets and restores soft(J+sqrt(JL)). All these executions use monic products/MPE and do not divide by possible collision values. Their actual restriction capability and old leaf localization remain available; there is no new restriction witness from the rational-solution theorem.

## Primary rational-solution contract: a hidden query is explicitly assumed

S. A. Abramov, *Rational Solutions of First Order Linear q-Difference Systems*, FPSAC 1999 primary proceedings manuscript:
https://fpsac-archive.github.io/FPSAC99/ARTICLES/abramov.pdf
Cached `sources/abramov-1999.pdf`, SHA256 `af8f32f0a8325c86992a47f058efa8f2a2a73c91742fd2e64582aefbf666c0e0`.

The introduction, pp2–4, assumes a computable characteristic-zero field, q not a root of unity, and a q-suitable field: integer powers at which a supplied polynomial vanishes must be computable. Sections 2–3 construct denominator and degree bounds; Theorem 2 bounds polynomial degrees using an indicial equation, after which coefficients can be solved by linear algebra. It is not a scalar endpoint complexity theorem. Applying its field test to our native polynomials would import the very geometric intersection operation sought here. Even bypassing that test using the known finite product and known degree leaves the reconstruction costs in (2). A norm/coordinate pivot classifier over the quadratic composite algebra can handle encountered nonunits; it cannot supply the assumed power-root search or erase the dense output requirement of this execution.

This is a precise applicability audit, not an assertion that every rational q-difference solver needs this oracle or dense output.

## Recent primary lead checked: an analytic gamma product

Arash Arabi Ardehali and Hjalmar Rosengren, *A new product formula for (z;q)_infinity, with applications to asymptotics*, February 2026, arXiv:2602.11329:
https://arxiv.org/abs/2602.11329
https://arxiv.org/pdf/2602.11329
Cached `sources/ardehali-rosengren-2026.pdf`, SHA256 `74d803e5140ee566c76ad4186f2a6ea4cd4c398c5fbfe02a6fb855fc541e15b8`.

Equation (2), p2, expresses (exp(-y);exp(-beta))_infinity by an absolutely convergent product indexed by all integers involving gamma functions, exponentials and a dilogarithm; Re(beta)>0 and branch conventions are required. It is an exact analytic identity, not a modular algorithm. For the finite target one can formally form

    P_L(z)=(z;q)_infinity/(q^L z;q)_infinity.

Substitution changes each gamma argument by the integer L. Using gamma's finite shift identity produces L linear factors per gamma ratio; the infinite index and analytic prefactors still require the analytic cancellation supplied by the theorem. The paper gives no finite algebraic circuit or certified modular truncation for our input. No infinite tail is zero merely because q has large finite order. The actual native D and E are not specialized to the analytic theorem's convergence parameters. Consequently this new 2026 identity does not initialize the missing finite class amplitudes.

## Result and preserved target

The search found no verified 2024–2026 primary theorem improving this initialized native endpoint bound. Existing q-holonomic variable-degree algorithms, formal polynomial reduction, explicit-input spiroid composition and circuit-GCD audits are prior work and are not counted again here. The known short Casoratian matrix and the paid endpoint ratios remain useful exact data. They do not become Z(C) by the two executions audited above. No faster factor exponent, universal obstruction or new family-coverage assertion follows.
