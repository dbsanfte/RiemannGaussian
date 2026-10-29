# Modular composition and middle-product test for the selected projective norms

26 October 2026. Paper-only continuation. No tests, numerical campaign, repository edits or new factoring implementation. Read the frozen [coefficient-forms README](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-coefficient-forms-20261026/README.md), current AGENTS tail and the old [quotient-gradient weak-readout §§2–4](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-recurrence-checkpoint-20261025/evidence/semiprime-quotient-gradient-20261024/weak-readout.md). The older initialized terminal-norm/modular-composition audit is also recorded at [journal line 41990 onward](/home/dbsanfte/riemann/formal/docs/semiprime-factorisation-investigation.md:41990).

**Result.** The newer two-relation-matrix composition theorem does not initialize the long q-factorial, and the arbitrary-ring nearlinear power-series composition theorem computes only a short germ unless its long outer input is supplied. The latter application has been executed below: its exact omitted tail is a terminating basic-hypergeometric polynomial multiplied by a certified *unit* in the native quotient. Thus it cannot be erased by truncation at degree J. I obtained a fully initialized scalar finite-pairing target for any linear remainder projection, but not a faster algorithm for those pairings or the nonlinear two-norm output. No improved whole-query bound is claimed.

## 1. Inputs and output, with no hidden long polynomial

Use one acquired monic family: F=product_j(X-y_j), J<=K, h=2K²+1, q=pi^(K²), weights w_j, and the uniform good-one-nonsplit-field unique-hit promise. All y_j are units, and 1-q^r for 1<=r<=16K² are certified units. Put rho=q^-1 and

    G_h(X)=product_(i=0)^(h-1)(1-rho^i X),
    g=G_h mod F.

F and the division-free weighted directions

    H0=XF'-JF,  Hw=sum_j w_j*y_j*F/(X-y_j)

are acquired in soft J. The desired pair may be just

    D_F(g;H0), D_F(g;Hw),
    D_F(g;H)=[epsilon]Res(F,g+epsilon H),

or the row cofactor pair formed from G_h(y_j). Only its ratio at the promised field matters. The coefficient vector g and the long row values are **not** supplied.

Once g is supplied, monic multipoint evaluation at all supplied y_j, weighted-direction evaluation, prefix/suffix products and two scalar sums already compute the directional pair in soft J. This works even with repeated nonhit nodes and uses no interpolation inverses. Faster generic modular composition therefore cannot improve this already cheap *post-g* step. Its possible contribution must be acquiring g or contracting the two norms without g.

## 2. New primary theorem: two relation matrices

Neiger–Salvy–Schost–Villard, [*Faster modular composition using two relation matrices*, arXiv:2601.17422v1, 24 January 2026](https://arxiv.org/html/2601.17422v1), Theorem 1.3, computes supplied degree-<n outer-polynomial composition modulo degree-n f in soft O(n^((omega+3)/4)) field operations for input a in an identified nonempty Zariski-open set (about n^1.343). Failure of its genericity test permits fallback, not guaranteed fast native success. Theorems 1.1–1.2 handle supplied dense bivariate inputs and generic ordinate data; §4 computes projected modular powers. These are field contracts, not deterministic composite-ring guarantees. Appendix C's characteristic-polynomial/composition discussion is generic and does not initialize an implicit element.

**Execute the tempting specialization.** Taking f=F, a=X, outer polynomial G_h has degree h, not <J. Splitting its coefficients into blocks gives the exact supplied-input problem

    S(U,V)=sum_(r<b,t) a_(tb+r) U^r V^t,
    G_h(X)=S(X,X^b).

This bivariate array has h+1 coefficient slots. The source theorem does not accept its q-hypergeometric description as a replacement for the dense input. Reducing S first by a relation basis is precisely the operation that must combine its long coefficient stream. If one instead supplies g=G_h mod F as the short outer polynomial, that is circular: a=X then merely returns g. Taking a=g to exploit the characteristic-polynomial/first-variation route also assumes g. No claim that this supplied-input size is a lower bound for a structured q-factorial algorithm is made.

Even granting every native genericity and ring issue, applying Theorem 1.3 to already supplied degree-J inputs costs more than the available soft-J split-root postprocessing. Its genuinely new speedup does not target the current unpaid operation.

## 3. Nearlinear composition over the actual ring: exact germ/tail execution

Kinoshita–Li, [*Power Series Composition in Near-Linear Time*, arXiv:2404.05177v2, 22 September 2024](https://arxiv.org/html/2404.05177v2), Theorem 1, works over arbitrary commutative rings. Given **supplied** f,g of degrees <m,<n, it computes f(g) mod X^n in O(M(n)log m+M(m)) ring operations. This is an actual available composite-ring theorem, but it is power-series composition at a nilpotent variable, not arbitrary-modulus remainder acquisition; its M(m) term pays the outer input.

Here is its most favourable cheap-germ instantiation. Write G_h=sum_(t=0)^h a_t X^t. All first J+1 coefficients are acquired in soft J from

    a_0=1,
    a_t/a_(t-1)=-rho^(t-1)*(1-rho^(h-t+1))/(1-rho^t).       (1)

Every numerator and denominator in (1), for 1<=t<=J, is a certified unit, since 1<=h-t+1<=h<16K². Thus a_J is a unit. Let A_<J=sum_(t<J)a_t X^t. A direct ratio calculation gives the exact polynomial decomposition

    G_h(X)=A_<J(X)+a_J X^J B(X),
    B(X)=sum_(s=0)^(h-J)
       rho^(h*s) * (rho^(J-h);rho)_s/(rho^(J+1);rho)_s * X^s.    (2)

All the displayed finite denominator factors have exponents J+1,...,h, so they too are certified units. The terminating numerator parameter is exact. Equation (2) is derived from (1); it is not an asymptotic tail estimate.

Now reduce modulo F. Since F(0) is a unit, X is a unit in B[X]/F (acquire its inverse by the explicit monic polynomial relation). Therefore a_J X^J is a **unit** there. Degree truncation alone cannot kill the omitted term: it gives no nilpotence or vanishing certificate for B mod F. Accidental vanishing of that remainder is not excluded. The remaining task is B mod F, a length-(h-J+1) terminating hypergeometric evaluation. At a supplied root y_j it is the same exact tail correction B(y_j); replacing it by zero changes the collision equation without a proved justification.

Consequently a quasi-linear computation of G_h mod X^J, or of compositions of its acquired short germ, is real but does not yield g. A rootwise Taylor expansion about y_j would instead have constant term G_h(y_j), the original unpaid diagonal. A full invocation with m=h+1 legally computes the long outer polynomial problem, but includes its M(h) input/processing cost, beyond soft K. This is a test of these particular theorem instantiations, not an exclusion of other formal-series transformations.

## 4. A precise initialized middle-product/power-projection target

For any acquired linear functional ell on B[X]/F, put

    b_t=ell(X^t mod F).

Its first J values cost soft J by transposed polynomial operations, and its generating series is a supplied proper rational function with denominator rev(F). In particular b_t satisfies the constant-coefficient recurrence defined by F. Its far single terms or width-J blocks can be acquired from X^s mod F and that rational recurrence; arbitrary fixed-index powering costs soft J log s. These are legitimate power-projection inputs.

The requested linear remainder projection is exactly

    ell(g)=sum_(t=0)^h a_t b_t.                         (3)

Thus (1), the J recurrence coefficients and J initial b-values fully initialize a finite **q-hypergeometric × rational-recurrence dot product**. The number of scalar output coordinates requested may be small, but the two norm derivatives are nonlinear functions of g, so a single arbitrary projection (3) is not automatically enough for them.

This is a concrete handoff for a middle-product or approximant algorithm: compute (3), with the actual rho, h and F and all boundary terms, faster than expanding the long stream, or compute the two nonlinear directional norms directly from this representation. The 2026 source's projected powers manipulate a supplied algebra element and a rational geometric generating function; they do not supply this q-hypergeometric-weighted finite contraction. Truncated powers of X can even be trivial here, while the a_t pairing remains.

The tail in (2) gives an equivalent strictly specified finite contraction, with shifted hypergeometric parameters and a paid unit multiplier. It retains the complete original support rather than silently moving the far boundary. This is not a newly acquired preparatory vector or an assertion that the dot product has a lower bound. A new algorithm exploiting the actual arithmetic F may still solve it.

## 5. Costs, old credit and stopping point

| Operation | Fully initialized cost/output |
|---|---|
| F, H0, Hw and metadata | soft J |
| First J+1 q-factorial coefficients; exact tail parameters | soft J |
| Nearlinear composition of supplied short germs | soft J up to logs; only a short germ |
| New generic-field modular composition on supplied degree-J data | source exponent (omega+3)/4; no acquired g |
| All original G_h(y_j), hence either weak pair | old soft(J+sqrt(Jh)) |
| Guarded tag validation and HH once a correct weak pair is acquired | soft K |

The old [unique-gcd §§3–4](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-recurrence-checkpoint-20261025/evidence/semiprime-unique-acquisition-20261024/unique-gcd.md) already charges growing numerator windows in Bostan–Mori decimation. The old weak-readout report already initializes a three-state projective reset without the full remainder. Neither is presented here as new. The newer theorems checked above have different positive algorithms, but their exact native instantiations still require either the long outer stream, a remainder already solved for, or the hypergeometric/rational contraction (3).

There is no improved factoring exponent in this pass. The simpler monic fallback remains soft K^(3/2), and the best existing shorter weighted complete query remains soft K^(5/4). A useful next theorem would perform the finite contraction with its actual q-hypergeometric coefficients and native F, or directly acquire the two selected norm derivatives under the good-one-prime promise. Generic composition, nilpotent-germ composition and approximant-basis existence alone do not provide that acquisition.
