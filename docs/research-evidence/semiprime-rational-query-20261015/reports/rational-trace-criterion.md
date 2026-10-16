# Rational adjoint certificates: an exact finite-order trace criterion

2026-10-15. New classical route obstruction. No fast query evaluator, general scalar lower bound, repository edit, or new Lean endpoint is claimed. The theorem allows rational certificates with arbitrary poles, rather than merely repeating the earlier finite-Laurent obstruction.

## Main theorem

Let K be a field containing gamma of exact order R, where R is invertible in K. Let d>=1, gcd(d,R)=1, q=gamma^d and 0<=L<R. For an integer U put u=gamma^(-U), A=U-dL, and

    T(p)=(1-x^d)p(x/gamma)-u(q^L-x^d)p(x).

For every integer e, define z_e=u gamma^e. Then

    T(p)=x^e has a solution p in K(x)
      IF AND ONLY IF P_L(z_e;q)=0,
    P_L(z;q)=prod_(i<L)(1-zq^i).                       (1)

Thus a NONZERO row product forbids ALL rational endpoint-only certificates for this operator, even with poles at summation boundaries. For independent formal weights, over K(w_1,...,w_J),

    T(p)=sum_j w_j x^(e_j)

has a rational solution exactly when EVERY P_L(u gamma^(e_j);q) is zero. Rational dependence of the certificate on the weights is allowed; the shift fixes every weight. A numerical specialization of weights does not retain this latter iff statement in general.

## 1. Conjugation and elementary cyclic solvability

Define nonzero rational functions

    H(x)=prod_(r=0)^(L-1)(1-q^(-r)x^d),
    h(x)=x^A H(x),
    B(x)=prod_(r=0)^L(1-q^(-r)x^d).

Direct substitution gives T(h)=0, and

    (1-x^d)h(x/gamma)
      =u(q^L-x^d)h(x)
      =gamma^(-A)x^A B(x)=:C(x).

Consequently, with S(y)(x)=y(x/gamma),

    T(hy)=C(x)(S-1)y,
    T(p)=x^e iff (S-1)(p/h)=g_e,
    g_e=gamma^A x^(e-A)/B(x).                         (2)

These are rational-function identities, not assertions that h or C are nonzero at each numerical orbit point.

Define Tr(g)=sum_(t=0)^(R-1) S^t(g). Since S^R=1, trace zero is necessary for (S-1)y=g. It is sufficient too:

    (S-1)sum_(t=0)^(R-1) t S^t(g)=R g-Tr(g).

If Tr(g)=0, a rational solution is therefore

    y=(1/R)sum_(t=0)^(R-1)t S^t(g).                   (3)

No external Hilbert-90 theorem or numerical pole evaluation is needed. Formula (3) is an R-term existence formula using a hidden order, not a fast algorithm.

## 2. Exact trace formula: its coefficient is the query

Put

    Q_L^-=prod_(s=1)^L(1-q^(-s)),
    b_n=prod_(s=1)^L(1-q^(-(n+s)))/Q_L^-, 0<=n<R.

The denominator is nonzero because q has order R and L<R. The finite rational identity

    1/B(x)=[sum_(n=0)^(R-1)b_n x^(dn)]/(1-x^(dR))     (4)

holds. Indeed the coefficient of y^n in the formal expansion of prod_(r=0)^L(1-q^(-r)y)^(-1) is the displayed b_n, by the finite q-binomial generating identity, which can also be checked inductively from (1-q^(-L)y)F_L(y)=F_(L-1)(y). This formula specializes safely because Q_L^- is nonzero. The coefficients are R-periodic and the last L positions before R vanish, giving (4). Equivalently B divides 1-x^(dR), and (4) explicitly expands the complementary quotient. These are identities in x, not evaluations at zeros of B.

Let v=e-A and let n_e be the unique integer in [0,R) satisfying

    v+d n_e=0 mod R.

The denominator in (4) is S-invariant. The trace of x^k is R x^k if R divides k, zero otherwise. Thus

    Tr(g_e)=gamma^A R b_(n_e)
             x^(e-A+d n_e)/(1-x^(dR)).                (5)

Moreover q^(n_e)=gamma^(U-e)q^(-L), so

    q^(-(n_e+s))=z_e q^(L-s),
    b_(n_e)=P_L(z_e;q)/Q_L^-.

The exact obstruction formula is

    Tr(g_e)=[gamma^A R/Q_L^-] P_L(z_e;q)
              x^(e-A+d n_e)/(1-x^(dR)).               (6)

Every other factor is a nonzero rational function. Equations (2), (3), and (6) prove (1), including sufficiency.

For a formal weighted right side, the trace numerator is proportional to

    sum_j w_j P_L(z_(e_j);q) x^(e_j-A+d n_(e_j)).

Algebraic independence of the weights makes this zero iff all row products vanish, even when p is rational in those weights. For fixed numerical weights, cancellation among terms may occur; no analogous simple iff is claimed.

## 3. Actual hidden fields and composite-ring meaning

In either retained hidden field F_P, gamma has exact prime order R=R_P>P^.677, with R>16m². Set d=m², U=N+3d, e_j=3d-delta_j. Then gcd(d,R)=1, R divides P-1 and is invertible, L<=4m²<R, and

    z_(e_j)=gamma^(-N-delta_j).

These are precisely the normalized original targets, with no phase or interval change. The independently reviewed actual full-row density theorem leaves m-o(m) complete row products that are units modulo N, simultaneously over the candidate menu and every L<=4m². Therefore the formal weighted source has nonzero trace in BOTH hidden fields. NO rational certificate for its full weighted adjoint equation exists in either field, allowing arbitrary poles and rational weight dependence.

No Omega(m) independent RATIONAL sectors are asserted. After the gauge change, the rational cyclic-difference cokernel is one-dimensional over the fixed field K(x^R), identified by trace; the row values are coefficients of its single formal-weight trace remainder. The earlier Laurent sector grading does not survive arbitrary rational mixing.

This closes the exact rational-function certificate escape for THIS fixed operator on the retained actual family. A colliding row alone has trace zero and does have a rational certificate mathematically. That existence distinction is exactly the row zero test, not an acquired factoring algorithm.

A legitimate composite rational certificate whose denominator is a non-zero-divisor polynomial reduces to certificates in both hidden fields and is therefore excluded. A denominator becoming the zero polynomial in a hidden field is not a legitimate inverse there; cross-multiplication could then give a vacuous identity. Such degeneration requires a paid factor-aware interpretation, not free rational equality.

## 4. Secondary pole-chain check

Consider a rational p for which T(p) is Laurent. In an algebraic closure, the relevant nonzero coefficient-zero orbits are x_t=gamma^t zeta, zeta^d=1. They are disjoint R-cycles because gcd(d,R)=1. The first coefficient vanishes at t=0; the second at t=L. A pole of p at t contributes through the second term at t and the first at t+1.

Any pole string shorter than a full cycle must START where the second coefficient vanishes, t=L, and END just before the first coefficient vanishes, t=0. Hence it contains

    L,L+1,...,R-1,

at least R-L DISTINCT poles. The orientation is R-L, not L+1 or R-L-1. On the actual supply P does not divide d, so these coefficient zeros are simple. Away from coefficient-zero orbits, a pole propagates around all R points. With infinite-order indeterminate gamma, the analogous finite string would run increasingly from L to -1, impossible; rational solutions with Laurent right sides then have no nonzero finite poles.

The finite-cycle bound is sharp for a HOMOGENEOUS solution: h(x)/(x^R-1) is in ker T and, after canceling its first L orbit zeros, has exactly R-L poles on the gamma orbit. It does not solve a nonzero-trace inhomogeneous equation. Many poles or a high-degree denominator do not imply an operation lower bound for succinct evaluation. Formula (6), not pole count, is decisive here.

## 5. Primary context, not premises of the new theorem

Middeke, Denominator Bounds and Polynomial Solutions for Systems of q-Recurrences over K(t) for Constant K, arXiv:1705.04188 / ISSAC 2017, explicitly assumes characteristic zero and q NOT a root of unity. It develops denominator and polynomial-degree bounds for rational-solution algorithms; those hypotheses do not cover the actual finite-order hidden fields. Primary: https://arxiv.org/html/1705.04188 . PDF/text saved locally.

Chen–Paule–Saad, Converging to Gosper's Algorithm, gives universal-denominator/dispersion analysis for ordinary shift equations over characteristic-zero rational functions. It contextualizes endpoint pole constraints, not a finite cyclic algorithm or a query bit clock. Primary saved PDF: https://www3.risc.jku.at/publications/download/risc_3804/PublishedVersion.pdf .

Wang–Yang–Zhong, Polynomial reduction for q-holonomic sequences, arXiv:2606.07061v1 (2026), section 2.1, assumes a characteristic-zero field and indeterminate q. Its adjoint identity and shifted-coprimality conditions frame the earlier Laurent reduction. The present finite-order proof is self-contained and imports neither that field hypothesis nor a symbolic denominator algorithm. Primary: https://arxiv.org/html/2606.07061v1 . Freshly checked PDF/text preserved locally.

## Algorithmic outcome and limits

No fast weighted evaluator follows. Computing the trace obstruction coefficient is precisely computing the original row product; testing it is not free denominator preprocessing. Formula (3) uses R shifted rational functions and the hidden order, with no compressed whole-family acquisition theorem. Pole regularization cannot alter rational-function identity solvability. A regularization that changes the equation or introduces anomaly terms needs a new exact contract and paid collision localization.

The theorem concerns exact rational-function identity T(p)=E in K(x), equivalently a valid cleared polynomial identity, as in a standard Gosper certificate. It does not exclude ad hoc pointwise finite-grid interpolation with poles at omitted points, an identity only modulo x^R-1, or parameter-deformation finite parts. Such objects have a different contract and need their own exact collision semantics and paid evaluation.

Another operator, nonrational or noncyclic functions, a weighted evaluator retaining a remainder, or a norm-only identity remains possible. No such softly linear algorithm was found. This is a rational solvability theorem for a specific proposed endpoint route, not a complexity lower bound or completed factorization algorithm.
