# Acquired constant-power core and an initialized boundary correction

23 October 2026. Scratch only. **Positive finite-ring operation:** the
matrix M=(I-C)D has an acquired characteristic polynomial and fast
Krylov conversion, so M^L e0 costs soft(J log L). The exact correction
below is initialized and executable with2J coordinates. No fast
evaluation of that correction, or improved original-query cost, is
proved. M^L e0 is not substituted for the covered product.

## 1. Actual finite-ring input

Use the normalized original query over R=Z/N. Its acquired unit-separated
targets are z_j=Y_j^-1, and F(X)=product_j(X-z_j) is monic of degree J.
The q-factorial units1-q^i are certified through the original horizon
16m², exceeding L=2m²+2 and J. Let C be multiplication by X on the
degree-<J monomial representatives modulo F, and

    D=diag(1,q,...,q^(J-1)), M=(I-C)D.

D is coefficient scaling on these representatives. It is NOT asserted
to descend arbitrary polynomial substitution modulo F.
Write F=X^J+sum_(i<J) f_i X^i, v=e_(J-1), and define

    w_i=f_i*(q^J-q^i), u=(I-C)w.

The companion boundary gives exact identities

    DC-qCD=w v^t,
    MC-qCM=u v^t.                                    (1)

All vectors and operator actions in(1) are acquired in soft J.
No unknown numerical order, cross-factor inverse or field extension
is supplied.

## 2. Characteristic polynomial, not merely an annihilator

Put P_k(X)=product_(0<=i<k)(1-q^i X), P_0=1, and let

    kappa_k=(-1)^k q^(k(k-1)/2)

be its unit leading coefficient. For EXACTLY0<=k<=J,

    M^k e0=P_k(C)e0.                                  (2)

Indeed before the last step the representative has degree<J, and
(1-X)P_k(qX)=P_(k+1)(X). At k=J only the final degree-J product is
reduced. Equation(2) is NOT extended to k>J.

Compute the q-Newton expansion

    F(X)=sum_(k=0)^J nu_k P_k(X), nu_J=kappa_J^-1.

There is a concrete finite convolution constructor. Acquire
`Q_i=product_(h=1)^i(1-q^h)` through J; all are certified units. Then

    [X^i]P_k=kappa_i*Q_k/(Q_i*Q_(k-i)),
    [X^i]F*Q_i/kappa_i
       =sum_(k>=i)(nu_k*Q_k)/Q_(k-i).                 (3a)

After reversing the index, (3a) is Toeplitz convolution with1/Q_n.
Its inverse kernel through the required finite length is kappa_n/Q_n:
their nth convolution is P_n(1)/Q_n, equal to0 for n>0 and1 for n=0.
Two finite polynomial convolutions and unit scalings therefore give
both basis conversions in soft J. No analytic q-series or unacquired
denominator is used. Thus all nu_k are actual acquired data.

The first J columns in(2) form a unit-triangular polynomial basis up to
the unit diagonal kappas. Call its coefficient matrix K. Both K and
K^-1 have soft-J actions by the same q-Newton conversions. Reducing
the expansion of F gives

    sum_(k<=J) nu_k M^k e0=0.

Since K is invertible, e0 is cyclic. In that actual basis,
K^-1 M K is the companion matrix of the monic polynomial

    mu_M(T)=kappa_J*sum_(k<=J) nu_k T^k.               (3)

This proves(3) is the CHARACTERISTIC polynomial over R, including
zero divisors, rather than only a guessed scalar annihilator over a
field. No eigenvalue extraction or simple-spectrum assumption is used.

Ordinary modular powering computes h(T)=T^L mod mu_M in soft(J log L).
Then K times its coefficient vector gives M^L e0. More generally the
same companion similarity gives M^k times any supplied vector with
that clock. All polynomial divisions use monic mu_M; its constant
coefficient need not be a unit. This fast core is legal even when a
native endpoint or an actual query leaf collides.

## 3. Exact initialized2J correction

Now divide the ACTUAL polynomial P_n as

    P_n(X)=F(X)Q_n(X)+R_n(X), deg R_n<J,
    t_n=v^t R_n, s_n=Q_n(qC)u.

The quotient is not supplied to the algorithm below. It specifies the
invariant. The two product identities for P_n imply

    R_(n+1)=M R_n-s_n,
    Q_(n+1)(X)=(1-q^n X)Q_n(X)-q^n*t_n.              (4)

For the first equality, use P_(n+1)=(1-X)P_n(qX) and
F(qC)e0=-w; hence the exact discarded-quotient contribution is
`(I-C)F(qC)Q_n(qC)e0=-Q_n(qC)u`. For the second, multiply
P_n by1-q^n X; the quotient from its proper part is precisely the
single scalar -q^n*t_n. Thus the fully initialized recurrence is

    R_0=e0, s_0=0,
    R_(n+1)=M R_n-s_n,
    s_(n+1)=(I-q^(n+1)C)s_n-q^n*u*(v^t R_n).         (5)

Every step uses constant many companion/diagonal actions, known unit
powers of q, and vector arithmetic. It costs soft J, uses O(J)
residues, and retains every quotient correction. No long integer
exponent or hidden input vector is being acquired for free. Direct
execution through L costs soft JL, which is NOT competitive with the
old soft(J+sqrt(JL)) blocked evaluator.

Equivalently the constant-power correction is the exact Duhamel sum

    R_L=M^L e0-sum_(n=0)^(L-1) M^(L-1-n) s_n.        (6)

The new fast core pays the first term and any supplied-vector M power.
It does not pay the jointly dependent forcing sum in(6).

## 4. Test of a constant gauge: what the feedback actually contains

Let A_n=I-q^n C and set eta_n=s_n-(M-A_n)R_n. Using(1), a direct
block shear of(5) gives

    R_(n+1)=A_n R_n-eta_n,
    eta_(n+1)=M eta_n, eta_0=0.                       (7)

The cancellation follows from
`A_(n+1)M-MA_n=q^n*u v^t`, with its displayed sign. Thus this exact
gauge isolates the constant-power channel but leaves the actual
variable-coefficient product in the other channel. It is not a
correction algorithm that uses only M^L. The initialized auxiliary
channel is zero; simply keeping it and dropping A_n would change the
answer. This is a specific tested gauge, not a general impossibility
theorem about another feedback solver.

The original one-shot target remains R_L, whose acquired target values
give all row products and ordinary bounded-leaf recovery. All source
and collision guarantees survive(5); no alternative family is used.
What is missing is a sub-blocked-cost algorithm for(5) or(6) using
their actual q-Newton/rank-one data. No such total-cost bound is
provided here.

## 5. Targeted q-Calogero primary check

The finite pair suggested by the Jackson conversion is actual data:

    A=C^-1*(D-I)/(q-1), AC-qCA=I+C^-1*w*v^t/(q-1).

C and q-1 are units by the original interface. Moreover A is just
the nilpotent q-derivative: A X^i=[i]_q X^(i-1), i>=1, A1=0.
Hence (-A,C) has the rank-one q-Calogero--Moser normalization.
This algebraic statement does not assert that every generic geometric
theorem's spectral or denominator hypotheses hold here.

Iliev's author thesis, chapter4 section4.1, formulas(4.1.11)--(4.1.12),
Proposition4.1.2 and Theorem4.1.3 (printed63--66), was read. Its wave
function is a finite determinant RATIONAL GAUGE TIMES the vacuum
q-exponential; its flows also contain exponential matrix data. These
are not a finite-ring algorithm for the initialized forcing in(5).
In particular Theorem4.1.3 assumes both spectra q-different, whereas
our Jackson A is nilpotent with repeated eigenvalue0 for J>1. The
more limited Proposition4.1.2 needs only its second spectrum condition;
that is not dismissed, but its determinant identity still does not
identify or compute the q-Pochhammer correction required here. No
analytic/infinite q-exponential is treated as a supplied modular scalar.

Primary URL: https://iliev.math.gatech.edu/thesis.pdf.
Cached PDF SHA256
`6267577c559475f22690a9bc42347a50d52edb7fead8e85038ca113986fc1647`.

The original q-Newton/unit interface and prior quotient guards are
credited; the new operation actually executed here is the fast core
(2)--(3), together with a fully initialized exact correction (5) and
its honest direct cost. No tracked/frozen edits, numerical examples,
downloaded-code execution, backend or improved factoring exponent.
