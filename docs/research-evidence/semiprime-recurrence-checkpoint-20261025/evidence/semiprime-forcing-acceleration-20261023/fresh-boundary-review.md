# Independent review: initialized q-grid boundary moments

23 October 2026. **PASS; no correction required.**

Reviewed complete `fresh-boundary-algorithm.md`, SHA256
`a0938be39b8877f1a3de75370de2440b9b800db3cdf3f3be50da6dd0044bdf24`.
This is a joint correction representation and supplied-moment decoder,
not an acquired nearlinear solve of the actual boundary feedback.

**q-grid split and gauge.** The exact identity
`X P_k=q^(-k)(P_k-P_(k+1))` gives the stated bidiagonal B modulo
`G=P_J/a_J`. Modulo the actual F, substitution of
`P_J=-f_J^(-1)sum_(k<J)f_k P_k` changes only its last column, with
the displayed positive rank-one vector a. Every f_J and q-power
inverted is a unit; no coordinate of a is inverted.

Evaluation in this P-basis at lambda_r=q^(-r) diagonalizes B. Here
`a(lambda_r)` means evaluation of the polynomial represented by the
q-Newton coefficient vector a. Extracting the last q-Newton coefficient
is extracting the leading monomial coefficient divided by a_(J-1).
Lagrange interpolation therefore gives exactly
`beta_r=1/(a_(J-1)G'(lambda_r))`, including its normalization.
All grid differences and derivative denominators use certified factors
`1-q^k` with k<J. The basis/gauge construction and inverse cost soft J.

**Actual startup and propagation.** Multiplication by `1-q^n C` in
this gauge gives (1), with its negative feedback sign. For n<J the
actual remainder is the nth q-Newton basis vector, so tau vanishes
until tau_(J-1)=1. This is the actual initialized trajectory, not an
assumed homogeneous zero solution.

In variation of constants, the free product contains the factor at
time r and vanishes once n>=J. A forcing at k<r also meets that zero;
for k>=r its remaining product is
`Q_(n-1-r)/Q_(k-r)`. This proves (2) with the displayed q^k factor
and no division by the zero at time r. Substituting A_r(q^k) gives
all J moment identities (3), retaining the entire correction.

**Joint decoder and horizons.** The coefficient formula for A_(r,s)
is correct. Writing `U_s=(-1)^s H_s/Q_s` and
`V_t=q^(binom(t,2))/Q_t` makes its inner sum one convolution,
followed by `Q_r q^(-binom(r,2))`. Hence decoding all J coordinates
from supplied H(L) costs soft J for this part, not J independent
projection calls. The terminal multipliers are the adjacent block
`Q_(L-J),...,Q_(L-1)`. One scalar q-factorial and J adjacent ratios
acquire them in soft `(sqrt L+J)`; inverse grid interpolation adds
soft J. The alpha factors are multiplied, not inverted, including
when they vanish at a native alignment. The supplied-moment decoding
claim is consequently valid over the composite ring.

All factorial denominators in (2)--(5), through the needed n=L,
lie inside the original through-L unit horizon. Negative powers of
q are known unit powers; no numerical local period or root is required.
The actual native range has L>=J, as used by this terminal block.

**Initialized rank-one feedback.** Equation (5) is exactly
`H(n+1)=(I+p_n gamma_n^t)H(n)`, where
`(p_n)_s=q^((s+1)n)/Q_n` and gamma_n is the displayed triangular
sum in tau_n. Its nonzero startup is
`H_s(J)=q^((s+1)(J-1))/Q_(J-1)`, including J=1. The triangular
transform and its transpose can compute one update nearlinearly in J;
running all n still incurs the long horizon. The coefficients of the
generating polynomial in (4) are not treated as already supplied.

The report thus proves a small initialized moment state, an exact common
moment kernel and a paid terminal decoder, while honestly leaving its
joint acquisition unproved. No query-rate gain or generic lower bound
is asserted. No source/repository edits, examples, tests, new literature
or backend expansion were used in this review.
