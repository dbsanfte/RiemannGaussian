# Binomial trigonometric tests and the arithmetic floor

The exact phase optimizer now has the independently proved arithmetic
floor `1/80` on `1 < sigma <= 5/4`, uniformly in the height. Its previous
floor was `1/120`. The general theorem applies to arbitrary finite or
summable infinite nonnegative real-frequency families with nonnegative
phase kernel; the optimizer is one application.

The [scale and full-energy refinement](zeta-phase-binomial-scale.md)
strengthens this floor further while retaining the linked phases at each
height. The statements below remain the uniform binomial baseline.

This strengthens the existing zero exclusion near the right edge of the
critical strip. The signed bound required for every hypothetical zero
right of one half, including the subpolynomial Suzuki floor, remains open.

## The trigonometric structure

For any real test vector c indexed from 0 through N, keep the full Gram

    G = sum_(i,j) c_i*c_j*K((j-i)*theta).

If K(t) is the convergent cosine kernel with nonnegative coefficients
a_n and real frequencies omega_n, a coefficient a_r at frequency zero
contributes exactly a_r*(sum_i c_i)^2. Every other frequency contributes
a nonnegative sum of a cosine square and a sine square. Test coefficients
c_i themselves may have either sign.

The new lag coefficient keeps both orientations:

    R_c(k) = sum_(|i-j|=k) c_i*c_j.

The exact identities are

    G = R_c(0)*K(0) + sum_(k=1..N) R_c(k)*K(k*theta),
    R_c(0) = sum_i c_i^2.

Thus, writing A=sum_n a_n,

    a_r*(sum_i c_i)^2 - A*sum_i c_i^2
      <= sum_(k=1..N) R_c(k)*K(k*theta).

No individual return is replaced by a common ceiling. The Lean entries
are `zetaPhase_gram_eq_returnCorrelation` and
`zetaPhase_returnCorrelation_source` in
[ZetaPhaseAutocorrelation.lean](../RiemannGaussian/ZetaPhaseAutocorrelation.lean).

The binomial vector c_j=choose(N,j) has the exact complex identity

    sum_j c_j*exp(i*j*theta) = (1+exp(i*theta))^N.

Its complete phase energy is therefore `(2+2*cos(theta))^N`. Lean proves
both identities for every N and theta, alongside

    sum_j c_j = 2^N,
    sum_j c_j^2 = choose(2*N,N).

These are canonical binomial coefficients for a test of the returns.
They do not change the optimizer's phase coefficients or its eight
nonconstant frequencies. The new return count is not a new claim about
the optimal frequency count.

## Direct comparison with the actual prime powers

At theta=y*log(p), the return K(k*theta) appears in the original arithmetic
work with amplitude

    w_k = log(p)*exp(-sigma*k*log(p)).

For any v>=0 for which v*R_c(k)<=w_k at every retained nonzero lag, the
nonnegative kernel gives the independent bound

    v*(a_r*(sum_i c_i)^2 - A*sum_i c_i^2)
      <= sum_m Lambda(m)*m^(-sigma)*K(y*log(m)).

`zetaPhase_returnCorrelation_primePower_floor` proves this with genuine
series convergence. All omitted arithmetic terms have a proved
nonnegative sign. The cost premise is finite and is discharged below.

For the degree-ten binomial test, the ordered lag coefficients are

    335920, 251940, 155040, 77520, 31008,
    9690, 2280, 380, 40, 2.

For each k=1,...,10, Lean checks the integer inequality

    R_c(k)^4 * 2^(5*k) <= 2480640^4.

It follows that v=log(2)/2480640 fits every actual amplitude for
sigma<=5/4. This uses ordinary kernel-checked integer decision and exact
exponential identities. There is no floating-point or native-decision
dependency.

The resulting all-family theorem is

    (log(2)/2480640)*(1048576*a_r - 184756*A)
      <= actual arithmetic work.

The coefficients are respectively 4^10 and choose(20,10). This is
`zetaPhase_binomial_primePower_floor` in
[ZetaPhaseBinomialFloor.lean](../RiemannGaussian/ZetaPhaseBinomialFloor.lean).
It supplies another available lower bound; it is not asserted to dominate
the earlier test for every possible family.

## Consequence for the existing exact optimizer

The already proved enclosures of the optimizer's coefficients imply

    1048576*a_0 - 184756*A >= 46790.

Together with the exact logarithm bound, this proves
`phaseContactExact_binomial_arithmetic_floor`: the actual arithmetic work
is at least 1/80 throughout the same strip and for every height.

The terminal nonvanishing theorem is
`phaseContactExact_binomial_exclusion`. With d=1-Re(s), it excludes points
with Re(s)>=15/16 and |Im(s)|>=1 satisfying

    448*d*((61/100)*log(|Im(s)|+22)+83/100)
      + (793/400)*d^2/Im(s)^2 < 11/625 + d/80.

The intermediate `phaseContactExact_binomial_zero_budget` retains the
exact source, full analytic multiplicity, actual frequency height sum,
and oscillatory pole correction. The arithmetic reserve in the explicit
test increases from d/120 to d/80. This is a 50% increase in that reserve;
it is not a 50% increase in the width of the zero-free region.

The right-half-plane goal is not closed. In particular, these statements
do not prove a one-sided subpolynomial bound for the complete Suzuki
potential or control long balanced blocks.

## Relation to established trigonometric methods

Nonnegative trigonometric polynomials already underlie classical and
improved zeta zero-free-region arguments. See
[Leong and Mossinghoff, introduction](https://arxiv.org/html/2404.05928v2#S1).
The repository already contains the three-four-one Euler-product bound
and a general infinite cosine-family arithmetic identity. This slice
uses the complete return correlations to obtain a stronger local
arithmetic floor from that infrastructure. No historical novelty or
optimality claim is made for the binomial test.
