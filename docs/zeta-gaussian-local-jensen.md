# Gaussian localization and shrinking-disc zero estimates

The actual near-one zeta bound now extends across a full strip of real
coordinates. It controls the complete analytic zero divisor on shrinking
discs with every center-value and analytic-growth premise discharged.
These are value and local multiplicity estimates; no additional zero-free
region is asserted by this slice.

## Parameters and terminal statements

For `k >= 1`, define

```text
alpha_k = 1/(2^(k+2)-2)
delta_k = (k+2)*alpha_k
sigma_k = 1-delta_k
H(t) = abs(t)+2
M_k(t) = log(32768/delta_k)+alpha_k*log(H(t))+log(log(H(t))).
```

For every complex `s` with `sigma_k <= Re(s) <= 3/2` and
`abs(Im(s)) >= 2`, the actual positive logarithm satisfies

```text
log⁺ norm(zeta(s)) <= M_k(Im(s))+14.
```

More generally, `local_norm_bound` and `local_posLog_bound` permit any
central height `t` with `abs(t) >= 2` and `abs(Im(s)-t) <= 1`. Their
right-hand side is evaluated at that same center `t`.

Put

```text
c = 1+x+i*t,       0 < x <= delta_k/4,
R = delta_k/2,     abs(t) >= 2,
A = M_k(t)+14+log(1+1/x).
```

Zeta is proved analytic on a neighborhood of the entire closed disc
`D=closedBall(c,R)`, and is nonzero at `c`. Zeros elsewhere in the disc,
including its boundary, are allowed. If `d_D` is its actual analytic
divisor, Lean proves

```text
sum_a d_D(a)*log(R/norm(c-a)) <= A,

sum_a divisor(zeta,closedBall(c,r))(a) <= A/log(R/r)  (0<r<R).
```

The sums are finite-support sums over the complex plane. Every zero is
counted with its full analytic multiplicity. `zero_source_bound` retains
the selected genuine zeta-zero contribution

```text
m_rho*log(R/norm(c-rho)) <= A
```

whenever `rho` belongs to the outer disc. There is no simple-zero
assumption or replacement of the distance by an unspecified constant.
The horizontal shift `x` may be arbitrarily small within its stated
range; its logarithmic cost remains explicit.

## Exact Gaussian carrier and full strip growth

The complex carrier is

```text
G_t(s) = zeta_1(s)/(s+1) * exp((s-i*t)^2),
zeta_1(s) = (s-1)*zeta(s) away from s=1.
```

The pole-removed function `zeta_1` is entire. Division by `s+1` is
analytic throughout the strip, and
`norm((s-1)/(s+1)) <= 1` when `Re(s) >= 0`.
This normalization avoids adding a height power while removing the
original pole. The exact complex factorization and inverse reconstruction
remain named theorems.

On the left boundary, the [complete logarithmic shift allowance](zeta-sech-vertical-bound.md)
gives

```text
M_k(t+v) <= M_k(t)+B_k(t,1)*abs(v),  0<=B_k(t,1)<=2.
```

The Gaussian absorbs that entire linear shift using
`2*abs(v)-v^2 <= 1`, giving
`norm(G_t(s)) <= exp(M_k(t)+2)` on `Re(s)=sigma_k`.
On the right boundary `Re(s)=3/2`, absolute Euler convergence gives
`norm(G_t(s)) <= 8*exp(3)`.

The Phragmen--Lindelof growth premise is proved independently using the
repository's existing polynomial bound for pole-removed zeta:

```text
norm(G_t(s)) <= 16*exp(3)*(1+(abs(t)+22)^2)
```

throughout `1/2<=Re(s)<=3/2`. Both infinite vertical tails are included.
This coarse bound is used only to justify the maximum principle; its
height dependence does not enter the final sharp boundary allowance.
The principle yields

```text
norm(G_t(s)) <= exp(M_k(t)+10)
```

on the entire closed strip between `sigma_k` and `3/2`.

In the local window, the inverse Gaussian has norm at most `exp(1)`
and the inverse rational factor has norm at most `4`. This proves
`norm(zeta(s)) <= exp(M_k(t)+14)`, with no additional height exponent.
The additive constants are deliberately coarse; optimized numerical
constants are not claimed.

## Euler center cost and retained Jensen identity

The full, absolutely convergent complex Möbius series is exactly
`1/zeta(s)` for `Re(s)>1`. Integral comparison of its coefficient mass
proves, uniformly on that whole half-plane,

```text
norm(1/zeta(s)) <= 1+1/(Re(s)-1).
```

At the actual center this gives
`-log norm(zeta(c)) <= log(1+1/x)`. No center-floor hypothesis remains.

The upstream signed identity is

```text
circleAverage(log norm(zeta),c,R)
  = sum_a d_D(a)*log(R/norm(c-a)) + log norm(zeta(c)).
```

Mathlib's meromorphic log-integrability and Jensen theorems justify the
circle average even through boundary zeros. The center is proved nonzero,
so no singular center value is silently totalized. Each divisor term is
nonnegative, and the complete signed boundary average is bounded only
after this exact identity is retained. The full divisor and individual
selected-zero estimates follow from the local upper bound and the
explicit Euler center allowance.

## Entry points

| Module | Principal results |
| --- | --- |
| [ZetaGaussianLocalizer](../RiemannGaussian/ZetaGaussianLocalizer.lean) | `regularized_eq`, `norm_carrier`, `carrier_bounded`. |
| [ZetaGaussianStrip](../RiemannGaussian/ZetaGaussianStrip.lean) | `left_boundary`, `carrier_growth`, `carrier_bound`. |
| [ZetaNearOneLocalDisc](../RiemannGaussian/ZetaNearOneLocalDisc.lean) | `reconstruction`, `full_strip_posLog_bound`, `analyticOnNhd_disc`, `disc_posLog_bound`. |
| [ZetaEulerReciprocalAllowance](../RiemannGaussian/ZetaEulerReciprocalAllowance.lean) | `inverse_eq_moebius`, `inverse_zeta_bound`, `neg_log_norm_zeta_le`. |
| [ZetaNearOneJensen](../RiemannGaussian/ZetaNearOneJensen.lean) | `jensen_identity`, `weighted_mass_bound`, `zero_source_bound`, `count_bound`. |

## Downstream zero exclusion and remaining work

The classical changing-order estimates in
[Yang's near-one zeta argument](https://arxiv.org/html/2301.03165v2)
motivate this work. Gaussian localization, Phragmen--Lindelof and Jensen
are established analytic techniques; no historical novelty or reproduction
of the paper's optimized constants is claimed here.

The downstream [signed local factorization and exclusion](zeta-arbitrary-log-zero-free.md)
now retain the selected reciprocal-distance source together with its
canonical correction. The complete residual is bounded, every other
coupled zero term is nonnegative, and actual prime phase positivity
proves eventual zero-free width `A/log(abs(t))` for every fixed `A>0`.
Each coefficient has its own unevaluated threshold. A logarithmic Jensen
weight alone does not supply this contradiction; the signed derivative
step is an additional proved ingredient.

This finite-disc route does not require a separately constructed full
signed vertical logarithmic integral for the statements proved here.
The earlier positive integral and signed finite windows remain available
for the alternative strip-contour route; their full signed limit is
still unproved. The stronger actual exclusion now feeds through the
[general width transport](zero-free-region-transport.md) to the entire
bounded-height divisor and every marked squarefree response. The
[joint order-height proof](zeta-log-log-zero-free.md) now also supplies a
specified log-log width with its complete moving costs discharged. The independent
signed ordinary-prime lower bound in the fixed-ordinate, growing-moment
RH contradiction remains open.

## Validation of the five-module Jensen slice

All five modules pass direct elaboration with warnings treated as errors.
The focused build passes 4,523 jobs and the full build passes 10,244 jobs.
Whole-project declaration lint and verbose lint of the five new modules
pass. Every one of the 43 new public theorems has been audited and uses
only `propext`, `Classical.choice` and `Quot.sound`.

The strict generated inventory contains 1,397 project modules and 26,316
project theorems, with no project axioms or placeholder-dependent
declarations; it continues to report `rhImplied = false`. Regeneration is
byte-identical. The source scan covers 1,540 Lean files, and the README and
related documentation pass local-link and whitespace checks. These are
local checks; work remains uncommitted under the user's hold.
