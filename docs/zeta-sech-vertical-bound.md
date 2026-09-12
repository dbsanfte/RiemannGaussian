# Complete vertical logarithmic bounds and signed zeta windows

The near-one line estimate now supplies a complete positive logarithmic
integral and a uniform upper bound on every finite signed window. All
integrability premises in these statements are proved for the actual
zeta function. No larger zero-free region is claimed by this slice.

## The bound and its domain

For every integer `k >= 1`, set

```text
alpha_k = 1/(2^(k+2)-2)
delta_k = (k+2)*alpha_k
sigma_k = 1-delta_k
H(y) = abs(y)+2
M_k(y) = log(32768/delta_k) + alpha_k*log(H(y)) + log(log(H(y)))
B_k(t,a) = (alpha_k + 1/log(H(t)))*abs(a)/H(t)
K(u) = 1/(2*cosh(u)^2).
```

The theorems hold for every real central ordinate `t` and every real scale
`a`. There is no omitted low-height interval or assumed bound outside a
truncation. The actual positive logarithmic density is

```text
P(u) = K(u)*log⁺ norm(zeta(sigma_k+i*(t+a*u))).
```

`ZetaSechVerticalBound.integrable_integrand` proves genuine integrability
on the whole real line. Its terminal estimates give

```text
integral_R P <= 2*M_k(t)+2*B_k(t,a)
             <= 2*M_k(t)+6*abs(a)/H(t).
```

`truncation_tendsto` proves that the integrals over `[-R,R]` converge to
this actual integral as `R` tends to infinity. The proof explicitly uses
the established integrability.

## How the full height range is paid

The short complete eta prefix at `N=2` has norm at most `4`; the proved
tail has norm at most `2` when `abs(Im(s)) <= 2` and `1/2 <= Re(s) < 1`.
The eta multiplier then gives
`norm(zeta(s)) <= 16/(1-Re(s))` on that low-height range.
Combined with the [complete line theorem](zeta-near-one-line-bound.md),
this proves at every real ordinate

```text
norm(zeta(sigma_k+i*y)) <= 32768/delta_k * H(y)^alpha_k * log(H(y)).
```

The majorant is at least one, so its exact logarithm bounds the positive
logarithm. The explicit order-dependent width cost becomes
`log(32768/delta_k)` and stays in every subsequent allowance.

Two concave-log tangent inequalities give the pointwise shift estimate

```text
M_k(t+a*u) <= M_k(t)+B_k(t,a)*abs(u),
0 <= B_k(t,a) <= 3*abs(a)/H(t).
```

The original density satisfies `0 <= K(u) <= exp(-abs(u))`. Both the
mass and the absolute first moment of this **envelope** are exactly `2`.
This is the source of the coarse coefficient `2` above; this slice does
not compute the sharper exact moments of `K` itself.

## The sign and zero singularities are retained

Define

```text
S(u) = K(u)*log norm(zeta(sigma_k+i*(t+a*u)))
N(u) = K(u)*log⁺ (norm(zeta(sigma_k+i*(t+a*u)))^(-1)).
```

The exact pointwise identity is `S=P-N`. Real analyticity of zeta on
the affine line and Mathlib's meromorphic log-integrability theorem
prove that `S` and `N` are genuinely integrable on **every finite
interval**, including intervals that cross zeros. No zero-free-window
hypothesis is introduced.

For `a != 0`, the zero ordinates are proved countable and Lebesgue-null.
Mathlib assigns `log(0)=0`; changing the assigned value at those isolated
ordinates does not change any integral. The singular behavior nearby is
included by the local integrability proof. At scale zero, the checked
formulas use Mathlib's real logarithm; an identically zero constant
parametrization should not be interpreted as an ordinary log potential.

For every `l <= r`, the complete retained identity and bound are

```text
integral_l^r S = integral_l^r P - integral_l^r N
integral_l^r S <= 2*M_k(t)+2*B_k(t,a) - integral_l^r N
               <= 2*M_k(t)+6*abs(a)/H(t).
```

The negative mass is nonnegative and increases when a symmetric window
is enlarged. Its full-line integrability or a finite full signed limit
has **not** been proved. Finite-window identities and positive-part
convergence do not silently discharge that obligation.

## Entry points

| Module | Principal results |
| --- | --- |
| [ZetaNearOneLogProfile](../RiemannGaussian/ZetaNearOneLogProfile.lean) | `low_height_bound`, `all_height_bound`, `posLog_bound`, `continuous_positiveLog`. |
| [SechVerticalKernel](../RiemannGaussian/SechVerticalKernel.lean) | `density_le_exp`, `integrable_affine`, `integral_affine`. |
| [ZetaLogarithmicShiftAllowance](../RiemannGaussian/ZetaLogarithmicShiftAllowance.lean) | `profile_shift_le`, `positiveLog_shift_le`, `shiftCost_le`. |
| [ZetaSechVerticalBound](../RiemannGaussian/ZetaSechVerticalBound.lean) | `integrable_integrand`, `integral_bound_simple`, `truncation_tendsto`. |
| [ZetaSechSignedWindows](../RiemannGaussian/ZetaSechSignedWindows.lean) | `ae_vertical_ne_zero`, `intervalIntegrable_signed`, `window_exact`, `window_bound_with_negative`, `window_bound_simple`, `negative_window_mono`. |

## Literature connection and remaining work

The logarithmic vertical average is an input to the zero detector in
[Yang, JMAA 2024, Section 4](https://arxiv.org/html/2301.03165v2#S4).
Our estimate uses the repository's eta line bound, enlarged height and
coarse Laplace envelope. It does not reproduce the paper's optimized
constants or its zero-free region. The all-height pointwise theorem
explicitly covers the full integration line.

The [Gaussian localization and Jensen package](zeta-gaussian-local-jensen.md)
now gives an alternative finite-disc route: actual strip growth, an
explicit Euler center allowance, the full local logarithmic zero divisor,
and smaller-disc multiplicity bounds are proved. Its downstream
[complete signed local source and prime contradiction](zeta-arbitrary-log-zero-free.md)
now give eventual zero-free width `A/log(abs(t))` for every fixed `A>0`,
with a coefficient-dependent, unevaluated threshold.
The full signed vertical limit remains open on the contour route.
The fixed-coefficient local proof chooses the order before taking the
height limit. Its downstream [joint-order extension](zeta-log-log-zero-free.md)
now controls every moving center and radius cost and proves a specified
log-log width. The existing
[general band and disc transport](zero-free-region-transport.md) now
applies the stronger proved width to the original marked
squarefree arithmetic response.

The independent ordinary-prime signed lower bound in the fixed-ordinate,
growing-moment contradiction remains open. These high-height analytic
estimates do not by themselves settle it or prove RH.

## Validation

All five modules pass strict direct Lean elaboration and the focused
build. The full warning-as-error build passes all 10,239 jobs. Whole-project
declaration lint and verbose lint of every new module pass. All 49 public
theorems use only `propext`, `Classical.choice` and `Quot.sound`.

The generated inventory contains 1,392 project modules, 29,968 declarations
and 26,256 theorems including generated declarations, with no project
axioms or placeholder-dependent declarations. The source scan covers all
1,535 Lean files. All 599 checked local Markdown links resolve; source
whitespace and the README regime pass. A second strict generator run
leaves both JSON and SVG byte-identical. These are local checks; work
remains uncommitted under the user's hold.
