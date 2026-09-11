# Exact Fermi reflection and the stronger zero-free-region program

The two new modules are imported by `RiemannGaussian.lean`:

- [FermiLaplaceReflection.lean](../RiemannGaussian/FermiLaplaceReflection.lean)
  proves the all-window mechanism.
- [GaussianFermiZeroPair.lean](../RiemannGaussian/GaussianFermiZeroPair.lean)
  discharges its hypotheses for every positive Gaussian scale and connects
  it to the repository's actual zeta zero-free strip.

These proofs have passed local Lean validation. The published numerical region is
not yet formalized. The [subsequent Gaussian comparison](gaussian-fermi-zero-free-region.md)
now proves a stronger eventual region with exact coefficient `3/20`; its
height threshold is proved to exist, not numerically evaluated.

## External target and provenance

Bellotti, Trudgian and Yang's March 2026 preprint, *Zero-free regions
inspired by work of Heath-Brown*, states nonvanishing for
`t >= 3` and `sigma > 1 - 1/(4.896 log(t))` in Theorem 1.
The strict boundary and height condition are part of the target.
Its reflection and smoothing discussion motivates our ideal multiplier.
The numerical proof itself uses a finite approximation and further
explicit estimates; we have not imported it as a theorem or assumed it.
[Primary source, version 1](https://arxiv.org/html/2603.21490v1).

Our construction uses the repository's existing eta Fermi kernel and
Gaussian Fourier identity. It proves an exact ideal mechanism independently
in Lean. It is not a claim of historical novelty or of reproducing the
paper's quantitative result. No external Lean code has been copied.

## The exact signal and its two reflections

For a real window `g` and `a > 0`, define

```text
f(u) = g(u)/(1+exp(-a*u)),
F(z) = integral_(u>0) f(u)*exp(-z*u) du.
```

The following identities hold before taking a norm:

```text
f(u) + exp(-a*u)*f(u) = g(u),
F(z) + F(a+z) = integral_(u>0) g(u)*exp(-z*u) du.
```

For even `g`, detailed balance gives

```text
f(-u) = exp(-a*u)*f(u),
F(z) + F(a-z) = integral_R f(u)*exp(-z*u) du.
```

The physical reflected-zero pair uses `a-conj(z)`, whereas the analytic
reflection uses `a-z`. These are not silently identified as complex values:

```text
F(a-conj(z)) = conj(F(a-z)).
```

Consequently the pairs have the same real part. The exact conjugation
identity remains available upstream of positivity.

If `g'(0)=0`, Lean also proves

```text
f(0)=g(0)/2,
f'(0)=a*g(0)/4,
2*f'(0)-a*f(0)=0.
```

Thus an interface assuming `f'(0)=0` cannot simply be applied to the ideal
weight. The displayed coefficient cancellation is exact. This slice does
not assert an unproved asymptotic expansion or an all-orders decay rate.

## The all-window positivity theorem

`transform_reflected_pair_re_nonneg` assumes:

1. `g` is continuous and real valued;
2. `g(u)*exp(-x*u)` is integrable on the full real line for every real `x`;
3. the real part of the one-sided transform of `g` is nonnegative at every
   imaginary argument.

It proves

```text
Re(F(z)+F(a-conj(z))) >= 0   whenever 0 <= Re(z) <= a.
```

The convergence assumptions prove that `F` is entire, through the existing
signed Laplace moment theorem. On the right half-plane its norm is at most
`integral_(u>0) |g(u)| du`. The partition identity supplies positivity on
both strip edges. Applying Phragmen--Lindelof to
`exp(-(F(z)+F(a-z)))` supplies positivity throughout the closed strip.

There is no assertion of positivity outside this strip. The boundary
transform condition is a real hypothesis for a general window, not a
renamed prime-tail bound or an assumed consequence of RH.

## All Gaussian scales and actual zeros

For every `b>0`, the actual window `g_b(u)=exp(-b*u^2)` has all real
exponential moments. Its boundary transform is exactly

```text
Re integral_(u>0) g_b(u)*exp(-i*y*u) du
  = sqrt(pi/b)*exp(-y^2/(4*b))/2 >= 0.
```

`reflected_pair_re_nonneg` discharges every general analytic hypothesis
using these Gaussian facts. `gaussian_pair_eq_bilateral` retains the
complex integral over the full time line.

Write `m(H)=zetaPoleReserveZeroMargin H`, the existing proved zero-free
width. For every height cap `H`, use

```text
sigma_H = 1-m(H),       a_H=2*sigma_H-1.
```

The checked margin satisfies `0<m(H)<1/4`, so this line lies strictly
inside the unit edge and strictly to the right of `3/4`. Every actual
nontrivial zero `rho=beta+i*gamma` with `|gamma|<=|H|` satisfies

```text
1-sigma_H < beta < sigma_H.
```

Therefore `z=sigma_H+i*t-rho` belongs to the required reflection strip,
for every real evaluation ordinate `t`. The terminal theorem
`nontrivial_zero_pair_re_nonneg_on_band` proves

```text
Re(F(s-rho)+F(s-(1-conj(rho)))) >= 0,
s=sigma_H+i*t.
```

This is a checked causal connection from the existing zero-free region
to an interior smoothing argument. It covers each genuine zero in the
specified band. It does not exchange an infinite zero sum with an integral
or omit analytic multiplicities.

## Remaining proof obligations

The [exact Gaussian mixture](gaussian-fermi-explicit-mixture.md) now transports
the unconditional Gaussian arithmetic explicit formula to this Fermi
weight. Its spectral density has proved positivity and unit mass, and the
whole-zero interchange retains every analytic multiplicity. The full
original zero sum is identified with an absolutely convergent arithmetic
average. The [prime and phase continuation](gaussian-fermi-prime-phase-budget.md)
now proves the literal convergent prime series, evaluates the pole and
constant terms, and proves gamma-average integrability and independence
from the positive Gaussian split.

The [subsequent zero-tail slice](gaussian-fermi-zero-tail.md) now controls
all outside-band zeros, including multiplicities, by an explicit
inverse-square bound and a genuine summable divisor tail. It also proves
a lower bound for the complete paired real zero side. Its quantitative
continuation bounds the full allowance by `K log(H+2)/sqrt(H)`, uniformly
over every scale `m(H)^2 <= b <= 1`, and proves that it tends to zero.
The general finite-phase budget now gives the whole prime series the
favorable sign while retaining any selected finite set of genuine zeros.
The [gamma continuation](gaussian-fermi-gamma-bound.md) now inserts an
explicit quarter-logarithm upper bound, uniform over shrinking scales,
into that budget. The [resonant continuation](gaussian-fermi-resonant-budget.md)
also supplies a Gaussian lower bound for both distinct target partners
and a proved upper envelope for every pole frequency. The
[independent Gaussian comparison](gaussian-fermi-zero-free-region.md)
now rules out the eventual edge width `3/(20*log(abs(t)))`, with every
tail condition discharged. Its height threshold has not been numerically
evaluated.
Reproducing the external `4.896` target also
requires its separate finite-height and explicit-estimate dependencies,
or rigorously proved replacements for them.

The existing normalized ordinary-prime tail still has no independent
cofinal signed lower bound. Neither this positivity theorem nor adopting
a wider external region automatically proves that bound or RH.

## Validation

All local gates passed: strict direct Lean elaboration of the four affected
modules, the focused build, the full warning-as-error build (10,114 jobs),
all declaration linters, 15 terminal axiom audits, the whole compiled
environment audit, and source and whitespace checks. The generated
inventory for that initial reflection slice had 1,267 modules, zero project axioms and zero declarations
depending on placeholders. The audited theorems use only `propext`,
`Classical.choice` and `Quot.sound`. README links and table formatting also
pass. These are local validation results; remote CI is checked separately
on the exact commit.
