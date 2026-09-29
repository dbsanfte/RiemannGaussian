# Arithmetic discrepancy through the coupled Riesz cutoffs

`ZetaRieszDiscrepancyEnergy` carries the sharper actual-prime discrepancy
through both Riesz cutoffs before applying the squarefree cofactor mean.
It proves two signed bounds for the prime-minus-smooth response. The smooth
response remains explicit; neither whole-carrier contradiction threshold
is proved.

The [proof audit](riesz-discrepancy-energy-audit.json) records the exact
endpoints, source hashes, allowed axioms and optional numerical diagnostic.

The preceding [joined-prime error](zeta-riesz-joint-prime-error.md) paid a
prime moment. The new theorem pays that discrepancy with the prime-dependent
Riesz response still present. It does not yet assemble the varying retained
factorial coefficients, cofactor phase rotations, ownership masks and all
radial intervals into a source-small total.

## Exact response and bound

For a common complete or externally clipped prime interval
`exp(a) < p <= exp(b)`, write

```math
J_F(n)=\sum_{e^a<p\le e^b}\frac{F(\log p)}p
       \bigl(\mathcal R_L(n)-\mathcal R_{L-\log p}(n)\bigr).
```

The assumptions on the smooth signed profile are `F'=G`, `G` continuous,
and `|F|<=W`, `|G|<=V` on `[a,b]`. The actual Chebyshev estimate proves a
single eventual threshold `T>=5000` for all these profiles. Its value is
**unevaluated**: the theorem does not claim validity from `a=5000` itself.

Define

```math
\varepsilon=\frac{5\,[2W+(V+2W)(b-a)]}{a^3}.
```

The exact smooth tail is

```math
U_F(t)=\mathbf1_{(L-b,L]}(t)
  \int_{\exp(\max(a,L-t))}^{e^b}
     \frac{F(\log x)}{x\log x}\,dx.
```

Its signed divisor-cutoff response is

```math
M_F(n)=\sum_{k=1}^{\lfloor e^L\rfloor}
  \left(\int_{\log k}^{\log(k+1)} U_F(t)\,dt\right)
  \sum_{d\le k,\ d\mid n}\mu(d).
```

For arbitrary squarefree `S subset (1,X]`, one proved but unevaluated
constant `E>0` gives

```math
\sum_{n\in S}|J_F(n)-M_F(n)|^2\le EXb\varepsilon^2.
```

Consequently arbitrary real cofactor weights have **both** signed bounds:

```math
\sum_{n\in S}w_nM_F(n)-K
\ \le\ \sum_{n\in S}w_nJ_F(n)
\ \le\ \sum_{n\in S}w_nM_F(n)+K,
\qquad K=\sqrt{EXb\sum_{n\in S}w_n^2}\,\varepsilon.
```

There is no cutoff-length, divisor-count, internal-period or maximum
prime-count multiplier. The only log-span factor in the squared error is
`b`. Cofactor weights may have either sign, and no low factorial order is
deleted.

## Why the cutoff crossings are paid

The literal two-hinge profile has consecutive difference equal to the
integral of its signed prime tail. Subtract `U_F` inside that integral.
The resulting arithmetic error vanishes outside `(L-b,L]` and is bounded
by `epsilon` everywhere inside. Cauchy on the logarithmic cells, with
`k*log(1+1/k)<=1`, therefore gives

```math
\sum_k k\left|\Delta f(k)-\Delta M(k)\right|^2
 \le \int |\text{prime tail}-U_F|^2\,dt
 \le b\varepsilon^2.
```

Finite Abel summation then retains every divisor sign. The existing
all-count squarefree mean supplies `E`; no unsigned sum over individual
Riesz crossings is used. This is a quantitative bound on the **arithmetic
discrepancy**, not a generic prime-density substitution at source scale.

## Endpoints and scope

- `eventually_profile_error_energy`: actual-prime two-cutoff energy bound.
- `response_error_eq_profile`: exact finite identity, including endpoints.
- `exists_response_error_mean`: squarefree mean over every cofactor count.
- `exists_joint_response_error_bounds`: both weighted signed comparisons.

All are unconditional arithmetic theorems. They require a common complete
prime interval and common profile. Cofactor-dependent prime holes are not
silently filled. The previous retained-factorial expansion remains exact,
but its order and phase components must still be assembled with these
error estimates and their actual masks. The signed smooth Riesz response
itself needs a bound. Neither a polynomial improvement nor this unevaluated
constant proves source-normalized decay.

The optional `scripts/probe_riesz_discrepancy_energy.py` uses actual primes
at log-height 10, outside the established eventual range, and numerical
quadrature. It tests the finite Abel identity, orders zero and one, phases,
several joined-period lengths and all-count cofactors. The identities agree
to floating-point precision. For its fixed fifth-order, sixteen-period
profile, increasing `L` from 11.5 to 13 increases the number of discrete
cutoffs from about 99,000 to 442,000 while the measured discrepancy energy
changes from about 1.246 to 1.268. This illustrates the absence of a cutoff
count multiplier; it is not a certificate or an asymptotic conclusion.

The joint `-79/1000-o(1)` floor and `3/2+o(1)` ceiling remain open. No new
zero-free region or RH proof follows.
