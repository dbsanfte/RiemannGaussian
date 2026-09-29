# Combined central cost at growing orders

The [Lean theorem](../RiemannGaussian/ZetaRieszCentralCostGrowth.lean)
now bounds the **combined** central cost, including every cofactor shell,
prime count and original retained label. The
[proof audit](riesz-central-cost-growth-audit.json) records its scope.

This is a large-order bound, but **it does not close the floor or ceiling**.
The bound still has an exponential factor greater than one.

The subsequent [joint radial estimate](zeta-riesz-central-radial-cost.md)
improves this same cost to `C sqrt(N)(2u)^N`. It preserves the exponential
gap and both endgame thresholds.

## The proved bound

For fixed `0<u<=10001/20000`, eventually at every order `N`, uniformly in
height `y` and the original count cutoff `K`, let `D_N` be the sum of the
existing joint costs over the actual dyadic owner-cofactor shells in
`1.971N < log n <= 2.029N`. Lean proves

```math
0\le D_N\le
C_E N\bigl(1+\log(16N+8)\bigr)(2u)^N,
\qquad
C_E=12\sqrt{6E}\,(2e^{1/2}\log4).
```

Here `E>0` is the proved universal squarefree-mean constant. It remains
unevaluated. The starting order also remains unevaluated. No finite prime
sum, cofactor energy or family cost is left on the right.

The exact original core obeys both signed bounds

```math
-D_N-Ce^{-N/10^6}
\le u^{N+1}\operatorname{Re}(\mathrm{coreResponse}_N)
\le D_N+Ce^{-N/10^6}.
```

The outer error is the previous proved payment and is charged once.
Squarefreeness, unique largest-prime ownership, the original allocation,
all factorial orders, full product phase and every nested support mask
remain in the cost and carrier. No zero hypothesis is used. This explicit
majorant uses absolute weight bounds, so it does not certify further
cancellation of the prime phase. The earlier optimized and signed-center
enclosures remain available and may be intersected with this enclosure.

## Why all counts and shells are now paid

The proof combines the factorial saddle inequality
`exp(-T/2) T^N/N! <= 2^N/sqrt(N)` with the unchanged allocation bound.
On a dyadic cofactor shell `M<n<=2M`, the squared weight sum is at most
`V_N^2/(M p^2)`. The squarefree mean costs at most `2 E M`, cancelling
that population size. The entire cutoff energy costs at most `log p`.

The existing literal prime-harmonic theorem pays the remaining prime sum
by a logarithm of a logarithm. Every central cofactor lies in one of at
most `4N` disjoint shells. Summing them gives the displayed bound. No
maximum prime-count multiplier or factorial-order triangle inequality is
introduced. This is deliberately a bound for the whole cost, not another
finite-sector percentage comparison.

## The remaining rate is explicit

At the upper radius, Lean proves

```math
\frac{99}{10^6}
<\log(2\cdot10001/20000)
<\frac1{10000}.
```

Numerically that exponent is about `0.000099995`. Lean also proves the
scalar majorant tends to infinity for every `u>1/2`, while its ratio to
`N^2(2u)^N` tends to zero. Thus the combined allowance has a genuine
polynomial saving relative to that quadratic saddle scale, but still
needs cancellation of the surviving exponential growth.

**Divergence is proved only for this majorant.** It is not a lower bound
on the actual signed carrier or on the best common-coordinate cost. It
is not a no-go theorem for a future joint signed estimate. A fixed
percentage saving, by itself, cannot turn this particular majorant into
a bounded eventual allowance.

The required joint floor remains `-79/1000-o(1)` for a simple exposed
zero; the ceiling remains `3/2+o(1)` for higher multiplicity. Neither is
proved. No new zero-free region or RH claim follows.
