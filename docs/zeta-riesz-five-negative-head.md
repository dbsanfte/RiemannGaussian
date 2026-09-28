# Paying both signs of the five-prime exponential head

The new [full lower and upper comparisons](../RiemannGaussian/ZetaRieszFiveNegativeHead.lean)
pay every negative-coefficient five-prime core label containing a prime
`p<=floor(exp(zeta*N))`, for a fixed `zeta>0`. Together with the existing
positive-coefficient payment, this covers both five-prime signs through
`floor(exp(min(delta,zeta)*N))`. The original six-prime exponential head
and all earlier charges remain paid from the same four-prime supply.
The complete boundary allowance and one exact signed rest are retained.

These are independent arithmetic component estimates. They assume neither
a zero nor simplicity. Both whole-sum bounds required by the
[multiplicity-aware endgame](zeta-riesz-joint-floor.md) remain open.

## Keep the minimum before counting the cofactor

For a squarefree five-prime label the parity-specific divisor-window
bound gives, at every positive cutoff,

\[
|c_L(n)|\le3\frac{\log n}{L}\log(\minFac n).
\]

On `2M<=log n<=2M+2`, `M>=100` and `L>=271M/200`, this is at most
`12*log(minFac n)`. Mark any prime `r<=Q`, where `log Q<=M/32`.
Another prime has logarithm above `M/8`; count it at its actual residual
product endpoint. For the four other logarithms `r,a,b,c` and their
minimum `t`, use

\[
t\le r^{1/2}a^{1/6}b^{1/6}c^{1/6}.
\]

This retains the simultaneous minimum-prime information. The already
proved literal prime mass inequality

\[
\sum_{\log p\le X}\frac{(\log p)^\alpha}{p}
\le C_\alpha X^\alpha,
\qquad C_\alpha=\frac{6\log4}{1-2^{-\alpha}},
\]

then yields the following [checked finite bound](../RiemannGaussian/ZetaRieszFiveFractionalHead.lean):

\[
\left\|\sum_{n\in S}f_{N,L,y}(n)\right\|
\le B_5\sqrt{\log Q}\sqrt{2M+2}
  \frac{e^{2M}}{M+1}\,\mathrm{radialEnvelope}(N,M),
\]

\[
B_5=192\log4\,e^4C_{1/2}C_{1/6}^{,3}>0.
\]

Here `f` is the original residual atom, including its complex phase,
allocation factor and factorial kernel. The bound applies to either sign,
any selected finite population satisfying the conditions, and every real
height. No prime-density or phase approximation is used.

For `log Q<=zeta*N` and `N<=2M`, the relative cost is at most
`4*B5*sqrt(zeta)`. Given any positive radial budget `b`, the explicit choice

\[
\zeta=\min\left(\frac1{128},\left(\frac{b}{4B_5}\right)^2\right)
\]

makes that cost at most `b`. The signed supply supplies the positive
calibration `c`; choosing `b=c/32` pays the negative five-prime head.
The constant is deliberately coarse: a floating evaluation gives
`B5` about `1.83e11`, so this argument may select a very small width.
The signed width and starting order remain existential. This is not a
numerical starting-order certificate or separate source-normalized decay
of the head.

## One supply, with both endgame orientations

| Selected charge | Fraction of the same supply |
| --- | ---: |
| Narrow balanced triple band | 1/2 |
| Three-prime exponential head outside that band | 1/8 |
| Four-prime exponential head | 1/8 |
| Positive-coefficient five-prime exponential head | 1/8 |
| Both signs of the six-prime exponential head | 1/16 |
| **Negative-coefficient five-prime exponential head** | **1/32** |
| **Unused supply** | **1/32** |

The new negative five-prime labels are disjoint from the positive ones by
coefficient sign, and from the other charges and the supply by prime count.
Their width `zeta` is chosen separately from the old width `delta` and the
six-prime width `epsilon`. The six-prime and negative five-prime charges
are grouped in the new signed inequality; their combined norm budget is
`3/32`. Each selected group's favorable real part is retained. The earlier
separate six-prime statements also remain available.

`eventually_core_full_floor` and `eventually_core_full_ceiling` apply on
`1/2<u<=10001/20000`, `|y|>=16`, eventually along the original dyadic
orders. They retain the original masks, one complete signed complement,
and the same vanishing boundary error

\[
r^N C+2\,\mathrm{majorantMass}(1+1/262144)e^{-N/10^6},
\qquad 0\le r<1.
\]

The lower and upper comparisons choose their own phase windows. They
are alternative uses of a supply, not additive credits. The cached central
five-prime capacity supplies are not used or spent in this argument.

`remaining_negative_five_log_gt` excludes every prime with `log p<=zeta*N`
from the unpaid negative five-prime population, even at the original
boundaries. `remaining_five_log_gt` combines the two signs: every remaining
five-prime label with nonzero coefficient has
`log p>min(delta,zeta)*N` for all its prime factors.
`remaining_six_log_gt` retains the separate six-prime restriction.

The unpaid interior populations, other triple shapes and higher counts
remain in the exact signed rest. Their joint signed bound is still needed;
these component payments do not prove the `-79/1000` floor, the `3/2`
ceiling, RH, or a new zero-free region.
