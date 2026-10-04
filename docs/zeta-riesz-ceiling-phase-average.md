# The actual joined carrier: geometric height-average saving

The full fixed-strip, all-height `42/25` ceiling remains **open**. This
slice proves a cofinal geometric estimate for the long-height mean square
of the **same native `joinedPhysical` carrier**. It does not prove its
value at the ordinate of a hypothetical zero, simplicity, a zero-free
region, or RH. The simple-zero floor is also still open.

The proof is
[`ZetaRieszCeilingPhaseAverage.lean`](../RiemannGaussian/ZetaRieszCeilingPhaseAverage.lean).
It uses no zero, exposure, multiplicity, sparsity, prime-density, or
independent-prime-phase assumption. The original radius interval is
unchanged: (1/2<u\le10001/20000).

## The exact carrier and quantitative estimate

For each fixed original order (N) and count cutoff (K), write

\[
 P_N(y)=u^{N+1}\operatorname{joinedPhysical}(u,y,N,K)
       =\sum_{n\in\operatorname{coreBand}} a_N(n)e^{-iy\log n}.
\]

`scaled_joined_eq_signal` proves this equality exactly. It retains the
unmatched signed complement: on the saturated band the joined multiplier
is one, and elsewhere it is exactly `1-selection`. The original residual
coefficient, `1-boundedShare`, moving Riesz length, physical support,
count/radial masks, factorial orders and diagonal remain intact. No new
carrier, completion or arithmetic measure is substituted.

Set

\[
 E_{N,K}=\sum_{n\in\operatorname{coreBand}}|a_N(n)|^2,
 \qquad C=32\sum_{n\ge1}\frac{\tau(n)^2}{n^{5/4}}<\infty.
\]

`joinedCoefficientEnergy_uniform` proves

\[
 0\le E_{N,K}\le
 C\left(\frac{10001}{20000}\right)^2
 \left(\frac{10001}{15000}\right)^{2N}.
\]

The geometric base in (N) is approximately (0.4445333378), strictly
below one. The constant is the genuine complete divisor-square Dirichlet
mass, not a sampled population or a free analytic remainder. No native
entry order is claimed without an explicit numerical bound for that
constant and the window term.

The coefficient estimate uses the actual inequality
`zetaMoebiusLogMajorant(n) <= tau(n)*log(n)` and squares the already-joined
coefficient. It does not require an unproved prime cancellation law.

For **every** starting height (H\in\mathbb R) and window length (T>0),
`joined_translated_heightMean_bound` gives

\[
 \frac1T\int_0^T|P_N(H+y)|^2\,dy
 \le C\left(\frac{10001}{20000}\right)^2
 \left(\frac{10001}{15000}\right)^{2N}
 +\frac{D_{N,K}}{T},
\]

with the explicit finite cost

\[
 D_{N,K}=
 \sum_m\sum_{\substack{n\in\operatorname{coreBand}\\n\ne m}}
 \frac{2|a_N(m)||a_N(n)|}{|\log m-\log n|}.
\]

`heightMean_eq_energy_add_crossing` retains the signed off-diagonal sum
exactly before this window bound is applied. Both incidences of every
distinct pair and the diagonal are present. This is averaging the one
literal phase (n^{-iy}), not randomizing phases separately on prime legs.

`joined_mean_square_cofinal` proves the precise order of limits:

\[
 \lim_{N\to\infty}\left(
   \lim_{T\to\infty}\frac1T\int_0^T|P_N(y)|^2\,dy
 \right)=0
\]

for any moving count schedule. The height limit comes **first**. There is
no reversed or simultaneous limit, almost-everywhere fixed-height claim,
pointwise bound, or uniform short-window saving in this theorem.

## What the numerical replay checks

The optional probe selects 48 distinct squarefree integer labels built
from 128 distinct actual prime factors, at orders 48 and 64 and counts
3 through 10. It evaluates the exact signed divisor hinge sum, moving
length, literal integer `unpaidOrders` and allocated fraction. All sampled
factors satisfy the original physical prime inequalities, and all sampled
total logs lie in the core window.

This is **not** a complete native-core enumeration. Core membership is
not certified, and the additional joined multiplier is not applied in
the sample; these are regressions for literal residual atoms and the
general phase identity. The Lean theorem, separately, applies to the
complete native joined carrier for every count and mask.

The 360-bit probe saves exact dyadic interval centres and radii. An
independent 420-bit replay re-enumerates actual integer divisors and uses
binomial marginals for the allocation, then checks all 16 windows by the
complex antiderivative. Eight short windows are also checked by direct
440-bit quadrature of the assembled sum. Interval widths are tracked.

| Order | Smallest sampled log spacing | Window cost / diagonal energy |
| --- | --- | --- |
| 48 | (1.09508\times10^{-12}) | (4.63263\times10^9) |
| 64 | (1.07774\times10^{-17}) | (1.12808\times10^{15}) |

Those are finite-sample quantities, **not** estimates of the full unpaid
carrier or its source. Near-equal integer products can retain a correlated
common phase despite having different prime incidences. This warns against
using individual prime features or independence assumptions to infer
fixed-height cancellation. Long-window orthogonality does not pay that
local correlation.

## Remaining arithmetic frontier

There is **zero new pointwise ceiling credit** in this slice. In
particular the native multiple-zero source remains
`-m+m^2*retainedCost(u)`; at the upper radius its (m=2) value is about
`1.680512811860...`, above `42/25`. The source ledger is unchanged.

The missing estimate must control the actual signed correlations at the
selected height, across the growing order range. The exact finite-window
cross terms are available, but (D_{N,K}/T) is not proved small for any
window that would control that height. A sparse set of resonant heights
can coexist with a small long-window mean square. Do not discard that
cost, exchange the limits, or identify generic finite examples with the
actual cofinal prime sum.

The preceding finite-Euler-jet, moving-kernel, synthetic cluster and all
other positive/no-go audits remain unchanged. The independent simple
floor, full all-height ceiling and zero exclusion remain open. Any next
use of the averaged estimate must give a quantitative bound on the actual
selected-height signed aggregate; another phase-independence assumption
or positive budget would not close the goal.

## Scoped validation

Only the optional leaf was built. All 14 linters passed; 58 theorems
including generated helpers use only `propext`, `Classical.choice` and
`Quot.sound` transitively. The independent numerical replay passed, and
all 249 prior source/proof/probe pins are preserved.

Artifacts and classifications are recorded in
[`riesz-ceiling-phase-average-audit.json`](riesz-ceiling-phase-average-audit.json).
Nothing is registered in the root or CI. No commits, pushes, subagents,
public metadata updates, wider checks or exhaustive certification runs
were performed.
