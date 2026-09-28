# The count-tail budget also pays a seven-prime head

The literal joint carrier now has an independent payment for every
seven-prime label with **any prime factor satisfying `log p<=theta*N`**,
for a fixed positive `theta`. Both coefficient signs, the original phase,
factorial kernel, allocation fraction and core boundaries are included.
The previous head widths and one-sixty-fourth reserve are preserved.

The two terminal comparisons are
[`ZetaRieszSevenCountTail.eventually_core_full_floor`](../RiemannGaussian/ZetaRieszSevenCountTail.lean)
and `eventually_core_full_ceiling`. Their remaining signed sums still need
the independent numerical bounds in the
[multiplicity-aware endgame](zeta-riesz-joint-floor.md).

## An actual weighted prime-count estimate

Let `S` be any finite selection of squarefree seven-prime integers in
`2M<=log n<=2M+2`, each with some prime factor at most `Q`. For
`M>=100`, `N<=2M`, `2<=Q`, `log Q<=M/32` and positive
`L>=271M/200`,
[`small_seven_fractional_norm_upper`](../RiemannGaussian/ZetaRieszSevenPrimeHead.lean)
proves

\[
\left\|\sum_{n\in S}c_{A,L,N}(n)\,
  \mathcal K_N(3/2+iy,n)\right\|
\le B_7\sqrt{\log Q}\sqrt{2M+2}\,
\frac{e^{2M}}{M+1}\operatorname{radialEnvelope}(N,M).
\]

Here `c` is the original `residualCoefficient`, and

\[
B_7=640\log(4)e^4 C(1/2)C(1/10)^5,
\qquad C(a)=\frac{6\log4}{1-2^{-a}}.
\]

The proof counts actual ordinary primes. One prime has `log p>M/8`;
Chebyshev bounds its population. The remaining minimum logarithm is
retained through the inequality

\[
\log p_{\min}\le
(\log r)^{1/2}\prod_{i=1}^{5}(\log q_i)^{1/10}.
\]

The already proved fractional prime moments then pay the six reciprocal
sums. No prime-density approximation, zero hypothesis, phase replacement
or prime completion is used. Nonselected labels never enter the carrier;
the counting majorant may overcount tuples only on the upper-bound side.

For every positive radial-scale budget `b`, the exact choice

\[
\theta=\min\left(\frac1{128},\left(\frac{b}{4B_7}\right)^2\right)>0
\]

makes the entire selected head cost at most
`b*M*exp(2M)/(M+1)*radialEnvelope(N,M)` eventually. This is
`eventually_small_seven_log_cost`, uniform in height and allocation set.

The [intersecting-window coefficient bounds](zeta-riesz-intersecting-window.md)
are preserved. The head payment above covers both signs by their common
norm majorant; it does not turn the halved negative coefficient cost into
a claimed halving of the entire seven-prime mass.

## One budget, with the earlier payments unchanged

The [high-count cost](zeta-riesz-log-count-tail.md) tends to zero relative
to the same supply scale. Therefore its previous one-sixty-fourth spending
can be split into:

| Charge | Fraction of the existing signed supply |
| --- | ---: |
| All `omega(n)>=8*clog(2,N+1)` | 1/128 |
| Seven primes, with some `log p<=theta*N` | 1/128 |
| Combined charge | **1/64** |

`eventually_seven_and_count_cost` and the two slab payment theorems prove
this simultaneous comparison. Every earlier charge and its cutoff remain;
the unused supply stays **1/64**. The tail labels have at least seven
factors, so they are disjoint from all older charges and supply, whose
counts are at most six. The two phase orientations use separate
comparisons and cannot be added as independent credits.

The full-core statements retain favorable observations for all earlier
low-count groups and for the combined enlarged tail, together with one
exact signed complement. The old separate high-count comparison remains
available as well. Their exterior error is `r^N*C`, `0<=r<1`.
The same checked radial edges `244N/125` and `2029N/1000` pay labels
outside the half-open radial union, including seven-prime head labels.
Earlier low-count complete-boundary theorems remain available separately;
the new statements explicitly preserve their radial payments.

`remaining_seven_log_gt` now proves that **every prime of any unpaid
seven-prime label has `log p>theta*N`**, including labels at the original
core boundaries. `remaining_count_lt` also retains the logarithmic ceiling
on every squarefree label left in the rest.

## Quantitative limits and the open target

The explicit counting constants are coarse. The optional
[scalar probe](../scripts/probe_riesz_seven_head.py), with
[recorded output](riesz-seven-head-probe.json), gives
`B7` approximately `4.07e16`. For the illustrative radial-scale budget
`b=1/128`, the displayed formula gives `theta` about `2.31e-39`.
That budget is **not** the unevaluated height-dependent supply constant,
so this is not a certified cutoff for the complete carrier or a starting
order. The theorem proves a positive asymptotic head, not a practically
large deleted region at the orders used in earlier probes.

This removes another actual boundary population from the unpaid sum.
The interior seven-prime population, the other unpaid lower-count shapes
and the remaining intermediate counts still require joint signed control.
The head itself is not asserted to be source-normalized `o(1)`; actual
signed supply pays its cost. Neither the `-79/1000-o(1)` whole-sum floor,
the `3/2+o(1)` ceiling, nor a zero exclusion follows from this payment.
