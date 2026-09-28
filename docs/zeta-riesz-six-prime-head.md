# Paying the six-prime head through an exponential threshold

The [exponential extension](../RiemannGaussian/ZetaRieszSixPrimeExponentialHead.lean)
now pays every six-prime core label containing a prime
`p<=floor(exp(epsilon*N))`, for some fixed `epsilon>0`. This includes both
coefficient signs and all radial boundaries. It keeps the previous
count-3/4/positive-5 head widths and spends the same one-sixteenth charge
from the same original supply. Its exact rest has
`log p>epsilon*N` for **every** prime of a surviving six-prime label.
The independent whole-sum floor and ceiling remain open.

The later [negative five-prime extension](zeta-riesz-five-negative-head.md)
preserves this six-prime payment and spends another one thirty-second of
the same supply, leaving one thirty-second. The older ledgers below remain
valid; their unused fractions must not be added to the new ledger.

This strengthens the polynomial result below. The later sections explain
the minimum-prime information that removes its logarithmic loss.

The [Lean module](../RiemannGaussian/ZetaRieszSixPrimeHead.lean) pays every
squarefree six-prime label of the original core that contains a prime
`p<=N^2`. Both arithmetic coefficient signs are included. The lower and
upper comparisons keep the actual complex phase, factorial weight,
allocation factor, physical masks and one exact signed complement.
They require no zero or simplicity hypothesis.

This is a component payment, **not** either whole-sum cofinal bound in the
[multiplicity-aware endgame](zeta-riesz-joint-floor.md). Its starting order
is existential; no finite numerical starting order is certified here.

## The literal counting estimate

On `2M<=log n<=2M+2`, with `N<=2M`, `M>=100`,
`L>=271M/200` and `log Q<=M/32`, the
[signed six-prime coefficient bound](zeta-riesz-signed-sperner.md) implies

\[
|c_L(n)|\le16\log r\qquad(r\mid n\text{ prime}).
\]

For six prime factors, at least one prime has logarithm greater than
`M/8`. A marked prime `r<=Q` cannot be that prime. Count the large prime
at its actual residual product endpoint using the existing Chebyshev
upper bound. The remaining four prime factors may have arbitrary sizes.
Half-unit logarithmic shells give the literal estimate

\[
\sum_{\log p\le2M+2}\frac1p
\le (2e^{1/2}\log4)\bigl(1+\log(4M+4)\bigr).
\]

Combining this with the proved marked mass bound
`sum_(r<=Q) log(r)/r <= log(4)*(1+log Q)` yields

\[
\left\|\sum_{n\in S}f_{N,L,y}(n)\right\|
\le B(1+\log Q)\bigl(1+\log(4M+4)\bigr)^4
  \frac{e^{2M}}{M+1}\,\mathrm{radialEnvelope}(N,M),
\]

where `f` is the original residual atom and

\[
B=256(\log4)^2e^4(2e^{1/2}\log4)^4.
\]

`small_six_norm_upper` proves this for every finite selected population
satisfying the literal conditions. The counting overestimate permits
repeated candidate tuples; it never inserts them into the actual carrier.
No prime-density or phase approximation is used.

For `Q=N^2` and `N<=2M`, the additional factor divided by `M` is bounded
by a constant times `(log M)^5/M`, which tends to zero.
`eventually_small_six_cost` therefore makes the cost an arbitrarily small
fraction of the existing signed supply's radial scale, uniformly in
height. It does **not** assert source-normalized decay of the head alone.
This original logarithmic estimate alone does not pay a fixed exponential
six-prime head. The fractional estimate below does.

## One supply and the complete boundary payment

The previous [lower](zeta-riesz-five-positive-head.md) and
[upper](zeta-riesz-head-ceiling.md) spending theorems now expose their
proved positive radial calibration in `..._with_scale`; their original
interfaces remain available. The new six-prime payment uses that same
supply and the following fractions:

| Selected charge | Fraction |
| --- | ---: |
| Original narrow balanced triple band | 1/2 |
| Exponential three-prime head outside that band | 1/8 |
| Exponential four-prime head | 1/8 |
| Positive-coefficient exponential five-prime head | 1/8 |
| Six-prime head, exponential after the refinement below | 1/16 |
| Unused supply | **1/16** |

The common exponential width is chosen together with this supply. Six-prime
labels are disjoint from every earlier charge and from the four-prime
supply. No previous credit is added again. Lower and upper comparisons
choose their respective phase windows and may have different widths;
they are alternative inequalities, not additive budgets.

`eventually_core_floor` and `eventually_core_ceiling` first perform this
payment in the radial union. `mem_radialSixes_of_geometry` covers every
six-prime head label in the inner window without a dominant-prime
restriction. `exists_full_head_missed_bound` then pays all remaining
radial/dominant boundary labels, jointly with the old heads, by the existing
source-normalized allowance

\[
r^N C+2\,\mathrm{majorantMass}(1+1/262144)e^{-N/10^6},
\qquad 0\le r<1.
\]

The terminal theorems are **`eventually_core_full_floor`** and
**`eventually_core_full_ceiling`**. For `1/2<u<=10001/20000` and
`|y|>=16`, they retain all favorable selected real parts, one sixteenth
of the actual signed supply, this vanishing boundary allowance and the
entire signed complement. `remaining_six_prime_gt` states the resulting
support restriction: every prime in a surviving six-prime label exceeds
`N^2`.

## Keep the minimum logarithm before summing

The original coefficient bound contains `log(minFac n)`. Replacing it by
only the marked prime logarithm threw away its simultaneous comparison
with the other four cofactor primes. If those five logarithms are
`r,a,b,c,d` and their minimum is `t>0`, the elementary inequality

\[
\boxed{t\le r^{1/2}a^{1/8}b^{1/8}c^{1/8}d^{1/8}}
\]

retains that information in a factorable upper bound. The largest prime
is still counted at its actual product endpoint. No prime is completed,
and the original signed carrier is unchanged.

The [fractional budget module](../RiemannGaussian/ZetaRieszPrimeFractionalBudget.lean)
proves for every `alpha>0`, `X>0` and actual finite prime set `D` with
`log p<=X` that

\[
\sum_{p\in D}\frac{(\log p)^\alpha}{p}
\le C_\alpha X^\alpha,
\qquad C_\alpha=\frac{6\log4}{1-2^{-\alpha}}.
\]

It partitions the literal primes into dyadic logarithmic shells and uses
the already proved Chebyshev logarithmic mass bound. The shell containing
any prime has upper logarithm greater than `1/2`, which pays the small
endpoint constant. A convergent geometric series pays all shells. This
is an upper counting inequality, not a prime-density approximation.

`small_six_fractional_norm_upper` in the original head module combines
these facts to replace the earlier logarithmic loss by

\[
\left\|\sum_{n\in S}f_{N,L,y}(n)\right\|
\le B_*\sqrt{\log Q}\sqrt{2M+2}
  \frac{e^{2M}}{M+1}\,\mathrm{radialEnvelope}(N,M),
\]

where `B_*=256*log(4)*exp(4)*C_(1/2)*C_(1/8)^4` is explicit and positive.
For `log Q<=epsilon*N`, `N<=2M` and `M>=100`, the relative cost is at most
`4*B_*sqrt(epsilon)`. For any desired positive fraction `b`, the proof
chooses

\[
\varepsilon=\min\left(\frac1{128},
                   \left(\frac{b}{4B_*}\right)^2\right)>0.
\]

`eventually_small_six_log_cost` proves the resulting literal bound.
The constants are deliberately coarse; neither this formula nor the
existential supply calibration certifies a useful finite starting order.

## Full signed transfer of the exponential payment

In `ZetaRieszSixPrimeExponentialHead`,
`eventually_core_full_floor` and `eventually_core_full_ceiling` pay this
whole exponential head on the original cofinal schedule, throughout
`1/2<u<=10001/20000` and `|y|>=16`. The old head width `delta` and supply
are taken unchanged from the calibrated spending theorem; the new
six-prime width `epsilon` is chosen separately. The old one-half plus
three one-eighth charges and the new one-sixteenth charge leave
**one sixteenth of the same supply**. Both signs, all favorable selected
observations, the original masks and one exact signed complement remain.

The full boundary theorem uses the same vanishing allowance displayed
above. `remaining_six_prime_log_gt` states the new support restriction.
`eventually_polynomial_head_included` verifies that this exponential
threshold eventually contains the entire earlier `N^2` head.

## What remains

The remaining six-prime population with all prime logarithms above
`epsilon*N`, other
unpaid triple configurations, the unselected five-prime sign, higher
counts and the unused signed credit still need a joint estimate. The
lower target `-79/1000-o(1)` for simple zeros and the upper target
`3/2+o(1)` for higher multiplicities remain open. There is no new zero
exclusion or claim of a whole-carrier numerical bound.
