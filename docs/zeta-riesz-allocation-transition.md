# Signed cancellation across the factorial allocation transition

Both whole comparisons now include a strictly larger actual six-prime
population. The enlargement crosses the former largest-prime allocation
threshold `19/32`. The proof retains the allocation inside the signed
prime period instead of requiring the allocated fraction to be small.
The final independent whole floor and ceiling remain open.

## What is bounded

For a squarefree label `n=p*a`, the cofactor `a` has five prime factors
and `p` is uniquely largest. The new cofactor set is

```
((B(v) union B(4v/5)) restricted to log(a)>203v/500)
union the previous extra band (3v/5,133v/200].
```

Here `B` is the existing, literally counted broad cofactor set. The
previous population is included. The largest prime still runs through
its complete original log period. All small primes, squarefreeness,
coefficient signs, factorial orders, eligibility masks and physical/core
restrictions remain. Prime shares are at most `1189/2000=0.5945`, below
the separate paid owner band beginning at `119/200=0.595`, so no credit
is counted twice.

`eventually_added_population_crosses_transition` constructs actual new
labels at every sufficiently large center, with owner share strictly
above `19/32`. It uses least prime two, four distinct primes in separate
log windows, and the last ordinary prime in its full phase period.
Unique ownership excludes any relabeling into the previous population.

## Exact allocation variation

Let `F_N(x)` be the sum of the original binomial masses over the original
`unpaidOrders N`. With `T=log(pa)`, Lean proves exactly

\[
\theta_N(pa)=F_N(\log(a)/T)+
 \sum_{q\mid a,\ q\in A}F_N(1-\log(q)/T).
\]

Every divisor in this sum is a prime divisor. The changing owner is
proved to stay in the literal intermediate-prime set `A`; all cofactor
eligibility decisions stay fixed. This membership condition is necessary:
an arbitrary phase-dependent selection of moving owners is not allowed.

The full binomial variance is exactly `(N+1)x(1-x)`. Cauchy–Schwarz
bounds the selected score before differentiating along `T`. The resulting
literal estimate, including all six possible incidences, is

\[
|\theta_N(pa)-\theta_N(p_0a)|
 \le \frac{24\sqrt{N+1}}v\,|\log(pa)-\log(p_0a)|.
\]

Across the complete period, `pi/abs(y)<=1/16`, this costs at most
`3 sqrt(N+1)/v`. No order-zero atom or small prime is deleted.
See [`ZetaRieszAllocationVariation.lean`](../RiemannGaussian/ZetaRieszAllocationVariation.lean).

The signed coefficient has amplitude
`(1-theta_N(pa))*R_(T-L)(a)`. Freeze it at an actual prime in the same
period, then retain the phase sum before bounding its change. The exact
Riesz bound `abs(R)<=3 log(minFac(a))` and cutoff slope eight give variation

\[
1+\frac{9\sqrt{N+1}}v\log(\minFac(a)).
\]

The existing actual cofactor counts and prime-period estimate yield the
relative radial budget

\[
1000\eta C_1+
720C_1\frac{\sqrt{N+1}}v+
100C_2v^{-1/2}.
\]

Here `C1,C2` remain four times the original broad constants. Choose the
fixed phase mesh sufficiently fine, then let `N` increase: the budget is
arbitrarily small. This proves the full residual population estimate in
[`ZetaRieszTransitionSixPeriod.lean`](../RiemannGaussian/ZetaRieszTransitionSixPeriod.lean).
It is relative local `o(radial)`, **not source-o(1)**. Thresholds are
existential. No hypothetical zero, simplicity or spectral phase enters.

## Both whole comparisons

[`CheckRieszTransitionSixJoint.lean`](../scripts/CheckRieszTransitionSixJoint.lean)
and [`CheckRieszTransitionSixWhole.lean`](../scripts/CheckRieszTransitionSixWhole.lean)
use the new population at the same `m*V*h/100000` cost. They preserve
`(sqrt(N+1)/16-1/8)*sourceCredit`, every favorable signed observation,
and only Q's separate allocation error. Earlier reflection savings apply
to exactly the smaller signed rest
`S minus (P union I union H union Q union transitionZ union D)`.
The old six-prime payment is replaced, never added a second time.
The cached numerical covers are reused unchanged.

The remaining labels and phase periods still require signed estimates.
Neither the independent `-79/1000` whole floor nor the independent `3/2`
whole ceiling has been proved. This is no zero exclusion or RH claim.

## Optional diagnostic

[`probe_riesz_allocation_transition.py`](../scripts/probe_riesz_allocation_transition.py)
checks the actual binomial allocation in a model with owner share
`0.593875`. At `N=1,000,000`, the allocated fraction is about `0.60055`,
while its span over a full height-54 period is about `1.86e-5`.
The rigorous six-incidence span bound there is `0.001501`.
These figures explain why variation works when smallness of the allocated
fraction does not. They are not prime-sum or source-scale certificates
and are not used in Lean. The probe is not part of CI.
