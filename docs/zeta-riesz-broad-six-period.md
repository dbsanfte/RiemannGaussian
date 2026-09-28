# Broad six-prime cancellation in the whole comparison

The new independent signed estimate replaces the small six-prime plateau
by a much broader population. Both whole comparisons retain their checked
margin and all earlier payments, with this larger population removed from
the exact unpaid rest. The final numerical whole floor and ceiling remain
open.

## Literal population and estimate

Write each selected squarefree integer uniquely as `n=p*a`, where `p` is
its largest prime and `a` has five distinct prime factors. For a negative
phase peak `cos(y*v)=-1`, retain precisely

\[
\frac{56}{125}v<\log a\le\frac35v,\qquad
\log q\le\frac{39}{100}v\quad(q\mid a),\qquad
v-\frac\pi{|y|}<\log n\le v+\frac\pi{|y|}.
\]

There is no lower least-prime cutoff or coefficient-sign restriction.
`old_population_subset` proves that this contains the previously paid
plateau population; the two payments must replace one another.

For fixed `|y|>=54`, any `epsilon>0`, and all sufficiently large `N`,
uniformly for `2N<=v<=2N+1` and `L>=67v/100`, Lean proves

\[
\left|\operatorname{Re}\sum_{n\in Z(v,y)}
 c_L(n)K_N(3/2+iy,n)\right|
\le\epsilon\frac{\pi}{4|y|}
 \frac{e^{-v/2}v^N}{N!}.
\]

The theorem is
[`eventually_raw_population_small`](../RiemannGaussian/ZetaRieszBroadSixPeriod.lean).
It uses actual prime counts and the original moving factorial kernel.
The starting order is existential and can depend on height and precision.
This is an arbitrarily small **relative local** cost, not source-normalized
`o(1)`; multiplying it by `u^(N+1)` does not establish absolute decay.

## What makes the broad estimate work

The exact reflected coefficient is

\[
c_L(pa)=-\frac{\log(pa)}L\mathcal R_{\log(pa)-L}(a).
\]

It varies across the last-prime period. Lean sums the signed phase with
central response `R_(v-L)(a)` first, then pays the cutoff movement using

\[
|\mathcal R_D(a)-\mathcal R_E(a)|\le8|D-E|,
\qquad |\mathcal R_D(a)|\le3\log\minFac(a).
\]

The actual cofactor populations satisfy

\[
\sum_a\frac{\log\minFac(a)}a\le C_1v,
\qquad \sum_a\frac1a\le C_2\sqrt v.
\]

Here `C1=momentConstant(1/2)*momentConstant(1/8)^4` and
`C2=(2*momentConstant(1/10))^5` are explicit positive counting constants.
Positive tuple overcounting is used only after the signed last-prime sum.
Consequently the relative cost is bounded by
`1000*eta*C1 + 100*C2/sqrt(v)`. Arbitrarily precise fixed prime-window
counts and saddle comparability make `eta` as small as needed. No Riesz
chamber, least-prime boundary, or phase is dropped.

## Both whole estimates

[`CheckRieszBroadSixJoint.lean`](../scripts/CheckRieszBroadSixJoint.lean)
spends the new population at the previous cost `m*V*h/100000`, using the
already verified optional cover assemblies. Both comparisons retain

\[
\left(\frac{\sqrt{N+1}}{16}-\frac18\right)G_N
\]

against exactly `S \ (P union I union H union Q union Z union D)`, now with
the **broad** `Z`. Every favorable coupled observation remains, and the
original allocation is paid with the same two geometric allocation errors.
Disjointness from every other paid population is proved.
[`CheckRieszBroadSixWhole.lean`](../scripts/CheckRieszBroadSixWhole.lean)
also applies the preceding second-reflection charges to precisely this
smaller unpaid rest.

These are independent arithmetic comparisons, with no zero or simplicity
premise. They do not prove the final `-79/1000` whole floor, the `3/2`
whole ceiling, a zero exclusion, or RH. Other populations and other phase
periods still require joint estimates.

## Numerical diagnostic

The optional
[`probe_riesz_broad_six_period.py`](../scripts/probe_riesz_broad_six_period.py)
records four independent scrambled Sobol replicates in
[`riesz-broad-six-period-probe.json`](riesz-broad-six-period-probe.json).
In the continuum angular model, the new region accounts for about 71%
of the sampled negative one-large six-prime mass. The earlier plateau's
separate quadrature gave about 0.003%. These diagnostics omit radial and
phase weights and are not rigorous enclosures or payments in the ledger.
The Lean bound is independent of the probe; routine CI does not run it or
repeat the exhaustive numerical covers.
