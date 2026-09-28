# Positive-five interior: exact debit and sharper boundary payment

This note records the preceding boundary and cap slice. The subsequent
[full positive-five payment](zeta-riesz-full-positive-five-payment.md)
proves the complete literal prime transfer and both expanded whole-sum
applications. Its exhaustive numerical cover is still under verification;
that note distinguishes the proved transfer from the pending acceptance.

The literal small-prime boundary has a 25 percent smaller proved cost:

```math
\sum_{n\in H_{t,h}} |f_N(n)|\le
\frac{3}{40000}\frac{e^{-t/2}(t+h)^N}{N!}h,
\qquad
\sum_{n\in H_{\rm period}}|f_N(n)|\le \frac{g}{1600}V_0h.
```

The old constants were `1/10000` and `g/1200`. The population is unchanged:
squarefree positive-coefficient five-prime labels in the original phase
period, largest share below `119/200`, and a prime share at most `1e-8`.
Every original finite support, allocation and complex phase remains. The
threshold is eventual and has not been numerically evaluated.

The sharper debit is spent in **both whole `J+C` comparisons**, with the
same paid populations and exact signed rest. Their margin improves from
`(12*sqrt(N+1)-1/8)*G_N` to

```math
\left(\frac{25}{2}\sqrt{N+1}-\frac18\right)G_N,
\qquad G_N=\frac{\pi u e^{-1}}{24000|y|}\frac{(2u)^N}{N+1}.
```

The raw period margin after the fixed positive-five and small-prime
payments is `51*g*V0*h/8000`. This pays `25/4` copies of the strengthened
saddle credit before the unchanged owner debit `G_N/8`. Lower and upper
budgets are alternatives; their credits are not additive. The numerical
whole floor `-79/1000-o(1)` and ceiling `3/2+o(1)` remain open.

The local bounds are
`ZetaRieszPositiveFiveBoundary.eventually_norm_mass_sharp` and
`eventually_period_norm_mass_sharp`. The final applications are
`RieszCentralCapacityTransfer.eventually_joint_saddle_boundary_floor` and
`eventually_joint_saddle_boundary_ceiling` in the
[cached transfer](../scripts/CheckRieszCentralCapacityTransfer.lean).
The [audit](riesz-central-capacity-audit.json) records exact source hashes.

## Exact target for the remaining interior

[ZetaRieszPositiveFiveInterior](../RiemannGaussian/ZetaRieszPositiveFiveInterior.lean)
proves the actual floor-dependent length satisfies
`693/1000 <= L_N/t <= 1733/2500` eventually for every `2N-1<=t<=2N+1`,
throughout `1/2<=u<=10001/20000`. The physical floor and logarithmic damping
are retained. The elementary `N>=20000` condition in the proof is **not**
the complete starting threshold.

Write `p` for the largest prime and order the four cofactor primes as
`q>a>b>r`. With `d=L-log p`, the exact positive coefficient is

```math
\begin{gathered}
(c_L(n))_+=\frac{\log n}{L}\left[\min\{\log r-r_0,c\}\right]_+,\\
r_0=\max\{0,d-\log b,2d-\log b-\log a\},\qquad
c=\min\{d,\log(n/p)-3d\}.
\end{gathered}
```

This is `positive_coefficient_eq_cap`, applied to the original prime-factor
set. It retains both pair and triple deficits. In normalized coordinates,
positivity forces exactly the cubature restrictions
`p>(3*lambda-1)/2`, `b>(lambda-p)/2`, and `a<(1-lambda)/2`.

For nonnegative cap height, the subtraction survives harmonic integration:

```math
\begin{aligned}
[\min(x-r_0,c)]_+&=\min(x,r_0+c)-\min(x,r_0),\\
\int_a^b\frac{[\min(x-r_0,c)]_+}{x(S-x)}\,dx
&=\int_a^b\frac{\min(x,r_0+c)}{x(S-x)}\,dx
-\int_a^b\frac{\min(x,r_0)}{x(S-x)}\,dx.
\end{aligned}
```

Both integrability conditions, including a zero lower endpoint, are proved.
`checked_shifted_cap_integral_le` turns two accepted existing cap certificates
into a bound for their difference. This is an entire-fibre inequality, not
a sample-point check.

## Still unproved

The [floating probe](riesz-positive-five-fibre-probe.json) suggests an
angular debit below `1/250` on the now-proved narrow bin. Its values remain
uncertified and are not used by either whole-sum theorem. A complete
three-variable cover, the literal ordered-prime transfer and the union
payment for the entire remaining positive-five interior are still required.
The original fixed positive-five population must not be charged a second
time when that union is paid. No new zero exclusion follows from this slice.
