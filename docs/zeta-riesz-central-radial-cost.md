# Joint radial saving for the whole central cost

The [Lean proof](../RiemannGaussian/ZetaRieszCentralRadialCost.lean) improves
the **same combined central cost** from the preceding `N log(N)` majorant
to square-root order. The [audit](riesz-central-radial-cost-audit.json)
records the precise scope and verification.

For the original central cost `D_N`, Lean proves

```math
D_N\le
\frac{12\sqrt{2E}}{\log2}\,
\bigl(4e^{1/2}\log4\bigr)
\sqrt{16N+8}\,(2u)^N.
```

This holds eventually for fixed `0<u<=10001/20000`, uniformly in the
height and count cutoff. The original allocation, all factorial orders,
squarefreeness, canonical ownership, full product phase and every previous
finite mask remain. There is no change of carrier and no completion.

The exact original whole core is bounded on both sides by the minimum
of this and the preceding majorant, plus the already proved outer error
`C exp(-N/1000000)`, charged once. The arithmetic constant `E>0` and
eventual starting order are still unevaluated.

## Where the saving comes from

For `f_N(T)=exp(-T/2) T^N/N!`, the exact positive radial mass is

```math
\int_0^\infty f_N(T)\,dT=2^{N+1}.
```

For every offset `x>=0`, spacing `h>0` and finite number of shells `J`,

```math
\sum_{j<J}f_N(x+jh)
\le \frac{e^{h/2}}h\,2^{N+1}.
```

Taking `h=log 2` sums the actual dyadic cofactor shells before charging
their maxima. A fixed prime cannot put every shell at the factorial saddle.
This removes a factor of order `sqrt(N)` from the earlier estimate.

The other loss came from charging every prime the largest profile energy.
Keeping its own energy instead leaves the literal finite prime sum

```math
\sum_{p\le X}\frac{\sqrt{\log p}}p
\le 4e^{1/2}\log4\,\sqrt{4\log X+8}.
```

This inequality uses the repository's proved Chebyshev counts on half-unit
logarithmic shells. It is an upper bound for actual primes, not a prime-density
approximation. It removes the former log-log loss. Together the two estimates
give the displayed square-root-order bound for the **whole** cost.

## What remains

This is a polynomial improvement, **not a new phase-cancellation estimate**.
The factor `(2u)^N` still grows in the right-half-zero campaign. Its exponent
at `u=0.50005` is approximately `0.000099995`, with the earlier exact Lean
bounds `0.000099 < log(2u) < 0.0001` preserved.

The next task is to prove a signed phase saving strong enough to overcome
this exponent, or a direct one-sided estimate that closes the endgame.
Another polynomial improvement is not that target. Neither the `-0.079`
floor nor the `1.5` ceiling is proved; there is no new zero exclusion.
