# Recovering the factorial square-root in both whole-sum bounds

The same whole `J+C` comparisons now retain

```math
\left(\frac{25}{2}\sqrt{N+1}-\frac18\right)G_N
\quad\text{instead of}\quad \frac{47}{8}G_N,
\qquad
G_N=\frac{\pi u e^{-1}}{24000|y|}\frac{(2u)^N}{N+1}.
```

Every paid population, favorable signed observation and exact signed rest
is unchanged. The improvement in each alternative comparison is
`(25/2*sqrt(N+1)-6)*G_N`. This recovers a loss in the factorial estimate; it
does not assert a new cancellation theorem for the remaining prime sum.
The independent numerical floor `-79/1000-o(1)` and ceiling `3/2+o(1)`
remain open, and no zero exclusion follows.

## The checked radial improvement

Monotonicity of Mathlib's Stirling sequence proves, for every `N>=1`,

```math
N!\le 3\sqrt N\,(N/e)^N.
```

Consequently, on the same actual central window `2N<=v<=2N+1`,

```math
\frac{e^{-1}2^N}{3\sqrt N}
\le \frac{e^{-v/2}v^N}{N!}.
```

The preceding proof used denominator `6*(N+1)`. Keeping the square-root
therefore gives the exact source-normalized comparison

```math
2\sqrt{N+1}\,G_N
\le u^{N+1}\frac{g}{1000}
        \frac{e^{-v/2}v^N}{N!}\frac{\pi}{4g|y|}.
```

Here `g` is the phase mesh count, not zero multiplicity. These are global
inequalities for `N>=1`, not an unevaluated use of Stirling asymptotics.
They are proved in
[ZetaRieszSaddleCredit.lean](../RiemannGaussian/ZetaRieszSaddleCredit.lean),
particularly `factorial_upper`, `saddle_radial_lower` and
`sourceCredit_le_scaled_margin`.

## Applying it after all old payments

Retain the central population `P`, the fixed positive-five population `B`,
the all-count owner population `D`, and the newly paid small-prime
boundary `H`. The [boundary payment](zeta-riesz-positive-five-boundary.md)
now has the sharper cost `g*V0*h/1600`, leaving raw period margin
`51*g*V0*h/8000`. This pays `25/4` copies of the strengthened radial comparison. The owner debit remains
only `G_N/8`.

Writing `b,d,h0` for the original complex sums over `B,D,H`, and `R` for
the unchanged exact signed rest, the new endpoints prove

```math
\begin{gathered}
u^{N+1}\bigl(\operatorname{Re}R+
 \max(\operatorname{Re}b,0)+\max(\operatorname{Re}h_0,0)+
 \max(\operatorname{Re}d,0)\bigr)
 +\left(\frac{25}{2}\sqrt{N+1}-\frac18\right)G_N-e_j
 \le \operatorname{Re}\bigl(u^{N+1}(J+C)\bigr),\\
\operatorname{Re}\bigl(u^{N+1}(J+C)\bigr)
 \le u^{N+1}\bigl(\operatorname{Re}R+
 \min(\operatorname{Re}b,0)+\min(\operatorname{Re}h_0,0)+
 \min(\operatorname{Re}d,0)\bigr)
 -\left(\frac{25}{2}\sqrt{N+1}-\frac18\right)G_N+e_j,
 \qquad e_j\longrightarrow0.
\end{gathered}
```

The respective lower and upper populations are alternative budgets, as
before; their reserves cannot be added. The statements hold on the original
dyadic orders for `1/2<u<=10001/20000` and fixed `abs(y)>=54`, without a
zero hypothesis. The full arithmetic starting order remains unevaluated.

The terminal declarations are
`RieszCentralCapacityTransfer.eventually_joint_saddle_boundary_floor` and
`RieszCentralCapacityTransfer.eventually_joint_saddle_boundary_ceiling` in
[the cached application](../scripts/CheckRieszCentralCapacityTransfer.lean).
The [audit](riesz-central-capacity-audit.json) records its exact inputs and
standard axioms. No optional exhaustive cover was rerun.

## Numerical direction for the remaining positive-five interior

The optional
[fibre probe](../scripts/probe_riesz_positive_five_fibre.py) integrates the
least-share cap first while retaining the denominator of the second-largest
cofactor. The [recorded output](riesz-positive-five-fibre-probe.json) is
explicitly uncertified. At 100,000 refinements its floating enclosure
estimates are approximately `0.004773` on the existing cutoff bin and
`0.003954` on the candidate tighter bin `0.693..0.6932`.

These numbers are not spent in either theorem. The tighter moving-length
range is now proved in [the interior debit work](zeta-riesz-positive-five-interior.md).
A complete checked integral enclosure, the literal prime transfer,
and all boundary/allocation costs remain obligations. The square-root
credit prevents a later positive period margin from being unnecessarily
lost in source normalization, but does not itself prove that margin after
the new interior cost.
