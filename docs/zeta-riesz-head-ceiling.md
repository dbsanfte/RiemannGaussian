# The upper counterpart of the exponential-head payment

[`ZetaRieszHeadCeiling.lean`](../RiemannGaussian/ZetaRieszHeadCeiling.lean)
proves an independent **upper comparison** for the original `coreResponse`,
including the complete selected exponential prime heads and their radial
and dominant-prime boundary errors. It does not prove the numerical
whole-carrier ceiling `3/2+o(1)` required to exclude multiple zeros.

The distinction matters: the retained source is
`-m+m^2*c_ret(u)`. A negative floor can contradict the simple-zero source;
it cannot contradict the positive source at multiplicity at least two.
The new theorem develops the additional upper-bound side of that same
endgame without assuming simplicity, exposure or any hypothetical zero.

## Actual negative supply

For every fixed `abs(y)>=16`, `exists_short_positive_window` places a
positive-cosine window inside each original two-unit radial slab. It
chooses `0<=v<=1/2` and a fixed `0<h<=1/20` such that

```math
\cos(yt)\ge\frac12\qquad(2M+v\le t\le2M+v+4h).
```

The already evaluated four-prime supply has negative Riesz coefficient
there. `supply_atom_upper` retains its original allocation, factorial
moment and complex phase and proves

```math
\operatorname{Re}f_N(n)
\le-\frac{M}{160}e^{-3/2}\operatorname{radialEnvelope}(N,M).
```

The proof reuses the earlier amplitude lower bound by calibrating its
observation at `pi/log n`, then returns to the **original** height `y`.
There is no change of carrier or prime mask. Literal counting gives
`eventually_supply_upper`: for some fixed `c>0`, eventually

```math
c\frac{M e^{2M}}{M+1}\operatorname{radialEnvelope}(N,M)
\le-\operatorname{Re}\sum_{n\in Y_M}f_N(n).
```

## The same heads are paid from above

`eventually_joint_slabs_upper_log_head` chooses a fixed common
`delta>0`. One negative four-prime supply pays the norm costs of the
original narrow balanced triple band, the count-three head, the
count-four head, and the **positive-coefficient** count-five head with
a prime below `floor(exp(delta*N))`.

The fractions are `1/2, 1/8, 1/8, 1/8`. They consume seven eighths of
one supply; the remaining eighth is negative in the upper comparison.
The exact finite theorem `re_sum_le_joint_spending` retains every
favorable **negative** observation of those populations:

```math
\operatorname{Re}\sum_{n\in S}f_N(n)
\le\operatorname{Re}W
 +\sum_{E\in\{X,Z,H,F\}}\min\left(\operatorname{Re}\sum_{n\in E}f_N(n),0\right)
 +\frac18\operatorname{Re}\sum_{n\in Y}f_N(n).
```

Here `W` is the exact sum over the complement of the disjoint paid
populations and supply. The upper inequality follows by applying the
proved finite lower spending identity to `-f`; the arithmetic supply
estimate itself is newly proved at the positive-cosine phase.

## Full core transfer and remaining obligation

`eventually_core_exponential_ceiling` transfers this inequality across
the disjoint radial slabs on the original dyadic schedule, with the
original moving Riesz length and finite support. The terminal
**`eventually_core_full_exponential_ceiling`** also pays the entire
selected head outside those slabs, using the existing bound

```math
\varepsilon_N=r^N C+
2\,\operatorname{zetaMoebiusLogMajorantMass}(1+1/262144)
e^{-N/1000000}\longrightarrow0.
```

It multiplies the displayed signed ledger by `u^(N+1)` and adds
`epsilon_N`, for `1/2<u<=10001/20000`. The exact rest excludes the
whole balanced triple band and every selected exponential head of
counts three/four and the positive five-prime class. No unestimated
radial or dominant-prime omission is hidden in that claim.

The [lower](zeta-riesz-five-positive-head.md) and upper ledgers may use
different widths and supply windows. They are **alternative comparisons
of the same carrier**, not independent credits to add together, and they
do not establish cancellation between their two signed rests.

Other triple shapes, larger-prime sectors, unselected five-prime signs,
higher counts and all remaining signed terms still need estimates. The
whole-joint-sum floor `-79/1000-o(1)` and ceiling `3/2+o(1)` remain open.
No zero exclusion or RH contradiction follows yet.
