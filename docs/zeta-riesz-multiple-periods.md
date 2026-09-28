# More signed prime periods at the same whole-sum cost

The six-prime payment now covers several disjoint full phase periods instead
of one. Both whole comparisons retain the previous margin
`(sqrt(N+1)/16 - 1/8) * sourceCredit`, and retain the favorable real part of
each period separately. The independent final floor `-79/1000` and ceiling
`3/2` remain open.

## The proved estimate

For fixed `|y| >= 54`, put

\[
M_y=1+\left\lfloor\frac{|y|}{4\pi}\right\rfloor,
\qquad v_i=v+\frac{2\pi i}{|y|}\quad(0\le i<M_y).
\]

If `2N <= v <= 2N+1/2` and `cos(y*v)=-1`, all these centers lie in
`[2N,2N+1]` and have the same phase. Each population is exactly the existing
`ZetaRieszTransitionSixPeriod.population v_i y`. Its half-open logarithmic
period is `(v_i-pi/|y|, v_i+pi/|y|]`. These periods are disjoint, so every
arithmetic label is counted once. The original period is included; the
additional periods contain actual prime labels eventually.

For the literal residual atom

\[
f_N(n)=\operatorname{residualCoefficient}(A,L,N,n)
       K_N(3/2+iy,n),
\]

Lean proves, for every fixed `epsilon>0`, eventually uniformly in the
admissible center,

\[
\sum_{i<M_y}\left|\operatorname{Re}
  \sum_{n\in Z(v_i,y)}f_N(n)\right|
\le \varepsilon\frac{\pi}{4|y|}
       \frac{e^{-v/2}v^N}{N!}.
\]

The signed sum is taken over each whole prime period before its absolute
value. We do not take absolute values of individual prime atoms. Every
small prime, factorial order, allocation factor, coefficient sign, and
physical/core mask from the preceding theorem remains present.

The proof fixes precision `epsilon/M_y`, applies the existing uniform
period theorem, and uses the exact decrease of `exp(-v/2)*v^N/N!` for
`v>=2N`. Since `y` is fixed, `M_y` is fixed before `N` tends to infinity.
This is relative local `o(radial)`, **not source-o(1)**. The starting order
is existential, and the result is not uniform in a growing height `y`.

## Both whole comparisons

The sum of period costs fits the same previous `m*V*h/100000` debit. The
floor retains `sum_i max(Re(sum_Zi f),0)`; the ceiling retains
`sum_i min(Re(sum_Zi f),0)`. In particular, the old period's favorable
contribution is not lost by combining it with other periods first.

The exact unpaid rest is now

`S \ (P union I union H union Q union multiZ union D)`.

All previous disjointness conditions are proved. The owner population `D`
is paid once. Earlier six-prime reflection costs are applied only to this
smaller rest. The previous single-period payment is replaced, never paid
twice. Only `Q` retains a separate geometric allocation error. The cached
finite numerical covers are reused unchanged.

The compiled applications are
[`CheckRieszMultiPeriodSixJoint.lean`](../scripts/CheckRieszMultiPeriodSixJoint.lean)
and
[`CheckRieszMultiPeriodSixWhole.lean`](../scripts/CheckRieszMultiPeriodSixWhole.lean).
The root-imported theorem is in
[`ZetaRieszMultiPeriodSix.lean`](../RiemannGaussian/ZetaRieszMultiPeriodSix.lean).
Validation is recorded in
[`riesz-central-capacity-audit.json`](riesz-central-capacity-audit.json).

## Size and limitation

At height 54, `M_y=5`; at heights 100, 1000 and 10000 the counts are 8, 80
and 796. These are elementary evaluations of the count formula, not prime
certificates. Lean proves `M_y>=5` for every admissible height, including
negative heights. The total logarithmic width covered is
`2*pi*M_y/|y|`, between `1/2` and `1/2+2*pi/|y|`.

This removes additional actual six-prime labels from both unpaid sums
without increasing the established debit. It does not cover the full
radial saddle, whose width grows with `sqrt(N)`, and does not bound the
remaining counts and phase periods. Neither a zero exclusion nor an RH
contradiction is asserted. The estimates use no zero or simplicity
hypothesis.
