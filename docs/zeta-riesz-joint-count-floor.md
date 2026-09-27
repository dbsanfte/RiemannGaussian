# Paying a larger prime-count part of the joint core

[`ZetaRieszJointCountFloor`](../RiemannGaussian/ZetaRieszJointCountFloor.lean)
proves an independent bound for a larger part of the **actual finite
arithmetic sum**. It keeps the existing moment schedule, core masks,
allocation factor and complex phase. No new carrier is defined.

Write

\[
U=\frac{10001}{20000},\qquad
K_j=2^{j+3},\qquad N_j=8(j+4)K_j,\qquad K'_j=K_{j-9}.
\]

For `j >= 9`, `512 K'_j = K_j`. Eventually, uniformly for every real
height and `0 <= u <= U`, the source-normalized sum over **any selection**
of original-band labels with at least `K'_j` prime factors has norm at most

\[
E_j=32U\log 2\;N_j\left(\frac{49999}{50000}\right)^{N_j}
\longrightarrow0.
\]

The summand is the literal `residualCoefficient * zetaPrimeLogKernel`.
In particular, the theorem covers the full integer response, rather than
only a frequency range. No zero hypothesis is used.

## Exact rate and its scope

The count-generating estimate uses the already summable Euler mass at
`sigma = 3/2 - q > 1`, with

\[
q=\frac{131071}{262144},\qquad
b=\frac{7001}{7000},\qquad s=\frac{100001}{100000}.
\]

For `j >= 64`, Lean proves `(K'_j)^(K'_j) >= b^(N_j)` by rational
logarithm bounds. The existing Euler-mass estimate supplies the factor
`s^(N_j)` eventually. The remaining rate satisfies the exact rational
inequality

\[
\frac{U}{q}\frac{s}{b}\le\frac{49999}{50000}<1.
\]

The **full arithmetic bound is eventual**. Its starting order has not
been numerically evaluated because the Euler-mass constant is unevaluated.
`j >= 64` is only the threshold of the count-power certificate.
The optional [rate probe](../scripts/probe_riesz_joint_counts.py) records
[uncertified scalar diagnostics](riesz-joint-count-probe.json); Lean
checks the stated inequalities independently.

## Direct joint comparison

Changing the count endpoint of `coreBand` is proved to be exactly a
filter, with no additional boundary term. Thus

\[
\operatorname{Re}\bigl(u^{N_j+1}\mathrm{coreResponse}(N_j,K_j)\bigr)
\ge
\operatorname{Re}\bigl(u^{N_j+1}\mathrm{coreResponse}(N_j,K'_j)\bigr)-E_j.
\]

`tendsto_joint_sub_smaller_count` also proves that the original joint
target `lowerThresholdPacket - shortOverflowPacket + rest` differs from
the smaller-count core by a source-normalized quantity tending to zero.
Neither component is estimated separately. The earlier radial/allocation
comparisons apply to this core because they allow an arbitrary count
endpoint.

For every newly retained squarefree label, any divisor `a` made entirely
of primes at most `N_j^2` now satisfies

\[
\log a\le\frac{N_j}{2048}.
\]

This improves the old `N_j/4` support budget. It does not delete the small
primes, their phase, or a boundary contribution.

The count endpoint still grows: **every fixed prime-count class remains
eventually**. In particular this is not a fixed 39- or 55-prime truncation,
and it does not remove the balanced-triple obstruction. The retained raw
signed sum and central allocation transition still need the
[joint cofinal floor](zeta-riesz-joint-floor.md) `-79/1000-o(1)`.
No independent whole-core floor, RH contradiction or new zero exclusion
is proved by this slice.
