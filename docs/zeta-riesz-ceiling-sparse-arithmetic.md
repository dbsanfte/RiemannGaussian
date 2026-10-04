# Pointwise payment of sparse arithmetic populations

The full objective remains the independent **42/25 ceiling** for the same
native `joinedPhysical`, throughout `1/2 < u <= 10001/20000` and at every
height. This slice does **not** prove that ceiling, simplicity, a zero
exclusion, or RH. It pays actual moving arithmetic subsums pointwise; the
previous slice paid only a long-height average.

## The proved arithmetic inequality

Write the already source-normalized coefficient of the original joined
carrier as `joinedAmplitude u N K n`. Every original radial, count, physical,
allocation and saturation/complement condition stays in that coefficient
and `coreBand`. For **any** literal subpopulation `S` of the core, Lean proves

\[
\left|\sum_{n\in S}a_{N,K}(n)n^{-iy}\right|^2
\le (3uN(2u)^N)^2 M_\varepsilon
       \sum_{n\in S}n^{-(1-\varepsilon)},
\qquad \varepsilon=\frac1{100000},
\]

where

\[
M_\varepsilon=\sum_{n\ge1}\frac{\tau(n)^2}{n^{1+\varepsilon}}<\infty.
\]

This is a complete convergent arithmetic constant. It is not a prime-density
model or a finite sampled mass. The signed integer coefficient is collected
before applying weighted Cauchy–Schwarz; no individual prime phase is
randomized. All factorial orders, including zero and one, remain unchanged.

An actual integer progression satisfies the exact endpoint count
`card S <= M/d + 1` below `M`. Partitioning the **whole** literal population
by `floor(log n)` and retaining the original core window proves, for
`N >= 1`, `d >= exp(N/2500)` and `n % d = r` on `S`,

\[
\sum_{n\in S} n^{-(1-\varepsilon)}
\le 5(3N+1)e^{-37N/100000}.
\]

The source growth is beaten uniformly at the original upper radius:

\[
(2u)^{2N}e^{-37N/100000}\le e^{-17N/100000}.
\]

Consequently, at **every** height and prime-count cutoff,

\[
\boxed{\left|\sum_{n\in S}a_{N,K}(n)n^{-iy}\right|
\le C(N+1)^2e^{-N/16384}},
\qquad C=12\,\mathrm{radiusCeiling}\sqrt{M_\varepsilon}.
\]

No exposure, hypothetical-zero, phase independence, sieve estimate or
height limit is used in this payment.

## Whole moving populations and the exact rest

The explicit modulus

\[
d_N=2^{\lfloor N/1600\rfloor+1}
\]

satisfies `exp(N/2500) <= d_N`. Thus every **complete native residue
population** for this modulus is paid, not just a finite sample or a selected
prime-count sector. A union of at most `exp(N/32768)` classes obeys

\[
\boxed{|\mathrm{residueUnionPacket}_N|
       \le C(N+1)^2e^{-N/32768}\longrightarrow0.}
\]

The conclusion remains valid for moving heights, counts, residue choices
and every cofinal order schedule. These packets are already normalized by
`u^(N+1)`; that power must not be applied a second time.

The complementary ledger is exact:

\[
u^{N+1}\mathrm{joinedPhysical}_N
=\mathrm{residueUnionPacket}_N+\mathrm{residueRestPacket}_N.
\]

Under the original exposed-zero hypotheses, the rest therefore retains
**the same** source limit

\[
-m+m^2\,\mathrm{retainedCost}(u).
\]

In particular, the multiple-source value at the upper radius is still
`1.680512811860... > 42/25`. **The numerical gap for the whole ceiling has
not decreased.** This slice gives a rigorous pointwise payment for sparse
actual populations; it does not pay their entire union.

## The remaining global cost

There are `d_N` possible classes. Summing their individual norm prices
would introduce the positive exponential rate

\[
\frac{\log 2}{1600}-\frac1{16384}
=0.0003721818315999\ldots>0.
\]

That is a **method price**, not a lower bound on the literal signed carrier.
The source can survive across many classes. The full rest still needs its
actual signed cross-class correlations, or a separate global arithmetic
inequality; no independent class phases are assumed. Merely choosing more
classes and summing their norm bounds cannot close the ceiling.

## Validation and numerical scope

The optional leaf build and scoped check pass: 14 linters, 42 theorems
including generated helpers, and only `propext`, `Classical.choice`, and
`Quot.sound` in transitive axiom dependencies.

The optional probe checks eight order values through `N=1048576` at 360-bit
precision. An independent 420-bit replay uses combined logarithmic
exponents and exact arithmetic-progression endpoints, with interval widths
checked. The source-squared exponent is
`-0.0001700099993333...`; the chosen pointwise rate has margin
`0.0000239698434166...`. Forty-nine finite integer endpoint controls replay
exactly. They are controls for the count and rate, not native-core
enumeration, actual-zero samples, or a full-ceiling certificate.

The complete constant `M_epsilon` is not numerically bounded here, so no
numerical native entry order is certified. All 267 earlier proof/probe pins
remain unchanged. This slice is local and uncommitted, outside root
registration, public metadata, CI and wider gates.

The proof is in
[ZetaRieszCeilingSparseArithmetic.lean](../RiemannGaussian/ZetaRieszCeilingSparseArithmetic.lean).
The scoped provenance is
[riesz-ceiling-sparse-arithmetic-audit.json](riesz-ceiling-sparse-arithmetic-audit.json).
