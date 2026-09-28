# A phase-correlated density error survives in the core

This is a negative test of **opposite-phase pairing justified only by local
density accuracy**. It is not an estimate or a counterexample for the actual
prime sum. It preserves the [multiplicity-safe joint criterion](zeta-riesz-joint-floor.md)
and every previously checked arithmetic comparison. Both whole-sum bounds
remain open.

The [central-period credit](zeta-riesz-central-reserve.md) grows at source
scale. Its signed complement must oppose it if the whole sum has a finite
source. It is tempting to pair neighboring positive and negative phase
windows using their nearly equal prime densities. The following calculation
identifies a correlation which that argument must control.

For fixed `1/2<u<=10001/20000`, nonzero `y`, and arbitrary real `a`, put

\[
e(T)=a e^{-(u-1/2)T}\cos(yT).
\]

[`ZetaRieszPhaseDensityAudit`](../RiemannGaussian/ZetaRieszPhaseDensityAudit.lean)
proves all of the following without a zeta-zero hypothesis:

- For every fixed natural `b`, `T^b*e(T)->0`.
- The model density `1+e(T)` is eventually strictly positive.
- If `yh=pi`, then
  `e(T+h)*cos(y(T+h))=exp(-(u-1/2)*h)*e(T)*cos(yT)`.
- With the exact factorial and complex phase,

\[
\boxed{
u^{N+1}\int_0^\infty
\frac{T^N}{N!}e^{-T/2}e^{-iyT}e(T)\,dT
=\frac a2\left[1+\left(\frac{u}{u+2iy}\right)^{N+1}\right]
\longrightarrow\frac a2.
}
\]

The two cosines are correlated: their real observation is
`a*exp(-(u-1/2)*T)*cos(yT)^2`. A sign change of the observing cosine alone
therefore does not imply cancellation between the two windows. This is
not the earlier argument allowing arbitrary rotations of complex bilinear
coefficients; the density error here is real, fixed in `T`, and compatible
with eventual positivity.

## Both core boundaries are paid

The terminal `tendsto_core_error_source` proves the same limit on precisely

\[
\frac{39}{20}N<T\le\frac{203}{100}N.
\]

There is no frozen `T=2N` substitution. For the normalized gamma density
`g_N(T)=u^(N+1)*T^N*exp(-uT)/N!`, Lean evaluates

\[
\int_0^\infty g_N(T)(T-N/u)^2\,dT=\frac{N+2}{u^2}.
\]

The core contains `N/u` with a uniform rational margin. This gives the
explicit exterior error bound

\[
\left|\text{full normalized error}-\text{core normalized error}\right|
\le |a|\frac{10000(N+2)}{u^2N^2}\longrightarrow0.
\]

This deliberately crude bound is enough to locate the nonvanishing error
inside the core. It uses the unit-mass gamma weight of the error itself,
not a relative error multiplied by the growing absolute carrier envelope.
It pays **no** prime-count, allocation, Riesz coefficient or other arithmetic
mask: those are absent from this inference audit.

For `a=-1/5`, the core error tends to `-1/10`, eventually below the proposed
`-79/1000` floor. For `a=4`, it tends to `2`, eventually above the `3/2`
ceiling. The two final Lean theorems assert these statements about the
**error model**, not about `coreResponse` or `J+C`. They show why neither
direction of the multiplicity-safe criterion follows from merely neglecting
a very small local density error.

## Numerical check

The optional [probe](../scripts/probe_riesz_phase_density.py), with
[recorded output](riesz-phase-density-probe.json), retains the complex phase
and both endpoints at `u=10001/20000`, `y=54`:

| N | Core error, a=-1/5 (real part) | Core error, a=4 (real part) |
| ---: | ---: | ---: |
| 256 | -0.0250170 | 0.500341 |
| 4096 | -0.0776427 | 1.552855 |
| 8192 | -0.0900625 | 1.801250 |
| 32768 | -0.0996697 | 1.993394 |
| 131072 | -0.0999999973 | 1.9999999462 |

These floating-point values are diagnostics, not certified finite-order
bounds. The limits and exterior estimate are proved separately in Lean.
No numerical prime sums, count-tail bounds or literal carrier estimates
are claimed. Reproduce with:

```sh
../.venv/bin/python scripts/probe_riesz_phase_density.py \
  --output docs/riesz-phase-density-probe.json
```

## Literature applicability

Goldston and Yıldırım's Theorem 1.1 evaluates pair/triple correlations of
the truncated divisor sum `Lambda_R`. Theorem 1.4 treats mixed prime
correlations under a level-of-distribution range; unconditionally its
three-factor range is `R<X^(1/4-epsilon)`. The current reflected cutoff
is about `X^0.307`, and the literal target additionally retains Möbius
parity, allocation and a coupled complex phase. Their results therefore
cannot be substituted for our missing signed comparison. This is an
applicability assessment, not a claim that their techniques cannot help.
[Primary paper, Theorems 1.1 and 1.4](https://arxiv.org/html/math/0111212).

Schlage-Puchta proves that an off-critical zero forces a large PNT-error
value in a controlled multiplicative interval. Its power-sum proof retains
oscillating zero contributions. This is consistent with the warning from
our model: an error small relative to the main density may carry the
observed source. It supplies no independent bound for our retained signed
sum. [Primary paper, Theorem 3 and proof](https://arxiv.org/html/1912.00853).

Pintz's 2026 preprint compares maximal/average absolute Möbius and PNT
errors to quantities determined by zeta zeros. It does not give the fixed
signed factorial observation needed here; an absolute-error comparison
cannot be used as the missing cofinal floor or ceiling.
[Primary preprint, Theorems 2.1–2.2](https://arxiv.org/html/2608.24878v2).

## Consequence for the next arithmetic estimate

Keep the same joint sum and its two open numerical thresholds. Any
successful comparison using interval counts must also control their
**phase-correlated signed error with the actual sieve and allocation
weights**. Improving relative count accuracy by more inverse logarithms,
adding further selected central credit, or pairing opposite cosine signs
does not discharge that requirement. The present audit is not an
impossibility theorem for arithmetic cancellation and proves no new zero
exclusion.
