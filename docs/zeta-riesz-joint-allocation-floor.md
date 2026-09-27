# Paying the old allocation inside the joint floor

The current target is the [cofinal joint floor](zeta-riesz-joint-floor.md).
This slice pays one of its existing arithmetic weights on a larger support,
without separating the main sum from its signed complement.

Let `S=coreBand u N K`, retain the original length `L`, intermediate prime
set `A`, and write

\[
b_n=c_L(n)K_N(3/2+iy,n),\qquad
\theta_n=\mathrm{boundedShare}(A,N,n).
\]

Choose any `D` contained in `S` such that every eligible selected prime
dividing a label in `D` obeys `log p <= (293/500) log n`. For example, one may
take the labels whose largest prime has share at most `293/500 = 0.586`. The checked
inequality `Refined.re_core_ge_joint_unallocated` is

\[
\boxed{
\Re\left(u^{N+1}\sum_{n\in S}(1-\theta_n)b_n\right)
\ge
\Re\left(u^{N+1}
 \left[\sum_{n\in D}b_n+\sum_{n\in S\setminus D}(1-\theta_n)b_n\right]\right)
-E_N.}
\]

Both terms on the right stay in **one signed real observation**. The bound
does not require separate floors or decay for either term. No new carrier
definition is introduced.

For every `0 <= u <= U=10001/20000`, every real height and every count cutoff,

\[
E_N=4U(N+1)r^N\,\mathrm{zetaMoebiusLogMajorantMass}(1+1/262144),
\qquad
r=U\frac{262144}{131071}e^{-1/8200}\le e^{-1/100000}<1.
\]

The refined rate is `Refined.allocationRate`; `allocationRate_le_exp`
proves the displayed exponential bound. `Refined.tendsto_allowance`
proves `E_N -> 0`. The earlier, faster bound below `9/16` remains unchanged.
The finite majorant constant is not evaluated, so this does not give a
small numerical allowance at a particular order.

The original unpaid binomial orders lie below `13N/32`. A prime share at
most `293/500` means its cofactor share is at least `207/500`. The rational
tilt `97/100` gives the checked logarithmic inequality

\[
\log\frac{49379}{50000}+\frac{13}{32}\log\frac{100}{97}
\le-\frac1{8200}.
\]

Thus each eligible prime contributes at most `exp(-N/8200)` of allocated
mass. The actual squarefree count is at most `4N` throughout the original
logarithmic window, so all counts cost only the displayed polynomial
factor. There is no count ceiling of 39 or 55, least-prime cutoff,
rectangle selection, phase approximation or zero hypothesis.

Combined with [the dominant-prime bound](zeta-riesz-joint-dominant-floor.md),
the allocation transition is now `0.586..0.601`, instead of
`0.5625..0.605`. `Refined.re_core_ge_joint_reduced` in the dominant-floor
module proves the two comparisons together, retaining the raw part and
transition in one signed real observation and paying both errors.

The main signed sum on the right is still unbounded. In particular, balanced
triples survive in it with their original phases. This theorem removes the
allocation cost on the stated region; it does not prove the required
`-79/1000` cofinal floor or any new zero exclusion.

## Numerical check of the joined target

The optional [probe](../scripts/probe_riesz_joint_core.py) now evaluates the
joined response and its rectangle/complement split on the **same** continuum
samples. It keeps the finite divisor-subset signs, moving length, binomial
allocation and radial phase. It replaces primes by their ordinary density;
it covers only the explicitly recorded rough/physical/core sector, not a
proved transport of the entire inherited arithmetic mask.

The [recorded refinement](riesz-joint-core-probe.json) sums counts 3 through
10, using 8,192 simplex samples per count and two deterministic Sobol seeds.
At `N=4096`, the height-zero joint values are approximately `0.29739` and
`0.29796`, while the rectangle values are `-0.00056` and `0.00006`. At
height 54, the joint real values are approximately `0.00001394` and
`0.00001377`; the rectangle real values are much smaller, about `2e-8`
and `8e-9`. This supports testing the joined target rather than treating
rectangle smallness as a proxy for it. The model's large positive
height-zero mass does not give positivity at a candidate zero height.

No digits are certified: higher counts, continuum transport, share
quadrature and floating error remain unpaid. The radial calculation was
cross-checked against independent oscillatory quadrature, and both signed
splits were checked numerically. Neither check certifies the prime sum or
an eventual sign. The Lean inequalities above do not depend on this probe.
Run the diagnostic outside ordinary CI with

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .lake/riesz-ball-venv/bin/python \
  scripts/probe_riesz_joint_core.py --orders 512 4096 --max-count 10 \
  --power 13 --seeds 117 241 --output /tmp/riesz-joint-core-probe.json
```
