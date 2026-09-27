# Small-factor compensation cannot remove balanced triples

[`ZetaRieszSmallDescendants`](../RiemannGaussian/ZetaRieszSmallDescendants.lean)
proves a quantitative limit on one possible cancellation mechanism.
Appending small factors to a fixed balanced triple supplies a vanishing
fraction of its weight, even if every appended phase helps. Cancellation
with different large-prime configurations remains open. This is **not** a
lower bound for the whole joint carrier.

The subsequent [all-core extension bound](zeta-riesz-core-extensions.md)
removes the `N^2` ceiling on inserted primes in the slightly sharper
balanced chamber `log(p),log(q),log(r)<=67N/100`. It proves the same
relative vanishing for every extension that remains in the core.

## Exact disappearance of composite descendants

Let `m=p*q*r` be a product of three distinct actual primes. On the chamber

\[
2N\le\log m,\qquad
\log p,\log q,\log r\le 27N/40,\qquad
137N/100\le L\le7N/5,
\]

adjoin a nonunit factor `a`, retaining squarefreeness and
`log a <= N/2048`. All three pair products times `a` are below the Riesz
cutoff, while the product `p*q*r` is above it. The exact eight-term prime
insertion identity gives

\[
\mathcal R_L(ma)=
\begin{cases}
\log a,&a\text{ prime},\\
0,&a\text{ composite}.
\end{cases}
\]

Thus the five-prime descendants with two small factors **vanish** here.
The previous five-prime sign theorem remains valid near the pair
boundaries; it does not supply credit everywhere balanced triples survive.
The cancellation also covers composite small factors with arbitrarily
many prime factors, without estimating their absolute divisor mass.

The smaller-count theorem already supplies `log a <= N/2048` for a
divisor whose prime factors are all at most `N^2`. The existing actual
balanced prime boxes eventually lie in this chamber, uniformly over
their bounded phase translations (`eventually_prime_boxes_in_chamber`).
The actual moving length has the displayed bounds eventually on the
restricted radius interval. No rational-log model is substituted into
these formal statements.

## Quantitative bound for the remaining prime insertions

Write `K_N(m)` for the original complex factorial kernel at `3/2+i*y`.
At `log m >= 2N`, its exact multiplicative transport proves

\[
\|K_N(ma)\|\le a^{-1}\|K_N(m)\|.
\]

There is no density compensation in this inequality. The factor
`(log(ma)/log(m))^N` and the full complex prime feature are used before
taking the bound.

For **any** selected set of descendants satisfying the chamber conditions,
with prime insertions at most `N^2`, `norm_descendants_le` and its geometric
specialization prove

\[
\left\|\sum_{a\in D}
 \mathrm{residualCoefficient}_{N,L}(ma)K_N(ma)\right\|
\le 4\log N(1+2\log N)\,\|K_N(m)\|.
\]

The allocation factor remains literal. All further support predicates can
remain in `D`; no deleted label or phase is supplied. Composite descendants
are removed by the exact zero identity first. The bound on the surviving
prime sum uses only the harmonic inequality for **all integers** up to
`N^2`, so it requires no prime-density approximation or unproved counting
estimate.

The base residual atom `B_N` satisfies
`||B_N|| >= (N/4)||K_N(m)||` once its unassigned fraction is at least half.
`eventually_balanced_unassigned_half` discharges that condition uniformly
using the existing allocation theorem. Therefore the entire appended
correction has at most the relative budget

\[
\epsilon_N=
\frac{16\log N(1+2\log N)}{N}\longrightarrow0.
\]

`dyadic_relative_budget_lt` proves `epsilon_(N_j) < 1/1000` already for
`j>=32` on the unchanged original schedule. **This is a fraction of the
base atom's modulus, not an absolute source-normalized allowance.**

`re_balanced_descendants_upper` gives the signed conclusion. If the base
atom is in its negative phase sector, `Re B_N <= -||B_N||/2`, then, for
any remaining signed complement `W`,

\[
\Re(W+B_N+\text{descendants})
\le \Re W+(\epsilon_N-1/2)\|B_N\|.
\]

The complement is retained verbatim. This shows why appending small
factors cannot itself neutralize those negative atoms. It neither proves
divergence of the whole core nor obstructs a cancellation which changes
the large prime factors. The independent joint `-79/1000-o(1)` floor
remains open.

## Optional numerical diagnostic

The [probe](../scripts/probe_riesz_small_descendants.py) enumerates all
ordinary prime insertions up to `N^2` and uses the full finite allocation,
moving length, factorial ratio and phase. Its base has **model** logarithms
`2N/3,2N/3,2N/3`; these are not asserted to be logarithms of actual distinct
primes. It is not a finite certification of the original dyadic core.

The [recorded output](riesz-small-descendants-probe.json) gives maximum
relative compensating masses of about 2.84%, 1.39% and 0.60% at
`N=640,1536,4096`. The actual signed observations at the tested nonzero
heights are smaller. These floating values motivated the inequality;
the Lean harmonic and kernel bounds prove the asymptotic conclusion.
The probe remains outside routine CI.
