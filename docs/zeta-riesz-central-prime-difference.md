# Exact small-prime cancellation in the central sum

[`exists_central_joint_bounds`](../RiemannGaussian/ZetaRieszCentralPrimeDifference.lean)
now bounds the original whole core using cancellation **inside the remaining
central range**, `1.971N < log n <= 2.029N`. Both cutoffs, all prime counts,
allocation orders, physical and prior masks, and the full product phase remain.
The [proof audit](riesz-central-prime-difference-audit.json) records its scope.
The whole eventual floor and ceiling remain open.

## The arithmetic saving

For a literal label write `n=p*r*b`, where `p` is its unique largest prime
and `r` is the smallest prime of its cofactor. With the existing hinge `h`,
squarefreeness and coprimality give the exact signed identity

```math
D_{rb}(h_{L,p})=D_b(g_{L,p,r}),\qquad
 g_{L,p,r}(d)=h_{L,r}(d)-h_{L-\log p,r}(d).
```

This takes the actual Möbius subtraction before the mean-square estimate.
It does not complete the carrier or approximate its prime distribution.
`atom_pulse` proves equality with the original residual coefficient and
phase, including the allocation factor.

Lean proves, for every finite population endpoint `X`,

```math
Q_X(g_{L,p,r})\le 2\log r,\qquad
\omega(n/p)\,Q_X(g_{L,p,r})\le 2\log(n/p),
```

where `Q_X(f)=sum_{1<=k<X} k(f(k)-f(k+1))^2`.
The energy identity retains the **negative twice-overlap term** between
the two nonnegative cutoff slopes. The count saving is automatic because
`r` is the least cofactor prime. It needs no special share geometry, height
or count ceiling. If `r^2<p`, the new energy cap is strictly below `log p`.
This compares explicit energy caps; it is not a uniform comparison against
the previously optimized cubic cost.

## Both bounds for the original carrier

`exists_whole_difference_bounds` applies the existing unconditional arithmetic
mean to the smaller actual cofactor population `b`. It allows one common
coordinate system across **all** labels, least-prime choices and counts,
so these cross terms can remain inside the squared energies. Every original
label is covered exactly; no interval-cover or arithmetic premise is added.
The resulting explicit cost is `D0`; its arithmetic constant is unevaluated.

Intersecting this enclosure with the existing signed quadratic and cubic
ones gives

```math
\max\{H_2-C_2,H_3-C_3,-D_0\}-Ce^{-N/10^6}
\le u^{N+1}\operatorname{Re}(\mathrm{coreResponse}_N)
\le \min\{H_2+C_2,H_3+C_3,D_0\}+Ce^{-N/10^6}.
```

All central costs use the exact retained support. The already proved outer
error is paid once. Neither bound can worsen. The new raw and previous
projected mean constants are kept explicit separately; no value such as
`E=1` is certified.

## Numerical test, not a certificate

The optional [probe](../scripts/probe_riesz_central_prime_difference.py)
uses actual prime labels and the exact allocation polynomial on test
populations, with earlier nested core deletions omitted. It compares the
raw hinge with its exact least-prime difference on **identical labels**.
Every coordinate direction is retained. At `N=10,u=0.50005,y=54`:

| Least cofactor prime | Labels | Raw cost | Difference cost | Reduction |
|---|---:|---:|---:|---:|
| 2 | 9,282,639 | 0.00260826 | 0.00114136 | 56.2% |
| 3 | 4,752,644 | 0.00187231 | 0.00075361 | 59.7% |
| 5 | 2,418,825 | 0.00133023 | 0.00046056 | 65.4% |

These are floating diagnostics **before the unevaluated `sqrt(E)`**.
They do not include the remaining sectors and are not comparisons against
the already cubic-projected whole cost. The [full output](riesz-central-prime-difference-probe.json)
also records `N=6,8` and exact-form divisor-identity regressions.

```bash
OPENBLAS_NUM_THREADS=4 ../.venv/bin/python \
  scripts/probe_riesz_central_prime_difference.py --max-order 10
```

A second check compares the **same least-prime-2 sector** against the
previous cubic projection, retaining its signed correction. At order ten,
the cubic cost is `0.00140943` with center `-0.00000205915`; the new
cost is `0.00114136` with center zero, about **19.0% smaller before the
arithmetic constants**. This is still a sector diagnostic, not a theorem
comparing total costs or a certified common constant. The small-prime
cancellation therefore improves the numerical test beyond the raw baseline.

The remaining target is an eventual bound for the **combined central
cost and signed corrections**, including rough cofactors whose least prime
is large. The improved finite estimates do not yet overcome the positive
central source exponent `log(2u)`. No `-79/1000` floor, `3/2` ceiling,
new zero exclusion or RH contradiction is asserted.

## A second cofactor prime

For an actual label `n=p*r*s*b`, extracting `s` retains the four signed
cutoffs in `secondPulse`. Lean proves energy at most `4 log r` when
`p>=r*s`. Since the arithmetic population shrinks from `sX` to `X`,
the explicit squared mean allowance contracts by `2/s`, with the same
mean constant and signed weights. The cap comparison is strict for
`s>=3` when the previous cap is positive. This is not a uniform comparison
with every optimized common-coordinate cost.

`exists_second_prime_bounds` and `exists_whole_second_bounds` identify
the new joint estimate with the literal fibre and label-set sums. Counts,
coprimality, allocation, full phase and finite masks remain. No support
complement is silently omitted.

The optional [second-prime probe](../scripts/probe_riesz_second_prime_difference.py)
and [recorded output](riesz-second-prime-difference-probe.json) compare
identical central labels. At order 10 the costs before the unevaluated
`sqrt(E)` change as follows:

| Two least cofactor primes | Labels | One extraction | Two extractions | Reduction |
|---|---:|---:|---:|---:|
| 2, 3 | 2,681,421 | 0.000646817 | 0.000483026 | 25.3% |
| 2, 5 | 1,407,719 | 0.000469199 | 0.000261001 | 44.4% |
| 3, 5 | 1,033,822 | 0.000370867 | 0.000206338 | 44.4% |

These remain finite diagnostics, with earlier nested core deletions
omitted. They are not an asymptotic saving or a certificate. Blindly
combining all small-prime patterns was also tested and made the cubic
budget worse; that unsuccessful construction was not expanded.

The new [combined central-cost bound](zeta-riesz-central-cost-growth.md)
now treats growing orders and all central sectors. Its surviving
`(2u)^N` factor, rather than another selected-sector percentage, is the
next quantitative target.
