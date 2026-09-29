# Exact composite cancellation lowers the signed prime budget

`ZetaRieszCenteredPrimeEnergy` proves a uniformly smaller cost for both
signs of the original retained carrier. It uses the exact constant and
logarithmic divisor moments of squarefree composites before measuring the
signed prime profile. The [audit](riesz-centered-prime-energy-audit.json)
records the compiled endpoints, source hashes, axioms and optional probes.

## The exact saving

For every squarefree composite `n>1`,

```math
\sum_{d\mid n}\mu(d)=0,\qquad
\sum_{d\mid n}\mu(d)\log d=0.
```

Consequently an affine function of `log d` can be added to any divisor
profile without changing its actual arithmetic response. On a population
`S subset (1,X]`, define

```math
h_k=\log(k+1)-\log k,\qquad
Q_X(f)=\sum_{1\le k<X}k(f(k)-f(k+1))^2,
```

```math
H_X=\sum_{1\le k<X}kh_k^2,\qquad
C_X(f)=\sum_{1\le k<X}k(f(k)-f(k+1))h_k.
```

The optimal slope is `a=C_X(f)/H_X`. Lean proves

```math
Q_X^\circ(f)
=\sum_{1\le k<X}k(f(k)-f(k+1)-ah_k)^2
=Q_X(f)-\frac{C_X(f)^2}{H_X}.
```

The centered energy is nonnegative, no larger than `Q_X`, and minimal
among **all** affine-log corrections. The degenerate `H_X=0` case is
included with Lean's zero-division convention; no positive denominator is
silently assumed.

The corrected profile is `f(d)+a log(d)-f(X)-a log(X)` for `d<=X`, and
zero beyond `X`. Its divisor response is exactly the original response,
and its boundary difference at `X` is zero. Thus the existing unconditional
squarefree divisor mean gives one constant `E>0` such that

```math
\sum_{n\in S}\left(\sum_{d\mid n}\mu(d)f(d)\right)^2
\le EXQ_X^\circ(f).
```

This constant is proved to exist but remains numerically unevaluated.

## Transfer to the literal retained sum

Apply this correction to both common cosine and sine prime profiles from
[the moving-interval theorem](zeta-riesz-moving-prime-intervals.md).
Every prime sum remains inside the quadratic energy, so its cross terms
are retained. Let `D_j^circ` be the binary subdivision sum of these two
centered energies. For cofactor-dependent prime intervals the squared
response is bounded by `4(b+1)EX D_j^circ`.

The exact retained factorial coefficients `B(n,j)` are unchanged. Put
`w_j(n)=exp(-log(n)/2)B(n,j)/n`. For the original real carrier `J`, Lean
proves both `-K^circ<=J` and `J<=K^circ`, where

```math
K^\circ=\frac1{LN!}\sum_{j=0}^{N+1}
\sqrt{\left(\sum_{n\in S}w_j(n)^2\right)4(b+1)EXD_j^\circ}.
```

`retainedCenteredCost_le` proves that this **entire cost is no larger**
than `retainedMovingCost` with the same `E`, exact coefficients and cells,
at every valid old physical cutoff `exp(L)<R+1`. This comparison is a
theorem, independently of the numerical probe.

The terminal theorems retain both Riesz hinges, all factorial orders
including zero and one, allocation, full phase and the original selected
prime masks. Disjoint cells and strict largest-prime ownership give an
actual duplicate-free set of integer labels. Finite radial/count families
share one `E` and sum their exact costs. There is no upper prime-count
ceiling, prime-density replacement, zero hypothesis or extra companion
credit. A disjoint cover of the whole core is still required; these
theorems do not fill gaps in a selected interval or assert such a cover.

## Optional numerical diagnostic

Run `../.venv/bin/python scripts/probe_riesz_centered_prime_energy.py`.
The probe uses actual primes and squarefree cofactors, unique ownership,
the moving physical length, the `1.95N..2.03N` core, the nondominant
`.65` mask, exact allocation and full phase. It checks the divisor response
is unchanged by the null correction. It is outside ordinary CI.

At `u=10001/20000`, `y=54`, the source-normalized cost formulas are:

| N | Cofactor cap | Selected labels | Previous cost | Centered cost |
|---|---:|---:|---:|---:|
| 6 | 4,096 | 2,130 | 0.155837 | 0.109178 |
| 8 | 65,536 | 285,908 | 0.165997 | 0.107339 |
| 10 | 1,048,576 | 30,510,285 | 0.235219 | 0.140558 |

These costs are **before the unevaluated `sqrt(E)`** and cover finite
truncated populations. Restricting further to cofactors whose primes all
exceed `N^2` gives centered costs `0.0277724`, `0.0309242`, `0.0412177`.
Neither population is asserted to be the whole surviving carrier. These
are floating diagnostics, not numerical certificates or an evaluation of
the full signed sum at order ten.

The 30–40% saving persists in these tests, but the order-ten cost exceeds
the order-eight cost. This proves neither eventual decay nor an asymptotic
obstruction. Uniformity over arbitrary moving endpoints cannot substitute
for an estimate exploiting the actual radial/prime correlations.

## Remaining target

We still need a disjoint whole-core cover and a sufficiently small total
source-normalized centered cost, or a stronger signed estimate that uses
the remaining correlations. Both whole-carrier thresholds, the
`-79/1000-o(1)` floor and `3/2+o(1)` ceiling, remain open. This slice proves
no new zero exclusion or RH claim; previously retained companion terms
cannot be counted again.
