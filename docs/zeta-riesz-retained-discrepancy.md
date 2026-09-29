# The retained carrier's joint arithmetic discrepancy

`ZetaRieszRetainedDiscrepancy` applies the
[two-cutoff discrepancy estimate](zeta-riesz-discrepancy-energy.md) to the
**original retained carrier**. The exact allocation, every factorial order,
both Riesz hinges and the full product phase remain. Arbitrary finite block
families keep their smooth contributions summed with their signs.

The [audit](riesz-retained-discrepancy-audit.json) records the theorem names,
source hashes, allowed axioms and optional numerical diagnostics.

The subsequent [joined smooth-tail theorem](zeta-riesz-smooth-prime-tail.md)
pays the smooth response on these common blocks. The signed comparison here
remains available; the total source-scaled cost and actual ownership holes
are still open.

## Signed comparison on a literal block

Let `S subset (M,2M]` consist of squarefree cofactors with at least two prime
factors. Let `P` be the complete, possibly externally clipped prime interval
`exp(a)<p<=exp(b)`. Every `p in P` must belong to the original eligible set
`A` and be coprime to every selected cofactor. The interval is common across
the population; no missing primes are silently filled.

The exact retained coefficients satisfy

```math
(1-\theta_{A,N}(pn))(\log(pn))^{N+1}
 =\sum_{j=0}^{N+1}B_{n,j}(\log p)^j,
\qquad
0\le B_{n,j}\le {N+1\choose j}(\log n)^{N+1-j}.
```

They retain all original allocation incidences and are independent of the
marked prime. The signed literal quantity is

```math
J=\Re\sum_{n\in S}\sum_{p\in P}
  \operatorname{residualCoefficient}(A,L,N,pn)
  K_N(3/2+iy,pn).
```

Let `smoothResponse` be the signed density response through the same two
Riesz cutoffs, defined and bounded in the preceding slice. The theorem keeps
the following explicit comparison term:

```math
H=-\frac1{LN!}\sum_{j=0}^{N+1}\sum_{n\in S}
 \frac{e^{-\log n/2}B_{n,j}}n\,
 \operatorname{smoothResponse}
 \left(t\mapsto e^{-t/2}t^j\cos(y(t+\log n))\right)(n).
```

There are proved constants `E>0` and `T>=5000`, both **unevaluated**, such
that, for `a>=T`, `a<=b` and `L>0`,

```math
H-K\le J\le H+K,
```

where

```math
K=\frac{\sqrt E\,e^{-\log M/2}\sqrt b}{LN!}
 \sum_{j=0}^{N+1}{N+1\choose j}
  (\log(2M))^{N+1-j}\varepsilon_j
```

and the actual-prime error price is

```math
\begin{aligned}
W_j&=\min\{e^{-a/2}b^j,\ e^{-j}(2j)^j\},\\
S_j&=|j/a-1/2|+j(b-a)/a^2,\\
\varepsilon_j&=5W_j[2+(S_j+|y|+2)(b-a)]/a^3.
\end{aligned}
```

The endpoint theorem is `exists_literal_retained_error`. The theorem
`exists_literal_family_error` uses the same `E,T` for any finite family:

```math
\sum_iH_i-\sqrt E\sum_i\operatorname{retainedErrorCost}_i
 \le\sum_iJ_i\le
\sum_iH_i+\sqrt E\sum_i\operatorname{retainedErrorCost}_i.
```

There is no maximum factorial order, prime-count ceiling or
family-cardinality multiplier. The signed `H_i` are not replaced by
`sum |H_i|`. The error sum itself still has to be controlled at source scale.

## What is paid

The cofactor-dependent phase is first rotated into cosine and sine
components. Their common squarefree means bound the original phase; no
phase is frozen or separately approximated. The global factorial-amplitude
maximum pays every order, including zero and one. Reciprocal cofactor
weights pay their square sum on the entire shell. Finally the exact
`B_{n,j}` expansion and the already-proved real carrier atom identity attach
these estimates to `residualCoefficient` and `zetaPrimeLogKernel`.

The arithmetic input is the proved Chebyshev/prime discrepancy, not an
assumed density approximation. Every Riesz cutoff crossing is included
before the cofactor mean. No zero, simplicity or exposed-phase hypothesis
enters these arithmetic theorems.

## Remaining work and numerical limits

The **joint signed smooth carrier is not paid**. Neither are arbitrary
cofactor-dependent prime holes, the exact ownership/incidence partition of
the remaining carrier, or the total source-normalized cost. A finite family
inequality does not justify counting an arithmetic label twice. Complete
intervals containing previously paid sectors do not supply additional
credits for those same sectors.

The threshold is not numerically evaluated: `a=5000` is not asserted to be
sufficient. The optional `scripts/probe_riesz_retained_discrepancy.py` uses
actual primes near log-height ten, squarefree cofactor counts two through
four, both eligible-cofactor choices and the full allocation polynomial.
Its 16 finite blocks verify the expansion to roughly `6e-14` relative
floating error and retain both cutoff boundaries in quadrature. They do not
certify the eventual bound or the whole carrier's physical/ownership masks.

The exploratory all-order **binomial-cap** budget, with `sqrt(E)` omitted,
has source-normalized base-ten logarithms about `-9.59, -9.27, -2.53, 29.81`
at `N=16384,65536,262144,1048576`. This exposes the surviving growth in that
positive error budget; it is neither a lower bound on the carrier nor a
proved asymptotic impossibility result. No source decay is inferred.

Both the whole `-79/1000-o(1)` floor and `3/2+o(1)` ceiling remain open.
There is no new zero exclusion or RH proof.
