# Actual smooth terms are now independently bounded

Lean now bounds every original squarefree arithmetic class whose prime
factors are at most `N²`. This controls the actual Riesz sum, including its
divisor weights and full factorial filter. The result combines with the
previous composite-cofactor deletion, so both support restrictions hold
in the remaining carrier. **Its independent joint signed floor remains open.**

Open the [smooth-prime theorem chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=smooth-prime-deletion)
for exact statements, hypotheses, source lines and axiom audits. The terminal
independent deletion is
[`tendsto_actual_band_sub_optimizedRoughResponse`](../RiemannGaussian/ZetaRieszSmoothCofactor.lean).
The default RH explorer continues to show the whole-carrier critical profile.

## Explicit rate for actual arithmetic terms

Let `D` be any squarefree subset of the original band whose prime factors
belong to a head `S` of primes through `N²`. Keep the original signed
coefficient `C_L(n)` and the complete polynomial kernel

```math
K_{P,N,y}(n)=n^{-3/2-iy}
\sum_{j\in\operatorname{supp}P}P_j\frac{(\log n)^{N+j}}{(N+j)!}.
```

Here `C_L(n)=-(log(n)/L)*sum_(d|n) mu(d)*max(0,L-log(d))` on
squarefree composites, and zero otherwise. Its Möbius signs and cutoff
weights remain unchanged in both parts of the exact partition.

For each `0<u<1`, Lean proves eventually in `N`, simultaneously for all
such `D,S`, every polynomial `P`, every ordinate `y`, and every `L>0`,

```math
\left|u^{N+1}\sum_{n\in D}C_L(n)K_{P,N,y}(n)\right|
\leq 32(\log 2)\,u\left(\sum_j|P_j|\right)N(\sqrt u)^N.
```

The threshold is uniform in the class, filter, ordinate and positive length;
its numerical value is not evaluated. The displayed coefficient norm pays
the entire filter. For every fixed filter the allowance tends to zero.
This is a bound on a selected sum, not a percentage of the full carrier or
a numerical zero-location bound.

The proof uses the exact squarefree divisor count and prime-subset factorization:

```math
\#\{d:d\mid n\}=2^{\omega(n)},\qquad
\sum_{n\in D}2^{\omega(n)}n^{-\sigma}
\leq\prod_{p\in S}(1+2p^{-\sigma}).
```

The original coefficient has norm at most `log(n)*2^omega(n)`.
The literal upper band endpoint gives `log(n)<=32*N*log(2)`, and the
factorial envelope with tilt one leaves `sigma=1/2`. Existing Chebyshev
prime density bounds the Euler product by
`exp(16*N/log(N²+2))`, eventually smaller than `exp(eps*N)` for every
`eps>0`. Choosing `eps=-log(u)/2` gives the displayed square-root rate.
The exact signed sum remains available before this downstream estimate.

## Both arithmetic restrictions survive together

The original band is still

```math
\mathcal B_N=\{n:1\leq n\leq2^{32N},\quad N\log(2)/4<\log n\},
\qquad L_N=\log((D_N+2)^2),\quad D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor.
```

First retain the [previous optimized composite-cofactor deletion](zeta-riesz-general-tilt-decay.md).
Intersect its complement with the new rough-prime class. Smooth-class decay
holds for every subband, so it pays the intersection without relying on
cancellation between separately unbounded pieces or counting labels twice.

Every nonzero remaining term is a squarefree composite with a prime factor
greater than `N²`. In addition, every eligible factorization `n=p*a` with
`p` prime and `a` composite has `a>A_N`, where `A_N` is the previously paid
optimized cofactor threshold. The scalar contact `u=exp(-1/2)` retains the
proved polynomial fallback; elsewhere that threshold eventually exceeds
every fixed power of `N`. The common physical length, coefficient, logarithmic
phase and every factorial offset remain unchanged.

| Remaining terms | Proven restriction | Still needed |
| --- | --- | --- |
| Semiprimes | At least one prime exceeds `N²` | Their signed contribution coupled with the other surviving terms |
| Squarefree terms with at least three prime factors | A prime exceeds `N²`; every prime-deletion composite cofactor exceeds `A_N` | Their joint signed lower bound with semiprimes |

The normalized difference between the original band and this combined
remainder tends to zero independently for every `1/2<u<1`.
`tendsto_quadraticResidual_sub_optimizedRoughResponse` also proves that the
signed Euler-window residual differs from this actual sum by a vanishing
normalized error. This preserves access to both representations. It does
not assert that the Euler factors separately have only large-prime support.

## Exact source and open closure

Under a hypothetical right-half zero, with its original pole-jet filter,
ordinate and scale `u=3/2-Re(rho)`, the combined remainder still tends to
`-multiplicity(rho)` at every original order. The checked theorem
`rh_of_optimizedRoughResponse_cofinal_floors` says that a cofinal real floor
`>=-c`, for some `c<1` for each complete remaining sum, would prove Mathlib RH.
That independent arithmetic floor is an explicit unproved premise.

No new zero-free region or historical novelty is claimed. The three ordinary
modules are `ZetaRieszSmoothHead`, `ZetaRieszSmoothDeletion` and
`ZetaRieszSmoothCofactor`. Their declarations and dependencies appear in the
[compiled status](proof-status.json) and [RH explorer audit](rh-proof-explorer/audit.json).
Ordinary CI checks the chain without running the optional exhaustive certificate.
