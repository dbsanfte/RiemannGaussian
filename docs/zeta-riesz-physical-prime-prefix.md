# The physical prime prefix is independently bounded

Lean now pays every original term `n=p*a` with one prime
`N²<p<=(D_N+2)²` and a squarefree cofactor whose prime factors are all at
most `N²`, for `1/2<u<exp(-1/2)`. There is no separate size cap on that
cofactor. The bound holds for every order-dependent subband, so it removes
these terms inside the previous remainder while preserving its other
arithmetic restrictions. **The full remaining signed floor is still open.**

Open the [physical-prime-prefix theorem chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=physical-prime-prefix-deletion)
for exact statements, hypotheses, source lines and axiom audits. The
independent deletion is
[`tendsto_actual_band_sub_prefixResidual`](../RiemannGaussian/ZetaRieszPhysicalPrefixDeletion.lean).
The default RH explorer still shows the whole-carrier critical profile.

## Actual primes, cofactors and the full filter

Keep the original band, cutoff and kernel:

```math
\mathcal B_N=\{n:1\leq n\leq2^{32N},\quad N\log(2)/4<\log n\},
\qquad D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,
\qquad X_N=(D_N+2)^2,\quad L_N=\log X_N,
```

```math
K_{P,N,y}(n)=n^{-3/2-iy}
\sum_{j\in\operatorname{supp}P}P_j\frac{(\log n)^{N+j}}{(N+j)!}.
```

The signed coefficient remains
`C_L(n)=-(log(n)/L)*sum_(d|n) mu(d)*max(0,L-log(d))` on squarefree
composites, and zero otherwise. Its cutoff, Möbius signs, logarithmic phase
and every factorial shift are unchanged.

Let `A_N` be all squarefree integers supported on primes through `N²`
(the divisors of the corresponding primorial), and let `Q_N` be the actual
primes in `N²<p<=X_N`. Retain any mask `keep_N(n)` on the original band.
Since `p` exceeds every cofactor prime, it is uniquely recoverable from
`n=p*a`. Lean proves that the pair sum counts each actual integer once.

## Explicit allowance and its proved scale interval

For any tilt `1/2<q<=1`, define

```math
H_N(q)=\prod_{p\leq N^2}\left(1+2p^{-(3/2-q)}\right),
\qquad r(u,q)=\frac{\exp((2-2q)\log u)}q,
```

```math
T(P,u,q)=u\left(\sum_j |P_j|q^{-j}\right)
\left(1+\frac1{q-1/2}\right)3^{2(q-1/2)}.
```

Products are over primes. The exact finite response satisfies

```math
\left|u^{N+1}\sum_{\substack{n\in\mathcal B_N,\ \mathrm{keep}_N(n)\\
n=pa,\ a\in A_N,\ p\in Q_N}}C_{L_N}(n)K_{P,N,y}(n)\right|
\leq64(\log2)T(P,u,q)\,N\,H_N(q)\,r(u,q)^N.
```

Prime insertion costs at most one extra divisor-choice factor.
The complete cofactor mass is an Euler product, and the prime prefix has
the proved real-power allowance. Chebyshev density gives
`H_N(q)<=exp(eps*N)` eventually for every `eps>0` in the stated tilt range.
Thus any strict `r(u,q)<1` pays the whole displayed class for every fixed
filter and ordinate, uniformly over all masks.

For every `1/2<u<exp(-1/2)`, Lean discharges these scalar conditions using
`q=1/(-2*log(u))`. This proves decay at every original order, without a
hypothetical-zero assumption. No numerical starting order is evaluated.
The theorem does not extend this component estimate to other source scales.

## What the surviving terms must contain

The mask is chosen to be membership in the
[previous joint cofactor/rough-prime remainder](zeta-riesz-smooth-prime-deletion.md).
Its exact signed partition and the new independent deletion preserve all
previous support restrictions. On the proved scale interval:

| Remaining class | Proved restriction | Still needed |
| --- | --- | --- |
| One prime above `N²`, with an `N²`-smooth cofactor | That prime must exceed the physical cutoff `X_N` | Control of this remaining contribution together with the other classes |
| At least two primes above `N²` | Every eligible composite prime-deletion cofactor still exceeds the previously paid threshold | Their joint signed contribution, including semiprimes |

`surviving_single_prime_above_physical_cutoff` proves the first restriction.
It is a statement about actual arithmetic support, not a bound on zero
height or a percentage of the carrier.

For `exp(-1/2)<=u<1`, the adaptive definition retains the previously proved
remainder. Consequently `tendsto_actual_band_sub_adaptivePrefix` has an
independently vanishing complete deletion error for every `1/2<u<1`.
Under a hypothetical right-half zero, with the original scale
`u=3/2-Re(rho)` and pole-jet filter, `tendsto_normalizedAdaptivePrefix`
preserves the exact limit `-multiplicity(rho)` at every order.

The compiled implication `rh_of_adaptivePrefix_cofinal_floors` would prove
Mathlib RH from a cofinal real floor `>=-c`, with `c<1`, for each full
remaining carrier. **That independent floor is an unproved premise.**
No new zero-free width or historical novelty is claimed.

The three ordinary modules are `ZetaRieszSmoothPrimeProduct`,
`ZetaRieszSmoothPrimePrefix` and `ZetaRieszPhysicalPrefixDeletion`. Their
dependencies appear in the [compiled status](proof-status.json) and
[RH explorer audit](rh-proof-explorer/audit.json). Ordinary CI does not
run the optional exhaustive numerical certificate.
