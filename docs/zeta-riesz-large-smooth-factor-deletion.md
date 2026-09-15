# Large smooth factors are bounded for every rough prime count

Lean now pays every original squarefree term whose complete `N²`-smooth
factor reaches the physical cutoff, allowing **any number of primes** in
its rough factor. The independent decay holds for `0<u` and `2*u²<1`,
and combines with every earlier deletion on the corresponding right-half
source interval. **The full remaining signed floor is still open.**

Open the [large-smooth-factor theorem chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=large-smooth-factor-deletion)
for exact statements, hypotheses, source lines and axiom audits. Its terminal
independent deletion is
[`tendsto_actual_band_sub_largeSmoothResidual`](../RiemannGaussian/ZetaRieszLargeSmoothDeletion.lean).
The default RH explorer continues to show the whole-carrier critical profile.

## The actual class and its complete divisor cost

Keep the original band, physical cutoff and length:

```math
\mathcal B_N=\{n:1\leq n\leq2^{32N},\quad N\log(2)/4<\log n\},
\quad D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,
\quad X_N=(D_N+2)^2,\quad L_N=\log X_N.
```

Write `n=b*a`, where `a` contains all prime factors through `N²` and
every prime factor of `b` exceeds `N²`. Lean proves existence of this
factorization for every squarefree integer, using
`a=gcd(n,primorial(N²))`, and proves unique recovery of both factors.
The actual integer sum therefore counts each label once. Every
order-dependent subband mask remains available.

The new paid class has `a>=X_N`. There is no separate upper size cap on
`a` or fixed prime count for `b`. The signed coefficient `C_L(n)` and
complete factorial kernel `K_(P,N,y)(n)` are unchanged; their definitions
are given in the [physical-prefix proof](zeta-riesz-physical-prime-prefix.md).

The exact divisor hyperbola identity holds for every real weight `f`:

```math
\sum_{n\leq X}d(n)f(n)=\sum_{a\leq X}\sum_{b\leq X/a}f(ab).
```

Indices are positive integers and `d(n)` counts all divisors. This gives,
for every `alpha>0` and any squarefree family of integers through `X`,

```math
\sum_b 2^{\omega(b)}b^{\alpha-1}
\leq\left(1+\frac1\alpha\right)X^\alpha(1+\log X).
```

The full rough divisor mass adds one logarithm to the earlier prime-prefix
estimate. Keeping the actual product restriction `b*a<=2^(32*N)` still
cancels the cofactor tilt power, leaving the harmonic smooth-factor mass
`2^omega(a)/a`. No restriction on the rough prime count is introduced.

## The literal full-filter allowance decays

For a fixed tilt `q>1/2`, set

```math
F(P,q)=\sum_j|P_j|q^{-j},\quad
H_N=\prod_{p\leq N^2}(1+2p^{-1/2}),\quad
r_2(u,q)=\frac{u^2\exp(32(q-1/2)\log2)}q.
```

The product is over primes. For the actual selected class, the finite
normalized response is bounded by

```math
32(\log2)uF(P,q)\left(1+\frac1{q-1/2}\right)
N(N+1)(1+32N\log2)H_Nr_2(u,q)^N.
```

The physical inverse-square-root saving remains
`X_N^(-1/2)<=(N+1)*u^N`, including its integer floor at every order.
The extra logarithm costs only a cubic polynomial in `N`. Chebyshev
density bounds the complete head by `exp(eps*N)` eventually for every
positive `eps`. Since `r_2(u,q)` tends to `2*u²` as `q` approaches
`1/2` from above, every `0<u` with `2*u²<1` admits a fixed strict saving.
Thus the whole allowance tends to zero for every fixed filter and ordinate,
uniformly over the selected masks and factor families. The filter cost is
displayed; no numerical starting order is evaluated.

## What this adds to the remaining arithmetic support

The deletion is taken inside the
[previous adaptive remainder](zeta-riesz-composite-smooth-deletion.md).
On `1/2<u` and `2*u²<1`, every nonzero surviving integer has its
**complete smooth factor strictly below `X_N`**. The checked theorem
`surviving_support_with_small_smooth_factor` supplies the factorization
itself, so this conclusion has no unproved existence premise.

| Retained information | Remaining obligation |
| --- | --- |
| All previous prime and composite-cofactor restrictions | Control their joint signed sum |
| Complete `N²`-smooth factor `a<X_N` on the new interval | Control the retained smaller smooth factors and their rough-factor correlations |
| Any number of actual rough primes, with their original phases and divisor signs | Obtain a source-beating signed floor for the full remainder |

The earlier deletion of every one-large-prime composite-smooth class
still has its own interval `1/2<u<exp(-1/2)`. The new result does not
extend that earlier assertion outside its proved interval. It adds a
different support restriction on the larger interval `2*u²<1`.

Outside that interval, the adaptive definition retains the previous
remainder. Its complete deletion error independently vanishes for all
`1/2<u<1`. Under a hypothetical right-half zero, the original scale
`u=3/2-Re(rho)` and pole-jet filter still give the exact limit
`-multiplicity(rho)`. An independent vanishing-error theorem also retains
the connection to the signed quadratic Euler-window residual.

The compiled RH implication assumes a cofinal real floor `>=-c`, with
`c<1`, for each **full** adaptive remainder. That arithmetic floor and RH
remain open. No new zero-free width, numerical zero bound or historical
novelty is claimed. The four ordinary modules appear in the
[family index](theorem-families/arithmetic.md), [compiled status](proof-status.json)
and [RH explorer audit](rh-proof-explorer/audit.json). Ordinary CI does not
run the optional exhaustive numerical certificate.
