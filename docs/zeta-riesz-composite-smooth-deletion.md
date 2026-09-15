# Complete composite-smooth classes are independently bounded

For `1/2<u<exp(-1/2)`, Lean now pays every actual term `n=p*a` where
`p>N²` is prime and `a` is squarefree, composite and supported on primes
through `N²`. There is no separate size cap on `a` and no physical-prime
cutoff on this complete class. The result holds for every order-dependent
subband, so the earlier arithmetic restrictions remain in force.
**The full remaining signed floor is still open.**

Open the [composite-smooth theorem chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=composite-smooth-deletion)
for exact statements, hypotheses, source lines and axiom audits. Its
independent terminal deletion is
[`tendsto_actual_band_sub_compositeResidual`](../RiemannGaussian/ZetaRieszCompositeDeletion.lean).
The default RH explorer continues to show the whole-carrier critical profile.

## Keeping the product restriction improves the bound

The original band and physical cutoff remain

```math
\mathcal B_N=\{n:1\leq n\leq2^{32N},\quad N\log(2)/4<\log n\},
\quad D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,
\quad X_N=(D_N+2)^2,\quad L_N=\log X_N.
```

Keep the original signed coefficient `C_L(n)` and full factorial kernel
`K_(P,N,y)(n)` as defined in the
[physical-prefix proof](zeta-riesz-physical-prime-prefix.md).
Writing `alpha=q-1/2>0`, the coefficient/kernel allowance has cofactor
weight `2^omega(a)*a^(alpha-1)`. The actual product restriction bounds
the prime prefix by `p<=2^(32*N)/a`. Its real-power estimate contributes
`a^(-alpha)`, leaving the harmonic cofactor weight **`2^omega(a)/a`**.

For cofactors `a>=X_N`, Lean then proves

```math
\sum_a\frac{2^{\omega(a)}}a
\leq X_N^{-1/2}\prod_{p\leq N^2}(1+2p^{-1/2}),
\qquad X_N^{-1/2}\leq(N+1)u^N.
```

The product is over primes. The sum may be any selected squarefree class
supported on that head; its full support and mask are retained. No maximum
cofactor size enters this allowance.

Set

```math
F(P,q)=\sum_j|P_j|q^{-j},\qquad
H_N=\prod_{p\leq N^2}(1+2p^{-1/2}),\qquad
r_2(u,q)=\frac{u^2\exp(32(q-1/2)\log2)}q.
```

The literal large-cofactor response has the finite bound

```math
\left|u^{N+1}\sum_{n=pa}C_{L_N}(n)K_{P,N,y}(n)\right|
\leq64(\log2)uF(P,q)\left(1+\frac1{q-1/2}\right)
N(N+1)H_Nr_2(u,q)^N.
```

The sum is restricted to the original band and chosen mask, with the
selected large smooth cofactors and actual prime insertions.
As `q` approaches `1/2` from above, the rate approaches `2*u²`.
For every `0<u` with `2*u²<1`, Lean therefore chooses a fixed admissible
tilt with strict saving. The complete head has the proved Chebyshev cost
`H_N<=exp(eps*N)` eventually for every positive `eps`, so the displayed
allowance tends to zero. Its constants depend on the chosen tilt and filter;
no numerical starting order is evaluated. Unique prime insertion proves
decay for the actual integer class, without counting any label twice.

## The rest of the composite class vanishes exactly

If `a` is composite and `a<=X_N<=p`, the original coefficient is exactly
zero: its full cofactor Riesz profile has saturated, and the shifted profile
has nonpositive length. This retains the common physical cutoff; it does
not replace that cutoff by a different one for each integer.

The [previous prefix bound](zeta-riesz-physical-prime-prefix.md) pays
`p<=X_N` for every smooth cofactor size on `1/2<u<exp(-1/2)`.
Above that prime cutoff, the exact identity pays smaller composite
cofactors and the new bound pays larger ones. Lean also proves that the
prefix interval satisfies `2*u²<1`, discharging every scalar condition in
this complete-class decay theorem.

## Exactly what remains

The complete deletion is made inside the previous remainder. On the proved
scale interval, `surviving_support_dichotomy` classifies every nonzero
remaining term:

| Remaining class | Proved restriction | Still needed |
| --- | --- | --- |
| One small and one large prime | `n=a*p`, with prime `a<=N²` and prime `p>X_N` | Its signed contribution coupled with the other remaining terms |
| At least two large primes | Two distinct prime factors exceed `N²`; earlier composite-cofactor thresholds remain | Their joint signed contribution, including large-prime semiprimes |

The coefficients, phases, factorial shifts and physical length remain
unchanged in the exact partition. This classification is not a percentage
of the full carrier or a numerical zero-location bound.

For `exp(-1/2)<=u<1`, an adaptive fallback retains the previous remainder.
The complete deletion error independently vanishes for every `1/2<u<1`.
Under a hypothetical right-half zero, with the original pole-jet filter
and scale `u=3/2-Re(rho)`, the adaptive carrier still tends exactly to
`-multiplicity(rho)` at every order. An independent vanishing-error theorem
also connects it to the signed quadratic Euler-window residual.

The displayed RH implication still assumes a cofinal real floor `>=-c`,
with `c<1`, for each **full** remaining carrier. That arithmetic floor and
RH remain open. No new zero-free width or historical novelty is claimed.
The four ordinary modules appear in the [family index](theorem-families/arithmetic.md),
[compiled status](proof-status.json) and [RH explorer audit](rh-proof-explorer/audit.json).
Ordinary CI does not run the optional exhaustive numerical certificate.
