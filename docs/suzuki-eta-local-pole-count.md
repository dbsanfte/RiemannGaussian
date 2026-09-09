# Logarithmic local counts for the actual carrier denominator

The compiled theorem
[`sum_suzukiXiCarrierGenuinePoleWindow_orders_le_log`](../RiemannGaussian/SuzukiCarrierLocalCount.lean)
bounds the total analytic multiplicity of the actual genuine carrier poles
in

```
abs(Re(z)+T) <= 1/4,    0 <= Im(z) <= 1/2
```

by `log(C*(abs(T)+4)^2)/log(18/17)` whenever `abs(T)>=2`.
Here `C=suzukiEtaLocalPoleJensenConstant` is one fixed, proved positive
constant, independent of the height. This is a local count of carrier
poles, not a new exclusion region for zeta zeros or a bound on the
signed residue sum.

## Exact normalization and multiplicities

Retain the original functions and coordinate:

```
s=1/2-i*z,              E(z)=A(z)+i*A'(z),
A(z)=xi(1/2+i*z),       F(s)=1-2*2^(-s),
G(s)=s*(1-s)*Gamma_R(s), R(s)=G'(s)/G(s).
```

The dyadic-cleared arithmetic denominator is

```
J(s)=F(s)*eta'(s)+((1+R(s))*F(s)-F'(s))*eta(s).
```

For `Re(s)>0`, `s!=1`, Lean proves

```
G(s)*J(s)=F(s)^2*(xi(s)+xi'(s)).
```

This identity includes the dyadic exceptions. Where `F(s)!=0`, it also
gives `J(s)=F(s)*D(s)` for the original full eta denominator. The
completion numerator `G` is analytic and nonzero on the stated domain.
The exact finite-order consequence is

```
ord J(s) = 2*[F(s)=0] + ord E(i*(s-1/2)).
```

Every zero of `F` is proved simple. Every order on the right is finite;
no simplicity assumption is imposed on `E`. Thus the cleared divisor
contains exactly two extra orders at a dyadic exception. Genuine
denominator orders remain unchanged.

See [the cleared identity](../RiemannGaussian/SuzukiEtaClearedDenominator.lean)
and [exact analytic orders](../RiemannGaussian/SuzukiEtaClearedPoleOrder.lean).

## Bounds on a moving disk

Take `c_T=3/2+i*T`, initially `T>=2`. On the closed disk
`abs(s-c_T)<=9/8`, the actual eta series, Cauchy's derivative estimate
and the Gauss digamma difference series give

```
abs(J(s)) <= C0*(T+4)^2.
```

The constant `C0>=1` is independent of `T`. This uses a new general
bound `abs(digamma(s))<=K_delta*(1+abs(s))` on each closed half-plane
`Re(s)>=delta>0`. The Cauchy estimate uses radius `1/8` inside the
already proved eta disk of radius `5/4`.

At the center, the existing safe-half-plane carrier bound and eta
lower bound give

```
abs(J(c_T)) >= b0,
b0=staticContourSafeEtaFactorFloor^2/staticContourSafeZetaDirichletMass > 0.
```

There is no exponentially small Gamma factor in this comparison and
no assumed zero-free interior. Jensen on the inner disk of radius
`17/16` therefore bounds its cleared divisor mass by

```
log((C0/b0)*(T+4)^2)/log(18/17).
```

The exact divisor accounting bounds the actual denominator's mass
by the same expression. Complex conjugation preserves the order of
`xi+xi'`, transferring the result to negative `T`. The fixed spectral
strip window above fits inside the rotated inner disk. The terminal
theorem is instantiated for the repository's actual
`suzukiXiCarrierGenuinePoleWindow`, with its original multiplicities.

See [polynomial growth](../RiemannGaussian/SuzukiEtaLocalGrowth.lean),
[Jensen and exact local divisor accounting](../RiemannGaussian/SuzukiEtaLocalPoleCount.lean),
and [both signs and genuine pole windows](../RiemannGaussian/SuzukiCarrierLocalCount.lean).

## Remaining source estimate

The [preceding signed-square theorem](suzuki-eta-signed-square.md)
already controls the adverse part of one eta remainder by a vanishing
quartic allowance. The complete pole contribution, quadratic strip
energy and favorable remainder must still be bounded together at the
source threshold.

The new count controls how much denominator multiplicity occurs in a
local window. It does not control the analytic unit remaining after
factoring those zeros, the size of a residue, or the sign of the
complete weighted pole sum. Higher-order poles and both strip sides
remain part of the problem. A useful next step is to apply local
canonical factorization to this full normalized denominator, retaining
its units and signed quotient identities while estimating the coupled
contribution. A pole count alone supplies no independent source ceiling.

This slice is locally validated only. Commits remain on hold.

The subsequent [analytic-factor theorem](suzuki-eta-canonical-unit.md)
constructs the full denominator's canonical factorization, bounds its
normalized logarithm and logarithmic derivative, and reconstructs the
actual carrier with the entire pole product visible. Its separate
absolute bound still has a large polynomial cost; the signed coupled
source estimate remains open.
