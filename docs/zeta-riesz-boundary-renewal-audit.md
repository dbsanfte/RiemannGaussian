# Boundary renewal on the literal Riesz pair form

23 September 2026. **No quantitative improvement to the open Type-II
estimate has been proved by this test.** The boundary identities and the
finite renewal compile. The checked obstructions rule out two automatic
transfers to an unweighted scalar recurrence; they do not rule out a new
weighted cancellation argument. This is not a successful endgame pass.

The original `LocalizedTypeIIBound`, its `1/1000` saving and its conditional
eventual `-3/40` floor are unchanged. See the
[exact target and earlier applicability audit](zeta-riesz-typeii-go-no-go.md).
No new zero exclusion follows.

## The threshold and the evaluated boundary

Write `n=p*q*a`, `t=log(n)`, `z=L-log(p)-log(q)` and `v=-z/t`.
The user-specified large primes are those with

```math
 \log p\ge t-L.
```

This is distinct from the repository's `p>N^2` smooth/rough threshold.
`ReflectedOuterPair L n (p,q)` requires an original ordered prime pair and
that the filtered set of large prime factors is exactly `{p,q}`. For
squarefree `n` with at least three primes, `reflectedOuterPair_data`
derives coprime nonunit cofactor saturation and the strict cutoff on its
prime factors. Hence the unsaturated correction vanishes on this sector.
It is retained elsewhere in the literal `pairForm`.

The following statements are checked in
[`ZetaRieszPairBoundary`](../RiemannGaussian/ZetaRieszPairBoundary.lean):

```math
 \Delta_{L,p,q}(a)=
 \begin{cases}
   \Lambda(a),&v\ge0,\\
   -\mathcal R_{-vt}(a),&v<0.
 \end{cases}
```

For `v<=0`, a prime cofactor is impossible on this exact support.
For `v>=0`, squarefreeness means that only a prime cofactor can contribute.
At `v=0` both expressions vanish. In the innermost layer,

```math
 0\le z=-vt\le\log\minFac(a)
 \quad\Longrightarrow\quad
 \mathcal R_z(a)=z,\qquad \Delta_{L,p,q}(a)=vt.
```

The last formula has no factor exponential in the prime count. However,
it evaluates an individual coefficient, not the difference between the
weighted masses of different integers. It does not prove that every
composite contribution outside this layer has the same sign.

## Exact finite renewal, without dropping any weight

[`ZetaRieszLeastPrimeRenewal`](../RiemannGaussian/ZetaRieszLeastPrimeRenewal.lean)
sets `r=minFac(a)` and proves

```math
 \mathcal R_z(a)=\mathcal R_z(a/r)
                  -\mathcal R_{z-\log r}(a/r).
```

The child is squarefree, coprime to `r` and strictly smaller. The recursive
`renewalHinge` terminates and equals the original finite divisor response.
`pairForm_eq_minFac_renewal` inserts the first step into the actual double
sum, with its original support, allocation `1-theta_N(n)`, factor `t/L`,
incidence denominator `omega(n)(omega(n)-1)`, factorial kernel and phase.
The cofactor changes inside the response; the outside weight remains at
the original full integer `n`. No completed sum or source identity is used.

In the inner layer, `inner_layer_renewal` proves something limiting:
the shifted branch is exactly zero and the unshifted child still equals
`z`. Thus this part of the finite tree has no within-label cancellation.
Any cancellation of these coefficients must involve other labels with
their actual weighted frequencies.

## Why a classical scalar renewal is not yet an estimate

[`ZetaRieszRenewalWeightAudit`](../RiemannGaussian/ZetaRieszRenewalWeightAudit.lean)
checks two concrete transfer failures.

1. Deleting a prime at least three changes `floor(log n)` and leaves the
   original unit log cell. The child's mask cannot be copied from the
   parent. This does not say that its contribution is negligible.
2. For `K_N(s,m)=(log m)^N m^(-s)/N!`, exact transport is

   ```math
   K_N(s,rm)=\left(\frac{\log(rm)}{\log m}\right)^N r^{-s}K_N(s,m).
   ```

   The phase and logarithmic ratio remain after the original cell
   normalization. With `s=3/2+iy`, the density-adjusted amplitude is

   ```math
   m\log m\,|K_N(s,m)|
      =\frac{(\log m)^{N+1}e^{-\log(m)/2}}{N!}.
   ```

   It increases up to `log m=2(N+1)`. In particular, for `r>=1`, `m>1`
   and `log(rm)<=2(N+1)`, the proved inequality is

   ```math
   \log m\,|K_N(s,m)|
      \le r\log(rm)\,|K_N(s,rm)|.
   ```

   `no_strict_density_contraction` excludes replacing the right side by
   a fixed factor below one times the left side. This is an audit of
   this kernel alone; it does not take absolute values inside the signed
   carrier or assert that arithmetic correlations cannot cancel.

The allocation and prime-count masks also remain in the exact theorem.
No source-scale bound has been proved for removing them, for the sectors
outside exactly two reflected-large primes, or for the unsaturated pair
correction. Consequently an estimate solely for the scalar hinge cannot
instantiate the original conditional floor.

## Literature check and decision

Friedlander–Iwaniec's *Asymptotic sieve for primes* assumes an independent
signed bilinear condition (B) in addition to the distribution condition
(R). Its sieve identities do not establish that condition for a new
sequence. We have not verified its density model or bilinear hypotheses
for this order-dependent masked complex form.
[Theorem 1 and conditions (R), (B)](https://arxiv.org/pdf/math/9811186).

Ford's *On Bombieri's asymptotic sieve* constructs sequences satisfying
strong distribution conditions whose generalized prime asymptotics still
fail (Theorem 1). This is evidence against inferring the missing signed
estimate merely from sieve distribution and algebraic identities. It is
not a counterexample for our particular weights.
[Primary paper](https://www.ford126.web.illinois.edu/wwwpapers/asymsieve.pdf).

The precise verdict is **no-go for an automatic unweighted renewal
transfer with current inputs; unresolved for the full weighted signed
renewal**. Neither a fixed power-saving remainder nor the sufficient
one-sided floor has been established. The new theorems are infrastructure
and applicability checks, not an improvement of the quantitative frontier.

The next useful result would have to estimate the signed error of a
prime/cofactor model with the transported weight and original masks,
uniformly over the existing cofinal orders and cells. A continuum delay
equation without that error estimate would leave the same gap. Do not
expand the route merely by formalizing such an equation.
