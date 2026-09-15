# Prime-count and antichain bounds for the original Riesz carrier

Two independent arithmetic bounds now strengthen the signed-carrier route.
The complete contribution above a growing prime-count threshold decays at
every fixed source radius below one. A separate Sperner bound improves the
literal Riesz coefficient for every squarefree composite, including the
lower prime counts that remain. Neither result proves a zero-free region.

## Cancellation inside each coefficient

For a squarefree integer `n` with `k>=2` prime factors and any `L>0`,
[`norm_coefficient_le_middle_layer`](../RiemannGaussian/ZetaRieszSperner.lean)
proves

```math
|c_L(n)|\le \frac{(\log n)^2}{kL}
  \binom{k-2}{\lfloor(k-2)/2\rfloor}.
```

The proof selects the two smallest primes `p,q`, with `n=pqm`. Their
four divisor fibres cancel exactly before taking an absolute value. The
remaining Riesz coefficient is an integral over an interval of length
`log p` of signed Mobius sums in windows of width `log q`. Each prime of
`m` is at least `q`. Two different comparable prime subsets therefore
cannot both lie in the same strict window: adding a prime crosses its
entire width. The surviving subsets form an antichain.

Mathlib's Sperner theorem bounds this antichain by the middle layer of the
Boolean lattice on the `k-2` cofactor primes. Squarefreeness makes the
encoding of divisors by prime subsets injective. The smallest prime
logarithm is at most `log(n)/k`, completing the bound. All prime-selection,
support, integrability and positive-length conditions are discharged for
the actual coefficient. The original signed window integral remains
available alongside the estimate.

`norm_original_band_le_middle_layers` carries the allowance through the
complete original finite band, retaining every polynomial coefficient and
factorial shift in the original filter. It does not prove that the sum of
these allowances tends to zero.

On the actual central band, where the previously proved support theorem
gives `log(n)<2L`, Lean further proves

```math
|c_L(n)|\le \log n\,
 \frac{2}{k}\binom{k-2}{\lfloor(k-2)/2\rfloor}
 \le \frac{2^k\log n}{2k}.
```

This removes at least a factor `2k` from the coarse Boolean divisor-count
allowance used by the complete mass estimate. Retain the sharper binomial
expression and the existing specific three-prime profile bounds as well;
the new general estimate is not asserted to improve every previous bound
on every individual integer. This is a bound after cancellation within
one integer, not a proof of cancellation between different integers.
Sperner's theorem and the average-logarithm step are standard mathematics;
no historical novelty claim is made.

## Complete count deletion throughout the right half-strip

Write

```math
K_j=2^{j+3},\qquad M_j=(j+4)K_j.
```

The new moment sequence tends to infinity. For every fixed `0<A<2`, Lean
proves `A^(M_j)<=K_j^(K_j)` eventually. The complete Euler-product cost
`exp(C K_j)` is subexponential in `M_j`: every fixed geometric slack
`s^(M_j)`, `s>1`, eventually absorbs it.

The [existing full count-mass bound](zeta-riesz-whole-prime-count-decay.md)
therefore gives, for arbitrary moving squarefree selections `D_j` from the
original band with at least `K_j` prime factors, moving heights, positive
lengths, and `0<=u_j<=U<1`,

```math
\left|u_j^{M_j+1}\sum_{n\in D_j}
 c_{L_j}(n)\,K_{P,M_j}(3/2+iy_j,n)\right|\longrightarrow0.
```

The fixed polynomial filter is arbitrary. Choose `A=1+U` and
`U/A<q<1/2`. The complete bound retains

```math
C(P,U,q)M_j\left(\frac{U}{qA}\right)^{M_j}
 \exp\bigl(2K_j\mathcal M(3/2-q)\bigr),
```

with the genuinely summable integer mass `mathcal M` and every divisor
choice included. The geometric rate is strictly below one; the final
Euler exponential is absorbed with room to spare. No zero is assumed in
this decay theorem. All frequencies of the selected integers are paid.
The starting order is unevaluated.

The earlier schedule was `N_j=8(j+4)K_j`. Shortening the moment schedule
exchanges the size of the deleted class for the wider radius range. This
is not a claim that the earlier, larger class now decays on the wider
range. No fixed small prime-count class or percentage of the carrier is
asserted negligible.

## The original source remains exact

[`tendsto_few_optimized_source`](../RiemannGaussian/ZetaRieszPrimeCountRightHalf.lean)
combines the count deletion with the already paid optimized cofactor
class, including its exceptional scalar contact. For every hypothetical
zero `rho` with `Re(rho)>1/2`, set `u=3/2-Re(rho)` and use its original
polynomial pole-jet filter. The remaining band consists exactly of the
old cofactor complement restricted to fewer than `K_j` prime factors.
Its unchanged signed response satisfies

```math
u^{M_j+1}\sum_{n\in D^{\rm remaining}_j}
 c_{L_j}(n)\,K_{P,M_j}(3/2+i\operatorname{Im}\rho,n)
 \longrightarrow -m_\rho.
```

This holds throughout `1/2<u<1`, without a zero-exposure or simplicity
assumption. The full analytic multiplicity is retained. Only the
intersection with the earlier cofactor complement is deleted, so no
overlap is counted twice. This broader source identity is distinct from
the narrower central-integral-plus-wing identity and its quadratic paid
cost. The wing has not independently vanished.

The remaining task is an independent bound for this lower-count signed
sum. The antichain allowance strengthens its atoms; cancellation across
integers, cutoff boundaries and full factorial observations remains to
be controlled. There is no new zero-free theorem, numerical zero bound
or RH conclusion from this slice.

## Validation and navigation

Both modules are imported by the ordinary root. The full slice contains
38 declarations. Strict compilation, ordinary-root lint and complete
transitive axiom audits permit only `propext`, `Classical.choice` and
`Quot.sound`. Ordinary validation does not run the optional exhaustive
numerical certificate.

The [supporting theorem explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=prime-count-sperner)
links compiled statements, exact source lines and audits after publication.
The default RH, proved zero-free and numerical-certificate endpoints remain
unchanged.
