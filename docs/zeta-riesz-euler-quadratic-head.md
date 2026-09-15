# Quadratic prime heads at every original order

Lean now pays the complete Euler correction multiplied by all actual head
primes through `N²`, at every original factorial order `N`. The earlier
linear-head result required a positive integer stride. Actual prime density
supplies the improvement, without a new analytic premise or coefficient search.

The terminal independent deletion theorem is
[`tendsto_actual_band_sub_quadraticResidual`](../RiemannGaussian/ZetaRieszEulerQuadraticHead.lean).
For every fixed polynomial filter `P`, ordinate `y`, and `0<u<1`, the normalized
difference between the literal arithmetic band and its explicit quadratic-window
residual tends to zero. This theorem has no hypothetical-zero premise.

Open the [quadratic-head theorem chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=euler-quadratic-head-deletion)
for exact statements, hypotheses, source lines and transitive axiom audits.
The default RH explorer still ends at the original whole-carrier critical profile.

## Where the additional arithmetic bound comes from

For every prime subset `S` through `b`, the existing Chebyshev estimate gives,
eventually in `b` and uniformly over `sigma>=1/2`,

```math
\prod_{p\in S}(1+2p^{-\sigma})
\leq \exp\!\left(2\sum_{p\in S}p^{-\sigma}\right)
\leq \exp\!\left(\frac{16\sqrt b}{\log(b+2)}\right).
```

At `b=N²`, this is at most `exp(eps*N)` eventually for **every** positive
`eps`. It bounds all the signed Fourier coefficients of the head together;
their exact signs and subset frequencies remain available upstream. The
full logarithmic frequency cost and original factorial factor have a
degree-five polynomial majorant. At the original center `3/2+i*y`, choose
`R=(u+1)/2`, so `u/R<1`, and then choose `eps>0` with
`(u/R)*exp(eps)<1`. The complete normalized correction has a vanishing allowance
of the form

```math
C(N+1)^5\bigl((u/R)e^{\varepsilon}\bigr)^N\longrightarrow0.
```

Constants may depend on the fixed filter and analytic parameters. The estimate
is uniform over all prime heads through `N²` and all eligible complementary
finite correction selections. It retains every interaction order in the
correction, both physical Fourier phases, the original inverse-length
normalization, every factorial offset and logarithmic mark, and genuine
frequency integrability. No infinite Euler-product identity is needed.

## Exact remaining obstruction

At order `N`, split the actual prime factors of `primorial(2^(32*N))` at
`p<=N²`. Write `S` for the head character, `G` for the complementary finite
Euler quotient, `H` for its complete correction, `A` for all ordinary-prime
compensation and `B` for the entire signed off-band boundary. The retained
identity is

```math
SGH-1-A-B
=\underbrace{(SG-1-A)+S(G-1)(H-1)-B}_{\text{full residual}}
+\underbrace{S(H-1)}_{\text{independently paid correction}}.
```

The leading `SG-1-A`, mixed `S(G-1)(H-1)`, and signed boundary `B` still need
their joint independent real floor. Small primes remain in `S` in these
terms: this is not a support deletion of every smooth integer from the residual.

Under a hypothetical right-half zero, `tendsto_normalizedQuadraticResidual`
preserves the exact negative multiplicity source at every original order.
`rh_of_quadraticResidual_cofinal_floors` proves that a cofinal floor above
`-1` for each full residual would imply Mathlib RH. That arithmetic floor is
an explicit unproved premise. This slice proves neither RH nor a larger
zero-free region.

## Modules and audits

The root library imports `ZetaRieszEulerPrimeHeadDensity` for the uniform
prime-density and filter estimates, and `ZetaRieszEulerQuadraticHead` for
the literal band deletion, preserved source and conditional closure.
The [compiled status](proof-status.json) and
[RH explorer audit](rh-proof-explorer/audit.json) track their dependencies.
Ordinary CI verifies this chain without running the optional exhaustive
numerical certificate.
