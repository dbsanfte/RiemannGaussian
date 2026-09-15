# Cancellation inside the retained signed sum

The Möbius divisor sum has one vanishing Fourier factor for each distinct
prime. Keeping opposite frequencies coupled gives an extra factor at odd
prime count. Lean now transports these cancellations through the actual
three-prime and four-or-more-prime responses, their original factorial
weights, and a genuinely convergent frequency integral.

The terminal estimate is
[`norm_nonlinear_sub_high_frequency_le`](../RiemannGaussian/ZetaRieszSignedFrequency.lean).
It bounds an explicitly identified frequency sector of the two arithmetic
classes. **The finite arithmetic cost, the complementary frequencies and
the tapered wing are not controlled at source scale.** No new zero-free
region, RH proof, or historical novelty is claimed.

## Exact signed structure

For a squarefree integer `n`, write `k = card(n.primeFactors)` and retain

```math
\begin{gathered}
Q_n(\xi)=\prod_{p\mid n}(1-e^{-i\xi\log p}),\qquad
h_n=L-\tfrac12\log n,\\
P_n(L,\xi)=e^{i\xi L}Q_n(\xi)+e^{-i\xi L}Q_n(-\xi),\\
Q_n(\xi)=(2i)^k e^{-i\xi\log n/2}
              \prod_{p\mid n}\sin(\xi\log p/2).
\end{gathered}
```

These are the existing `primeProduct` and `primePair`, now related to the
signed `centeredFactor`. No norm is used in
`primeProduct_eq_centeredFactor` or `primePair_eq_centered`. When `k` is odd,
the centered factors at opposite frequencies have opposite signs.
Consequently `norm_primePair_le_of_odd` proves

```math
|P_n(L,\xi)|\le
2|\xi|^{k+1}|h_n|\prod_{p\mid n}\log p.
```

For exactly three primes, `primePair_three_eq_sine_product` is the exact
four-sine identity

```math
P_n(L,\xi)=16\sin(\xi h_n)
                  \prod_{p\mid n}\sin(\xi\log p/2).
```

The full zeta observation still includes the original complex factorial
filter. With `P = 1`, its real phase is `cos(y log n)`, by
[`re_filterKernel_one`](../RiemannGaussian/ZetaRieszCosineCarrier.lean).
The four sine factors and that cosine therefore remain correlated through
the same prime logarithms and their sum. The new estimate uses cancellation
within each divisor measure and between opposite frequencies; it does not
establish cancellation between different integers or different prime counts.

## Both nonlinear classes

Let `S_3` and `S_4` be the exact filters of `centralUnpairedBand u N` with
three and at least four distinct prime factors. All earlier physical,
cofactor, prime and central masks are preserved. Let

```math
f_N(n)=K_{P,N}(3/2+iy,n),\qquad
L=L_N=\log\left((\lfloor u^{-N}/(N+1)\rfloor+2)^2\right).
```

Sums below retain the existing squarefree, nonunit, nonprime filter.
The independently proved pointwise estimates are

```math
\begin{aligned}
\left|\frac{P_n(L,\xi)}{\xi^2}\right|
 &\le 2|\xi|^2|h_n|\prod_{p\mid n}\log p
 &&(k=3),\\
\left|\frac{P_n(L,\xi)}{\xi^2}\right|
 &\le 2|\xi|^2(\log n)^4
 &&(k\ge4,\ |\xi|\log n\le1).
\end{aligned}
```

The second theorem covers every higher count without a maximum degree.
The actual integral is over positive frequencies and is independently
proved integrable; its use does not rely on assigning a value at the
singular endpoint.

Define the explicit finite costs (`threeFrequencyCost`,
`higherFrequencyCost` and their actual sum `nonlinearFrequencyCost`):

```math
\begin{aligned}
C_{3,N}&=\sum_{n\in S_3}\frac{\log n}{L}|f_N(n)|
       \left|L-\frac{\log n}{2}\right|\prod_{p\mid n}\log p,\\
C_{\ge4,N}&=\sum_{n\in S_4}\frac{\log n}{L}|f_N(n)|(\log n)^4.
\end{aligned}
```

For the literal frequency sum `F_N = nonlinearFrequency P u y N`,
`nonlinearResponse_eq_integral` proves

```math
T_{3,N}+T_{\ge4,N}=\frac1{2\pi}\int_0^\infty F_N(\xi)\,d\xi.
```

`norm_nonlinear_sub_high_frequency_le` gives, for every `u >= 0`, height `y`,
polynomial `P`, order `N` and `delta >= 0` satisfying
`delta * (8N/3) <= 1`,

```math
\left|u^{N+1}\left(T_{3,N}+T_{\ge4,N}
 -\frac1{2\pi}\int_\delta^\infty F_N(\xi)\,d\xi\right)\right|
 \le\frac{u^{N+1}\delta^3}{3\pi}(C_{3,N}+C_{\ge4,N}).
```

The support condition follows from the actual central mask,
`log n <= 8N/3`. `natural_frequency_window` proves the concrete positive
choice `delta_N = 3/(8(N+1))` valid at every `N`, including zero. The
inequalities require no hypothetical zero, simplicity or exposure premise.
Their constants retain the original filter and arithmetic cost. This does
not enlarge the range of the separate three-unpaid source decomposition.

## What the estimate has not paid

The cubic frequency factor cannot be counted independently of the prime
logarithms inside the costs. At the natural frequency scale, logarithms of
size proportional to `N` compensate powers of `1/N`. The checked inequality
therefore does **not** show that its right-hand side tends to zero, is below
the source magnitude, or even stays bounded as `N` increases.

The exact pending pieces are:

1. The cost of the low-frequency sector above, or a stronger signed bound
   for that sector which uses cancellation between integers.
2. The complementary **coupled** integral of `F_N` over `xi > delta_N`.
3. The tapered wing from the existing three-unpaid decomposition.

The last published source theorem remains
[`tendsto_three_unpaid_exact_source`](../RiemannGaussian/ZetaRieszCentralHarmonicCost.lean):
under the original exposed-zero hypotheses and original local source range,
`u^(N+1)(T3+T>=4+taperedWing) -> -m+m^2 c(u)`. Unrestricted multiplicity and
all earlier completion errors remain accounted for. An independent bound
incompatible with that source is still needed.

The repo already has an exact all-degree Euler-product representation in
[`ZetaRieszCompositeProduct`](../RiemannGaussian/ZetaRieszCompositeProduct.lean)
and a factorial-filtered version in
[`ZetaRieszFilteredCompletion`](../RiemannGaussian/ZetaRieszFilteredCompletion.lean).
Using them to seek cancellation between prime counts must retain their
signed completion boundary. Recombination alone is not a new estimate.

The independently checked [global deviation window](zeta-riesz-deviation-window.md)
widens the support analysis across all right-half source radii; it likewise
does not supply the missing signed floor.

## Validation

The module belongs to the ordinary Lean root. Direct warning-as-error
compilation, ordinary-root declaration lint and complete transitive axiom
checks validate the slice. Only the standard logical axioms are permitted.
The optional exhaustive numerical-certificate build is not involved.
The [RH explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/)
provides the generated statements, source lines and proof audits under the
signed-frequency endpoint after publication.
