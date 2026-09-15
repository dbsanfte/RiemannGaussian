# Signed window energy for the complete original carrier

The original finite Riesz carrier now has one exact complex window lift
across **all** prime-pair families. Its squared norm is bounded by an
explicit signed Gram form. Separately, the middle-layer coefficient bound
has an explicit square-root improvement, and prime ordering deletes the
unit-divisor window from every actual central atom with at least four
prime factors. These results do not prove a zero-free region.

## The whole sum, before taking norms

For every nonzero original summand, Lean selects the two smallest primes
`p_n,q_n` and the squarefree cofactor `m_n`, with `n=p_n q_n m_n`.
It proves and retains coprimality, both prime-ordering conditions and the
exact cofactor prime count. Let `A_n` be the existing `bandAmplitude`,
including the actual support, `-log(n)/L` and the complete complex
factorial filter. For every labelled divisor `i=(n,d)` with `d|m_n`, set

```math
G_i=(\log p_n)A_n\mu(d),\qquad
\ell_i=\frac{L-\log d-\log q_n}{\log p_n},\qquad
r_i=\frac{L-\log d}{\log p_n}.
```

Each prime pair is rescaled to the same unit interval. The proof checks
this rescaling by exact interval lengths, including empty intervals and
strict edges. Define

```math
F(v)=\sum_i G_i\mathbf1_{(\ell_i,r_i)}(v),\qquad
K_{ij}=\max\{0,\min(1,r_i,r_j)-\max(0,\ell_i,\ell_j)\}.
```

The terminal
[`exists_original_band_primeWindowGram`](../RiemannGaussian/ZetaRieszWholeWindow.lean)
proves, with every support and prime-selection premise discharged,

```math
B=\int_0^1F(v)\,dv,\qquad
|B|^2\le\Gamma
  =\operatorname{Re}\sum_{i,j}G_i\overline{G_j}K_{ij}
  =\int_0^1|F(v)|^2\,dv.
```

Here `B` is the full original `zetaArithmeticBand`, for arbitrary fixed
polynomial, order, height and length. Only zero summands are removed.
Genuine integrability and square integrability are proved from the finite
interval construction. No norm is taken between prime-pair families and
no factor counting the families is introduced. This does not claim a
numerical improvement over every previous bound: the new upper bound
still contains the complete signed correlation energy.

The fixed-prime version is retained in
[`ZetaRieszWindowGram`](../RiemannGaussian/ZetaRieszWindowGram.lean).
On the full real line its equal-width kernel is exactly
`max(b-|log d-log e|,0)`. On the physical finite interval the kernel also
retains the cutoff and both divisor positions. The original signed
window identities remain upstream of every energy inequality.

## Concrete arithmetic savings

[`norm_actual_central_coefficient_le_root_saving`](../RiemannGaussian/ZetaRieszSpernerRate.lean)
proves, for every nonzero actual central coefficient with `k` prime factors,

```math
|c_L(n)|\le
 \frac{2^k\log n}{2k\sqrt{k-1}}.
```

Thus the gain over the coarse Boolean allowance is `2k sqrt(k-1)`.
Both parity cases follow from exact binomial recurrences. The sharper
middle-binomial bound and earlier three-prime bounds remain available;
this is not asserted to improve every prior estimate on every integer.
It is a coefficient saving, not source-normalized decay of the whole sum.

[`exists_central_higher_unit_window_zero`](../RiemannGaussian/ZetaRieszWindowUnitDeletion.lean)
proves that the cofactor's unit divisor contributes **exactly zero** on
all these actual central windows when `k>=4`. The two smallest primes
satisfy `2(log p+log q)<=log n`, and actual annular support gives
`log n<2L`, hence `log p+log q<L`. The unit window therefore lies wholly
outside the integration interval. The whole-lift deletion theorem keeps
all other divisor labels and complex cross terms intact. This is the unit
of the selected cofactor window, not the separate Euler prime-head term.
The central conclusions retain their existing domain `u<exp(-2/3)`.

## What still needs bounding

The remaining signed Gram form contains prime and composite divisor
pairs, their Mobius signs, relative complex filter phases, exact prime
factor compatibility and the overlap of their physical windows. Its
source-normalized upper bound remains open. An exact energy identity or
positivity of that energy does not establish its smallness.

For the original pole-jet filter, a hypothetical right-half zero still
gives the existing source limit `u^(N+1) B_N -> -m`, with full analytic
multiplicity. A bound keeping `u^(2N+2) Gamma_N` uniformly below one on a
cofinal subsequence would contradict that source. No such bound is claimed.
The whole-carrier Gram construction is not restricted to the narrower
central decomposition and does not assume exposure or simplicity.

The related signed divisor moments studied by
[de la Bretèche, Dress and Tenenbaum](https://arxiv.org/abs/1902.09956)
provide research leads. Their mean-square argument uses zero-free
information; it has not been imported here and does not independently
supply the new source-scale estimate. These finite interval identities,
Cauchy--Schwarz and binomial bounds carry no historical novelty claim.

The [prime-replacement bounds](zeta-riesz-prime-replacement.md) now retain
shared-prime cutoff shifts, restrict surviving interactions and bound actual
disjoint integer pairs with their exact relative phases.
