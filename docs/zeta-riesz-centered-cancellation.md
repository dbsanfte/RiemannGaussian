# Centered cofactor cancellation across prime families

Lean now halves the complete opposite-phase pair allowance for **every
eligible squarefree nonunit cofactor**, and combines all eligible
prime-insertion families in one finite disjoint-matching bound for the
original carrier. Prime-to-product pairs also gain a factor of two in
their complete amplitude/profile estimate.

The new saving comes from an exact arithmetic fact: the cofactor's total
signed Mobius divisor mass is zero. This does not establish a positive
aggregate saving, control the unmatched remainder at source scale, or
prove a new zero-free region.

## The cancellation before the norm

Write the original Riesz profile and its absolute divisor mass as

```math
R_L(n)=\sum_{d\mid n}\mu(d)\max(0,L-\log d),
\qquad M(n)=\sum_{d\mid n}|\mu(d)|.
```

For every nonunit n, its complete signed divisor mass vanishes. If K is
at least L, the increment of each hinge lies between zero and K-L.
Subtracting the midpoint leaves the signed sum unchanged and halves its
absolute allowance. The compiled
[`riesz_cutoff_lipschitz_centered`](../RiemannGaussian/ZetaRieszCenteredCofactor.lean)
proves, at every real cutoff,

```math
|R_L(n)-R_K(n)|\le \frac{|L-K|}{2}M(n),\qquad n\ne1.
```

This includes both clipped endpoints. It uses the complete divisor measure;
it does not assume that a truncated divisor sum has zero mass. The same
centering applies to the nonnegative compact two-prime tent. The original
signed finite differences and phase identities remain available upstream.

## Actual opposite-phase pairs

For distinct prime insertions p and q into the same squarefree nonunit n,
the profile difference is exactly

```math
R_L(pn)-R_L(qn)=R_{L-\log q}(n)-R_{L-\log p}(n).
```

The original band weight is the profile times its full complex amplitude,
including the physical normalization and polynomial factorial filter. The
new estimate preserves the amplitude sum, whose relative phase contributes

```math
2\left|\cos\!\left(\frac{t}{2}(\log p-\log q)\right)\right|.
```

The common cofactor cancels from that angle. The real-line smooth amplitude
and its derivative have proved allowances on the actual pair interval.
[`norm_bandWeight_prime_pair_le_half_phaseCost`](../RiemannGaussian/ZetaRieszCenteredPhase.lean)
pays half the previously defined complete opposite-prime cost. All band,
coprimality, cutoff and filter conditions are explicit and discharged.
No smaller-profile saturation is required for these prime-to-prime pairs.

The separate
[`norm_bandWeight_replacement_pair_centered`](../RiemannGaussian/ZetaRieszCenteredCofactor.lean)
halves the full amplitude/profile bound for a prime-to-product pair. That
result retains its two smaller-profile saturation conditions. It is not
included in the prime-insertion matching below without a new candidate-set
and cost construction.

## All eligible families, with no repeated integers

For original integers i and j, the candidate test uses their **actual**
gcd g. Both quotients i/g and j/g must be primes not dividing the squarefree
nonunit g, and both integers must belong to the original finite band.
Both orientations are available. Every disjoint subfamily is considered;
this is a finite maximum, not a search for a special coefficient family.

Let C(e) be the complete centered phase cost for a candidate pair. Its
certified saving is

```math
S(e)=\max\{|B(i)|+|B(j)|-C(e),0\}.
```

[`exists_actual_band_optimal_prime_pairs`](../RiemannGaussian/ZetaRieszPrimeMatching.lean)
proves that the maximum over disjoint candidate families is attained and
that the whole original carrier obeys

```math
\left|\sum_{n\in\mathcal B}B(n)\right|
\le \sum_{n\in\mathcal B}|B(n)|-\max_E\sum_{e\in E}S(e).
```

The exact complex partition into pairs and unmatched original integers is
proved before this inequality. The maximum can be zero. This bound is no
worse than the original triangle bound, but is not claimed to dominate
every earlier whole-carrier estimate or to capture every cancellation.

## What must still be bounded

There are three quantitative tasks: the unmatched original mass; the
complete costs of the selected pairs; and cancellation between different
pair sums and the remainder, which the exact partition still retains.
A useful finite fraction saved does not by itself remove the surviving
exponential source-scale cost. These results prove neither pair coverage
nor a sufficiently large aggregate saving as the moment order grows.

The default RH endpoint, the proved zero-free region and the numerical
certificate remain unchanged. Floating-point matching experiments are
exploration only and do not run in ordinary CI. No historical novelty
claim is made for these centering or finite matching identities.
