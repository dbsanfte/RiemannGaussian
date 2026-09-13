# Independent reduction to ordinary Gaussian-prime energy

[ZetaGaussianPrimeReduction](../RiemannGaussian/ZetaGaussianPrimeReduction.lean)
proves that, at the current fixed-strip dilation, proper prime powers and
both auxiliary responses have one fixed summable remainder. It pays all
their mixed quadratic terms before transporting the original squared
zero-source constraint to ordinary Gaussian-prime energy.

With reciprocal-dilation tuning, the complete additive allowance divided
by the squared dilation tends to zero for every moving family with bounded
nonconstant mass. The subsequent [ordinary-prime energy bound](zeta-gaussian-prime-energy-bound.md)
now supplies an independent logarithmic-height estimate; making it beat
the actual source remains open. This is not a new zero-free region or an RH proof, and no
historical novelty claim is made.

## Exact splitting of the original measure

Use `k=9`, `q>=1`, `x=shift(q)` and `B=gaussianScale(q)` from the
[scaled Gaussian budget](../RiemannGaussian/ZetaGaussianScaledBandBudget.lean).
Let `W_q` be the full common amplitude from
[ZetaGaussianPrimeBlocks](../RiemannGaussian/ZetaGaussianPrimeBlocks.lean).
The displayed arithmetic formulas are for `n>=2`; zero and one carry
zero weight. Define

```math
G_q(n)=\Lambda(n)e^{-(1+x)\log n}e^{-B(\log n)^2},\qquad
P_q(n)=\mathbf1_{\{n\ {m prime}\}}G_q(n).
```

`primeAmplitude` is exactly `P_q`. The remainder `R_q` is the non-prime
part of `G_q`, plus the original shifted Euler and averaged logarithmic
responses with their original multipliers. `amplitude_eq` proves

```math
W_q(n)=P_q(n)+R_q(n),\qquad P_q(n),R_q(n)\ge0.
```

The ordinary-prime amplitudes, phases and support are unchanged. The
non-prime von Mangoldt terms are precisely proper prime powers; other
composites, zero and one carry zero weight.

## One summable bound for the whole remainder

The right boundary stays on or to the right of the fixed Euler line
`sigma_*=1+delta(9)=1+11/2046`. The original multiplier is at most
`1/50000`, and the averaged-response multiplier is at most `94`.
The Gaussian window is at most one. Hence `remainder_le_majorant` proves

```math
R_q(n)\le
\Lambda(n)\mathbf1_{\{n\ {m not\ prime}\}}e^{-\log n}
+\frac{\Lambda(n)}{50000}e^{-\sigma_*\log n}
+94\frac{\Lambda(n)}{\log n}e^{-\sigma_*\log n}.
```

The first term is summable by the existing proper-prime-power Dirichlet
theorem at exponent one. That theorem uses the independently proved
square-root bound for the Chebyshev difference `psi-theta`. The other two
series converge on the fixed line `sigma_*>1`.

Put

```math
C=\operatorname{zetaProperPrimePowerExpMass}(1)
+\frac1{50000}\operatorname{Re}\frac{-\zeta'(\sigma_*)}{\zeta(\sigma_*)}
+94\log|\zeta(\sigma_*)|.
```

`hasSum_majorant` proves that this displayed constant is the genuine total
mass of the majorant. `remainder_mass_le` proves

```math
0\le\sum_n R_q(n)\le C.
```

The bound is independent of dilation, height, frequencies and the retained
finite set. `finite_remainder_cosine_le` consequently gives, for every
finite `S` and every real `v`,

```math
\left|\sum_{n\in S}R_q(n)\cos(v\log n)\right|\le C.
```

These are independent arithmetic bounds. No hypothetical zero or desired
ordinary-prime cancellation is used to prove them. The constant is
mathematically defined; no numerical enclosure of it is asserted here.

## Every mixed quadratic term is paid

For any nonnegative summable coefficient family `a`, let `Q_a(W)` denote
the exact real pair energy from
[ZetaGaussianPrimeCorrelation](../RiemannGaussian/ZetaGaussianPrimeCorrelation.lean),
on the same height, frequency family and finite set. It keeps both product
and ratio phases and has the convergent expansion

```math
Q_a(W)=\sum_n a_n
\left(\sum_{p\in S}W(p)\cos(\omega_n t\log p)\right)^2.
```

The amplitude splitting takes place inside each cosine sum, before its
square. Young's inequality then gives, for every `epsilon>0`,

```math
Q_a(W_q)\le (1+\varepsilon)Q_a(P_q)
+(1+\varepsilon^{-1})\left(\sum_n a_n\right)C^2.
```

This is `real_energy_le_prime_energy`. It includes ordinary-prime/remainder
cross terms and every cross term within the remainder. The ordinary-prime
sum itself is never replaced by a sum of absolute values.

When `omega_0=0`, `real_energy_tail` removes the constant channel exactly:

```math
Q_a(W)-a_0\left(\sum_{p\in S}W(p)\right)^2=Q_{\widetilde a}(W),
\qquad \widetilde a_0=0,\quad \widetilde a_n=a_n\ (n\ne0).
```

Let `m=sum_n tilde a_n=sum_n a_n-a_0`. The same comparison therefore
applies to the nonconstant energy, with error `(1+1/epsilon)*m*C^2`.

## The actual squared source, with a vanishing allowance

Let `mathcal S_Z` be the coefficient-weighted compensated source of an
actual finite zero group, `mathcal B_exact` the original signed budget,
and `M_S=sum_(p in S) W_q(p)`. Define its positive source surplus by

```math
U_S=\max\{0,a_0M_S+\mathcal S_Z-\mathcal B_{\rm exact}\}.
```

`finite_source_le_prime_energy` proves

```math
U_S^2\le(1+\varepsilon)mQ_{\widetilde a}(P_q)
+(1+\varepsilon^{-1})m^2C^2.
```

The finite zero group, its full compensated source, the actual common
mass and the signed boundary budget remain intact. Every original phase,
strip and summability hypothesis is retained and the current scaled
geometry is discharged. The only arithmetic energy on the right uses
ordinary Gaussian primes, including their complete diagonal and mixed
prime-pair terms.

Choose `epsilon=1/q`. The directly compiled specialization
`finite_source_le_prime_energy_scaled` gives

```math
U_S^2\le(1+q^{-1})mQ_{\widetilde a}(P_q)+E(q,m),
\qquad E(q,m)=(1+q)m^2C^2.
```

For `0<=m<=A`, `normalized_energyAllowance_le` proves

```math
0\le\frac{E(q,m)}{q^2}\le\frac{2A^2C^2}{q}.
```

`tendsto_normalized_energyAllowance` proves the resulting limit for
arbitrary moving masses `m_N` under one fixed bound and any `q_N` tending
to infinity with `q_N>=1`. In particular it covers the current eligible
class `m_N<=61/100`. The coefficient families, frequencies, heights and
retained prime sets may change: no corresponding uniform counting or
phase-independence premise is needed for the error bound.

The multiplier `1+1/q` tends to one. Thus these remainder terms cannot
consume a persistent positive margin at the squared-dilation scale.
This statement does not assert that the actual source surplus has such
a margin for every remaining zero. Its size and the signed boundary
budget must still be checked at the chosen geometry.

## Remaining arithmetic

The subsequent [independent upper bound for the complete
ordinary-prime energy](zeta-gaussian-prime-energy-bound.md) uses mass
and the first logarithmic frequency moment. The later
[signed Poisson comparison](zeta-gaussian-prime-energy-decay.md) removes
its surviving height coefficient and proves normalized complete-energy
decay at the current dilation. The full source cost now decays there.
A positive source surplus over the retained signed boundary budget
remains to be proved.
The [product and ratio heat coordinates](zeta-gaussian-prime-correlation.md)
now apply directly to its ordinary-prime pairs. Both oscillations, the
logarithmic separation factor and the diagonal must remain accounted for.

The remainder's decay is not decay of this ordinary-prime energy. Nor
does sending the dilation to infinity automatically exclude a fixed zero:
the selected source changes with the detector geometry. The separate
direct centered-prime carrier still requires its independent cofinal real
floor. These distinctions remain in the
[carrier audit](signed-prime-carrier-information-audit-2026-09-12.md).

The root import, compiled theorem inventory and **Ordinary primes**
explorer endpoint include the actual source specialization, the complete
remainder bound and its normalized limit. This slice is held locally
under the current no-commit instruction.
