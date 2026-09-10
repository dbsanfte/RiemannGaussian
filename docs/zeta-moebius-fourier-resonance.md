# Finite Möbius resonance and the complete boundary budget

The actual moving Möbius tail now has an exact finite Fourier representation,
an independent difference-energy estimate away from a chosen resonant set,
and a geometrically vanishing cyclic boundary budget. The boundary estimate
includes the entire finite arithmetic square mass. The interior energy and
resonant interaction remain uncontrolled at the source scale; this slice
does not improve the existing zero-free region or prove RH.

The subsequent [weighted resonance decay theorem](zeta-moebius-resonance-decay.md)
avoids the unweighted full-energy cost and proves independent decay of the
entire complementary interaction, even for a geometrically shrinking
resonant region. The unweighted identities and estimates below remain
available; the signed interaction inside the weighted resonant region is
the current obstruction.

## The actual source survives the finite representation

Write `c_D(n)` for `zetaMoebiusLogTailCoefficient D n`, `K_N(x)` for the full
complex kernel `zetaPrimeFilterKernel p N (3/2+i*y) x`, and

```text
M_N = 2^(32*N),
B_N = {n : 1 <= n <= M_N and N*log(2)/4 < log(n)},
F_N = sum_{n in B_N} c_D(n)*K_N(n).
```

[ZetaMoebiusMomentBand.lean](../RiemannGaussian/ZetaMoebiusMomentBand.lean)
proves `norm_zetaMoebiusLogTailFilter_sub_band_le`: the difference from the
original infinite tail is at most `2^(-N)*C(p)`, uniformly in the divisor
cutoff and ordinate. The majorant is an actual absolutely convergent divisor
logarithm series in the Euler half-plane.

For any hypothetical zero `rho=beta+i*gamma` with `beta>1/2`, the existing
pole-jet polynomial and canonical growing divisor cutoff therefore satisfy

```text
u^(N+1)*F_N -> -m,    u=3/2-beta,
```

where `m` is its analytic multiplicity. This is
`tendsto_zetaRightHalfMoebiusBand`. No arithmetic cancellation hypothesis
is added to the selected-zero premise.

## Exact frequency transport and the gap estimate

Embed `c_D` on `B_N` in `ZMod (M_N+1)`, setting other coefficients to zero.
Sample the full kernel at the positive indices, with its unused zero index
explicitly set to zero. There is no aliasing of the band indices.

[FiniteFourierResonance.lean](../RiemannGaussian/FiniteFourierResonance.lean)
proves, with `q=M_N+1` and the unnormalized finite Fourier transform,

```text
sum_j a(j)*f(j) = (1/q)*sum_k DFT(a)(-k)*DFT(f)(k),
DFT(Delta^r f)(k) = lambda(k)^r*DFT(f)(k),
Delta f(j) = f(j+1)-f(j),
lambda(k) = exp(2*pi*i*k/q)-1,
|lambda(k)|^2 = 2-2*cos(2*pi*k/q).
```

The multiplier vanishes exactly at the central mode. For any region `S`
where `|lambda(k)|>=delta>0`, Parseval and the finite energy inequality give

```text
|FourierPart(S)|^2 <= delta^(-2*r)
  * (sum_j |a(j)|^2) * (sum_j |Delta^r f(j)|^2).
```

`norm_finiteFourierPart_sq_le_physical_difference` proves this for every
order and sample vector.
[ZetaMoebiusFourierResonance.lean](../RiemannGaussian/ZetaMoebiusFourierResonance.lean)
applies it to the literal arithmetic coefficients and full kernel. Its
resonant region consists of **all** modes with `|lambda|<delta`, including
zero. Every frequency partition, even one varying with `N`, retains the
source in the sum of its two signed parts:
`tendsto_zetaRightHalfMoebiusFourier_parts`.

The discrete central mode is a product of discrete means. It has not been
identified with the continuous logarithmic mean or proved negligible.
Likewise, the resonant part alone has not been shown to carry `-m`.

## The cyclic boundary is controlled with its arithmetic weight

For `N>=1`, the first kernel sample vanishes. The exact derivative of the
full complex kernel is

```text
G_N(x) = (K_(N-1)(x) - (3/2+i*y)*K_N(x))/x.
```

[ZetaMoebiusFourierEnergy.lean](../RiemannGaussian/ZetaMoebiusFourierEnergy.lean)
proves both the signed adjacent integral identity and

```text
sum_j |Delta f(j)|^2
 = sum_{n=1}^{M_N-1} |integral_n^{n+1} G_N(x) dx|^2 + |K_N(M_N)|^2
 <= integral_1^{M_N} |G_N(x)|^2 dx + |K_N(M_N)|^2.
```

The last term is the actual wraparound jump. The continuous integrals have
proved regularity and integrability. The damping and rotation terms are
not split before forming their square.

Let `A_D,N=sum_{n in B_N}|c_D(n)|^2`. Define

```text
C_boundary(p) = (sum_k |p_k|*8^k)
  * zetaMoebiusLogMajorantMass(5/4).
```

[ZetaMoebiusFourierBoundary.lean](../RiemannGaussian/ZetaMoebiusFourierBoundary.lean)
proves the independent quantitative estimate

```text
A_D,N * |K_N(M_N)|^2 <= (2^(-N)*C_boundary(p))^2.
```

This is `zetaMoebiusFourierBoundary_energy_le`. Its limit theorem allows
arbitrary moving cutoffs **and** ordinates. The proof uses the positive
majorant only for this boundary cost: the upper-endpoint exponential tilt
absorbs the full arithmetic first mass, which bounds its square mass.

Combining these results, `norm_zetaMoebiusBand_sub_resonant_sq_le_interior`
proves, for every polynomial, cutoff, ordinate, `N>=1`, and `delta>0`,

```text
|F_N - ResonantPart_N|^2
 <= delta^(-2) * (A_D,N * integral_1^{M_N}|G_N(x)|^2 dx
                    + (2^(-N)*C_boundary(p))^2).
```

For fixed positive `delta`, the second budget vanishes independently.
A shrinking threshold must also account for its explicit `delta^(-2)` cost.

## What the implementation leaves open

The exact pairing and exact adjacent integrals remain available upstream
of the estimates. The Fourier Cauchy–Schwarz step forgets correlation
between the two Fourier vectors; the physical-space bound also enlarges
frequency-restricted energies to full energies. The last continuous bound
forgets cancellation within individual unit intervals. These are named
downstream estimates, so subsequent work can use the richer identities.

The next useful targets are an independent bound for the interior
interaction at the normalization `u^(N+1)`, and signed control of the
resonant interaction. The present theorem does not assert that
`A_D,N*integral |G_N|^2` decays, that the nonresonant interaction is negligible,
or that its bound is sharp. Frequency-restricted energies and exact signed
integrals are available if the full-energy estimate proves too costly.

The Fourier and unit-interval energy mechanisms are standard analysis.
The contribution here is their checked application to this particular
moving arithmetic carrier, its unchanged multiplicity source, and the
uniform bound on its complete cyclic boundary cost. No priority claim for
new mathematics is made.

## Local validation

The slice is imported from `RiemannGaussian.lean`. Direct elaboration and
focused/full builds use warnings as errors. The root declaration lint,
terminal-theorem axiom audit, source scan, and deterministic generated
inventory are checked locally. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. Commits and remote CI remain held at the user's
request.
