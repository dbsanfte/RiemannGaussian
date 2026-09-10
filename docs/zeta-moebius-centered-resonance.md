# The source in centered arithmetic Fourier increments

The constant arithmetic Fourier component is now independently negligible on
the entire shrinking resonant region. After its exact subtraction, the full
selected-zero source survives. The remaining actual Möbius Fourier increment
has a uniform fractional modulus for every exponent below one quarter.
Its signed interaction with the kernel remains open; no additional zeta zeros
have been excluded.

The subsequent [fractional budget audit](zeta-moebius-fractional-budget-audit.md)
proves that the absolute kernel allowance below cannot be bounded at the
required source scale for any available fractional exponent, including
moving choices through `1/4`. The exact signed interaction is retained.

The terminal source theorem is
`tendsto_zetaRightHalfMoebius_centered_resonance` in
[ZetaMoebiusCenteredResonance.lean](../RiemannGaussian/ZetaMoebiusCenteredResonance.lean).
The independent arithmetic bound is `norm_zetaMoebiusWeightedDFT_sub_zero_le`;
`zetaMoebiusWeightedDFT_sub_zero_uniformly_small` makes its uniformity explicit.

## The exact subtraction

Keep the same finite arithmetic band, polynomial, and fixed Dirichlet
weight as in the [preceding decay theorem](zeta-moebius-resonance-decay.md):

```text
q_N = 2^(32*N)+1,
b_D,N(n) = c_D(n)*n^(-5/4) on the original band, zero elsewhere,
f_N(n) = K_p,N(1/4+i*y,n) for n>0, f_N(0)=0,
B_N(k) = DFT(b_D,N)(k),  F_N(k) = DFT(f_N)(k),
lambda(k) = exp(2*pi*i*k/q_N)-1,
S_N = {k : |lambda(k)| < (31/32)^N}.
```

The previous resonant interaction is

```text
R_N = (1/q_N) sum_{k in S_N} B_N(-k)*F_N(k).
```

Fourier inversion gives `sum_k F_N(k)=q_N*f_N(0)=0`. Therefore subtracting
the same coefficient `B_N(0)` at every frequency leaves the complete original
pairing unchanged. Define the centered interaction

```text
C_N = (1/q_N) sum_{k in S_N} [B_N(-k)-B_N(0)]*F_N(k).
```

Its correction on a partial region is retained exactly:

```text
C_N - R_N
 = -B_N(0)*(1/q_N) sum_{k in S_N} F_N(k)
 =  B_N(0)*(1/q_N) sum_{k outside S_N} F_N(k).
```

These statements are proved for general finite vectors in
[FiniteFourierCentering.lean](../RiemannGaussian/FiniteFourierCentering.lean),
then applied to the actual arithmetic samples. `centeredFourierPart_zero`
and `centeredFourierPart_erase_zero` prove that the central frequency itself
contributes exactly zero after centering.

The constant Fourier component and the central frequency are different
objects: the former has the same value at all frequencies; the latter is
one term of the Fourier sum. Both distinctions matter in this argument.

## The correction is independently controlled

Let `H(sigma)=zetaMoebiusLogMajorantMass(sigma)` and let
`L_N=sum_j |Delta^2 f_N(j)|` be the complete cyclic second-difference mass,
including every boundary term. The already proved absolute arithmetic mass
bound gives `|B_N(0)|<=H(5/4)`. The complementary symbol gap gives

```text
|C_N-R_N| <= H(5/4)*delta_N^(-2)*L_N,
delta_N=(31/32)^N.
```

This is `norm_zetaMoebiusCenteredFourierPart_sub_weighted_le`. The right
side tends to zero by the previous full difference estimate, with the same
geometric bases `8192/8649` and `512/961`. The limit theorem
`tendsto_zetaMoebiusCenteredFourierPart_sub_weighted` holds for every moving
divisor schedule, every fixed polynomial, and every fixed ordinate.

Thus the correction is removed by an independently proved estimate, not
by assuming its sign or treating a partial Fourier sum as zero.

## A uniform modulus for the actual arithmetic factor

The exact signed increment is

```text
B_N(-k)-B_N(0)
 = sum_{n in band} c_D(n)*n^(-5/4)
     * [exp(2*pi*i*k*n/q_N)-1].
```

`zetaMoebiusWeightedDFT_sub_zero_eq` retains every original divisor sign,
the strict divisor cutoff, and the phase difference within the same sum.
Before specializing the arithmetic coefficients, Lean proves for every
unit complex number `z`, integer `n>=0`, and `0<=tau<=1` that

```text
|z^n-1| <= 2*(n*|z-1|)^tau.
```

For the actual weighted coefficients, the positive divisor majorant gives

```text
sum_n |b_D,N(n)|*n^tau <= H(5/4-tau),    tau<1/4.
```

The right side is genuinely finite because `5/4-tau>1`. Consequently,
for every `0<=tau<1/4`,

```text
|B_N(-k)-B_N(0)| <= 2*H(5/4-tau)*|lambda(k)|^tau.
```

This holds uniformly in both cutoffs and in every cyclic frequency. On
`S_N`, replace `|lambda(k)|` by `delta_N`. For every positive exponent in
the stated range and every `epsilon>0`, the proof supplies one sufficiently
large order after which **all** divisor cutoffs and **all** resonant
frequencies have increment smaller than `epsilon`.

The new norm allowance keeps the fractional phase factor:

```text
|C_N| <= 2*H(5/4-tau)/q_N
  * sum_{k in S_N} |lambda(k)|^tau * |F_N(k)|.
```

This is `norm_zetaMoebiusCenteredFourierPart_le`. The whole complex pairing
remains defined upstream; the bound is an optional downstream estimate.

## What is still required for the goal

For every hypothetical zero `rho=beta+i*gamma` with `beta>1/2`, use the
original pole-jet polynomial and canonical divisor schedule. With
`u=3/2-beta` and actual analytic multiplicity `m>0`, Lean now proves

```text
u^(N+1)*C_N -> -m.
```

The full source survives after removal of both the complementary
interaction and the constant Fourier component. The original infinite
arithmetic tail and finite band still differ by the previously proved
geometric error.

The target remains an independent signed lower bound that beats this source
by a fixed positive amount at arbitrarily late orders. Decay of `C_N` is
sufficient but is not required. The new fractional kernel norm allowance
has **not** been proved small enough at the source scale, and no exchange
of a pointwise limit with the growing Fourier sum is justified. Uniformly
small arithmetic increments can still correlate with an increasing kernel
budget across an increasing number of frequencies.

The subtraction closes the constant-component estimate and exposes the
phase difference explicitly. The fractional bound uses the positive
majorant; it does not establish additional cancellation between Möbius
signs. Improving their signed interaction is the remaining arithmetic
work. No novelty priority claim is made for Fourier centering or fractional
moment interpolation.

## Validation

Both modules are imported from the project root. Verification uses the pinned
toolchain, warnings as errors, focused and full builds, root declaration
lint, terminal axiom checks, the full source scan, and deterministic status
generation. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Commits and remote CI remain held at the user's request.
