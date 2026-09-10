# Independent weighted Möbius decay outside shrinking resonance

The complete nonresonant interaction now tends to zero independently,
including its interior contribution. This holds outside an explicitly
shrinking finite Fourier region, for every fixed polynomial filter and
ordinate and every moving divisor cutoff. Every hypothetical right-half
zero retains its full normalized negative multiplicity in the remaining
resonant interaction. Its independent signed lower bound remains open;
this does not exclude additional zeta zeros or prove RH.

The subsequent [centered resonance theorem](zeta-moebius-centered-resonance.md)
also removes the constant arithmetic Fourier component with an independently
vanishing correction. The full source survives in Fourier increments with a
uniform fractional modulus. Their signed interaction is still open.

The terminal theorems are
`tendsto_zetaMoebiusWeightedFourierPart_shrinking_compl` and
`tendsto_zetaRightHalfMoebius_shrinking_resonance` in
[ZetaMoebiusResonanceDecay.lean](../RiemannGaussian/ZetaMoebiusResonanceDecay.lean).

## The cost removed by the weight transfer

The preceding [unweighted estimate](zeta-moebius-fourier-resonance.md)
multiplied the kernel difference energy by the unweighted arithmetic square
mass over a band ending at `M_N=2^(32*N)`. Its boundary cost was controlled,
but the full interior estimate paid for the enormous arithmetic range.

Let `c_D(n)` denote the genuine signed Möbius divisor coefficient. Transfer
the fixed weight `n^(-5/4)` into the coefficient and compensate in the
kernel:

```text
b_D(n) = c_D(n)*exp(-(5/4)*log(n)),
f_N(n) = zetaPrimeFilterKernel p N (1/4+i*y) n,
b_D(n)*f_N(n) = c_D(n)*zetaPrimeFilterKernel p N (3/2+i*y) n.
```

The last equality is an exact complex identity at every positive integer.
It preserves the original band sum; it does not evaluate an arithmetic
Dirichlet series in the critical strip.

[ZetaMoebiusWeightedFourier.lean](../RiemannGaussian/ZetaMoebiusWeightedFourier.lean)
proves

```text
sum_j |b_D(j)| <= H,
H = zetaMoebiusLogMajorantMass(5/4) < infinity,
```

uniformly in both `D` and `N`. The samples vanish outside the original
band. All arithmetic hypotheses are discharged by the existing positive
divisor majorant and its genuine absolute convergence beyond one.

## The complete second-difference estimate

For `s=1/4+i*y`, differentiating twice keeps the exact three-moment expression

```text
f_(n+2)''(x)
 = [K_n(s,x) - (2*s+1)*K_(n+1)(s,x) + s*(s+1)*K_(n+2)(s,x)]/x^2.
```

Here the subscript is moment order, not an arithmetic index. The complex
coefficient identity is retained before applying the envelope. With the
positive exponential tilt `9/8`,
[ZetaPrimeKernelSecondDifference.lean](../RiemannGaussian/ZetaPrimeKernelSecondDifference.lean)
proves

```text
|f_(n+2)(x+2)-2*f_(n+2)(x+1)+f_(n+2)(x)|
 <= (8/9)^n * exp(-(9/8)*log(x)) * Q(p,y),    x>=1.
```

The spatial weight is summable at the positive integers. The same bound
holds for the second derivative; two applications of the mean-value
inequality give the signed finite difference.

Write `P_a(p)=sum_k |p_k|*a^k` and
`H_s=sum_n exp(-(9/8)*log(n))`, including the explicitly specified unused
zero term. Then

```text
Q(p,y) = P_(8/9)(p)
  * [1 + |2*s+1|*(8/9) + |s*(s+1)|*(8/9)^2],
C(p,y) = Q(p,y)*H_s + 2*P_(8/9)(p),
B(p) = 8*P_8(p).
```

The complete cyclic second-difference mass satisfies, for `N>=2`,

```text
L_N = sum_j |Delta^2 f_N(j)|
 <= C(p,y)*(8/9)^(N-2) + B(p)*(1/2)^N.
```

This is `sum_norm_cyclicSecond_quarterKernel_le`. The first sample is
explicitly zero, and the sample at one vanishes at positive moment order.
The exact cyclic formula retains the sample at two and both final terms:

```text
L_N = sum_{n=1}^{M_N-2}|f_N(n+2)-2*f_N(n+1)+f_N(n)|
      + |f_N(2)| + |f_N(M_N-1)-2*f_N(M_N)| + |f_N(M_N)|.
```

[FiniteFourierDifferenceDecay.lean](../RiemannGaussian/FiniteFourierDifferenceDecay.lean)
proves this identity before its boundary estimate. No factor proportional
to the group size multiplies the three exceptional-index costs.

## An independently negligible complementary interaction

Let `q=M_N+1` and

```text
lambda(k)=exp(2*pi*i*k/q)-1,
delta_N=(31/32)^N,
S_N={k in ZMod q : |lambda(k)|<delta_N}.
```

The set includes the central mode and uses cyclic distance: frequencies
near either end of the standard index interval can lie near zero phase.
The threshold is positive and tends to zero. This is a shrinking Fourier
region, not a region containing zeta zeros in the complex plane.

The exact Fourier pairing of the weighted vectors splits the original
arithmetic band into signed parts `R_N` on `S_N` and `T_N` on its complement.
The checked mass estimate gives

```text
|T_N| <= H*delta_N^(-2)*L_N
 <= H*[(81/64)*C(p,y)*(8192/8649)^N
        + B(p)*(512/961)^N],    N>=2.
```

Both displayed bases are strictly less than one. This is the public bound
`norm_zetaMoebiusWeightedFourierPart_shrinking_compl_le`; its limit is
`tendsto_zetaMoebiusWeightedFourierPart_shrinking_compl`.

This decay is independent of hypothetical zeros and uniform over every
choice of moving divisor cutoffs. The polynomial and ordinate are fixed
in each limit; no uniformity in unbounded moving ordinates or growing
polynomial budgets is asserted. A fixed positive symbol threshold is also
covered by `tendsto_zetaMoebiusWeightedFourierPart_compl`.

## The source left to contradict

For any hypothetical zero `rho=beta+i*gamma` with `beta>1/2`, use the
original pole-jet filter and canonical divisor schedule. With
`u=3/2-beta` and analytic multiplicity `m`, the previously proved band
source is `u^(N+1)*(R_N+T_N) -> -m`. The independent complementary decay
now proves

```text
u^(N+1)*R_N -> -m.
```

This is `tendsto_zetaRightHalfMoebius_shrinking_resonance`, with no
additional cancellation premise. The original infinite-to-finite error
also remains geometrically controlled by
[ZetaMoebiusMomentBand.lean](../RiemannGaussian/ZetaMoebiusMomentBand.lean).

The remaining target is an independent signed lower bound for `R_N` that
beats this negative source. Full decay of `R_N` would suffice but is
unnecessary: for the selected zero, any fixed `eta>0` and arbitrarily
large orders with `Re(u^(N+1)*R_N)>=-m+eta` would contradict the proved
limit. Neither such signed recovery nor a sufficiently strong norm bound
inside `S_N` has been proved.

The upper bounds use only an absolute arithmetic majorant. They do not
establish new Möbius cancellation within the resonant region. Its complete
complex Fourier products, divisor cutoff, and coefficient coupling remain
available upstream of the estimates. Fourier smoothness and exact
Dirichlet reweighting are standard mechanisms; no mathematical-priority
claim is made for this formalized application.

## Validation

The four new modules are imported from the root library. Local gates use
the pinned toolchain, warnings as errors, focused and full builds, all
project declaration linters, terminal-theorem axiom checks, the source
scan, and deterministic status generation. Permitted axiom dependencies
are only `propext`, `Classical.choice`, and `Quot.sound`. Commits and remote
CI remain held at the user's request.
