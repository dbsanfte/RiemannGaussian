# Exact cancellation inside the retained real arithmetic work

Lean now proves two exact cancellations for the actual sieved Fourier
carrier. Opposite-frequency pairing removes the imaginary **physical**
kernel from the required real part. Each arithmetic row then annihilates
the canonical even reflection of the real physical kernel. The same
multiplicity source survives in a signed odd-reflection correlation.
Its independent strict upper bound remains open.

These are identities at every finite stage. They add no approximation,
decay hypothesis, coefficient search, or new error allowance to the
[existing sieve and localization](zeta-sieved-fourier-localization.md).

## Opposite frequencies cancel one physical component

Let `q=2^(32N)+1`, let `S` be the retained region, and keep its original
cyclic character `chi(k)=exp(2*pi*i*k/q)`. Every symbol region
`|chi(k)-1|<delta` is proved closed under `k -> -k`, including central and
self-opposite modes. Its normalized projection kernel is

\[
H_S(j)=\frac1q\sum_{k\in S}\chi(k)^j.
\]

Pairing opposite frequencies proves exactly

\[
H_S(-j)=H_S(j),\qquad \operatorname{Im}H_S(j)=0.
\]

For real arithmetic samples `A(n)` and arbitrary complex physical kernel
`f`, the centered pairing therefore has real part

\[
\operatorname{Re}C_S(A,f)
=\sum_n A(n)\sum_m K_S(n,m)\operatorname{Re}f(m),
\qquad K_S(n,m)=H_S(n-m)-H_S(m).
\]

Every purely imaginary physical perturbation `i*g(m)`, with real `g`,
contributes exactly zero. Lean discharges the hypotheses for the actual
sieved coefficients and quarter-line kernel at every cutoff.

This does **not** discard the imaginary Fourier component of the real
physical kernel: a real function can have a nonzero sine Fourier transform.
That component is retained in the exact real formula. The real physical
quarter-line kernel also still depends on the original logarithmic phase
and the full complex pole-jet polynomial.

## Physical reflection cancels the even part row by row

All physical indices remain in `ZMod q`. For each fixed arithmetic row `n`,
the map `m -> n-m` is an involution, with cyclic wraparound included. The
centered real kernel is odd under this reflection:

\[
K_S(n,n-m)=-K_S(n,m).
\]

Consequently, for every real profile `g`,

\[
\sum_mK_S(n,m)g(m)
=\frac12\sum_mK_S(n,m)\bigl(g(m)-g(n-m)\bigr).
\]

The canonical even component `(g(m)+g(n-m))/2` contributes zero, whether
or not `g` itself has any symmetry. A cyclic midpoint satisfying `m+m=n`
also has `K_S(n,m)=0`. No division by two in the finite group is assumed.

The reflection center depends on the arithmetic row. This removes an
even component within each row, not one fixed global even function.

These exact cancellations are proved in
[FiniteFourierReflection.lean](../RiemannGaussian/FiniteFourierReflection.lean):

- `centeredFourierPart_eq_kernel`
- `cyclicFourierKernel_neg` and `cyclicFourierKernel_im`
- `centeredFourierPart_re_imaginary_eq_zero`
- `cyclicCenteredRealKernel_reflect` and `cyclicCenteredRealKernel_midpoint`
- `sum_cyclicCenteredRealKernel_mul_even_part_eq_zero`
- `centeredFourierPart_re_eq_reflection`

## The remaining sign is an explicit sine product

Write `theta_k(n)=2*pi*k*n/q` using the original integer representatives.
Product-to-sum gives the exact real kernel

\[
\begin{aligned}
K_S(n,m)
&=\frac1q\sum_{k\in S}
\left[\cos(\theta_k(n)-\theta_k(m))-\cos\theta_k(m)\right]\\
&=-\frac2q\sum_{k\in S}
\sin\!\left(\frac{\theta_k(n)}2\right)
\sin\!\left(\frac{\theta_k(n)}2-\theta_k(m)\right).
\end{aligned}
\]

Both phases stay coupled. Lean also records the endpoint signs
`K_S(n,n)>=0` and `K_S(n,0)<=0`. Thus a sign for the entire centered kernel
cannot simply be assumed. The signed arithmetic coefficients and the odd
real kernel profile must be controlled jointly.

## The actual source and finite scalar error are preserved

At a hypothetical zero `rho=beta+i*gamma` with `beta>1/2`, keep the same
`u=3/2-beta`, divisor cutoff `D_N`, cofinal sieve `S_N`, polynomial `p`,
and retained frequency region `R_N` as before. Let `A_N` be the original
sieved coefficient multiplied by `n^(-5/4)` on the logarithmic band, and
let `f_N` be the original quarter-line physical samples, including their
zero value at index zero. Define

\[
W_N=-\frac14\sum_n A_N(n)\sum_mK_{R_N}(n,m)
\left[\operatorname{Re}f_N(m)-\operatorname{Re}f_N(n-m)\right].
\]

Lean proves that `W_N` is exactly the previous signed trigonometric work
`T_N`. In particular,

\[
\operatorname{Re}C_N=-2W_N,\qquad
u^{N+1}W_N\longrightarrow m_\rho/2.
\]

Every original arithmetic sign, sieve restriction, kernel parameter, and
wrapped reflection sample remains present. Removing the two annihilated
components loses none of this scalar source.

Let `L_N` be the original pole-jet response and write the previously proved
total error as `B_rho,N=C_rho*(sqrt u)^N+E_N`, where `E_N` contains the band
and complementary-frequency allowances and tends to zero. For `N>=2`,

\[
\left| -\frac{u^{N+1}\operatorname{Re}L_N}{2}
       -u^{N+1}W_N\right|\le\frac{B_{\rho,N}}2.
\]

The factor one half is the exact normalization of the real work. It does
not improve the decay rate or the mathematical strength of the source.

Compiled entry points in
[ZetaSievedFourierReflection.lean](../RiemannGaussian/ZetaSievedFourierReflection.lean):

- `zetaMoebiusResonantModes_neg_closed`
- `cyclicCenteredRealKernel_eq_cosine` and `cyclicCenteredRealKernel_eq_sine`
- `cyclicCenteredRealKernel_self_nonneg` and `cyclicCenteredRealKernel_zero_nonpos`
- `zetaMoebiusSievedFourier_imaginary_eq_zero`
- `zetaMoebiusSievedFourier_even_reflection_eq_zero`
- `zetaArithmeticTrigWork_eq_reflection`
- `zetaRightHalfSievedTrigWork_eq_reflection`
- `tendsto_zetaRightHalfSievedReflectionWork`
- `exists_zetaRightHalfReflection_error_bound`

## What still needs proof

For some fixed `epsilon>0`, an independent inequality

\[
u^{N+1}W_N\le m_\rho/2-\epsilon
\]

at arbitrarily late orders would suffice. Full complex decay, positivity
of every summand, and a new power-saving rate are unnecessary. The next
useful estimate must act on the joint signed sine-product and odd-profile
correlation, using the actual arithmetic information. The exact identities
alone do not establish its sign or its required upper bound.

These reflection identities alone exclude no additional zeros. The later
[completion-reserve argument](zeta-completion-reserve-zero-free.md) proves
the stronger edge margin `1/(10*log(|gamma|+2))`. The remaining interior
zeros still require an independent signed bound; RH remains open.
Validation is local with commits and remote CI held at the user's request.
