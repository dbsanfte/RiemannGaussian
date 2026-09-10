# The full signed source survives on squarefree integers

Lean proves independent geometric decay of the **entire nonsquarefree
arithmetic contribution**, including every prime square and all overlaps
with the existing quadratic prime sieve. This removes all repeated-prime
terms from the original source. The remaining squarefree coefficients
retain the full signed source, physical window, Fourier region, and
complete finite error allowance. Their independent strict upper bound
is still open.

## The exponent margin that makes all squares affordable

The previous unit Cauchy circle reached `Re(s)=1/2`, where summing
the weights of prime squares has a convergence obstruction. The new
bound permits every radius `0<r<1` around `3/2+i*y`, with the exact
moment cost `r^(-N)`. The circle stays within the region avoiding the
pole at one whenever `|y|>1`; this condition is already proved at every
actual nontrivial zero ordinate.

Set

\[
\sigma=\frac32-r,\qquad \tau=1-\frac r2,\qquad
\delta=\sigma-\tau=\frac{1-r}{2}>0,\qquad
w_\tau(P)=e^{-\tau\log P}.
\]

The original two entire multipliers of the signed divisor-prefix
response satisfy

\[
|f_{D,P}(s)|\le D\,w_\tau(P),\qquad
|g_{D,P}(s)|\le D\,\delta^{-1}w_\tau(P)
\quad(\operatorname{Re}s\ge\sigma).
\]

This holds for **every positive factor**, including one and prime powers.
The logarithmic companion is paid by the positive exponent margin.
The original complex response `f*(-zeta')+g*zeta` remains available,
and every filtered response keeps the full radius-weighted norm
`sum_k |p_k|*r^(-k)`.

Compiled entry points:

- [ZetaMultiplierRadiusBound.lean](../RiemannGaussian/ZetaMultiplierRadiusBound.lean):
  `exists_zetaEntireMultiplier_radius_moment_bound`,
  `exists_zetaEntireMultiplier_radius_filter_bound`.
- [ZetaDivisibilityPrefix.lean](../RiemannGaussian/ZetaDivisibilityPrefix.lean):
  `zetaMoebiusLogTailCoefficient_eq_vonMangoldt_add_prefix`,
  `hasSum_zetaDivisibilityPrefixFilter`,
  `exists_zetaDivisibilityPrefixFilter_expWeight_bound`.

## Keep the shared primes through the square intersections

Let `W` select first-power primes and `V` select prime squares.
Their literal intersection factor is

\[
P(W,V)=\left(\prod_{p\in W\setminus V}p\right)
       \left(\prod_{p\in V}p\right)^2.
\]

Its divisibility condition agrees exactly with the two original
conditions. The full weight factors as

\[
w_\tau(P(W,V))=
\prod_{p\in W}w_\tau(p)
\prod_{p\in V}
\begin{cases}
w_\tau(p),&p\in W,\\
w_\tau(p)^2,&p\notin W.
\end{cases}
\]

Thus shared primes retain their correction. With

\[
M_\tau=\sum_{n\ge0}w_\tau(n)^2<\infty,\qquad
b_\tau(p)=w_\tau(p)(1+w_\tau(p)),
\]

Lean proves, for every finite selected square family `Q`,

\[
\sum_{V\subseteq Q}w_\tau(P(W,V))
\le e^{M_\tau}\prod_{p\in W}b_\tau(p).
\]

The totalized zero-index weight in `M_tau` is harmless; actual
intersection factors are strictly positive. The mass is genuinely
summable because `2*tau>1`.

Combine this with the exact first-power prime-pattern expansion.
For selected first-power primes at most `R`, the complete transform
is bounded by a fixed multiple of `exp(4*sqrt(R))`. Its constant pays
**every selected square and every shared-prime correction**. It does
not depend on the number or largest member of `Q`.

Compiled entry points:

- [FinitePrimeSquareOverlap.lean](../RiemannGaussian/FinitePrimeSquareOverlap.lean):
  `primeSquareIntersection_dvd_iff`,
  `zetaPrimeExpWeight_primeSquareIntersection`,
  `sum_primeSquareIntersection_weight_le`,
  `prod_one_add_primeSquareCorrectedWeight_le`.
- [FinitePrimeSquareSieve.lean](../RiemannGaussian/FinitePrimeSquareSieve.lean):
  `primeSquareMultipleMask_mul_eq`, `primeSquareSurvivorMask_mul_eq`.
- [FinitePrimeSquareTransform.lean](../RiemannGaussian/FinitePrimeSquareTransform.lean):
  `primeSquareSurvivorTransform_indicator`,
  `hasSum_primeSquareSurvivorTransform`,
  `norm_primeSquareSurvivorTransform_le`.

## The genuine arithmetic includes its prime-power correction

The original logarithmic Möbius tail is its full von Mangoldt
coefficient plus the negative finite divisor prefix. Restricting the
distinct-prime tail to selected square multiples leaves the exact
correction

\[
\text{mask}\cdot
\bigl(\Lambda(n)-\text{prime-power-tail}_D(n)\bigr).
\]

This mask vanishes on squarefree integers, including primes. Its
correction is bounded by the existing proper-prime-power majorant
plus the existing prime-power-tail majorant. Both weighted series
converge strictly past one half. No leakage is omitted.

The full literal repeated-prime response therefore satisfies

\[
|A_{D,S,Q,p,N}(3/2+iy)|
\le C_{y,r}\,D\,e^{4\sqrt R}r^{-N}
\sum_k|p_k|r^{-k},
\]

for every `D>=1`, every moment order, every polynomial filter, every
finite first-power prime family `S` through `R`, and every finite
square family `Q`.

Now increase `Q` through all primes. Each physical coefficient
stabilizes at the literal nonsquarefree mask. The original sieved
arithmetic series supplies a summable dominator, so Lean proves
dominated convergence of the full kernel sums. The uniform bound
survives this limit. **Every prime square is included in the resulting
bound on the full infinite arithmetic series.**

Compiled entry points:

- [ZetaPrimeSquarePrefixResponse.lean](../RiemannGaussian/ZetaPrimeSquarePrefixResponse.lean):
  `hasSum_zetaPrimeSquarePrefixFilter`,
  `exists_zetaPrimeSquarePrefixFilter_bound`.
- [ZetaPrimeSquareDeletion.lean](../RiemannGaussian/ZetaPrimeSquareDeletion.lean):
  `zetaPrimeSquareCoefficient_eq_prefix_add_leakage`,
  `norm_zetaPrimeSquareLeakageCoefficient_le`,
  `exists_zetaPrimeSquareFilter_bound`.
- [ZetaSquarefreeSieve.lean](../RiemannGaussian/ZetaSquarefreeSieve.lean):
  `tendsto_zetaPrimeSquareFilter`,
  `zetaMoebiusSievedPrimeFilter_eq_squarefree_add_nonsquarefree`,
  `exists_zetaNonsquarefreeFilter_bound`.

## Every nonsquarefree term has a vanishing allowance

For any hypothetical right-half zero, keep the original quantities

\[
u=\frac32-\operatorname{Re}\rho\in(1/2,1),\quad
q=u^{-1/4},\quad D_N=\lfloor q^N\rfloor,\quad
R_N=\left\lfloor\frac{N\log q}{8}\right\rfloor^2.
\]

Choose the exact radius and resulting rate

\[
r=\frac{1+\sqrt u}{2},\qquad
\lambda=\frac{\sqrt u}{r}=\frac{2\sqrt u}{1+\sqrt u}\in(0,1).
\]

The original rounded prime cutoff satisfies `exp(4*sqrt(R_N))<=q^N`.
Since `D_N<=q^N` and `u*q^2=sqrt(u)`, the **entire** nonsquarefree
response has normalized bound

\[
u^{N+1}|A_N|\le C_\rho\lambda^N\longrightarrow0.
\]

This is an independent estimate on the actual arithmetic, with all
prime squares and their interactions with the quadratic prime sieve
already paid. Constants may depend on the fixed hypothetical zero.

[ZetaSquarefreeSource.lean](../RiemannGaussian/ZetaSquarefreeSource.lean)
proves `exists_zetaRightHalfNonsquarefree_error_bound`,
`tendsto_zetaRightHalfNonsquarefreeFilter`, and the full surviving source
`tendsto_zetaRightHalfSquarefreeFilter`.

## The complete signed source and the remaining obligation

The new window coefficient is **exactly the old quadratic-sieved
window coefficient on squarefree integers**, and zero elsewhere.
Every nonzero retained index now satisfies

- `2*N/5<=log(n)<=8*N` and `n>D_N^2`;
- `Squarefree n` and at least two distinct prime divisors;
- at most one prime divisor among all primes through `R_N`.

The `(6/7)^N` Fourier region, complete centered complex products,
and odd-reflection identity are retained. Their actual carriers satisfy

\[
\operatorname{Re}C_N=-2W_N,\qquad
u^{N+1}C_N\to-m_\rho,\qquad u^{N+1}W_N\to m_\rho/2.
\]

The finite signed comparison with the original pole-jet response has
the entire allowance

\[
\frac{C_1(1+N^4)(\sqrt u)^N+C_2\lambda^N+
\operatorname{zetaAveragedWindowError}(p_\rho,N,\operatorname{Im}\rho)}2
\longrightarrow0.
\]

All original head, prime-power, prime-pattern, square-overlap, physical,
and complementary-frequency errors appear in this comparison.

[ZetaSquarefreeWindowSource.lean](../RiemannGaussian/ZetaSquarefreeWindowSource.lean)
proves `zetaRightHalfSquarefreeWindowCoefficient_support`,
`tendsto_zetaRightHalfSquarefreeWindowReflectionWork`,
`exists_zetaRightHalfSquarefreeWindowReflection_error_bound`, and
`tendsto_zetaRightHalfSquarefreeWindowTotalError`.

The next task is an independent strict bound below `m_rho/2` for
this squarefree signed survivor at arbitrarily late orders. Removing
repeated primes does not establish that bound: squarefree products
still retain the full source. No additional zeros are excluded by
this slice; the [all-height edge strip](zeta-completion-reserve-zero-free.md)
remains unchanged and RH is open.
