# Retaining divisor scale enlarges the actual arithmetic sieve

Lean improves the complete multiple-sector cost from `D` to a constant
times `sqrt(D)`. The saving applies to the original convergent arithmetic
sum, uniformly over every positive mixed-prime factor, every moment order,
and every fixed polynomial filter. It allows a cubic overlap budget at
the unchanged divisor cutoff and supplies an explicit larger sieve.

The full signed source survives that sieve, the smaller logarithmic
window, and the retained Fourier region together. The new error allowance
tends to zero. The independent bound for the surviving correlation is
still open, and no additional zeta zeros are excluded by this slice.

The [averaged-symbol extension](zeta-averaged-symbol-window.md) keeps
this same cubic sieve and physical window while reducing the retained
Fourier threshold to `(6/7)^N`. Its complete source comparison includes
the arithmetic errors proved here and the improved frequency allowance.

## The scale that the preceding estimate discarded

For a head divisor `d>=1` and factor `P>=1`, put

\[
L=\operatorname{lcm}(d,P),\qquad R=\log L-\log d\ge0.
\]

Lean preserves the exact complex identity

\[
e^{-s\log L}=e^{-s\log d}e^{-sR}.
\]

The preceding factor-independent estimate paid for the whole logarithm
using the entire physical weight, then bounded each divisor contribution
by a constant. Keeping `exp(-s*log d)` separately gives, on `Re(s)>=1/2`,

\[
|e^{-s\log d}|\le d^{-1/2},\qquad
|e^{-s\log L}|R\le2d^{-1/2}.
\]

The second inequality uses `R*exp(-R/2)<=2`, with the divisor weight
still present. The full reciprocal-square-root prefix satisfies

\[
\sum_{1\le d\le D}d^{-1/2}\le2\sqrt D.
\]

That telescoping inequality was already used in the repository's
Chebyshev/Möbius argument. It is now a documented reusable theorem,
`sum_inv_sqrt_Icc_le`, without changing its proof or the existing
Chebyshev statements.

The actual signed multipliers of `-zeta'` and `zeta` consequently obey

\[
|A_{D,P}(s)|\le2\sqrt D,\qquad |B_{D,P}(s)|\le4\sqrt D.
\]

The richer multipliers and their phases remain defined upstream. These
norm bounds are companion estimates on pieces being deleted, not a
replacement for the surviving signed arithmetic.

Compiled entry points:

- [ChebyshevMoebiusCancellation.lean](../RiemannGaussian/ChebyshevMoebiusCancellation.lean):
  `sum_inv_sqrt_Icc_le`.
- [ZetaMoebiusScaleBound.lean](../RiemannGaussian/ZetaMoebiusScaleBound.lean):
  `zetaPrimeFeature_lcm_eq_offset`,
  `norm_zetaPrimeFeature_lcm_mul_offset_le`,
  `norm_zetaMoebiusMultipleMultipliers_le_sqrt`, and
  `exists_zetaMoebiusMultipleFamily_sqrt_bound`.

## A bound for all complex factor families

The existing Cauchy argument transfers the multiplier estimate to the
full filtered arithmetic response. For each fixed ordinate `|y|>1`, one
constant `C_y` gives

\[
\left|\sum_{P\in S}w_P\sum_n c_{D,P}(n)k_{p,N}(3/2+iy,n)\right|
\le C_y\sqrt D\,\|p\|_1\sum_{P\in S}|w_P|.
\]

Here `c_{D,P}` is the literal Möbius-tail coefficient on multiples of
`P`; every factor is positive and has at least two distinct prime factors.
All arithmetic series are genuinely summable. The factors may overlap,
vary with the moment order, and have arbitrary size and prime valuations.
The weights may be any complex numbers. No coefficient search is involved.

For a hypothetical right-half zero, put `u=3/2-Re(rho)` and retain the
original schedule `D_N=floor(q^N)`, `q=u^(-1/4)`. If the whole family has
coefficient mass at most `D_N^3`, then

\[
u^{N+1}\sqrt{D_N}\,D_N^3
\le u\bigl(u\sqrt q\,q^3\bigr)^N
=u\bigl(u^{1/8}\bigr)^N.
\]

Lean checks that exact rate and `0<u^(1/8)<1`. Thus the **entire cubic
family budget** has an independently vanishing error. This extends the
previously implemented linear family budget. It is not a claim that the
preceding linear schedule was optimal, or that the new cubic schedule is.

## The larger sieve is fully discharged

Use every eligible mixed-prime factor below

\[
H_N=\lfloor\log_2(D_N^3)\rfloor.
\]

The complete grouped inclusion-exclusion cost is at most `D_N^3`.
Consequently the uniform cubic-family theorem applies to the actual
union, including every overlap. No cost hypothesis remains unproved for
this chosen sieve. Integer rounding is retained:

\[
3\lfloor\log_2 D_N\rfloor\le H_N.
\]

Each surviving product has no mixed-prime divisor below `H_N`. In
particular, every pair of distinct prime divisors has product at least
`H_N`. One prime may still be small; both primes are not separately
bounded below by `H_N`.

Compiled entry points in
[ZetaMoebiusCubicSieve.lean](../RiemannGaussian/ZetaMoebiusCubicSieve.lean):

- `exists_zetaRightHalfMoebiusMultipleFamily_cubic_bound`
- `zetaMoebiusHeadGrowth_sqrt_cubic_rate`
- `zetaRightHalfCubicSieve_budget`
- `three_mul_natLog_le_natLog_cube`
- `tendsto_zetaRightHalfCubicSieve`
- `tendsto_zetaRightHalfCubicSievedPrimeTail`

## The complete signed comparison remains intact

Apply the earlier localization to these actual coefficients. The retained
indices still satisfy `2*N/5<=log(n)<=8*N` and `D_N^2<n`. All centered
Fourier products and cyclic reflection partners remain. If `C_N` is the
full retained complex interaction and `W_N` its odd real reflection work,
Lean proves

\[
\operatorname{Re}C_N=-2W_N,\qquad
u^{N+1}C_N\longrightarrow-m_\rho,\qquad
u^{N+1}W_N\longrightarrow m_\rho/2.
\]

The comparison with the original pole-jet response `L_N` has one finite
bound, for every `N>=2`:

\[
\left|-\frac{u^{N+1}\operatorname{Re}L_N}{2}-u^{N+1}W_N\right|
\le\frac12\left[C_1(\sqrt u)^N+C_2(u^{1/8})^N+
E_{p,N}+F_{p,N,\operatorname{Im}\rho}\right].
\]

Here `C_1` pays for the original head and prime-power removal, `C_2` pays
for the larger sieve, and `E+F` is the already proved complete physical
shell and complementary Fourier allowance. **The entire allowance tends
to zero.** The larger sieve decays more slowly; its rate still suffices
for comparison with any fixed source gap.

Compiled entry points in
[ZetaCubicWindowSource.lean](../RiemannGaussian/ZetaCubicWindowSource.lean):

- `zetaRightHalfCubicWindowCoefficient_support`
- `tendsto_zetaRightHalfCubicWindowFourierCarrier`
- `zetaRightHalfCubicWindowFourierCarrier_re_eq_reflection`
- `tendsto_zetaRightHalfCubicWindowReflectionWork`
- `exists_zetaRightHalfCubicWindowReflection_error_bound`
- `tendsto_zetaRightHalfCubicWindowTotalError`

The remaining goal is an independent inequality
`u^(N+1)*W_N<=m_rho/2-epsilon`, for some fixed positive `epsilon` at
arbitrarily late orders. The sieve threshold still grows only linearly
with `N`, while the retained product indices grow exponentially. The
larger deletion does not exhaust that support or establish its sign.
The next arithmetic estimate must use the surviving prime-pair
restriction and separated divisor ranges with the full product phases
retained. Dropping those restrictions can restore prime-power terms that
carry the source.

The [all-height zero-free edge region](zeta-completion-reserve-zero-free.md)
is unchanged. The global signed bound and RH remain open.
