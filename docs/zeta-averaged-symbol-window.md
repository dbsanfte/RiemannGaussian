# Averaging the Fourier symbol while preserving the whole zeta source

Lean proves a smaller frequency region for the full signed arithmetic
source associated with any hypothetical right-half zeta zero. The new
estimate applies to every moving complex coefficient family dominated by
the divisor-log majorant. The actual cubic sieve and logarithmic window
remain in place, and every discarded contribution has an independently
vanishing allowance. The signed bound inside the retained region remains
open; this result excludes no additional zeros.

The next [joint divisor-factor estimate](zeta-lcm-window-factor-bound.md)
uses this same physical window to remove the cutoff growth cost for every
large factor's full arithmetic response. It leaves the complete signed
source here unchanged; control of the collective surviving interaction
remains open.

## The general inverse-symbol estimate

For any positive cyclic modulus `q`, write

\[
\sigma(k)=e^{2\pi i k/q}-1.
\]

For every frequency set `S` with `|sigma(k)|>=delta>0`, Lean proves

\[
\frac1q\sum_{k\in S}|\sigma(k)|^{-2}\le\frac2\delta.
\]

The proof retains the actual distribution of frequencies. Pairing
opposite modes and applying the sine chord bound gives
`|sigma(k)|>=4*k/q` in the positive half-cycle. Splitting at
`floor(q*delta/4)` and summing the inverse-square tail gives a bound
uniform in `q`, including the trivial cyclic group. The positive gap
excludes the zero symbol before division.

For the repository's unnormalized DFT and centered interaction

\[
\mathcal C_S(a,f)=\frac1q\sum_{k\in S}
  [\widehat a(-k)-\widehat a(0)]\widehat f(k),
\]

the exact second-difference identity then proves

\[
|\mathcal C_S(a,f)|\le
\frac4\delta\|a\|_1\|\Delta^2 f\|_1.
\]

Both terms of the centering correction are paid for. The preceding
worst-gap estimate used an inverse-square gap cost. Averaging the actual
inverse symbols reduces that cost to one inverse power. The exact
centered complex products remain available upstream.

Compiled entry points in
[FiniteFourierSymbolMass.lean](../RiemannGaussian/FiniteFourierSymbolMass.lean):

- `four_mul_val_div_le_norm_cyclicDifferenceSymbol`
- `sum_inv_sq_cyclicDifferenceSymbol_le`
- `norm_finiteFourierPart_le_inverseSymbolMass`
- `norm_centeredFourierPart_le_averaged_gap`

## A continuum of admissible rates for all coefficient families

On the physical window `2*N/5<=log(n)<=8*N`, the actual coefficient
weight `n^(-5/4)` has an additional exponential saving relative to the
summable majorant at `9/8`. For every complex family `|a_N(n)|<=M(n)`,

\[
\|a_N^{\mathrm{window,weighted}}\|_1
\le (20/21)^N M_{9/8},
\qquad M_{9/8}=\sum_n M(n)n^{-9/8}.
\]

The existing complete kernel second-difference bound contains interior
rate `8/9` and cyclic-boundary rate `1/2`. With threshold `delta=r^N`,
the new complementary interaction consequently tends to zero whenever

\[
r>\frac{20}{21}\frac89=\frac{160}{189}.
\]

This is a sufficient analytic criterion for all dominated moving
families, with no coefficient tuning. A shrinking threshold additionally
uses `r<1`. The concrete choice `r=6/7` gives exact rational error rates

\[
\frac{20}{21}\frac76\frac89=\frac{80}{81},\qquad
\frac{20}{21}\frac76\frac12=\frac59.
\]

All constants are checked in Lean. No optimality of this threshold or
criterion is claimed. The selected modes obey

\[
\{k:|\sigma(k)|<(6/7)^N\}
\subseteq\{k:|\sigma(k)|<(14/15)^N\}.
\]

The full arithmetic filter differs from its centered window interaction
on the smaller region by at most

\[
E^{\mathrm{avg}}_{p,N,y}
=E^{\mathrm{window}}_{p,N}
 +4M_{9/8}G_{p,N,y}(20/21,6/7)\longrightarrow0.
\]

Here `G` is `zetaQuarterAveragedGapError`; it contains both frequency
error rates with their full constants. `E_window` retains both original
physical-shell errors. The decomposition is exact before taking norms.

Compiled entry points in
[ZetaAveragedResonance.lean](../RiemannGaussian/ZetaAveragedResonance.lean):

- `sum_norm_zetaArithmeticWindowSamples_le`
- `tendsto_zetaArithmeticWindowCenteredPart_compl`
- `zetaAveragedResonantModes_subset`
- `zetaQuarterAveragedGapError_six_sevenths_eq`
- `norm_zetaArithmeticFilter_sub_averaged_window_le`
- `tendsto_zetaAveragedWindowError`

## The actual source and complete finite comparison

Apply this estimate to the unchanged
[cubic-sieved coefficients](zeta-mobius-scale-sieve.md). For a hypothetical
right-half zero `rho`, let `u=3/2-Re(rho)` and let `m_rho` be its analytic
multiplicity. Every surviving product remains in the logarithmic window,
exceeds `D_N^2`, and obeys the larger sieve's prime-pair restriction.
The complex carrier `C_N` uses the original full centered products on the
smaller frequency region; `W_N` is its exact odd real reflection work.
Lean proves

\[
\operatorname{Re}C_N=-2W_N,\qquad
u^{N+1}C_N\longrightarrow-m_\rho,\qquad
u^{N+1}W_N\longrightarrow m_\rho/2.
\]

The comparison with the original pole-jet response `L_N`, for every
`N>=2`, retains the entire allowance:

\[
\left|-\frac{u^{N+1}\operatorname{Re}L_N}{2}-u^{N+1}W_N\right|
\le\frac12\left[C_1(\sqrt u)^N+C_2(u^{1/8})^N+
E^{\mathrm{avg}}_{p,N,\operatorname{Im}\rho}\right]
\longrightarrow0.
\]

The original head and prime-power errors, cubic sieve overlaps, both
physical shells, both centering terms, and cyclic boundary costs are
all included. No independent arithmetic bound is assumed to obtain this
source transfer or its finite comparison.

Compiled entry points in
[ZetaAveragedWindowSource.lean](../RiemannGaussian/ZetaAveragedWindowSource.lean):

- `tendsto_zetaRightHalfAveragedWindowFourierCarrier`
- `zetaRightHalfAveragedWindowFourierCarrier_re_eq_reflection`
- `tendsto_zetaRightHalfAveragedWindowReflectionWork`
- `exists_zetaRightHalfAveragedWindowReflection_error_bound`
- `tendsto_zetaRightHalfAveragedWindowTotalError`

The remaining goal is an independent strict inequality
`u^(N+1)*W_N<=m_rho/2-epsilon` for some fixed `epsilon>0` at arbitrarily
late orders. Shrinking the frequency region does not itself prove that
inequality: the entire hypothetical-zero source survives inside it.
The next arithmetic estimate must use the joint divisor restrictions and
phases in the retained correlation, before a triangle bound discards them.

The [all-height zero-free edge region](zeta-completion-reserve-zero-free.md)
is unchanged. RH remains open.
