# The full signed source in a smaller arithmetic window

Lean now proves that the actual sieved source can be confined to

\[
\frac25N\le\log n\le8N.
\]

Both omitted physical shells have independent geometric bounds. The
original cofinal sieve, centered Fourier products, and exact odd-reflection
identity survive together. The complete source still remains inside the
window; its independent strict upper bound is open. Localization alone
excludes no additional zeta zeros.

## General exponential tilting

The actual complex logarithmic kernel is

\[
k_{N+k}(s,n)=\frac{(\log n)^{N+k}}{(N+k)!}e^{-s\log n}.
\]

The existing exponential-series inequality, with any positive tilt `q`,
gives

\[
|k_{N+k}(s,n)|\le q^{-(N+k)}e^{-(\operatorname{Re}s-q)\log n}.
\]

Retain an arbitrary reference weight `exp(-tau*log n)`. If
`(q+tau-Re(s))*log n <= A*N`, then

\[
|k_{N+k}(s,n)|
\le(q^{-1}e^A)^Nq^{-k}e^{-\tau\log n}.
\]

For a positive logarithmic endpoint `v`, taking `q=1/v` gives the
Chernoff rate

\[
r(v) = v\exp\bigl(1-(\operatorname{Re}s-\tau)v\bigr).
\]

It controls a lower shell when `(Re(s)-tau)*v<=1` and `log n<=v*N`;
it controls an upper shell when `(Re(s)-tau)*v>=1` and `v*N<=log n`.
The parameter theorem keeps the endpoint, reference abscissa, and moment
offset available for other windows. It does not select phase coefficients.

These are estimates on discarded pieces. The complex kernel and all its
phases remain unchanged inside the retained arithmetic sum.

## A concrete window with genuine arithmetic convergence

At the actual sampling line `Re(s)=3/2`, choose the reference abscissa
`tau=17/16>1`. The original nonnegative divisor-logarithm majorant `M(n)`
has a proved finite mass

\[
\mathcal M=\sum_n M(n)e^{-(17/16)\log n}.
\]

Lean proves the two kernel bounds

\[
\begin{aligned}
\log n\le\tfrac25N&\implies
|k_{N+k}(3/2+iy,n)|
\le(15/16)^N(1/2)^k e^{-(17/16)\log n},\\
8N\le\log n&\implies
|k_{N+k}(3/2+iy,n)|
\le(3/4)^N8^k e^{-(17/16)\log n}.
\end{aligned}
\]

The lower estimate uses `q=2`, and the upper estimate uses `q=1/8`.
Exact logarithmic inequalities discharge the rational rate bounds in Lean.
Both estimates are uniform in the ordinate.

For any complex coefficient sequence with `|a(n)|<=M(n)`, restrict its
coefficients to the window and leave every retained value unchanged. For
the full polynomial filter `p`, the complete difference is bounded by

\[
E_{p,N}=\sum_{k\in\operatorname{supp}p}|p_k|\,
\bigl[(15/16)^N(1/2)^k+(3/4)^N8^k\bigr]\mathcal M.
\]

Every infinite series is genuinely summable. Lean proves `E_{p,N}->0`,
including every polynomial coefficient and offset moment. Arbitrarily
moving coefficient families, divisor cutoffs, and arithmetic sieves are
allowed under the same pointwise majorant, with `p` and `y` fixed in each
limit.

At positive orders the new window lies inside the preceding finite band
`N*log(2)/4 < log n <= 32*N*log(2)`. Thus the new arithmetic is a genuinely
finite restriction, with upper product index at most `exp(8*N)`. The shell
rates are slower than the preceding broader-band rate; their decay still
suffices for the source comparison. No stronger decay rate is claimed.

Compiled entry points:

- [ZetaLogMomentTilt.lean](../RiemannGaussian/ZetaLogMomentTilt.lean):
  `norm_zetaPrimeLogKernel_le_tilt`,
  `norm_zetaPrimeLogKernel_le_lower_chernoff`,
  `norm_zetaPrimeLogKernel_le_upper_chernoff`, and the two concrete window bounds.
- [ZetaLogWindowLocalization.lean](../RiemannGaussian/ZetaLogWindowLocalization.lean):
  `norm_zetaArithmeticFilter_sub_window_le`,
  `tendsto_zetaArithmeticFilter_sub_window`,
  `zetaLogWindow_subset_band`, and `zetaArithmeticFilter_window_eq_band`.

## The original source and all Fourier products coexist

For a hypothetical right-half zero `rho=beta+i*gamma`, set `u=3/2-beta`.
Restrict the actual sieved coefficient to the new window, retaining the
same geometric divisor cutoff, cofinal sieve, pole-jet filter, cyclic
modulus, and Fourier region `|chi(k)-1|<(14/15)^N`.

Let `C_N` be this full centered Fourier interaction and `W_N` its exact
odd real reflection work. Lean proves

\[
\operatorname{Re}C_N=-2W_N,\qquad
u^{N+1}C_N\longrightarrow-m_\rho,\qquad
u^{N+1}W_N\longrightarrow m_\rho/2.
\]

The physical expansion contains only distinct-prime products in the
smaller window which survive the original sieve. Each retains its full
signed Möbius coefficient and centered Fourier weight. All cyclic
reflection partners of the physical profile remain in the inner sum;
only the arithmetic row index is restricted.

If `L_N` denotes the original pole-jet response, one positive constant `C`
gives, for every `N>=2`,

\[
\left|-\frac{u^{N+1}\operatorname{Re}L_N}{2}
-u^{N+1}W_N\right|
\le\frac12\left[C(\sqrt u)^N+E_{p,N}+F_{p,N,\gamma}\right],
\]

where `F` is the already proved whole complementary-frequency allowance.
Lean proves the **entire displayed allowance tends to zero**, including
the sieve error and both shell errors. No new arithmetic premise is hidden
inside this error.

Compiled entry points in
[ZetaSievedLogWindow.lean](../RiemannGaussian/ZetaSievedLogWindow.lean):

- `norm_zetaArithmeticFilter_sub_window_fourier_le`
- `zetaRightHalfWindowFourierCarrier_eq_physical`
- `tendsto_zetaRightHalfWindowFourierCarrier`
- `tendsto_zetaRightHalfWindowReflectionWork`
- `exists_zetaRightHalfWindowReflection_error_bound`
- `tendsto_zetaRightHalfWindowTotalError`

## The complementary head has only large cofactors

Let `D_N=floor(u^(-N/4))` be the unchanged moving divisor cutoff.
For every positive order and every product in the new window, Lean proves

\[
D_N^2<n.
\]

The proof retains the actual cutoff schedule: `u>1/2` implies
`D_N^2<=(10/7)^N`, while `log(10/7)<2/5`. In particular, if `d|n` and
`d<=D_N`, then `n/d>D_N`.

This becomes useful when combined with the existing complete divisor
identity. Every surviving integer has at least two distinct prime factors,
so its full von Mangoldt coefficient vanishes. Its actual sieved window
coefficient is therefore exactly

\[
-\sum_{\substack{1\le d\le D_N\\d\mid n,\ n/d>D_N}}
\mu(d)\log(n/d).
\]

The original tail already restricts its Möbius divisor to be large. The
new separation also applies to this **complementary head**: every small
divisor is paired with a large cofactor. Substituting the identity into
the physical carrier keeps its complete complex weight on the product
`n`, including all centered Fourier products and reflection partners.
The cofactor restriction follows from the proved window; it incurs no
additional error and supplies no cancellation estimate by itself.

Compiled entry points in
[ZetaSievedLogWindow.lean](../RiemannGaussian/ZetaSievedLogWindow.lean):

- `zetaLogWindow_gt_moebiusCutoff_sq`
- `zetaLogWindow_factor_gt_moebiusCutoff`
- `zetaLogWindow_quotient_gt_moebiusCutoff`
- `zetaRightHalfWindowCoefficient_eq_neg_prefix`

## Remaining goal

The required independent inequality remains
`u^(N+1)*W_N <= m_rho/2-epsilon` for some fixed positive `epsilon` at
arbitrarily late orders. The proved localization removes both outer
arithmetic shells from this obligation. The exact complementary-head form
now separates its divisor and cofactor ranges. The required signed
cancellation between those ranges is still open.

The [all-height zero-free edge region](zeta-completion-reserve-zero-free.md)
remains unchanged. The strict signed bound for every remaining right-half
zero, and RH itself, remain open.

The subsequent [divisor-scale estimate](zeta-mobius-scale-sieve.md) lowers
the complete multiple-sector cost to a square-root cutoff and justifies
a larger simultaneous sieve in this same physical window. The full source
and its vanishing total error remain together after that further deletion.
