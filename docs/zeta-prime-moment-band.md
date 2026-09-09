# The remaining source is a finite signed ordinary-prime band

The [exact zero-mode filter](zeta-zero-mode-filters.md) has now been
combined with two independent arithmetic estimates. Proper prime powers
vanish at every off-critical source scale, and both tails of the remaining
ordinary-prime log-moment sum have an explicit geometric bound. The
surviving carrier is one finite sum over ordinary primes, retaining its
complex coefficients, phases, and factorial normalization.

The independent lower bound on this finite band's signed value is still
open. This slice excludes no new zero and does not prove RH. Its tail
estimates use standard exponential-series and Chebyshev tools, and no
claim of mathematical priority is made.

The subsequent [signed Abel transport](zeta-prime-band-chebyshev.md)
places this same source inside a Chebyshev-error integral, with independent
geometric control of its continuous background and both finite endpoints.

## The arithmetic envelope

For moment order `j`, exponent `s`, and integer `m`, define

\[
K_j(s,m)=\frac{(\log m)^j}{j!}\exp(-s\log m).
\]

`norm_zetaPrimeLogKernel_le` proves, for every real `q>0`,

\[
\boxed{|K_j(s,m)|\le q^{-j}m^{-(\Re s-q)}.}
\]

The statement uses exponential weights at `m=0`; the actual arithmetic
coefficient there is zero. It follows from the positive exponential series
inequality `(q log m)^j/j! <= exp(q log m)`. The full complex kernel remains
defined separately. The envelope is applied to omitted arithmetic terms,
not to the retained signed band.

## All proper prime powers are independently negligible

Let

\[
a(m)=\begin{cases}0,&m\text{ prime},\\\Lambda(m),&\text{otherwise}.
\end{cases}
\]

The existing theorem `chebyshevPsi_sub_theta_le_eighteen_sqrt` gives

\[
\sum_{m\le X}a(m)=\psi(X)-\theta(X)\le18\sqrt X\quad(X\ge1).
\]

`LSeriesSummable_zetaProperPrimePower` consequently proves absolute
convergence of the actual proper-prime-power Dirichlet series for
`Re s>1/2`, including all higher log moments. Write

\[
A(\sigma)=\sum_{m\ge1}a(m)m^{-\sigma}<\infty\quad(\sigma>1/2).
\]

For any fixed polynomial `P(X)=sum p_k X^k`, its proper-prime-power filter
at `s0=3/2+iy` obeys the independent, ordinate-uniform bound

\[
\boxed{
|F^{\rm powers}_{P,N}(s_0)|
\le q^{-N}A(3/2-q)\sum_k|p_k|q^{-k}\qquad(0<q<1).
}
\]

Thus for every complex `a` with `|a|<1`,

\[
a^{N+1}F^{\rm powers}_{P,N}(s_0)\longrightarrow0.
\]

This is proved in `tendsto_zetaProperPrimePowerFilter_mul_pow`. It uses no
zero hypothesis. For a selected zero with `u=3/2-beta<1`, choose `u<q<1`:
the error can grow unnormalized but is strictly smaller than the source
`u^(-N)`. No full absolute decay of this proper-power term is asserted.

The exact theorem `zetaPrimeLogFilter_eq_prime_add_proper` retains both
arithmetic components before using this estimate. The selected negative
multiplicity limit therefore passes to ordinary primes in
`tendsto_zetaRightHalfOrdinaryPrimeLogFilter`.

## Two explicit geometric tail bounds

Define the finite integer band

\[
\mathcal B_N=
\{m\in\mathbb N:1\le m\le2^{32N},\quad
 N\log2/4<\log m\}.
\]

The endpoints are intentionally generous. No optimality is claimed.
Every omitted positive integer belongs to one of the following two tails,
with all endpoint cases included in the checked definitions.

`norm_zetaPrimeLogKernel_le_lower_band` proves

\[
\log m\le N\log2/4
\quad\Longrightarrow\quad
|K_{N+k}(3/2+iy,m)|\le2^{-N}4^{-k}m^{-3/2}.
\]

`norm_zetaPrimeLogKernel_le_upper_band` proves

\[
\log m\ge32N\log2
\quad\Longrightarrow\quad
|K_{N+k}(3/2+iy,m)|\le2^{-N}8^k m^{-5/4}.
\]

Both inequalities are uniform in `y`. Set

\[
D(\sigma)=\sum_{m\ge1}\Lambda(m)m^{-\sigma},\qquad
C(P)=\sum_k|p_k|\bigl(4^{-k}D(3/2)+8^kD(5/4)\bigr).
\]

All defining series genuinely converge. For the complete ordinary-prime
filter and its retained finite band, Lean proves

\[
\boxed{|F^{\rm primes}_{P,N}(3/2+iy)-B_{P,N}(y)|\le C(P)2^{-N}.}
\]

This is `norm_zetaOrdinaryPrimeLogFilter_sub_band_le`. The omitted
ordinary-prime tails tend to zero even without source normalization. The
constant depends on the fixed polynomial and is independent of height.

## The literal finite arithmetic target

`zetaOrdinaryPrimeBandFilter_eq_prime_sum` identifies the retained object as

\[
\boxed{
B_{P,N}(y)=
\sum_{\substack{p\in\mathcal B_N\\p\ {m prime}}}
 \frac{\log p}{p^{3/2+iy}}
 \sum_k p_k\frac{(\log p)^{N+k}}{(N+k)!}.
}
\]

Here the summation variable `p` is a prime, while `p_k` denotes a
coefficient of the fixed polynomial `P`. The finite band expands with `N`;
this is not a certificate based on a fixed prime prefix.

For every actual `rho=beta+i*gamma` with `beta>1/2`, take its exact
zero-isolating polynomial `P_rho` and `u=3/2-beta`. The terminal theorem
`tendsto_zetaRightHalfOrdinaryPrimeBandFilter` proves

\[
\boxed{u^{N+1}B_{P_\rho,N}(\gamma)\longrightarrow-m(\rho).}
\]

Its real-part consequence
`zetaRightHalfOrdinaryPrimeBandFilter_eventually_negative` proves

\[
\boxed{\Re B_{P_\rho,N}(\gamma)
<-\frac{m(\rho)}{2u^{N+1}}\quad\text{for all sufficiently large }N.}
\]

All omitted analytic terms, reflected modes, proper prime powers, and
ordinary-prime tails have now been controlled at the source scale for this
carrier. The proof does not require a uniform inverse-Vandermonde bound,
but neither does it give an effective uniform onset in zero height or
spacing. The filter coefficients depend on the actual local zero divisor.

## What remains toward the goal

The required independent estimate is a lower bound for this exact signed
finite prime sum that contradicts the displayed negative limit. A uniform
sub-source bound would suffice; full power saving is not required. None of
the proved positive tail estimates is such a bound for the retained band.

The next arithmetic attack should operate on the band's complete factorial
log kernel and retain correlations between its prime phases. The repo's
mixed Gram, Gaussian Abel, and Moebius identities may provide ways to
rewrite this carrier, but their existing positivity or absolute estimates
do not presently supply the missing signed lower bound. The original goal
remains active, and the separate Suzuki arithmetic decay gap is unchanged.

## Validation

The slice comprises `ZetaPrimeMomentEnvelope.lean`,
`ZetaPrimePowerMoments.lean`, and `ZetaPrimeMomentBand.lean`, all imported by
the root library. Direct warning-as-error checks passed. Focused/full
builds passed with 4,277 and 9,796 jobs respectively. Whole-package and
module declaration lint passed. A root-import audit of all 34 public
theorems found only `propext`, `Classical.choice`, and `Quot.sound`. Source
and whitespace checks passed. Commits and remote CI remain held at the
user's request.
