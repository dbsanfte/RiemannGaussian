# Bounded prefix components and a narrower signed carrier

Lean independently bounds two components of the completed prime prefix
and both outer portions of the actual Riesz carrier. The remaining
arithmetic sum retains its complete hypothetical-zero source. The
independent whole-sum lower bound, and RH, remain open.

Use the unchanged definitions

$$
 u=\frac32-\beta,\qquad
 D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
 X_N=(D_N+2)^2,\qquad L_N=\log X_N,
$$

and the original factorial filter

$$
 K_{P,N}(s,n)=n^{-s}\sum_jP_j\frac{(\log n)^{N+j}}{(N+j)!},
 \qquad s=\frac32+iy.
$$

Every bound below is for a fixed polynomial $P$, uniformly in $y$ and
the indicated finite selections. It retains the actual floor and all
factorial shifts. No hypothetical-zero premise is used in the estimates.

## Two prefix components are now paid

The completed head $H_N$ from the
[annular completion](zeta-riesz-annulus-prime-completion.md) introduces
the finite prefix

$$
 B_N=-\sum_{N^2<a<X_N\atop a\text{ prime}}\frac{\log a}{L_N}
       \sum_{p<X_N\atop p\text{ prime}}\log(ap)K_{P,N}(s,ap).
$$

The diagonal $p=a$ has precisely one incidence. Its coefficient is at
most $2\log a$ in absolute value. Genuine summability of the prime-square
mass gives

$$
 |u^{N+1}B_N^{\rm diag}|
 \le C_{\rm diag}(P,u)\left(\frac{2u}{u+1}\right)^N\longrightarrow0
 \qquad(0<u<1).
$$

See [`norm_normalized_diagonalResponse_le` and
`tendsto_diagonalResponse`](../RiemannGaussian/ZetaRieszPrefixDiagonal.lean).

The mixed class $p\le N^2<a<X_N$ also has exactly one selected cofactor
incidence per integer. Its weight is the **intermediate-prime** mark
$-\log(ap)\log(a)/L_N$, which is bounded in norm by $\log(ap)$.
Since $ap\le N^2X_N$, a general physical-prefix estimate proves

$$
 |u^{N+1}B_N^{\rm mixed}|
 \le C_{\rm mix}(P,u,q)(N+1)^3r(u,q)^N,
 \qquad r(u,q)=\frac{\exp((2-2q)\log u)}q.
$$

For $1/2<u<\exp(-1/2)$, the mathematically defined tilt
$q=1/(-2\log u)$ lies in $(1/2,1]$ and satisfies $r(u,q)<1$.
This pays the mixed class for every changing selected intermediate-prime
family. It does not replace the mark by a small-prime logarithm.
See [`norm_mixedResponse_le` and
`tendsto_mixedResponse`](../RiemannGaussian/ZetaRieszMixedPrefix.lean).

Exact disjoint integer partitions connect both deletions to the whole
carrier. [`tendsto_refinedJoint_exposed`](../RiemannGaussian/ZetaRieszMixedPrefixTransport.lean)
preserves the entire source on the existing annular range
$1/2<u<\exp(-2/3)$. The wider mixed-component estimate does not extend
the range of prime completion.

## The remaining prime-pair correction is explicit

After those deletions, every nonzero prefix label is a product of two
distinct intermediate primes. The two cofactor incidences at the same
integer add to $-(\log n)^2/L_N$. Both incidences are retained, while
the integer response counts $n$ once; there is no omitted diagonal or
unordered-pair factor. See
[`remainingPrefix_eq_log_square_sum`](../RiemannGaussian/ZetaRieszRemainingPrefix.lean).

Let $\mathcal P_N$ be these distinct-prime integer products, and $U_N$
the original all-subcutoff carrier with $\mathcal P_N$ removed. Lean
checks all earlier support masks above $X_N$; below $X_N$ the original
Riesz coefficient is exactly zero. Consequently, eventually the full
refined carrier is

$$
 J_N=H_N+U_N+
 \sum_{n\in\mathcal P_N}\log n\min\!\left(1,\frac{\log n}{L_N}\right)K_{P,N}(s,n).
$$

This is [`eventually_refinedJoint_eq_clipped_split`](../RiemannGaussian/ZetaRieszPairedCorrection.lean).
The clipped coefficient is nonnegative, but the product phase remains
signed. This identity does not bound the sum of these three components.

## The actual carrier has a smaller central window

For every $0<u<\exp(-2/3)$, all divisor-majorized coefficients outside

$$
 \frac32N<\log n\le\frac83N
$$

have the independent source-normalized allowance

$$
 uA(P,2/3,257/256)\,r_-^N+
 uA(P,3/8,257/256)\,r_+^N,
$$

$$
 r_-=\frac32\exp(-631/1536)<1,
 \qquad r_+=\frac83\exp(-95/96)<1.
$$

Here $A(P,q,\sigma)$ is the existing fixed-filter cost times the genuinely
convergent divisor-log mass. The bound applies to arbitrary changing finite
coefficient masks, including the original Riesz coefficient, regardless of
prime-factor count. See
[`norm_sub_centralBand_le`](../RiemannGaussian/ZetaRieszCentralWindow.lean).

The new actual support is the intersection of this central window with
the physical annulus and **every previous arithmetic restriction**.
[`tendsto_centralAnnulus_exposed`](../RiemannGaussian/ZetaRieszCentralWindow.lean)
proves that its constant-filter normalized response still tends to
$-m_\rho$ at exposed zeros in the annular source range. No previous
fallback outside that range is superseded.

## Remaining obligation and verification

The central signed Riesz sum still needs an independent cofinal lower
floor at least $-c$ for some $c<1$. In the completed representation,
the completed head $H_N$, the unpaired subcutoff response $U_N$, and the
explicit prime-pair correction require their **joint** phase control.
The [central prime-layer refinement](zeta-riesz-central-prime-layers.md)
now proves that transport with error at most twice the displayed allowance,
while keeping the head whole. It also identifies the exact central pair
weight and bounds the actual three-prime coefficients. No separate decay
of the three surviving sums is asserted.

The component decay rates do not give a numerical starting order, a
new zero-free region, or RH. All eight modules belong to the arithmetic
family and are imported by the ordinary root. The supporting explorer
endpoint is `prefix-central-window`; the default whole-carrier frontier
and the two ten-entry README lists are unchanged. The ordinary build,
declaration lint, transitive axiom audit and dependency export check these
proofs without rerunning the exhaustive numerical certificate.
