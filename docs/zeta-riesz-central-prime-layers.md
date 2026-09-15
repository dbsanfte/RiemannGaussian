# The central carrier and its three-prime sign bound

The complete prime representation now admits the independently bounded
central-window restriction, while its infinite prime head stays whole.
Every surviving three-prime coefficient has a proved nonnegative sign
and two explicit amplitude bounds. The joint source-scale lower floor
remains open; these results do not enlarge the proved zero-free region.

Keep the physical quantities and original filter from the
[prefix and central-window bounds](zeta-riesz-prefix-central-window.md):

$$
 D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\quad
 X_N=(D_N+2)^2,\quad L_N=\log X_N,\quad
 K_{P,N}(s,n)=n^{-s}\sum_j P_j\frac{(\log n)^{N+j}}{(N+j)!},
 \qquad s=\frac32+iy.
$$

All independent transport estimates below hold for each fixed polynomial
$P$ and uniformly in $y$. The complete representation is used on
$1/2\le u<\exp(-2/3)$. Other source scales retain their earlier fallback
regimes; an estimate in this interval alone does not prove RH.

## The central transport keeps the complete head

The earlier exact representation consists of the completed prime head
$H_N$, the unpaired subcutoff response $U_N$, and the clipped pair
correction $Q_N$. Restrict only the latter two finite sums to

$$
 \mathcal C_N=\{n:3N/2<\log n\le8N/3\}.
$$

[`eventually_norm_refined_sub_centralJoint_le`](../RiemannGaussian/ZetaRieszCentralPair.lean)
proves that this changes the normalized whole response by at most

$$
 2E_N=2u\left(A(P,2/3,257/256)r_-^N+
                  A(P,3/8,257/256)r_+^N\right),
$$

where the previously checked rates are
$r_-=(3/2)\exp(-631/1536)<1$ and
$r_+=(8/3)\exp(-95/96)<1$. The head $H_N$ is never truncated or
estimated separately in this transport.

For $u\ge1/2$ and **$N\ge20$**, Lean proves $L_N\le3N/2$ using the
literal floor. Thus the clip on every central pair is exactly one:

$$
 Q_N^{\mathrm{central}}=
 \sum_{n\in\mathcal P_N\cap\mathcal C_N}\log n\,K_{P,N}(s,n),
$$

where $\mathcal P_N$ counts each product of two distinct intermediate
primes $N^2<p<X_N$ once. See
[`centralPairResponse_eq_log_sum`](../RiemannGaussian/ZetaRieszCentralPair.lean).
Order twenty is the explicit threshold for removing this clip, not a
starting order for all earlier asymptotic transports.

The same module proves that every nonzero unpaired coefficient eventually
has at least three distinct prime factors. It keeps all original masks,
all prime factors below $X_N$, and at least two factors above $N^2$.

## A fixed sign and two bounds for the entire three-prime class

Write the original coefficient as

$$
 C_L(n)=-\frac{\log n}{L}R_L(n),\qquad
 R_L(n)=\sum_{d\mid n}\mu(d)\max(0,L-\log d)
$$

on squarefree composites, and zero otherwise. For three distinct primes
$n=pqr$, prime insertion gives the exact difference

$$
 R_L(pqr)=T_{\log p,\log q}(L)-T_{\log p,\log q}(L-\log r),
$$

where $T_{a,b}(x)=x_+-(x-a)_+-(x-b)_++(x-a-b)_+$ is the existing
two-prime tent. All cutoff translations stay coupled before taking a norm.
For **$L>0$ and $\log n\le2L$**, Lean proves

$$
 0\le C_L(n)\le\frac12\log n,
 \qquad
 |C_L(n)|\le\frac{\log n}{L}(2L-\log n).
$$

These are
[`actual_three_prime_coefficient_bounds` and
`norm_actual_three_prime_le_midpoint_gap`](../RiemannGaussian/ZetaRieszTriplePrime.lean).
The second allowance vanishes at the reflection midpoint $L=\log n/2$.
[`central_three_coefficient_bounds`](../RiemannGaussian/ZetaRieszCentralPrimeLayers.lean)
discharges the logarithmic premise for the actual surviving support using
$X_N<n<X_N^2$. No hypothetical-zero or prime-cancellation assumption enters.

For any finite observations $f(n)$ of these three-prime integers, the
known sign also gives the independent lower bound

$$
 \operatorname{Re}\sum_n C_L(n)f(n)
 \ge -\frac12\sum_n\log n\,\max(0,-\operatorname{Re}f(n)).
$$

See [`re_three_prime_sum_ge_negative_phase`](../RiemannGaussian/ZetaRieszTriplePrime.lean)
and its source-normalized application
[`re_normalized_three_ge_negative_phase`](../RiemannGaussian/ZetaRieszCentralPrimeLayers.lean).
Positive real observations incur zero lower-bound cost. For the constant
filter, the remaining negative observations are precisely the negative
cosine phases, with their original exponential-factorial envelopes.
**The displayed phase cost has not been bounded by a constant below one.**
Known coefficient sign does not establish positivity of the oscillating sum.

## The four terms still requiring joint control

[`eventually_centralJoint_eq_prime_layers`](../RiemannGaussian/ZetaRieszCentralPrimeLayers.lean)
gives the exact signed partition

$$
 J_N^{\mathrm{central}}=
 H_N+Q_N^{\mathrm{central}}+T_N^{(3)}+T_N^{(\ge4)}.
$$

| Term | What is retained | What remains unbounded |
| --- | --- | --- |
| $H_N$ | Complete prime sum, intermediate cofactor marks and all factorial orders | Its correlation with the three finite terms |
| $Q_N^{\mathrm{central}}$ | One integer label per distinct prime pair, coefficient $\log n$ | Its cosine-weighted response |
| $T_N^{(3)}$ | Actual three-prime coefficients, known sign, half-logarithm and midpoint-gap bounds | The explicit negative-phase cost |
| $T_N^{(\ge4)}$ | Actual squarefree coefficients with at least four prime factors and every old support cut | Both divisor signs and phase correlations |

[`tendsto_centralJoint_exposed`](../RiemannGaussian/ZetaRieszCentralPair.lean)
retains the whole limit $-m_\rho$ under the exposed-zero hypothesis in
the annular source range. An independent cofinal real lower floor at
least $-c$, for any fixed $c<1$, would contradict that source there.
Full decay is unnecessary, but the floor for the **whole** coupled sum
is still unproved, as are the corresponding remaining global source ranges.

All three modules belong to the arithmetic family and enter the ordinary
root, declaration lint, transitive axiom audit and dependency explorer.
The supporting endpoint is `central-prime-layers`; the default RH endpoint
and both ten-entry README lists remain unchanged. The exhaustive numerical
certificate verifier is not part of this slice's ordinary checks.
