# An independently paid part of the complete prime head

[`ZetaRieszHeadOrders`](../RiemannGaussian/ZetaRieszHeadOrders.lean)
proves an explicit geometric bound for the high factorial orders of the
actual completed prime head. The remaining cofactor phases stay coupled.
This does not prove a floor for the whole signed carrier, RH, or a new
zero-free region.

Use the original physical cutoff and prime set:

$$
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\qquad
X_N=(D_N+2)^2,\qquad L_N=\log X_N,\qquad
A_N=\{a\text{ prime}:N^2<a<X_N\}.
$$

The independent head estimate holds for every **fixed** polynomial filter
$P$, uniformly in the ordinate $y$, on $1/2\le u<\exp(-2/3)$.
Other source scales retain the earlier fallback regimes. The actual
integer floor, all original finite masks, and all factorial shifts remain.

## The exact convolution preserves the cofactor phases

At $s=3/2+iy$, write

$$
K_k(s,n)=n^{-s}\frac{(\log n)^k}{k!},\quad
G_{A,k}(s)=\sum_{a\in A}\log(a)K_k(s,a),\quad
B_m(s)=\sum_{p\text{ prime}}K_m(s,p).
$$

The complete prime series $B_m$ is genuinely absolutely convergent,
including $m=0$. Theorems `log_mul_kernel`,
`completedMoment_eq_convolution`, and `completedHead_eq_convolution`
give the exact identity

$$
H_N=-\sum_j\frac{P_jM}{L_N}
       \sum_{k=0}^{M}G_{A_N,k}(s)B_{M-k}(s),\qquad M=N+j+1.
$$

The finite cofactor sum is inside $G_{A_N,k}$ before any norm. This retains
correlations between different cofactor primes that the older separate
cofactor norm estimate could not use. No prime variable is truncated in
this identity, and no cofactor is completed to an infinite series.

## A definite high-order component now decays independently

The floor's damping denominator gives, for $u\ge1/2$ and $N\ge2$,

$$
D_N+2\le2^N,\qquad L_N\le2N\log2\le\frac{45}{32}N.
$$

Consequently, if $16k\ge15M$ and $a\in A_N$, then
$\log a\le3k/2$. The existing lower logarithmic-window estimate controls
$G_{A_N,k}$ at its own factorial order. A separate Euler estimate at the
positive tilt $127/256$ controls the complementary complete prime order.
Both estimates are independent of any zeta-zero hypothesis:

$$
\begin{aligned}
\lVert u^{k+1}G_{A_N,k}(s)\rVert
  &\le e^{-k/200}\,uT,\\
\lVert u^mB_m(s)\rVert
  &\le e^{m/25}\,Z,\\
T&=\operatorname{tiltConstant}(1,2/3,257/256),\qquad
Z=\sum_{n\ge0}e^{-(257/256)\log n}.
\end{aligned}
$$

Here $Z$ uses Lean's totalized logarithm at the unused index zero;
it is a finite dominating mass, not a claim that zero is a prime.
For $m=M-k$, the two exponents combine to at most $-7M/3200$.
Theorem `norm_highConvolution_le` sums all these high orders and keeps
their complete prime factors.

Let $H_N^{\mathrm{high}}$ denote precisely the part with $16k\ge15M$.
The final physical bound, `norm_highHead_le`, is

$$
\boxed{\displaystyle
\lVert u^{N+1}H_N^{\mathrm{high}}\rVert
 \le C(P,u)(N+1)^2e^{-7N/3200}\longrightarrow0\quad(N\ge2),}
$$

with the explicitly defined finite cost

$$
C(P,u)=uTZ\sum_j |P_j|u^{-(j+1)}(j+2)^2.
$$

The factor $(N+1)^2$ pays the order count and the product-logarithm
prefactor; the reciprocal physical length is bounded by one. No filter
coefficient or factorial shift is omitted. Order two is the threshold
for this estimate, not for all earlier asymptotic transports.

## What remains in the actual signed obstruction

`completedHead_eq_remaining_add_high` partitions the original head
exactly. The remaining head keeps $16k<15(N+j+1)$, with each complex
$G_{A_N,k}B_{N+j+1-k}$ intact. `centralJoint_sub_orderReduced` identifies
the difference of the actual joint carriers with the paid high part.

The remaining joint response consists of:

- The lower and middle factorial orders of the complete prime head.
- The central finite prime-pair correction, with its original phases.
- The actual three-prime response, whose coefficient sign and amplitude
  are known but whose negative phase cost is still uncontrolled.
- The actual four-or-more-prime response, retaining every inherited cut.

`tendsto_orderReducedJoint_exposed` proves that these remaining components
still carry the entire negative multiplicity source at an exposed zero
in the stated annular interval. The required independent cofinal real
floor strictly above $-1$ remains open. A norm bound for one discarded
component is not that floor, and this interval alone does not cover all
right-half zero parameters.

See the [preceding prime-degree decomposition](zeta-riesz-central-prime-layers.md),
the [RH proof explorer](rh-proof-explorer/), and its
[Lean-derived proof audit](rh-proof-explorer/audit.json). This result is a
supporting endpoint; the default whole-carrier endpoint remains unchanged.
