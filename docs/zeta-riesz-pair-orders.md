# Paid outer prime orders and the remaining shared phases

The [subsequent matched middle block](zeta-riesz-matched-middle.md) uses
independent prime completion to obtain a signed budget for part of the
remaining head and pair response together, with explicit exposed-zero premises.

Lean now independently bounds both outer order ranges of the finite
prime-pair response, removes its repeated-prime diagonal, and enlarges
the controlled high-order part of the completed head. The remaining
head and pairs share one exact complex quadratic expression. Its joint
signed floor, together with the higher-prime terms, remains open.

The definitions retain the original physical cutoff:

$$
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\quad
X_N=(D_N+2)^2,\quad L_N=\log X_N,\quad
A_N=\{a\text{ prime}:N^2<a<X_N\}.
$$

At $s=3/2+iy$, use the genuine finite and complete prime moments

$$
K_k(s,n)=n^{-s}\frac{(\log n)^k}{k!},\qquad
F_{A,k}(s)=\sum_{a\in A}K_k(s,a),\qquad
B_m(s)=\sum_{p\text{ prime}}K_m(s,p).
$$

Every $B_m$ is absolutely convergent here, including order zero. Every
polynomial $P$ below is fixed; all its coefficients and factorial shifts
remain. Write $M=N+j+1$ within each filter term.

## What is now bounded independently

[`norm_adaptiveHead_le`](../RiemannGaussian/ZetaRieszHeadAdaptiveTransport.lean)
controls every head order $8k\ge7M$.
[`norm_outerPairResponse_le`](../RiemannGaussian/ZetaRieszPairOrders.lean)
controls both pair ranges $8k\le M$ and $8k\ge7M$ together. For $N\ge3$,
uniformly in $y$ and on $0<u<e^{-2/3}$, their respective estimates are

$$
\boxed{\begin{aligned}
\|u^{N+1}H_N^{\rm high}\|&\le C_H(P,u)(N+1)^2e^{-7N/9216},\\
\|u^{N+1}Q_N^{\rm outer}\|&\le C_Q(P,u)(N+1)^2e^{-7N/9216}.
\end{aligned}}
$$

The costs are explicitly defined, finite, and independent of height:

$$
\begin{aligned}
S(P,u)&=\sum_j|P_j|u^{-(j+1)}(j+2)^2,\\
Z&=\sum_{n\ge0}e^{-(1025/1024)\log n},\qquad
T=\operatorname{majorantMass}(1025/1024),\\
C_H(P,u)&=uTZS(P,u),\qquad C_Q(P,u)=uZ^2S(P,u).
\end{aligned}
$$

The dominating masses use Lean's harmless totalized zero index; zero
is never included as a prime. Both allowances tend to zero without a
zero, exposure, or cancellation assumption. These are controlled order
ranges, not percentages of arithmetic mass.

The improvement retains the correlation between $u$ and the actual
floor. [`length_le_source_log`](../RiemannGaussian/ZetaRieszHeadAdaptive.lean)
proves $L_N\le-2N\log u$ for $0<u\le3/5$, $N\ge3$; the annular
parameter range lies inside this interval. Two exponential tilts then
pay the finite cofactor and complementary complete prime moment together.
The original $15M/16$ head cutoff can consequently be lowered to $7M/8$.

## Exact pair counting and reflection

[`pairLogResponse_eq_convolution_sub_diagonal`](../RiemannGaussian/ZetaRieszPrimePairConvolution.lean)
proves

$$
Q_N^{\log}=\sum_j\frac{P_jM}{2}
       \sum_{k=0}^{M}F_{A_N,k}F_{A_N,M-k}-\Delta_N,
\qquad
\Delta_N=\sum_{a\in A_N}\log(a)K_{P,N}(s,a^2).
$$

Each distinct product has exactly two ordered prime incidences, and each
repeated prime contributes once to the ordered diagonal. The factor
$1/2$ and the diagonal above are proved from those counts. The diagonal
decays independently for **every** $0<u<1$, even for arbitrary moving
finite prime masks, with rate $2u/(u+1)$.

The product $F_{A,k}F_{A,M-k}$ is invariant under $k\mapsto M-k$.
`full_sub_middle_eq_twice_high` therefore identifies the two outer ranges
with twice the upper range, including their endpoints when $M>0$.
That factor two cancels the original pair half. This is an identity of
complex products and gives no positivity assertion about the middle.

`tendsto_centralPair_sub_middle` connects these estimates to the **actual**
central prime-pair term on $1/2\le u<e^{-2/3}$. The earlier central-window
error and the physical clip are discharged. The clip threshold $N\ge20$
is distinct from the new component-estimate threshold $N\ge3$.

## The remaining obstruction, with shared information explicit

The head's logarithmic mark satisfies $G_{A,k}=(k+1)F_{A,k+1}$ exactly.
`middleJoint_eq_unpaired_add_form` gives the surviving whole response as

$$
\begin{aligned}
J_N^{\rm middle}=U_N+\sum_jP_jM\Bigg[&
 \frac12\sum_{\substack{0\le k\le M\\M<8k<7M}}
       F_{A_N,k}F_{A_N,M-k}\\
 &-\frac1{L_N}\sum_{\substack{0\le k\le M\\8k<7M}}
       (k+1)F_{A_N,k+1}B_{M-k}\Bigg].
\end{aligned}
$$

$U_N$ is the original central unpaired arithmetic response, with every
previous support cut. Its existing eventual decomposition retains the
actual three-prime and four-or-more-prime terms. The three-prime
coefficient is nonnegative and at most half the product logarithm, but
its cosine phase cost is still uncontrolled.

The finite prime array is now visibly shared between the pair and head.
The head has an adjacent factorial order, a derivative weight $k+1$, and
a complete prime factor; the pair has two finite factors. No finite
prime set has been completed, no complete prime series truncated, and
no complex product replaced by a Hermitian square.

`tendsto_centralJoint_sub_middleJoint` proves independently that every
deleted whole-carrier component has vanishing source error on the
annular interval. `tendsto_middleJoint_exposed` then preserves

$$
u^{N+1}J_N^{\rm middle}\longrightarrow-m_\rho,
\qquad u=3/2-\Re\rho,
$$

at an exposed hypothetical right-half zero in that interval, for the
unfiltered source $P=1$. What is needed is an independent cofinal real
floor at least $-c$, for some $c<1$, for this **whole** normalized
response. Separate component identities or positive coefficients do not
give that floor. Other source ranges retain their earlier obligations;
this slice proves neither RH nor an enlarged zero-free region.

The [RH explorer](rh-proof-explorer/) has a `pair-orders` supporting
endpoint with exact Lean statements and source lines. Its
[proof audit](rh-proof-explorer/audit.json) records the transitive checks.
The default whole-carrier endpoint remains unchanged. The preceding
[head-order estimate](zeta-riesz-head-orders.md) and
[prime-degree decomposition](zeta-riesz-central-prime-layers.md) retain
the earlier proof history.
