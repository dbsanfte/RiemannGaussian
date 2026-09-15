# A larger signed block with the same negative budget

Lean now controls a **strictly larger actual matched head/pair block** at
the same negative cost. Under the existing exposed-zero hypotheses, with
the full multiplicity $m_\rho$ and $u=3/2-\Re\rho<e^{-2/3}$, eventually

$$
\boxed{-\frac{m_\rho^2}{8}
\le \Re\!\left(u^{N+1}\mathcal M_N\right)
\le-\frac{m_\rho^2}{1536}.}
$$

The endpoint is
[`eventually_matchedBlock_persistent_bounds`](../RiemannGaussian/ZetaRieszWiderMatched.lean).
It assumes an actual hypothetical right-half zero and that every other
nontrivial zero is strictly farther than $u$ from $3/2+i\Im\rho$.
The source transport remains restricted to $1/2\le u<e^{-2/3}$ and the
original unfiltered source $P=1$. No simplicity assumption is made.
The cost $m_\rho^2/8$ need not be subunit, and the whole signed floor is open.

## The completion rate is optimized analytically

Keep the same physical cutoff and prime array:

$$
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\quad
X_N=(D_N+2)^2,\quad L_N=\log X_N,\quad
A_N=\{p\text{ prime}:N^2<p<X_N\}.
$$

Write $F_{N,k}=\sum_{p\in A_N}K_k(s,p)$ and
$B_k=\sum_{p\text{ prime}}K_k(s,p)$, with
$K_k(s,p)=p^{-s}(\log p)^k/k!$ and $s=3/2+iy$.
All complete prime series used here converge genuinely.

For a physical lower bound $L_N\ge\ell N$ and order ceiling $k\le\theta N$,
the independent upper completion exponent is

$$
E(q)=\theta\log(u/q)-(3/2-q-\sigma)\ell.
$$

[`completionExponent_sub_ideal`](../RiemannGaussian/ZetaRieszPrimeCompletionRate.lean)
proves, for positive $u,\theta,\ell,q$,

$$
E(q)-E(\theta/\ell)
=\theta\left(\frac{q\ell}{\theta}-1-\log\frac{q\ell}{\theta}\right)\ge0.
$$

The inequality is strict away from $q=\theta/\ell$. This is a unique
optimum over positive exponential tilts for **this estimate**, not over
all arithmetic weight families. Application still requires $\sigma>1$,
$0<q\le u$, $3/2-q-\sigma\ge0$ and $u<e^{-\ell/2}$.
The full completion theorem also pays the omitted small primes separately.

A checked choice $\theta=17/32$, $\ell=4/3$, $q=2/5$ and
$\sigma=8193/8192$ proves, eventually uniformly in height and eligible order,

$$
\boxed{\|u^k(F_{N,k}-B_k)\|
\le e^{-11N/30720}(Z_{1025/1024}+Z_{8193/8192}),\quad
N\le3k,\quad32k\le17N.}
$$

Here $Z_\sigma=\sum_{n\ge0}e^{-\sigma\log n}$ is a finite dominating
mass; its harmless totalized zero index never enters a prime array.
The theorem assumes $1/2\le u<e^{-2/3}$ and has **no zero hypothesis**.
The derivative-weighted completion error also tends to zero for every
moving eligible order and every moving height. Only its subsequent
transfer of the phase $k u^k F_{N,k}\to-m_\rho$ uses the exposed zero.

## More actual orders fit in the same signed budget

Put $M=N+1$ and $l=M-k$. The new set $S_N$ selects the original orders
for which $k$, $l$ and $k+1$ all satisfy $N\le3r$ and $32r\le17N$.
It contains every previously matched order. For $N\ge256$, the explicit
order $\lfloor17N/32\rfloor-1$ belongs to the new block and fails the old
successor cut, proving strict enlargement.

The original shared atom is unchanged:

$$
J_{N,k}=\tfrac12F_{N,k}F_{N,l}
       -\frac{k+1}{L_N}F_{N,k+1}B_l,\qquad
\mathcal M_N=M\sum_{k\in S_N}J_{N,k}.
$$

The counting bounds hold for $N\ge256$. The head-cost bounds also require
the proved eventual length bound $L_N\ge4N/3$:

$$
\frac{N}{32}\le|S_N|\le\frac{N}{16},\qquad
\frac1{16}\le\sum_{k\in S_N}\frac{M}{kl}\le\frac5{16},
\qquad \frac59\le\frac{k}{uL_N}\le\frac45.
$$

The common product-phase error is at most $m_\rho^2/24$ and gives

$$
-\frac{17m_\rho^2}{48}
\le\Re(kl u^M J_{N,k})
\le-\frac{5m_\rho^2}{432}.
$$

Summing with the actual reciprocal weights proves the boxed whole-block
budget. These counts are not percentages of arithmetic mass. The threshold
$256$ is a structural threshold only; the common phase threshold remains
eventual and depends on the exposed zero.

`not_tendsto_matchedBlock_zero` proves that this block cannot be treated as
a vanishing error under those hypotheses.
`not_tendsto_unmatched_full_source` proves that its complement alone cannot
retain the original $-m_\rho$ limit. The exact source identity keeps
**unmatchedJoint plus matchedBlock**. The complement retains all remaining
head and pair orders and the actual three-prime and higher-prime sums.

## An endpoint cancellation remains available in the complementary orders

[`taperedMoment_eq`](../RiemannGaussian/ZetaRieszEndpointTaper.lean)
identifies the head subtraction with the literal weighted prime moment

$$
T_l=F_{N,l}-\frac{l+1}{L_N}F_{N,l+1}
=\sum_{p\in A_N}\left(1-\frac{\log p}{L_N}\right)K_l(s,p).
$$

The weight is positive on the actual prime array and vanishes at its
physical endpoint. The exact reflected atom identity is

$$
J_{N,k}+J_{N,l}
= B_kT_l-\frac{k+1}{L_N}B_{k+1}B_l
 +(F_{N,k}-B_k)F_{N,l}
 -\frac{k+1}{L_N}(F_{N,k+1}-B_{k+1})B_l.
$$

Both completion errors retain their multiplying factors. For $q>0$,
$\sigma>1$ and $a=q+\sigma-3/2>0$, the independent bound is

$$
\|T_l\|\le \frac{q^{-l}e^{aL_N}}{aL_N}Z_\sigma.
$$

This saves an inverse physical length in the norm envelope, uniformly in
height, without a zero hypothesis. The exponential factor may still grow.
A small completion error cannot be multiplied by an uncontrolled other
factor and then called negligible. Paying those products and bounding
the retained tapered term jointly with the negative complete head and
the three-prime and higher-prime carrier remains open. Other global source
ranges also remain open; this slice proves no RH or zero-free enlargement.
