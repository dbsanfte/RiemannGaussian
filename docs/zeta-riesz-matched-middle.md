# A signed budget for a matched middle prime block

Lean now bounds a nonempty middle part of the **actual prime head and
pair response together**. At an exposed hypothetical zero
$\rho=\beta+i\gamma$, with multiplicity $m_\rho$ and
$u=3/2-\beta<e^{-2/3}$, the checked statement is eventually

$$
\boxed{-\frac{m_\rho^2}{8}\ \le\
\Re\!\left(u^{N+1}\mathcal M_N\right)\ <\ 0.}
$$

The theorem is
[`eventually_matchedBlock_re_bounds`](../RiemannGaussian/ZetaRieszMatchedMiddle.lean).
Its zero and exposure hypotheses are explicit. This is a bounded negative
contribution, not a decay theorem or an independent floor for the whole
carrier. Multiplicity is unrestricted: $m_\rho^2/8$ need not be less than
one. The remaining joint floor and the other global source ranges stay open.

## Independent completion makes the finite phases accessible

Retain the literal physical cutoff and prime mask:

$$
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,\quad
X_N=(D_N+2)^2,\quad L_N=\log X_N,\quad
A_N=\{p\text{ prime}:N^2<p<X_N\}.
$$

At $s=3/2+iy$, write

$$
K_k(s,n)=n^{-s}\frac{(\log n)^k}{k!},\quad
F_{N,k}=\sum_{p\in A_N}K_k(s,p),\quad
B_k=\sum_{p\text{ prime}}K_k(s,p).
$$

The complete series is genuinely absolutely convergent. For
$0<u<e^{-2/3}$, [`eventually_norm_finite_sub_complete_le`](../RiemannGaussian/ZetaRieszPrimeCompletion.lean)
proves, eventually **uniformly over all eligible orders and all heights**,

$$
\boxed{\displaystyle
\|u^k(F_{N,k}-B_k)\|\le 2Z e^{-17N/12288},\qquad
N\le3k,\quad128k\le65N.}
$$

Here $Z=\sum_{n\ge0}e^{-(1025/1024)\log n}$ is a finite dominating
mass, with Lean's harmless totalized zero index. Zero is never a prime.
The omitted primes $p\le N^2$ have allowance $Ze^{-95N/3072}$;
the omitted primes $p\ge X_N$ have allowance $Ze^{-17N/12288}$.
Both estimates are independent of any zero or cancellation assumption.
Their exact sum is the finite-to-complete error, with no endpoint changed.

`tendsto_finite_sub_complete` permits both the order and height to move
arbitrarily within this band. The extra derivative weight $k$ is also
absorbed by the geometric saving. Consequently
[`tendsto_weighted_finite`](../RiemannGaussian/ZetaRieszPrimeCompletionPhase.lean)
transfers the exposed complete-prime phase to the actual finite array:

$$
k_Nu^{k_N}F_{N,k_N}(3/2+i\gamma)\longrightarrow-m_\rho.
$$

This last statement uses the existing exposed-zero hypothesis: every
other nontrivial zero is strictly farther than $u$ from $3/2+i\gamma$.
It does not assert that every zero satisfies that hypothesis.

## The head shift changes the sign of the matched contribution

For the original unfiltered source $P=1$, let $M=N+1$ and $l=M-k$.
The shared atom is exactly

$$
J_{N,k}=\frac12F_{N,k}F_{N,l}
       -\frac{k+1}{L_N}F_{N,k+1}B_l.
$$

Set $a=k u^kF_{N,k}$, $b=l u^lF_{N,l}$,
$c=(k+1)u^{k+1}F_{N,k+1}$ and $d=l u^lB_l$.
`normalized_sharedAtom_eq` proves

$$
kl u^M J_{N,k}=\frac12ab-\frac{k}{uL_N}cd.
$$

Every eligible weighted factor tends to $-m_\rho$. The proof upgrades
those limits to one threshold uniform over all eligible orders, so both
products are within $m_\rho^2/24$ of the same positive real square.
The actual cutoff and order constraints also give

$$
\frac7{12}\le\frac{k}{uL_N}\le1.
$$

Thus the positive pair product is accompanied by a larger negative head
coefficient. Lean proves the two-sided atom estimate

$$
-\frac9{16}m_\rho^2
\le\Re(kl u^M J_{N,k})
\le-\frac{11}{288}m_\rho^2.
$$

The head's adjacent order, derivative weight, negative sign and factor
$1/L_N$ are essential to this conclusion. Positive pair phases alone
would not pay the matched contribution.

## Actual order counts give the whole block budget

The selected set $S_N$ contains precisely the $0\le k\le N+1$ for which
$k$, $N+1-k$ and $k+1$ all satisfy $N\le3r$ and $128r\le65N$.
It is a proved subset of both the surviving middle pair and head ranges.
Define the actual block

$$
\mathcal M_N=(N+1)\sum_{k\in S_N}J_{N,k}.
$$

For $N\ge256$, Lean proves

$$
\lfloor N/2\rfloor\in S_N,\qquad
32|S_N|\le N,\qquad
\sum_{k\in S_N}\frac{N+1}{k(N+1-k)}\le\frac5{32}.
$$

These are counts and reciprocal factorial-order weights, not percentages
of arithmetic mass. Summing the signed atom inequalities gives the boxed
block budget above. The order $256$ is **only the structural counting and
nonemptiness threshold**; the common phase threshold remains eventual
and depends on the exposed zero.

## The complementary arithmetic remains in the chain

`middleJoint_one_eq_unmatched_add_matched` is an exact identity at every
order. `unmatchedJoint` retains the original central unpaired arithmetic
response, the head sum outside $S_N$, and the pair sum outside $S_N$.
Those complementary sums keep their original signs and physical masks.
The unpaired response retains the actual three-prime and higher-prime
terms from the earlier decomposition.

`tendsto_unmatched_add_matched_exposed` preserves the full source for
**the sum of both pieces**:

$$
u^{N+1}(\operatorname{unmatchedJoint}_N+\mathcal M_N)
\longrightarrow-m_\rho.
$$

The bounded block is retained. No separate limit for the unmatched part,
or vanishing limit for the matched block, is assumed. Closing RH still
requires the remaining joint arithmetic estimate and all applicable
global source ranges; this result gives no new zero-free region.

See the `matched-middle` endpoint in the [RH explorer](rh-proof-explorer/),
its [proof audit](rh-proof-explorer/audit.json), and the preceding
[outer pair-order bounds](zeta-riesz-pair-orders.md). The default
whole-carrier endpoint and both ten-entry README lists remain unchanged.
