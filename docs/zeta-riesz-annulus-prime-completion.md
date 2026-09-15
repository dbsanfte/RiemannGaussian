# Completing the annular prime range with a proved error

The actual cross-prime part of the physical annulus can now be replaced
by a genuinely complete prime sum, with an independently bounded error.
Its exact finite prime prefix stays beside the other surviving arithmetic
terms. This does not prove the independent lower floor or RH.

Write

$$
 D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,
 \qquad X_N=(D_N+2)^2,\qquad L_N=\log X_N.
$$

The new annular comparison holds for
$1/2\le u<\exp(-2/3)$. At a hypothetical exposed zero
$\rho=\beta+i\gamma$, use $u=3/2-\beta$.
All previous support restrictions retain their own parameter ranges;
the other source scales keep the previous residuals.

## What is bounded

For every fixed polynomial filter $P$, every height $y$, and every changing
selection of intermediate primes $N^2<a<X_N$, let $T_N$ be the original
annular cross-prime response. Let $H_N$ be the corresponding complete prime
head and $B_N$ its exact physical prime prefix. Lean proves eventually

$$
 \left|u^{N+1}\bigl(H_N-B_N-T_N\bigr)\right|
 \le r^N u A(P,3/8,257/256),
 \qquad r=\frac83\exp(-95/96)<1.
$$

The allowance $A$ is the existing convergent divisor mass with every fixed
factorial shift. No zero premise is used. The starting order is eventual,
not numerically evaluated. The result is
[`eventually_norm_annulus_completion_error_le`](../RiemannGaussian/ZetaRieszAnnulusCompletion.lean).

The proof first extends the finite upper bound to every changing **infinite**
mask with $n\ge X_N^2$. Genuine summability is proved, then the finite bounds
are made uniform before taking the infinite sum. This avoids exchanging two
limits without justification. See
[`eventually_norm_infinite_upper_le`](../RiemannGaussian/ZetaRieszInfinitePhysical.lean).

## What the completion retains

Put $s=3/2+iy$ and keep the original kernel

$$
 K_{P,N}(s,n)=n^{-s}\sum_j P_j\frac{(\log n)^{N+j}}{(N+j)!}.
$$

For the full intermediate prime set $A_N$, the completed head and its prefix are

$$
 H_N=-\sum_{a\in A_N}\frac{\log a}{L_N}
           \sum_{p\text{ prime}}\log(ap)K_{P,N}(s,ap),
$$

$$
 B_N=-\sum_{a\in A_N}\frac{\log a}{L_N}
           \sum_{\substack{p\text{ prime}\\p<X_N}}
                \log(ap)K_{P,N}(s,ap).
$$

On $a<X_N\le p$, the original coefficient is exactly
$-\log(ap)\log(a)/L_N$. The disjoint prime ranges count each actual integer
once. The introduced prefix has different incidence counts: it can include
$p=a$, and a distinct-prime product can occur twice. Both are retained.
[`hasSum_crossCoefficient`](../RiemannGaussian/ZetaRieszCrossCompletion.lean)
proves the convergent identity with this entire correction.

The support proof also checks every earlier deletion. Two rough primes
have no nontrivial smooth divisor, their cofactors are prime, and the
cross-range extreme-prime set is a singleton. The entire physical annulus
eventually lies in the original and narrowed logarithmic windows.
Consequently no extra arbitrary mask is imposed on the complete prime sum.
See [`eventually_cross_semiprime_mem_annulus`](../RiemannGaussian/ZetaRieszCrossSupport.lean).

## The whole remaining arithmetic target

Let $S_N$ be the actual annular contribution whose prime factors are all
below $X_N$. The whole carrier is $S_N+T_N$, and Lean proves

$$
 u^{N+1}\bigl[(S_N+H_N-B_N)-(S_N+T_N)\bigr]\longrightarrow0
$$

with the same geometric allowance. At exposed right-half zeros in the
stated source interval,

$$
 u^{N+1}(S_N+H_N-B_N)\longrightarrow-m_\rho.
$$

These are [`eventually_norm_joint_sub_annulus_le` and
`tendsto_jointResponse_exposed`](../RiemannGaussian/ZetaRieszAnnulusJoint.lean).
The negative limit is conditional on the hypothetical zero; the error
bound is independent. The prime phases in $B_N$ and $S_N$ are still shared,
and their joint contribution with $H_N$ remains unbounded by the needed
independent cofinal floor. Positivity of a coefficient alone would not
control its cosine-weighted contribution.

The existing contradiction needs a cofinal lower floor at least $-c$ for
some $c<1$ for the **whole** normalized response. No separate decay claim
is made for $H_N$, $B_N$ or $S_N$. The new results do not enlarge the
zero-free region or provide a numerical zero bound.

## Verification and explorer

The five modules are imported by the ordinary root and assigned to the
arithmetic family. The supporting explorer endpoint is
`annulus-prime-completion`; the default whole-carrier frontier is unchanged.
Compiled dependency exports and transitive axiom checks cover the endpoint.
Ordinary CI does not run the exhaustive numerical certificate verifier.
