# The full signed source avoids every selected prime

Lean independently controls the **entire squarefree contribution with
exactly one selected prime divisor**, including every overlap and its
finite ordinary-prime correction. Combined with the preceding complete
prime-pattern and square sieves, this leaves the full original source on
squarefree integers whose **every prime divisor exceeds the quadratic
cutoff**. The complete signed correlation on those integers still needs
an independent strict upper bound.

## A uniform bound on squarefree intersections

Write the original negative divisor prefix as

\[
b_D(n)=-\sum_{\substack{d\mid n\\d\le D}}\mu(d)\log(n/d).
\]

For a finite set of primes `W`, retain this coefficient only when `n`
is squarefree and `prod(W)` divides `n`. The new arithmetic response
is the full convergent series with that literal coefficient and the
original complex polynomial kernel.

The preceding [all-square intersection bound](zeta-squarefree-signed-source.md)
is uniform over every finite square selection. Dominated convergence
therefore gives a bound on the squarefree response itself:

\[
|B_{D,W,p,N}(3/2+iy)|
\le C_{y,r}D r^{-N}\left(\sum_k|p_k|r^{-k}\right)
\prod_{a\in W}b_\tau(a),
\]

where

\[
0<r<1,\qquad \tau=1-r/2>1/2,\qquad
w_\tau(a)=e^{-\tau\log a},\qquad
b_\tau(a)=w_\tau(a)(1+w_\tau(a)).
\]

The constant is uniform over all first-power intersection families `W`.
The factor `1+w_tau(a)` pays the shared-prime correction from the
square sieve. No disjointness between the two prime selections is assumed.

[ZetaSquarefreeDivisibilityPrefix.lean](../RiemannGaussian/ZetaSquarefreeDivisibilityPrefix.lean)
proves the actual infinite-square limit in
`tendsto_zetaSquarefreeDivisibilityPrefixFilter` and the complete bound
in `exists_zetaSquarefreeDivisibilityPrefixFilter_bound`.

## Keep the complete one-prime pattern

The pattern with exactly one selected prime is the full response minus
the exact zero-prime and at-least-two-prime patterns. For a response `F`
indexed by prime subsets, its signed transform is

\[
F(\varnothing)
-\sum_{\substack{T\subseteq S\\|T|\ge2}}
  \sum_{U\subseteq S\setminus T}(-1)^{|U|}F(T\cup U)
-\sum_{U\subseteq S}(-1)^{|U|}F(U).
\]

All intersections and their original signs are present. If
`|F(W)|<=A*prod_{p in W}w(p)` on every subset of `S`, with `w>=0`,
the complete transform has the independent bound

\[
3A\prod_{p\in S}(1+2w(p)).
\]

This identity and bound apply to every finite selected family and every
complex physical weight. They preserve the entire kernel before the
companion norm estimate.

[FinitePrimeCountOne.lean](../RiemannGaussian/FinitePrimeCountOne.lean)
proves `primeCountOneTransform_indicator`,
`hasSum_primeCountOneTransform`, and `norm_primeCountOneTransform_le`.
Instantiating the transform with the actual squarefree intersection
responses uses the already proved bound

\[
\prod_{p\in S}(1+2b_\tau(p))
\le e^{2M_\tau}e^{4\sqrt R},\qquad
M_\tau=\sum_{n\ge0}w_\tau(n)^2<\infty,
\]

whenever all selected primes are at most `R`.

## The finite prime correction is part of the theorem

On squarefree integers the original distinct-prime tail satisfies

\[
\mathbf1_{\mathrm{squarefree}(n)}a_D(n)
=\mathbf1_{\mathrm{squarefree}(n)}b_D(n)
 +\mathbf1_{\mathrm{prime}(n)}\log n.
\]

After restricting to exactly one selected prime divisor, the correction
is **exactly** `1_{n in S}*log(n)`. Its full complex kernel sum is finite
and has bound

\[
R^2r^{-N}\sum_k|p_k|r^{-k}.
\]

Consequently the **entire actual one-prime squarefree contribution** obeys

\[
|A_{D,S,p,N}(3/2+iy)|
\le C_{y,r}(1+R^2)D e^{4\sqrt R}r^{-N}\sum_k|p_k|r^{-k}.
\]

This holds for every `D>=1`, polynomial filter and moment order, every
finite selected prime family through `R`, and every fixed `|y|>1`.
The height condition is already proved at every nontrivial zero ordinate.

Compiled entry points:

- [ZetaOnePrimeSquarefree.lean](../RiemannGaussian/ZetaOnePrimeSquarefree.lean):
  `zetaOnePrimeSquarefreeCoefficient_eq_prefix_add_primes`,
  `hasSum_zetaOnePrimeSquarefreePrefixFilter`, and
  `exists_zetaOnePrimeSquarefreePrefixFilter_bound`.
- [ZetaOnePrimeSquarefreeBound.lean](../RiemannGaussian/ZetaOnePrimeSquarefreeBound.lean):
  `zetaOnePrimeSquarefreeCoefficient_eq_sieved`,
  `hasSum_zetaOnePrimeSquarefreeFilter`, `norm_selectedPrimeFilter_le`, and
  `exists_zetaOnePrimeSquarefreeFilter_bound`.

## The actual moving family has independent decay

At each hypothetical right-half zero, retain the original choices

\[
u=3/2-\operatorname{Re}\rho,\quad q=u^{-1/4},\quad
D_N=\lfloor q^N\rfloor,\quad
R_N=\lfloor N\log(q)/8\rfloor^2,
\]

and select every prime through `R_N`. With

\[
r=(1+\sqrt u)/2,\qquad
\lambda=\frac{2\sqrt u}{1+\sqrt u}\in(0,1),
\]

the whole normalized one-prime squarefree response satisfies

\[
u^{N+1}|A_N|\le C_\rho(1+N^4)\lambda^N\longrightarrow0.
\]

The proof includes the integer rounding, the complete overlap cost, the
finite ordinary-prime correction, and the original divisor cutoff.
No coefficient budget or cancellation hypothesis remains to be supplied
for this deletion.

[ZetaRoughSquarefreeSource.lean](../RiemannGaussian/ZetaRoughSquarefreeSource.lean)
proves `exists_zetaRightHalfOnePrimeSquarefree_error_bound` and
`tendsto_zetaRightHalfOnePrimeSquarefreeFilter`, together with the exact
series reconstruction and the full complementary source.

## The remaining signed correlation

Every nonzero retained window coefficient now satisfies

- `2*N/5<=log(n)<=8*N` and `n>D_N^2`;
- `Squarefree n` and at least two distinct prime divisors;
- **every prime divisor of `n` is strictly greater than `R_N`**.

The full centered Fourier products remain in the same `(6/7)^N` region.
Their original reflection normalization and full source are retained:

\[
\operatorname{Re}C_N=-2W_N,\qquad
u^{N+1}C_N\longrightarrow-m_\rho,\qquad
u^{N+1}W_N\longrightarrow m_\rho/2.
\]

The finite signed comparison with the original analytic response has
complete allowance

\[
\frac{C_1(1+N^4)(\sqrt u)^N+C_2(1+N^4)\lambda^N+
\operatorname{zetaAveragedWindowError}(p_\rho,N,\operatorname{Im}\rho)}2
\longrightarrow0.
\]

[ZetaRoughSquarefreeWindowSource.lean](../RiemannGaussian/ZetaRoughSquarefreeWindowSource.lean)
proves `zetaRightHalfRoughSquarefreeWindowCoefficient_support`,
`tendsto_zetaRightHalfRoughSquarefreeWindowReflectionWork`,
`exists_zetaRightHalfRoughSquarefreeWindowReflection_error_bound`, and
`tendsto_zetaRightHalfRoughSquarefreeWindowTotalError`.

The full goal still requires an independent strict inequality
`u^(N+1)*W_N<=m_rho/2-epsilon`, for some fixed `epsilon>0` at arbitrarily
late orders, for every hypothetical right-half zero. The new estimate
controls the entire last selected-prime contribution; it does not prove
that inequality for its rough squarefree complement. No additional zeros
are excluded. The [all-height edge strip](zeta-completion-reserve-zero-free.md)
is unchanged, and RH remains open.

The subsequent [completion test](zeta-rough-squarefree-prime-balance.md)
proves that the entire completed rough squarefree divisor prefix has a
geometric normalized bound. Completing that sum restores ordinary primes
whose contribution carries the full source. The bound for the completion
therefore does not establish the required bound for the composite carrier.
