# The source requires distinct-prime interactions

The [large-divisor Möbius tail](zeta-moebius-pole-jet-tail.md) now has a
further independent arithmetic bound: its entire prime-power contribution
is negligible at every right-half zero's source scale, uniformly over a
varying positive divisor cutoff. The full multiplicity source survives on
integers with at least two distinct prime factors. Both removed pieces
fit the same explicit geometric error rate.

The independent opposite signed bound for the remaining interactions is
still open. This result supplies no additional zero exclusion. Literature
priority for these formal connections has not been established.

## Exact single-prime cancellation

Recall the literal coefficient

\[
A_D(n)=\sum_{dk=n\atop d>D}\mu(d)\log k.
\]

For every prime `p`, cutoff `D>=1`, and integer `k>=0`, Lean proves

\[
\boxed{
A_D(p^{k+1})=
\begin{cases}
-k\log p,&p>D,\\
0,&p\le D.
\end{cases}}
\]

This is `zetaMoebiusLogTailCoefficient_prime_pow`. The unit divisor is
outside the tail, and every divisor `p^j` with `j>=2` has zero Möbius
coefficient. The negative term is retained exactly before taking a norm.

Let `a_D(n)` be `A_D(n)` restricted to prime powers and put

\[
W(n)=\frac{\log n}{\log2}\Lambda_{\rm proper}(n),
\]

where `Lambda_proper` is von Mangoldt restricted to proper prime powers.
The exact coefficient calculation gives the cutoff-independent bound

\[
|a_D(n)|\le W(n).
\]

`norm_zetaMoebiusTailPrimePowerCoefficient_le` proves it. The existing
proper-prime-power series converges absolutely for `Re s>1/2`, and an
extra logarithm preserves that abscissa. Hence

\[
B(\sigma)=\sum_{n\ge1}W(n)n^{-\sigma}<\infty
\quad(\sigma>1/2).
\]

Theorems `LSeriesSummable_zetaMoebiusTailPrimePowerMajorant` and
`summable_zetaMoebiusTailPrimePowerMajorant` discharge this convergence.

## Uniform geometric control

For every polynomial `P(X)=sum p_k X^k`, define its actual single-prime
tail filter

\[
S_{P,D,N}(s)=\sum_{n\ge1}a_D(n)n^{-s}
 \sum_k p_k\frac{(\log n)^{N+k}}{(N+k)!}.
\]

The coefficient bound and exponential-series envelope give, for `0<r<1`,

\[
|S_{P,D,N}(3/2+iy)|\le
r^{-N}B(3/2-r)\sum_k|p_k|r^{-k}.
\]

`norm_zetaMoebiusTailPrimePowerFilter_le` is uniform in `D>=1` and `y`.
There is no pole-cancellation hypothesis and no assumption about zeros.
The arithmetic sum genuinely converges throughout `Re s>1/2`.

For a real source normalization `0<u<1`, choose `r=sqrt(u)`. Then, for
any sequence of positive divisor cutoffs `D_N`,

\[
\boxed{|u^{N+1}S_{P,D_N,N}(3/2+iy)|\le C_{P,u}(\sqrt u)^N.}
\]

This is `exists_zetaMoebiusTailPrimePowerFilter_geometric_bound`. A
separate limit theorem allows arbitrary complex normalizations of norm
less than one and cutoffs that are only eventually positive.

## The remaining literal arithmetic sum

Let `rho=beta+i gamma` be a hypothetical nontrivial zero with `beta>1/2`,
and use the previously constructed exact pole-jet filter `Ptilde_rho`.
Set

\[
u=3/2-\beta,\quad s_0=3/2+i\gamma,\quad
D_N=\lfloor u^{-N/4}\rfloor.
\]

The remaining filter is the convergent signed sum

\[
R_N=\sum_{n:\;\#\{p\text{ prime}:p\mid n\}\ge2}
 A_{D_N}(n)n^{-s_0}
 \sum_k\widetilde p_{\rho,k}\frac{(\log n)^{N+k}}{(N+k)!}.
\]

Every nonzero coefficient also satisfies `n>=2(D_N+1)`.
`zetaMoebiusDistinctPrimeCoefficient_support` supplies two actual distinct
prime divisors and the index bound.
`hasSum_zetaMoebiusDistinctPrimeFilter` proves the convergence and exact
filter value. The split from the original tail is an exact complex
identity before its prime-power part is bounded.

Let `F_N` be the complete filtered negative logarithmic derivative, whose
normalized source limit was already proved to be `-m(rho)`. The combined
independent bound is

\[
\boxed{|u^{N+1}(F_N-R_N)|\le C_\rho(\sqrt u)^N.}
\]

This is `exists_zetaRightHalfDistinctPrimeTail_error_bound`. It combines
the finite Möbius head estimate with the new prime-power estimate, without
weakening the geometric rate. Consequently

\[
u^{N+1}R_N\longrightarrow-m(\rho),\qquad
\Re R_N<-\frac{m(\rho)}{2u^{N+1}}\quad\text{eventually}.
\]

These are `tendsto_zetaRightHalfDistinctPrimeTail` and
`zetaRightHalfDistinctPrimeTail_eventually_negative`.
The coefficients retain the full local-zero geometry, multiplicities,
Möbius signs, divisor cutoff, and phase `n^(-i gamma)`.

## The open estimate

An independent lower bound for the coupled distinct-prime sum must beat
the forced negative source, for arbitrarily large moment orders. Neither
its restricted support nor the controlled single-prime part supplies
that bound. This is now specifically an arithmetic interaction between
different primes; prime-power estimates alone cannot finish this route.

The error constants are independent of moment order. The combined
constant depends on the selected zero and its filter, and no effective
uniform starting order or uniform height bound is claimed.

## Local validation

Both new modules are imported by the root library. Checks comprise direct
warnings-as-errors elaboration, focused and full builds, whole-project
declaration lint, a root-imported audit of every new public theorem's
axioms, and source/whitespace checks. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted. Work remains local under the commit hold.
