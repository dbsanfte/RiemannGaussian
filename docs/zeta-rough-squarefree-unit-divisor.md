# Removing all nonunit divisor rows with a proved error

Lean now controls the **entire dependence on the moving Möbius divisor
prefix**. The rough squarefree carrier can be replaced by minus the
logarithmic weight on rough squarefree composites, with a geometric error
at the hypothetical-zero source scale. The replacement has nonnegative
arithmetic weights; its full complex kernel still oscillates. No independent
strict upper bound for that remaining signed sum is proved here, and no
additional zeta zero is excluded.

All entry points below are in
[ZetaRoughSquarefreeUnitDivisor.lean](../RiemannGaussian/ZetaRoughSquarefreeUnitDivisor.lean).
The original [rough squarefree carrier](zeta-rough-squarefree-signed-source.md)
and [completed-prefix comparison](zeta-rough-squarefree-prime-balance.md)
remain unchanged.

## The exact arithmetic replacement

For a finite set of selected primes `S`, let

\[
L_S(n)=\begin{cases}
\log n,&n\text{ squarefree, not prime, and no }p\in S\text{ divides }n,\\
0,&\text{otherwise}.
\end{cases}
\]

The unit has weight zero. `zetaRoughSquarefreeCompositeLogWeight_nonneg`
proves nonnegativity at every integer. Write `A_{D,S}(n)` for the original
rough squarefree coefficient. The cutoff-one identity is

\[
A_{1,S}(n)=-L_S(n).
\]

For every `D>=1`, the richer identity keeps every nonunit divisor:

\[
A_{D,S}(n)+L_S(n)
=-\mathbf1_{\mathrm{squarefree}(n),\ \forall p\in S\ p\nmid n}
\sum_{\substack{1<d\le D\\d\mid n}}\mu(d)\log(n/d).
\]

This is
`zetaRoughSquarefreeCoefficient_add_compositeLog_eq_nonunit`. In a
divisor--cofactor representation, `n=dm`, every `d>1,m>1` is already
composite; the `m=1` term is zero because `log(1)=0`. Consequently the
ordinary-prime correction cancels between the two positive cutoffs.
The original coefficient can still change sign; the new one-sign statement
applies to the replacement weight `L_S`.

## Independent bound for the whole difference

Use the full original polynomial kernel

\[
K_{p,N}(s,n)=\left(\sum_k p_k\frac{\log(n)^{N+k}}{(N+k)!}\right)n^{-s}.
\]

All series in this comparison genuinely converge for `Re(s)>1`. Let
`A_{D,S,p,N}` and `L_{S,p,N}` denote their complete complex filtered sums,
and let `B_{D,S,p,N}` be the completed negative divisor prefix, including
ordinary primes. Lean proves the exact identity

\[
A_{D,S,p,N}+L_{S,p,N}=B_{D,S,p,N}-B_{1,S,p,N}.
\]

`zetaRoughSquarefreeFilter_add_compositeLog_eq_prefix_sub` retains the full
complex phase before any bound. The already proved independent estimates
for the two completed prefixes control their difference. No cancellation
bound for the prime correction is assumed.

At a hypothetical right-half zero, retain the original parameters

\[
u=\tfrac32-\Re\rho,\quad q=u^{-1/4},\quad D_N=\lfloor q^N\rfloor,
\quad R_N=\lfloor N\log(q)/8\rfloor^2,
\quad S_N=\{p\le R_N:p\text{ prime}\}.
\]

Use the unchanged pole-jet polynomial `p_rho` and ordinate `Im(rho)`.
With `lambda=2*sqrt(u)/(1+sqrt(u))<1`, the new theorem proves

\[
\boxed{
\left|u^{N+1}\bigl(A_{D,S_N,p_\rho,N}+L_{S_N,p_\rho,N}\bigr)\right|
\le C_\rho\lambda^N
\qquad(1\le D\le D_N).
}
\]

The constant works simultaneously for every such cutoff and every order.
The entry points are
`exists_zetaRightHalfRoughSquarefreePrefix_uniform_cutoff_bound` and
`exists_zetaRightHalfRoughSquarefree_nonunit_error_bound`. These estimates
use independent prefix bounds, not the hypothetical-zero source limit.

## Original source and finite errors

At `D=D_N`, the entire nonunit-divisor response tends to zero after
normalization. Combining this bound with the original source gives

\[
u^{N+1}L_{S_N,p_\rho,N}\longrightarrow m_\rho.
\]

This is `tendsto_zetaRightHalfRoughSquarefreeCompositeLogFilter`. It is
source transport, not an independent upper bound on `L`.

For the original finite Fourier carrier `C_N` and reflection work `W_N`,
whose exact relation is `Re(C_N)=-2W_N`, the new comparisons prove

\[
|u^{N+1}(L_N+C_N)|\le C_\rho\lambda^N+E_N,
\]

\[
\left|\frac{u^{N+1}\Re L_N}{2}-u^{N+1}W_N\right|
\le\frac{C_\rho\lambda^N+E_N}{2}\longrightarrow0.
\]

Here `E_N` is the existing `zetaAveragedWindowError`, containing both
physical localization and complementary Fourier errors. The terminal
theorems are
`exists_zetaRightHalfRoughSquarefreeCompositeLog_fourier_error_bound` and
`exists_zetaRightHalfRoughSquarefreeCompositeLog_reflection_error_bound`.

The remaining task is an independent strict upper bound for the real part
of this logarithmically weighted composite sum at the source scale, on a
cofinal subsequence. Its positive arithmetic weights do not make the
complex kernel terms positive. A bound for **all** rough squarefree
integers would again include the ordinary primes: their removal must be
paid, exactly as in the existing prime-balance theorem. No unrestricted
squarefree exponential-sum estimate is silently applied to composites.

This slice removes all nonunit divisor rows in one checked estimate. The
all-height edge width remains `1/(10 log(|t|+2))`; RH is open.
