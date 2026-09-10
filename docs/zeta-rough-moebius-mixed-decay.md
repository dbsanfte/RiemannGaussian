# Mixed Möbius decay and the exact square source

The mixed logarithmic term now has an independent geometric bound in Lean.
The full multiplicity source transfers to a sum with a nonnegative squared
Möbius coefficient. Its oscillatory signed upper bound remains open.

The modules are
[`ZetaRoughSquarefreeBareFilter.lean`](../RiemannGaussian/ZetaRoughSquarefreeBareFilter.lean)
and
[`ZetaRoughMoebiusMixedDecay.lean`](../RiemannGaussian/ZetaRoughMoebiusMixedDecay.lean).
They build on the [all-divisor family bound and exact mask](zeta-rough-divisor-incidence.md).

## The precise term

For a hypothetical zero \(\rho=\beta+i\gamma\) with \(\beta>1/2\), keep

\[
u=\tfrac32-\beta\in(\tfrac12,1),\quad q=u^{-1/4},\quad
D_N=\lfloor q^N\rfloor,\quad R_N=\lfloor N\log(q)/8\rfloor^2.
\]

Let \(S_N\) contain every prime at most \(R_N\), and put

\[
M_D(n)=\sum_{\substack{d\mid n\\d\le D}}\mu(d),\qquad
L_D(n)=\sum_{\substack{d\mid n\\d\le D}}\mu(d)\log d.
\]

The original polynomial and its complete phase stay fixed:

\[
K_N(n)=\left(\sum_{k\in\operatorname{supp}p_\rho}
a_k\frac{(\log n)^{N+k}}{(N+k)!}\right)n^{-3/2}e^{-i\gamma\log n}.
\]

Here \(p_\rho\) is the existing exact pole-jet polynomial. The mixed response is

\[
T_N=u^{N+1}\sum_{\substack{n\text{ squarefree}\\
\forall a\in S_N,\ a\nmid n}}M_{D_N}(n)L_{D_N}(n)K_N(n).
\]

`RoughMoebiusMixed.exists_actual_bound` proves, for every \(N\ge1\),

\[
\boxed{|T_N|\le C_\rho(1+N)\eta_\rho^N\longrightarrow0,\qquad
\eta_\rho=\frac{2u^{1/8}}{1+u^{1/8}}<1.}
\]

`tendsto_actualResponse` states the full complex limit. Source convergence
is not used in this estimate. Completing this term to include ordinary
primes introduces no correction: \(M_D(p)L_D(p)=0\) for every prime.
For \(p\le D\), the first factor is zero; for \(p>D\), the second is zero.

## Why this estimate closes

For every polynomial \(p=\sum a_kX^k\), define

\[
p^{[N]}=\sum_k\frac{a_k}{N+k+1}X^k.
\]

`RoughSquarefreeBare.log_mul_kernel` proves exactly

\[
\log n\,K_{p^{[N]},N}(n)=K_{p,N+1}(n).
\]

Its coefficient envelope does not increase. This turns the existing
cutoff-one logarithmic prefix into a genuine bare squarefree series.
All finite small-prime exclusion intersections are retained. For every
natural divisibility mark \(P\), every \(0<r<1\), and \(|y|>1\), the complete
marked response at order \(N+1\) has bound

\[
C_{y,r}e^{4\sqrt R}r^{-N}
\sum_k|a_k|r^{-k},
\]

uniformly in \(P\). Zero, nonsquarefree and excluded marks are handled
exactly. The estimate uses the complete shared-prime correction, bounded
by the existing lcm divisor mass and then by four.

The mixed coefficient has the exact ordered-pair expansion

\[
M_D(n)L_D(n)=\sum_{d,e\le D}
\mu(d)\mu(e)\log e\;\mathbf1_{\operatorname{lcm}(d,e)\mid n}.
\]

`coefficient_eq_lcm_sum` retains every shared prime and lcm coincidence.
`hasSum_response` justifies the finite/infinite sum interchange. The entire
family costs at most \(D^2\log D\), giving the independent general bound

\[
C_{y,r}D^2\log D\;e^{4\sqrt R}r^{-N}
\sum_k|a_k|r^{-k}
\]

at order \(N+1\). On the actual schedule, this fits inside the proved
geometric allowance. No numerical coefficient selection is involved.

## What now remains

Write \(A_N(n)\) for the original rough squarefree composite coefficient.
The full pointwise identity, including zero-support cases, is

\[
M_D(n)A_N(n)=-M_D(n)^2\log n+M_D(n)L_D(n)
\]

on rough squarefree composites, and the corresponding supported identity
holds at every natural index. Hence the remaining response is exactly

\[
\boxed{Q_N=u^{N+1}
\sum_{\substack{n\text{ squarefree composite}\\
\forall a\in S_N,\ a\nmid n}}
M_{D_N}(n)^2\log n\;K_N(n)\ \longrightarrow\ m_\rho\ge1.}
\]

`tendsto_actualSquareResponse` proves this source limit.
`exists_actualSquare_source_error_bound` bounds **both** errors relative to
the negative of the original full rough response by one
\(C_\rho(1+N)\eta_\rho^N\) allowance: the full Möbius incidence error and
the mixed term just controlled.

The remaining arithmetic obligation is an independent inequality

\[
\Re Q_N\le1-\varepsilon
\]

for some fixed \(\varepsilon>0\) on a cofinal subsequence, for each
hypothetical right-half zero. `false_of_cofinal_square_bound` checks its
sufficiency. This inequality is not proved. Nonnegative coefficients do
not imply a sign or upper bound after multiplication by the complex kernel.

These theorems concern complete convergent arithmetic series. Any further
physical-window restriction needs its own allowance. The earlier balanced
weight \(1-k_N\) is a separate representation; its support estimates are
not transferred without proof. No additional zero is excluded, no new
zero-free margin is claimed, and RH remains open.

The subsequent [all-family correlation theorem](zeta-rough-divisor-correlation.md)
places this exact Möbius square inside the full class of admissible complex
divisor correlations. It controls every nonunit entry uniformly and shows
precisely which unit coefficient retains the multiplicity source.
