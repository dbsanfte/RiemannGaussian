# All divisor correlations and the surviving unit source

[`ZetaRoughDivisorCorrelation.lean`](../RiemannGaussian/ZetaRoughDivisorCorrelation.lean)
proves an independent uniform bound for every nonunit entry of a complex
divisor correlation. The original arithmetic source survives exactly in
the product of its two coefficients at divisor one. This applies to whole
classes of weights; the strict signed upper bound needed for RH is open.

## The full two-family carrier

Keep the original hypothetical right-half zero \(\rho=\beta+i\gamma\),
\(u=3/2-\beta\in(1/2,1)\), \(q=u^{-1/4}\), \(D_N=\lfloor q^N\rfloor\),
and small-prime cutoff \(R_N=\lfloor N\log(q)/8\rfloor^2\).
The set \(S_N\) contains the primes through \(R_N\).
Let \(b_S(n)\) be \(\log n\) on rough squarefree composites and zero elsewhere.
Retain the full original pole-jet kernel

\[
K_N(n)=\left(\sum_k a_k\frac{(\log n)^{N+k}}{(N+k)!}\right)
n^{-3/2}e^{-i\gamma\log n}.
\]

For **arbitrary complex families** \(w,v\), define

\[
W_{D,w}(n)=\sum_{\substack{d\le D\\d\mid n}}w(d),\qquad
C_N(w,v)=u^{N+1}\sum_n
W_{D_N,w}(n)\overline{W_{D_N,v}(n)}\,b_{S_N}(n)K_N(n).
\]

Both families may change with \(N\). They need not be Möbius coefficients,
real, multiplicative, or equal. The complete series genuinely converges.
The diagonal coefficient is exactly \(|W_{D,w}(n)|^2b_S(n)\ge0\), but the
kernel remains complex.

## The exact matrix and its independent bound

Every coefficient has the exact ordered-pair expansion

\[
W_{D,w}(n)\overline{W_{D,v}(n)}b_S(n)
=\sum_{d,e\le D}w(d)\overline{v(e)}\,
\mathbf1_{\operatorname{lcm}(d,e)\mid n}\,b_S(n).
\]

`coefficient_eq_pairs` and `hasSum_response` retain all shared-prime
intersections, lcm coincidences, coefficient phases and kernel phases.
The pair \((1,1)\) is separated exactly. Every other pair has a nonunit
lcm at most \(D^2\). The existing all-divisor estimate applies at original
divisor cutoff one; it includes the entire ordinary-prime correction.
Nonsquarefree or small-prime-excluded marks vanish exactly.

For \(L_D(w)=\sum_{d\le D}|w(d)|\), the complete nonunit remainder has bound

\[
C_{y,r}L_D(w)L_D(v)\,D(1+\log D^2)e^{4\sqrt R}r^{-N}
\sum_k|a_k|r^{-k},\qquad 0<r<1,\quad |y|>1.
\]

The original two-family remainder is retained as a complex finite sum
alongside this bound. No source limit is used to estimate it.

## Uniform source classification

Let

\[
U_N=u^{N+1}\sum_n b_{S_N}(n)K_N(n),\qquad
\eta_\rho=\frac{2u^{1/8}}{1+u^{1/8}}<1.
\]

For every pair of families satisfying the mass budget

\[
L_{D_N}(w)L_{D_N}(v)\le D_N^2,
\]

`exists_actual_error_bound` proves, uniformly in both families and at every
order,

\[
\boxed{\left|C_N(w,v)-w(1)\overline{v(1)}\,U_N\right|
\le C_\rho(1+N)\eta_\rho^N\longrightarrow0.}
\]

Thus this entire class has an asymptotically rank-one response: only its
unit interaction survives. Every pointwise bounded pair \(|w(d)|,|v(d)|\le1\)
fits the budget, as do some larger sparse weights. The bound does not
cover unrestricted coefficient mass or arbitrary larger support.

The original checked source satisfies \(U_N\to m_\rho\ge1\). Consequently,
if \(w_N(1)\overline{v_N(1)}\to c\), `tendsto_actualResponse` proves

\[
C_N(w_N,v_N)\longrightarrow c\,m_\rho.
\]

This is a statement about all admissible moving families. The unit product
may carry a complex phase; that phase is not discarded. Setting it to zero
removes the leading source, while keeping it equal to one preserves the
full multiplicity.

## The actual Möbius square and the open estimate

For \(w=v=\mu\), the divisor weight is the exact truncated mask \(M_D(n)\).
`coefficient_moebius` and `actualResponse_moebius` identify the diagonal
correlation with the [already checked squared Möbius source](zeta-rough-moebius-mixed-decay.md),
with no changed support, normalization or kernel.

This clarifies what coefficient selection can change: within the proved
budget, it changes the independently small nonunit remainder, while the
unit product determines the leading source. It does **not** establish that
all representations are equally useful for proving an independent bound,
and it does not rule out such a proof.

The goal still requires an independent cofinal upper bound strictly below
the retained unit source, with a positive margin after all errors. No such
bound is proved here. A useful next estimate must control the full signed
kernel against the original arithmetic support; nonnegative diagonal
coefficients alone do not do this.

All sums here are complete convergent arithmetic series. Physical-window
localization needs its own allowance. No additional zero is excluded,
the all-height edge width remains \(1/(10\log(|\gamma|+2))\), and RH is open.
