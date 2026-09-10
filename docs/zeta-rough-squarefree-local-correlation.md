# Local arithmetic correlations and the remaining source

The independent strict bound for the original signed reflection work is
still open. This slice bounds an actual growing part of a quadratic form
built from the same physical samples. It does not improve the proved
zero-free region or establish an upper bound for the complete form.

## The unchanged samples and their finite comparison

For a hypothetical right-half zero `rho`, write

\[
u=3/2-\Re\rho\in(1/2,1),\qquad
D_N=\lfloor u^{-N/4}\rfloor,
\]

and let `p` be the existing complete pole-jet polynomial. On the original
finite band, the samples are exactly

\[
f_N(n)=u^{N+1}a_N(n)K_{p,N}(3/2+i\Im\rho,n),
\]

where `a_N` is the existing rough squarefree window coefficient. All its
divisor, squarefree, prime-avoidance and physical-window restrictions
remain unchanged. The full kernel keeps every complex polynomial
coefficient and the ordinate phase.

[`norm_sum_zetaRightHalfRoughSquarefreeNormalizedSample_sub_fourier_le`](../RiemannGaussian/ZetaRoughSquarefreeLocalCorrelation.lean)
proves, for every `N>=2`, that the difference between `sum f_N` and the
original normalized Fourier carrier is at most
`zetaLogWindowError + zetaAveragedWindowError`. Both complete errors already
have proofs of convergence to zero. The physical sum itself tends to
`-m_rho`, where `m_rho` is the actual analytic multiplicity.

## The independent estimate

The [general energy module](../RiemannGaussian/ZetaArithmeticLocalEnergy.lean)
first proves, for every dominated complex coefficient family, finite set
`T`, polynomial `p`, ordinate `y`, and `0<r<1`,

\[
\sum_{n\in T}|a(n)K_{p,N}(3/2+iy,n)|^2
 \le A(p,r)r^{-2N}.
\]

The constant is explicit in the genuine divisor-square Dirichlet mass at
exponent `2-r>1`. The proof combines the full kernel tilt with
`zetaMoebiusLogMajorant <= divisor_count*log(n)` and the previously proved
divisor-square summability. No signed cancellation or zero-free premise
enters this estimate.

For arbitrary complex samples, the complete ordered-pair form within
additive distance `H` satisfies

\[
\left|\sum_{\substack{n,m\in T\\ |n-m|\le H}}
 f(n)\overline{f(m)}\right|
 \le (2H+1)\sum_{n\in T}|f(n)|^2.
\]

The exact complementary form remains available before applying this
estimate. Setting `r=(1+sqrt(u))/2` and `H=D_N^4` gives the compiled theorem
[`exists_zetaRightHalfRoughSquarefreeLocalCorrelation_bound`](../RiemannGaussian/ZetaRoughSquarefreeLocalCorrelation.lean):

\[
\left|\sum_{\substack{n,m\in T_N\\ |n-m|\le D_N^4}}
 f_N(n)\overline{f_N(m)}\right|
 \le C_\rho\lambda_\rho^{2N}\longrightarrow0,
\qquad \lambda_\rho=\frac{2\sqrt u}{1+\sqrt u}<1.
\]

The cutoff includes its exact floor, and its fourth power is proved to
tend to infinity. The bound holds for every order, including the initial
orders. It covers the diagonal and all cross terms within that distance.

## What remains

The literal local and complementary ordered pairs sum to
`(sum f_N)*conj(sum f_N)`. Consequently
[`tendsto_zetaRightHalfRoughSquarefreeFarCorrelation`](../RiemannGaussian/ZetaRoughSquarefreeLocalCorrelation.lean)
proves

\[
\sum_{\substack{n,m\in T_N\\ |n-m|>D_N^4}}
f_N(n)\overline{f_N(m)}\longrightarrow m_\rho^2.
\]

This is a source theorem for the remaining pairs, not their independent
upper bound. Squaring is a test of an energy approach; the original target
remains one strict signed deficit for the original reflection work on a
cofinal subsequence. A bound for the quadratic complement would be another
possible route, but its premise has not been proved.

The new separation is additive. At large indices, pairs outside this band
can still have very close logarithms and nearly aligned ordinate phases.
The estimate therefore supplies no decorrelation claim at a fixed ratio
of indices. Extending the local band alone is not evidence that the full
source can be bounded. The next useful test must address a signed estimate
for the remaining actual pairs, with its full source-scale cost.

The earlier [completed-prefix test](zeta-rough-squarefree-prime-balance.md)
also remains relevant: the completed divisor sum is small, while its
ordinary-prime correction carries the full source. These new estimates do
not remove that correction.

All changes remain local. No new zero-free-region or RH milestone is
claimed; the generated panel remains an inventory of checked declarations.
