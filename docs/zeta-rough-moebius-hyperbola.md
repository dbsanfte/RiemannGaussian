# Divisor reflection and the remaining mixed source

[`ZetaRoughMoebiusHyperbola.lean`](../RiemannGaussian/ZetaRoughMoebiusHyperbola.lean)
proves an exact divisor-complement identity for the actual compensated
arithmetic series, and an independent bound for its complete small-product
part. The global signed bound and RH remain open.

Write

\[
M_D(n)=\sum_{\substack{d\mid n\\1\le d\le D}}\mu(d),\qquad
L_D(n)=\sum_{\substack{d\mid n\\1\le d\le D}}\mu(d)\log d,
\qquad E_D(n)=\left\lfloor\frac{n}{D+1}\right\rfloor.
\]

Here \(A_{D,S}(n)\) is the existing rough squarefree composite tail
`zetaRoughSquarefreeCoefficient D S n`. Let
\(B_{D,S}(n)\) be \(M_D(n)L_D(n)\) on squarefree integers with no
prime divisor in \(S\), and zero elsewhere. Its value on every ordinary
prime and on the unit is already proved to be zero.

The exact reflected identity

For every squarefree nonunit \(n\), divisor complementation gives

\[
M_D(n)+\mu(n)M_{E_D(n)}(n)=0.
\]

On the original rough squarefree composite support,

\[
A_{D,S}(n)=\mu(n)L_{E_D(n)}(n).
\]

Combining these identities, with \(\mu(n)^2=1\), yields the fully
supported identity, including all excluded indices:

\[
\boxed{M_D(n)A_{D,S}(n)=-B_{E_D(n),S}(n).}
\]

The inclusive reflected endpoint is essential. For \(d\mid n\) and
\(n>0\), the proof uses exactly
\(D<n/d\iff d\le n/(D+1)\). It does not replace integer division by
a continuous cutoff. The general `weighted_tail_reflection` theorem
retains an arbitrary complex cofactor weight, as well as total Möbius
parity. This is an application of the classical divisor involution; no
claim of mathematical priority is made.

Writing \(b_S(n)\) for the original rough squarefree composite logarithmic
weight also gives the pointwise complementary split

\[
M_D(n)^2b_S(n)=B_{D,S}(n)+B_{E_D(n),S}(n).
\]

`compensatedCoefficient_reflection` and
`squareCoefficient_eq_complementary_mixed` prove these statements with
the literal coefficients. `hasSum_response` proves convergence of the
complete reflected series for \(\Re s>1\).

An independently controlled part

At a hypothetical right-half zero \(\rho\), keep the existing definitions

\[
u=3/2-\Re\rho\in(1/2,1),\qquad q=u^{-1/4},\qquad
D_N=\lfloor q^N\rfloor.
\]

The sieve \(S_N\), polynomial \(p_\rho\), ordinate and complex kernel
are unchanged. On positive integers that kernel is

\[
K_N(n)=\left(\sum_{k\in\operatorname{supp}(p_\rho)}
\frac{a_k(\log n)^{N+k}}{(N+k)!}\right)
n^{-3/2}e^{-i\Im(\rho)\log n}.
\]

The new independent estimate is

\[
\left|u^{N+1}\sum_{n\in T}
B_{E_{D_N}(n),S_N}(n)K_N(n)\right|
\le C(p_\rho)(9/10)^N,
\qquad T\subseteq\{n:n\le D_N^3\}.
\]

`norm_normalized_reflected_head_le` is stronger in scope: it covers
every finite subset of this range, every complex polynomial, every real
ordinate, and every finite prime sieve. `norm_actualHead_le` specializes
it to the actual source. The explicit constant is the existing
`zetaArithmeticSmallProductConstant`.

The proof bounds the reflected coefficient by the original divisor-log
majorant times \(D_N\). Applying the existing cubic small-product
estimate to the coefficient divided by \(D_N\) costs at most
\(D_N(3/4)^N\). Since \(D_N\le q^N\) and \(q\le6/5\), this is at most
\((9/10)^N\). The argument does not use a source limit or assume prime
cancellation.

What remains

The complete normalized reflected response tends to the positive
multiplicity \(m_\rho\), by `tendsto_actualResponse`.
`summable_tailResponse`, `tailResponse_eq` and `actualTail_eq` justify
its exact partition into the finite head and the literal infinite series
over \(n>D_N^3\). Since the head tends independently to zero,
`tendsto_actualTail` retains the entire source in that high-product series.
On its support the reflected cutoff satisfies the exact inequality
\(D_N^2<E_{D_N}(n)+D_N\), proved by `reflected_cutoff_large`.

The earlier mixed-decay theorem bounds a series with one fixed cutoff at
each moment order. Here the cutoff changes with each summation integer.
That theorem therefore does not bound this adaptive series. The identity
clarifies this distinction and controls the stated head; it does not
establish a signed saving on the surviving tail. Such a saving, strictly
below the unit source on a cofinal subsequence, remains the required
arithmetic step. No additional zero exclusion or improvement of the
all-height edge strip is claimed.
