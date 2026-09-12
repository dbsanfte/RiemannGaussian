# Keeping polynomial factors inside the prime heat average

The positive Gaussian does not make the original complex prime moment
positive. A second issue is the order of operations: multiplication by a
pole-clearing polynomial does not commute with Gaussian smoothing. This
slice proves the exact correction for every complex polynomial and
transports it through the complete convergent ordinary-prime series.

The identities are applications of the Gaussian Stein/Weyl identity and
Hermite recursion. No historical novelty is claimed for those general
identities. Their use here retains the original arithmetic support,
factorial moment filter and all complex signs.

## Full polynomial transport

For `B > 0`, define the unnormalized vertical average

\[
H_B[q](s,x)=\int_{\mathbb R}q(s-iy)
 e^{-y^2/(4B)}e^{iyx}\,dy,
\qquad M_B=\sqrt{4\pi B}.
\]

Lean uses the equivalent mass expression
`sqrt(pi/(1/(4*B)))`. Every polynomial-weighted integral is genuinely
integrable. Integration of the full derivative gives

\[
H_B[Xq](s,x)=(s+2Bx)H_B[q](s,x)-2B H_B[q'](s,x).
\]

Define the finite signed moments by

\[
W_0(B,z)=1,\quad W_1(B,z)=z,\quad
W_{n+2}(B,z)=zW_{n+1}(B,z)-2B(n+1)W_n(B,z),
\]

and, for `q(X)=sum_k q_k X^k`, set

\[
T_Bq(z)=\sum_k q_k W_k(B,z).
\]

Then the exact all-polynomial theorem is

\[
H_B[q](s,x)=M_B e^{-Bx^2}T_Bq(s+2Bx).
\]

In [GaussianPolynomialTransport.lean](../RiemannGaussian/GaussianPolynomialTransport.lean),
the terminal theorems are `weighted_X_mul`, `weighted_eq_transport` and
`transport_factor`. In particular,

\[
T_B[(X-r)q](z)=(z-r)T_Bq(z)-2B T_Bq'(z),
\]

and the complete double-factor identity is

\[
\begin{aligned}
T_B[(X-r)^2q](z)
={}&((z-r)^2-2B)T_Bq(z)\\
&-4B(z-r)T_Bq'(z)+4B^2T_Bq''(z).
\end{aligned}
\]

Here `T_Bq'` means transport of the derivative polynomial. Both derivative
terms are retained by `transport_double_factor`. For the squared factor
alone, `transport_linear_square` gives

\[
T_B[(X-r)^2](z)=(z-r)^2-2B,
\qquad T_B[(X-r)^2](r)=-2B.
\]

Thus the transport does not preserve a double polynomial root. This is an
operator identity, not evidence of an error in the existing source theorem:
the earlier diagonal comparison does not assume these operations commute.

## The actual full prime series

Retain the original response

\[
P_{p,D,S,N}(s)=\sum_n c_{D,S}(n)K_{p,N}(s,n),
\]

where the polynomial `p` is the original factorial moment filter. For
`D >= 1`, the coefficient `c` is `log(n)` precisely for ordinary primes
`n > D` outside the finite prime sieve `S`, and is zero otherwise. The new
polynomial `q` is a separate multiplier on the spectral variable. It must
not be identified with `p` without a proved conversion.

For every `Re(s) > 1`, `B > 0`, complex polynomials `q,p`, moment order `N`,
cutoff `D` and finite prime sieve `S`, Lean proves

\[
\begin{aligned}
&\int_{\mathbb R}q(s-iy)e^{-y^2/(4B)}P_{p,D,S,N}(s-iy)\,dy\\
&\quad=M_B\sum_n c_{D,S}(n)K_{p,N}(s,n)e^{-B\log^2 n}
 T_Bq(s+2B\log n).
\end{aligned}
\]

Both the entire average and the resulting arithmetic series are absolutely
integrable/summable. The exact integral norm of each term is the original
arithmetic term's norm times

\[
\int_{\mathbb R}|q(s-iy)|e^{-y^2/(4B)}\,dy.
\]

That finite mass pays for the complete infinite interchange before the
formula is used. The proof makes no positivity assertion about the complex
moment or about the transported multiplier.

The terminal theorems in
[ZetaPrimePolynomialHeat.lean](../RiemannGaussian/ZetaPrimePolynomialHeat.lean)
are `integrable_polynomialHeatPrimeResponse`,
`integral_polynomialHeatPrimeResponse` and
`summable_polynomialHeatPrimeResponse`.
`polynomialHeatPrimeResponse_double_factor` retains the entire three-term
double-factor correction inside the prime sum. The specialization
`integral_squaredFactor_primeHeat` retains the literal multiplier

\[
(s+2B\log n-r)^2-2B.
\]

All coefficients are mathematically defined. No search for a preferred
numerical family is involved.

## Clearing, differentiation and the remaining bound

Clearing a meromorphic function before differentiating it also needs the
full product rule. For normalized signed moments `M_N`, the existing
[signedTaylorMoment_mul](../RiemannGaussian/AnalyticDoublePoleMoments.lean)
proves

\[
M_N(qF)(s)=\sum_{k=0}^{N}\frac{(-1)^k}{k!}q^{(k)}(s)M_{N-k}(F)(s).
\]

Multiplying an already differentiated moment by a fixed low-degree
polynomial generally does not clear its higher-order poles.
[ZetaPrimeClearedHeat.lean](../RiemannGaussian/ZetaPrimeClearedHeat.lean)
now proves this full ordering for the actual fixed-support prime series
`F(s) = LSeries(c_(D,S),s)`. Write

\[
q_k=\frac{(-1)^k}{k!}q^{(k)},\qquad
C_{q,D,S,N}(s)=M_N(qF)(s).
\]

The theorems `clearedPrimeMoment_eq_leibniz` and
`integral_clearedPrimeMoment_heat` give, with absolute integrability proved,

\[
\begin{aligned}
&\int_{\mathbb R} e^{-y^2/(4B)}C_{q,D,S,N}(s-iy)\,dy\\
&\quad=M_B\sum_{k=0}^{N}\sum_n c_{D,S}(n)K_{1,N-k}(s,n)
 e^{-B\log^2 n}T_Bq_k(s+2B\log n).
\end{aligned}
\]

Every downward factorial order and every Hermite correction is present.
This is a formula for the moment of the cleared function; `q` is still
distinct from the earlier factorial filter `p`.

## The actual divisor polynomial and its selected source

[MeromorphicPolynomialSource.lean](../RiemannGaussian/MeromorphicPolynomialSource.lean)
identifies the existing common clearing weight on a compact domain with
the literal polynomial

\[
Q(X)=\prod_{z\in\operatorname{supp}e}(X-z)^{e(z)},\qquad
e(z)=\begin{cases}
0&z=\rho,\\
\max(0,-\operatorname{div}f(z),-\operatorname{div}g(z))&z\ne\rho.
\end{cases}
\]

The support is proved finite and all exponents are nonnegative. The selected
value `Q(rho)` is nonzero. A linear regularization fills every removed pole
and retains exactly `Q(rho)` times the selected simple-pole residue.
`exists_meromorphicClearingPolynomial_source` bounds the normalized moment's
error by `C*(abs(s-rho)/R)^N` on the actual analytic disc.

This is applied to the actual arithmetic response in
[ZetaPrimeClearedSource.lean](../RiemannGaussian/ZetaPrimeClearedSource.lean).
For every **fixed** `D >= 1` and finite prime sieve `S`, its continuation is

\[
F_{D,S}(s)=-\frac{\zeta'(s)}{\zeta(s)}-E(s)
 -\sum_{\substack{p\text{ prime}\\p\le D\ \text{or}\ p\in S}}
   (\log p)p^{-s},
\]

where `E` is the actual proper-prime-power series, analytic on `Re(s)>1/2`.
Lean proves equality with the original convergent prime tail on `Re(s)>1`
and proves that the residue at every hypothetical right-half zero is
exactly `-m_rho`. Neither subtraction changes it.

At `s_rho=3/2+i*Im(rho)`, use the existing compact radius
`R=5/4-Re(rho)/2`. The actual divisor defines `Q`, and
`q=Q/Q(rho)` has selected value exactly one. With `u=3/2-Re(rho)`,
`exists_normalizedClearedPrimeMoment_source_error` proves

\[
\left|u^{N+1}C_{q,D,S,N}(s_\rho)+m_\rho\right|
 \le C\left(\frac{u}{R}\right)^N,
\qquad 0<\frac{u}{R}<1.
\]

`tendsto_normalizedClearedPrimeMoment` therefore retains the negative
multiplicity source. The same actual polynomial is covered by the complete
Leibniz and heat identities above. Its coefficients are determined by the
whole finite divisor; no numerical coefficient search or assumed arithmetic
bound is used.

## Remaining obligations

The new source estimate is **before Gaussian smoothing**, for fixed cutoff
and exclusions. Its constants and clearing polynomial may depend on that
fixed data. It does not supply uniformity for moving cutoffs or a joint
growing-order, shrinking-width source estimate. The earlier source theorems
for the original factorial filter remain intact.

The subsequent [quadratic heat source slice](prime-quadratic-heat-source.md)
evaluates the exact Gaussian pole factor and proves that every positive
relative quadratic width retains a fixed nonzero source fraction. It also
proves an exact decomposition of the actual full prime heat, uniform
central residual decay, and a global Euler-line envelope. The whole residual
heat now tends to zero at every fixed positive quadratic relative width,
including the outer Gaussian tails. The actual full negative source survives
on this explicit schedule for fixed cutoff and sieve.
An independent signed arithmetic estimate for the full expression remains
necessary. The original required cofinal lower bound with a fixed gap above
`-1` is open. A positive Gaussian does not make the complex Leibniz/Hermite
sum positive. No improved zero-free region or proof of RH follows here.
