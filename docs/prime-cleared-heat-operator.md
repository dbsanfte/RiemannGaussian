# The exact clearing weights inside the prime heat

The complete corrected prime heat now has one exact polynomial operator
inside each original prime summand. This applies to every complex clearing
polynomial. It identifies the factorial displacement and the signed
correction that must be included in an arithmetic lower bound. It supplies
no such independent bound and excludes no additional zeta zeros.

## Clearing before differentiation

Write `D` here for polynomial differentiation, `x=log(p)>0`, and let `N`
be the factorial order. Define

\[
S_{N,x}q=(1-x^{-1}D)^Nq.
\]

This is a power of an actual linear endomorphism of the whole polynomial
space. In
[FactorialPolynomialTransport.lean](../RiemannGaussian/FactorialPolynomialTransport.lean),
`shift_eq_binomial` proves its complete finite expansion

\[
S_{N,x}q=\sum_{k=0}^{N}\binom Nk(-x^{-1})^k q^{(k)}.
\]

The Gaussian transform `T_B` is the existing exact finite Hermite transform.
Put

\[
H_{B,N,x}q(z)=T_B(S_{N,x}q)(z).
\]

The theorem `heat_eq_binomial` retains every transformed derivative. With
`q_k=(-1)^k q^{(k)}/k!`, the arithmetic normalization is exactly

\[
\frac{x^N}{N!}H_{B,N,x}q(z)
 =\sum_{k=0}^N\frac{x^{N-k}}{(N-k)!}T_Bq_k(z).
\]

This is `factorialHeat_eq_leibniz` in
[ZetaPrimeClearedHeatOperator.lean](../RiemannGaussian/ZetaPrimeClearedHeatOperator.lean).
The proof uses the exact binomial/factorial identity and proves the required
nonzero logarithm at every supported prime.

## The same complete ordinary-prime expression

For any fixed cutoff and finite prime exclusion, `hasSum_clearedHeatPrime_operator`
and `clearedHeatPrimeResponse_eq_operator` prove genuine summability and

\[
\operatorname{clearedHeatPrimeResponse}_{B,q,D,S,N}(s)
 =\sum_{\substack{p\text{ prime}\\p>D,\ p\notin S}}
 \log(p)\,p^{-s}\frac{(\log p)^N}{N!}e^{-B(\log p)^2}
 H_{B,N,\log p}q\bigl(s+2B\log p\bigr),
 \qquad \operatorname{Re}s>1,\ B>0.
\]

The natural-index Lean sum has exactly this support. The indices zero and
one have zero actual coefficient. Every Leibniz row is absolutely summable
before the finite/infinite interchange. In particular the factor
`exp(-i*Im(s)*log(p))` stays in the original summand; no norm or sign
estimate replaces it.

`normalizedClearedPrimeHeat_eq_operator` specializes the identity to the
actual divisor polynomial and the unchanged source normalization. Thus the
[proved whole residual decay and negative source](prime-quadratic-heat-source.md)
apply to this very expression, without an extra analytic premise.

## The correction exposed by a squared factor

For every order, complex root and nonzero logarithmic coordinate,
`shift_factor` and `shift_factor_sq` give

\[
S_{N,x}(X-r)=X-r-N/x,
\]

\[
S_{N,x}(X-r)^2=(X-r-N/x)^2-N/x^2.
\]

After Gaussian transport, `heat_factor_sq` proves

\[
H_{B,N,x}(X-r)^2(z)
 =(z-r-N/x)^2-\underbrace{(2B+N/x^2)}_{\text{full signed correction}}.
\]

The term `N/x^2` comes from factorial differentiation before the Gaussian
acts. The term `2B` comes from Gaussian transport. Keeping only the latter
would miss part of the true arithmetic multiplier.

`clearedHeatPrimeResponse_factor_sq` inserts this exact formula into the
complete actual prime series. For real `x`, the separate sign test
`clearedHeatSquareMultiplier_displaced_root_neg` proves that at the
displaced root `z=r+N/x` the multiplier has strictly negative real part
whenever `B>0`. This rejects an inference from the untransformed square's
nonnegativity to the transformed multiplier's nonnegativity. It does not
claim that the repository's actual clearing polynomial is a single square,
or that the whole signed prime sum has been bounded.

## Arbitrary cofactors and the information needed next

The identity is not restricted to a chosen quadratic polynomial. For every
cofactor `q`, `heat_factor_mul_succ` proves

\[
\begin{aligned}
H_{B,N+1,x}((X-r)q)(z)
={}&(z-r)H_{B,N+1,x}q(z)\\
 &-2B H_{B,N+1,x}q'(z)
 -\frac{N+1}{x}H_{B,N,x}q(z).
\end{aligned}
\]

The theorem `clearedHeatPrimeResponse_factor` keeps these three channels
in the same original prime sum. It makes the derivative and adjacent-order
coupling available to a lower-bound argument without discarding their
correlations or the prime phase.

The remaining task is to control that complete signed arithmetic
expression independently of the hypothetical zero. A cofinal bound above
`-m*exp(-c)` by a fixed positive margin would contradict its proved
quadratic-width source. The operator identity and the negative-square test
do not establish such a margin. RH remains open. These finite derivative
and Hermite identities are not presented as historically novel mathematics.

## The closed recurrence for the complete prime heat

In [ZetaPrimeHeatRecurrence.lean](../RiemannGaussian/ZetaPrimeHeatRecurrence.lean),
`heat_succ` retains the derivative in the adjacent factorial step:

\[
H_{B,N+1,x}q=H_{B,N,x}q-x^{-1}H_{B,N,x}q'.
\]

At the actual displaced argument `z=s+2Bx`, `heat_factor_closed` combines
this step with the cofactor identity. Its derivative channel cancels
exactly against the displacement, provided the next order is retained.
After the exact factorial normalization and genuinely convergent prime
summation, `clearedHeatPrimeResponse_three_order` proves

\[
A_{N+1}[(X-r)q]=(s-r)A_{N+1}[q]-A_N[q]+2B(N+2)A_{N+2}[q].
\]

Here `A_N[q]` is the complete actual prime heat at fixed `B,s,D,S`.
The theorem holds for every complex polynomial `q` and root `r`, with
`B>0`, `Re(s)>1`, `D>=1` and a finite set `S` of primes. It preserves the
negative lower-order coefficient and the original prime phases.

For the actual normalized divisor polynomial, put `u=3/2-Re(rho)>0`,
`s_rho=3/2+i*Im(rho)` and `P_N(B)=u^(N+1)*A_N[q](B,s_rho)`.
Then `normalizedClearedPrimeHeat_three_order_quadraticWidth` proves

\[
\begin{aligned}
u^{N+1}A_{N+1}[(X-\rho)q](B_N,s_\rho)
={}&P_{N+1}(B_N)-P_N(B_N)\\
 &+\frac{2c}{N+1}P_{N+2}(B_N),
\qquad B_N=\frac{cu^2}{(N+1)(N+2)}.
\end{aligned}
\]

Every order here uses **the same `B_N`**. This is not a recurrence among
`P_N(B_N)`, `P_(N+1)(B_(N+1))` and `P_(N+2)(B_(N+2))`.

## Bounding the whole upper-order contribution

[ZetaPrimeHeatNeighbourBound.lean](../RiemannGaussian/ZetaPrimeHeatNeighbourBound.lean)
discharges the shared-width estimate. Under the hypothetical right-half
zero, for every fixed offset `j`, cutoff, sieve and `c>0`,
`tendsto_clearedPrimeRemainderHeat_sharedWidth` proves

\[
E_{N+j}(B_N)\longrightarrow0.
\]

The earlier central bound becomes `C*theta^(N+j)` with `0<theta<1`.
The outer bound becomes `A*G^(N+j)*T(B_N)`. Since `j` is fixed, its two
extra factors enter the constants, and the same quadratic Gaussian tail
absorbs the complete exponential order growth. No neighbouring width is
substituted for the original width.

The exact source identity `P_k(B)=-m*attenuation(k,u,B)+E_k(B)` and the
proved bounds `0<=attenuation<=1` give, at every positive width,

\[
|P_k(B)|\le m+|E_k(B)|.
\]

Consequently `eventually_norm_clearedPrimeHeat_upper_coupling_le` proves
the quantitative bound for the **whole** upper-order term:

\[
\left|\frac{2c}{N+1}P_{N+2}(B_N)\right|
\le\frac{2c(m+1)}{N+1}
\quad\text{eventually}.
\]

The right side tends to zero. The terminal theorem
`tendsto_clearedPrimeHeat_extraFactor_sub_difference` therefore proves

\[
u^{N+1}A_{N+1}[(X-\rho)q](B_N,s_\rho)
-\bigl(P_{N+1}(B_N)-P_N(B_N)\bigr)\longrightarrow0.
\]

This is a proved asymptotic identity under the hypothetical zero, not an
independent lower bound against that zero. The extra factor `X-rho`
deliberately removes the selected pole. Even if its heat tends to zero,
that would be compatible with a nonzero negative source in `P_N`.
Likewise, a bound on consecutive differences needs a controlled boundary
value and a justified reconstruction before it can bound the original
heat. Changing widths during that reconstruction also needs its own
estimate. The [complete-band audit](prime-heat-band-accumulation.md) now
proves that the accumulated upper corrections retain a fixed negative
source, even though a single neighbour vanishes. Its exact telescoping
identity preserves this band and both endpoint heats. The remaining
independent signed prime inequality is still open. RH and the zero-free
region are unchanged.
