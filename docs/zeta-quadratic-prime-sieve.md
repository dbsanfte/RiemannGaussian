# A complete prime-pattern sieve with a quadratic cutoff

Lean proves an independent bound for the entire arithmetic contribution
from integers divisible by at least two selected primes. The exact
expansion includes every overlap. Its proved cost permits selecting all
primes through an explicit cutoff growing quadratically with the moment
order. The complete hypothetical-zero source survives this deletion,
the physical logarithmic window, and the existing smaller Fourier region.
Its independent signed upper bound remains open.

## Count the entire union before bounding it

Let `S` be any finite set of primes, and let `F(n)` be any complex
physical weight. Partition integers by their exact set `T` of selected
prime divisors, then expand the excluded primes:

\[
\mathbf1_{\#\{p\in S:p\mid n\}\ge2}F(n)
=\sum_{\substack{T\subseteq S\\|T|\ge2}}
  \sum_{U\subseteq S\setminus T}(-1)^{|U|}
  \mathbf1_{\prod_{p\in T\cup U}p\mid n}F(n).
\]

This identity holds for every physical integer, including zero. All
signs and coincident intersection factors are retained. Every actual
intersection factor contains at least two distinct primes, so the
existing mixed-prime arithmetic response applies to it. The pair-factor
description also agrees exactly with the original simultaneous sieve,
coefficient by coefficient and for the full convergent series.

Compiled entry points:

- [FinitePrimePatternSieve.lean](../RiemannGaussian/FinitePrimePatternSieve.lean):
  `primePairSieve_eq_signed_patterns`, `primePairSieve_card_iff`,
  `prime_pattern_factor_eligible`.
- [ZetaPrimePatternResponse.lean](../RiemannGaussian/ZetaPrimePatternResponse.lean):
  `zetaMoebiusPrimePatternCoefficient_eq_sieve`,
  `zetaMoebiusPrimePatternFilter_eq_sieve`,
  `hasSum_zetaMoebiusPrimePatternFilter`.

## Pay for every overlap together

Use the preceding [joint divisor-factor estimate](zeta-lcm-window-factor-bound.md),
with its complete correction

\[
A(P)=P^{-1/2}\sum_{g\mid P}g^{-1/2},\qquad
\kappa(P)=\min\{3,(1+\log P)A(P)\}.
\]

Multiplicativity on coprime products gives one bound for the whole
pattern expansion:

\[
\sum_{\substack{T\subseteq S\\|T|\ge2}}
\sum_{U\subseteq S\setminus T}\kappa\left(\prod_{p\in T\cup U}p\right)
\le \left(1+\sum_{p\in S}\log p\right)
     \prod_{p\in S}(1+2A(p))=:B(S).
\]

For every prime `p`, `A(p)<=2/sqrt(p)`. Summing the elementary bound
through any integer cutoff `R` proves, for every `S` of primes at most `R`,

\[
B(S)\le(1+R^2)e^{8\sqrt R}.
\]

Consequently the genuine union response, denoted `U_{D,S,p,N}(s)`, obeys

\[
|U_{D,S,p,N}(3/2+iy)|
\le C_y\sqrt D\,\|p\|_1 B(S)
\le C_y\sqrt D\,\|p\|_1(1+R^2)e^{8\sqrt R}
\]

for every polynomial filter, divisor cutoff, moment order, finite selected
prime family, and fixed `|y|>1`. This is a bound for the full signed
Möbius-tail series on the union. It includes its logarithmic companion,
all multiples, and all prime valuations. No overlap-budget hypothesis is
left to prove for this union.

Compiled entry points:

- [FinitePrimePatternSieve.lean](../RiemannGaussian/FinitePrimePatternSieve.lean):
  `sum_prime_pattern_lcm_cost_le`, `primePatternSieveCost_le_exp_sqrt`.
- [ZetaPrimePatternResponse.lean](../RiemannGaussian/ZetaPrimePatternResponse.lean):
  `exists_zetaMoebiusPrimePatternFilter_bound`,
  `exists_zetaMoebiusPrimePatternFilter_cutoff_bound`.

## An explicit quadratic cutoff is affordable

For any hypothetical right-half zero `rho=beta+i*y`, retain the original
divisor cutoff and choose

\[
u=\frac32-\beta\in(1/2,1),\quad q=u^{-1/4}>1,\quad
D_N=\lfloor q^N\rfloor,\quad c=\frac{\log q}{8},\quad
R_N=\lfloor cN\rfloor^2.
\]

Select **every prime at most `R_N`**. Lean proves `R_N` tends to infinity
and checks the complete cost, including integer rounding:

\[
B(S_N)\le(1+c^4N^4)q^N.
\]

Combining this with `sqrt(D_N)<=q^N` and `u*q^2=sqrt(u)` gives the
whole normalized union bound

\[
u^{N+1}|U_N|\le C_\rho(1+N^4)(\sqrt u)^N\longrightarrow0.
\]

The theorem concerns the actual source filter at the actual zero
ordinate. All analytic side conditions are discharged. The cutoff is a
proved sufficient choice, with no optimality claim.

Compiled entry points in
[ZetaQuadraticPrimeSieve.lean](../RiemannGaussian/ZetaQuadraticPrimeSieve.lean):

- `primePatternSieveCost_actual_le`
- `tendsto_zetaRightHalfPrimePatternCutoff`
- `exists_zetaRightHalfPrimePattern_error_bound`
- `tendsto_zetaRightHalfPrimePatternFilter`
- `exists_zetaRightHalfQuadraticSievedPrimeTail_error_bound`
- `tendsto_zetaRightHalfQuadraticSievedPrimeTail`

## The complete signed source reaches the new survivor

Apply the existing physical window `2*N/5<=log(n)<=8*N` and
[averaged-symbol localization](zeta-averaged-symbol-window.md) to the
actual remaining coefficients. Every nonzero retained coefficient has:

- `n>D_N^2` and the proved physical-window bounds;
- at least two distinct prime divisors overall;
- at most one prime divisor among all primes through `R_N`.

Keep the complete centered Fourier products in the `(6/7)^N` symbol
region. If their sum is `C_N` and their signed odd-reflection work is
`W_N`, Lean proves the exact identity and source limits

\[
\operatorname{Re}C_N=-2W_N,\qquad
u^{N+1}C_N\longrightarrow-m_\rho,\qquad
u^{N+1}W_N\longrightarrow\frac{m_\rho}{2}.
\]

For the original pole-jet response `L_N`, the finite comparison at every
`N>=2` is

\[
\left|-\frac{u^{N+1}\operatorname{Re}L_N}{2}-u^{N+1}W_N\right|
\le\frac{C_\rho(1+N^4)(\sqrt u)^N+
  \operatorname{zetaAveragedWindowError}(p_\rho,N,y)}2
\longrightarrow0.
\]

This allowance includes the original finite head, prime powers, the
entire prime-pattern union, both outer physical shells, and the whole
complementary Fourier interaction. The exact reflection cancellation
retains the centering corrections and all cyclic partners.

Compiled entry points in
[ZetaQuadraticWindowSource.lean](../RiemannGaussian/ZetaQuadraticWindowSource.lean):

- `zetaRightHalfQuadraticWindowCoefficient_support`
- `tendsto_zetaRightHalfQuadraticWindowFourierCarrier`
- `zetaRightHalfQuadraticWindowFourierCarrier_re_eq_reflection`
- `tendsto_zetaRightHalfQuadraticWindowReflectionWork`
- `exists_zetaRightHalfQuadraticWindowReflection_error_bound`
- `tendsto_zetaRightHalfQuadraticWindowTotalError`

## The remaining bound

The proved overlap budget controls the deleted prime-pattern union.
It does **not** control every remaining integer with at most one small
prime divisor. The cutoff grows quadratically in `N`, while the physical
indices in the window grow exponentially. The survivor is therefore
still a substantial arithmetic object with its full source intact.

The next task is to exploit that survivor's prime structure and signed
coupling to prove an independent upper bound strictly below
`m_rho/2` at arbitrarily late orders. Its decay is more than is needed;
any fixed strict saving suffices. No additional zeta zeros are excluded
by the present slice. The [all-height edge strip](zeta-completion-reserve-zero-free.md)
remains `1/(10 log(|t|+2))`, and RH remains open.

The next [complete squarefree sieve](zeta-squarefree-signed-source.md)
uses the retained shared-prime information and a variable Cauchy radius
to remove every nonsquarefree term, including all prime squares, with
independent geometric decay. The full signed source remains on the
squarefree survivor, whose strict upper bound is still open.
