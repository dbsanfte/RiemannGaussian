# Simultaneous arithmetic deletion with a cofinal sieve

Lean now combines the [uniform multiple-sector bounds](zeta-moebius-factor-decay.md)
into one explicit growing sieve, with every overlap correction included.
The deleted union is independently negligible at the original zero-source
scale. The original finite head, prime powers, and sieve corrections fit
one geometric error bound. The surviving distinct-prime arithmetic sum
still carries the full source; its signed bound remains open.

The [joint sieve and Fourier localization](zeta-sieved-fourier-localization.md)
now transports this exact support through the finite-band and centered
Fourier reductions. Retaining the band's lower endpoint gives extra
geometric mass decay and a smaller justified frequency region, with the
whole multiplicity source preserved.

## Exact overlaps before taking norms

For an arbitrary finite set `S` of factors, let

\[
\mathcal T(S)=\{T\subseteq S:T\ne\varnothing\},\qquad
L_T=\operatorname{lcm}(T).
\]

The union mask has the exact inclusion-exclusion expansion

\[
\mathbf1_{\exists P\in S:P\mid n}
 =\sum_{T\in\mathcal T(S)}(-1)^{|T|+1}\mathbf1_{L_T\mid n}.
\]

Equal least common multiples are grouped first:

\[
w_S(Q)=\sum_{\substack{T\in\mathcal T(S)\\L_T=Q}}(-1)^{|T|+1},
\qquad W(S)=\sum_Q|w_S(Q)|.
\]

These are the exact prescribed overlap coefficients. They are not chosen
by numerical fitting. The full complex arithmetic test function remains
inside the identity. Lean proves

\[
W(S)\le|\mathcal T(S)|\le2^{|S|},
\]

while retaining the exact grouped cost for later sharper bounds. If all
members of `S` are positive, greater than one, and not prime powers,
every nonempty intersection factor has those same properties.

Compiled entry points in
[FiniteDivisibilitySieve.lean](../RiemannGaussian/FiniteDivisibilitySieve.lean):

- `divisibilitySieve_eq_intersections`
- `sum_divisibilitySieveCoefficient`
- `divisibilitySieve_eq_grouped`
- `divisibilitySieveCost_le_card` and `divisibilitySieveCost_le_pow`
- `divisibilitySieveSupport_eligible`

## An independent bound for the actual union

Keep the original coefficient and kernel

\[
c_D(n)=\sum_{ab=n,\ a>D}\mu(a)\log b,\qquad
K_{p,N,s}(n)=n^{-s}\sum_k p_k\frac{(\log n)^{N+k}}{(N+k)!}.
\]

Define the actual removed arithmetic sum

\[
U_{D,S,N}(s)=\sum_{\exists P\in S:P\mid n}c_D(n)K_{p,N,s}(n).
\]

Each product is included once. Lean proves genuine convergence on
`Re s>1` and its exact equality with the grouped multiple-sector family.
For `|y|>1`, the independent sector bound gives

\[
|U_{D,S,N}(3/2+iy)|\le C_yD\Bigl(\sum_k|p_k|\Bigr)W(S).
\]

This controls the norm of the signed arithmetic sum. It does not replace
that sum by its termwise absolute values. The norm is taken after the
arithmetic sector identities and overlap grouping.

At a hypothetical right-half zero `rho=beta+i*gamma`, set

\[
u=3/2-\beta\in(1/2,1),\quad
D_N=\lfloor(u^{-1/4})^N\rfloor,
\]

and use the existing pole-jet polynomial. One constant gives the uniform
bound `|u^(N+1) U_{D_N,S,N}|<=C_rho*(sqrt u)^N` for every eligible finite
`S` with `W(S)<=D_N`.

Compiled entry points in
[ZetaMoebiusFiniteSieve.lean](../RiemannGaussian/ZetaMoebiusFiniteSieve.lean):

- `hasSum_zetaMoebiusSieveFilter`
- `zetaMoebiusSieveFilter_eq_grouped`
- `exists_zetaMoebiusSieveFilter_bound`
- `exists_zetaRightHalfMoebiusSieve_uniform_bound`
- `zetaMoebiusLogTailFilter_eq_sieve_add_remainder`

## One explicit cofinal schedule

Take the binary integer logarithm

\[
H_N=\lfloor\log_2D_N\rfloor,\qquad
S_N=\{P<H_N:P>1,\ P\text{ is not a prime power}\}.
\]

Lean discharges the whole cost chain at every order:

\[
W(S_N)\le2^{|S_N|}\le2^{H_N}\le D_N.
\]

It also proves `H_N` tends to infinity and every fixed eligible factor
eventually belongs to this same sieve. Thus all multiples of an increasing
collection of factors are deleted simultaneously, including arbitrarily
large product indices. No unbounded factor sum is exchanged with a limit.

Compiled entry points in
[ZetaMoebiusGrowingSieve.lean](../RiemannGaussian/ZetaMoebiusGrowingSieve.lean):

- `divisibilitySieveCost_zetaMoebiusSieveHead_log_le`
- `tendsto_natLog_two_of_tendsto`
- `zetaRightHalfMoebiusSieve_budget`
- `eventually_mem_zetaRightHalfMoebiusSieve`
- `tendsto_zetaRightHalfMoebiusGrowingSieve`
- `tendsto_zetaRightHalfMoebiusGrowingSieve_divisor_remainder`

## Prime powers, total error, and the surviving support

Every mixed-prime multiple sector lies inside the already defined
distinct-prime coefficient, so this deletion commutes with the earlier
prime-power removal. Define the final actual coefficient by

\[
b_{D,S}(n)=\mathbf1_{\nexists P\in S:P\mid n}\,
 \mathbf1_{n\text{ has at least two distinct prime factors}}\,c_D(n).
\]

Let `R_N=sum_n b_{D_N,S_N}(n) K_{p,N,3/2+i*gamma}(n)` and let `L_N`
denote the original `zetaPrimeLogFilter`. Lean proves both

\[
|u^{N+1}(L_N-R_N)|\le C_\rho(\sqrt u)^N,
\qquad u^{N+1}R_N\longrightarrow-m_\rho.
\]

The first theorem accounts for the finite Möbius head, all prime powers,
and the entire simultaneous sieve. Its constant is finite and every
arithmetic and convergence premise is discharged for the selected data.

For a nonzero final coefficient, Lean also proves

\[
n\ge2(D_N+1),\qquad
\exists p\ne q\text{ prime dividing }n,\qquad
pq\ge H_N\text{ for every such pair}.
\]

This is a restriction on every pair of distinct prime divisors. One
individual prime may still be small, and no separation of their Fourier
phases is asserted.

Compiled entry points in
[ZetaMoebiusSievedPrimeTail.lean](../RiemannGaussian/ZetaMoebiusSievedPrimeTail.lean):

- `zetaMoebiusDistinctPrimeCoefficient_eq_sieve_add_remainder`
- `hasSum_zetaMoebiusSievedPrimeFilter`
- `exists_zetaRightHalfSievedPrimeTail_error_bound`
- `tendsto_zetaRightHalfSievedPrimeTail`
- `zetaMoebiusSieveHead_survivor_prime_pair`
- `zetaMoebiusSievedPrimeCoefficient_support`

## The remaining arithmetic target

The source has not been contradicted. Its real part still tends to
`-m_rho`, with positive integer multiplicity. An independent bound such as
`Re(u^(N+1)*R_N)>=-1/2` at arbitrarily late orders would therefore suffice
for a contradiction. No such bound has been proved.

The next estimate can use the surviving prime-divisor restrictions while
keeping the original Möbius signs, full product phases, and grouped
overlap coefficients. The sieve threshold is not a zeta-zero bound, and
this slice excludes no additional zeros. The previously ruled-out
fractional absolute-kernel allowance remains ruled out. These sieve
identities use classical inclusion-exclusion; no historical novelty claim
has been established.
