# All bounded prime-incidence families inside the rough squarefree carrier

[`ZetaRoughPrimeIncidence.lean`](../RiemannGaussian/ZetaRoughPrimeIncidence.lean)
proves an independent bound for the original arithmetic carrier marked by
each selected prime. Its companion,
[`ZetaRoughPrimeIncidenceSource.lean`](../RiemannGaussian/ZetaRoughPrimeIncidenceSource.lean),
uses that bound to cancel the unbalanced semiprime arm exactly and retain
the full source on a corrected balanced sum. Squarefreeness, roughness and
every incidence correction remain present. The independent signed bound
needed for RH remains open.

## The actual terms

For a hypothetical zero `rho` with real part greater than one half, put

\[
u=\tfrac32-\Re\rho\in(\tfrac12,1),\qquad
q=u^{-1/4},\qquad D_N=\lfloor q^N\rfloor,
\]
\[
R_N=\left\lfloor\frac{N\log q}{8}\right\rfloor^2,
\qquad S_N=\{p\le R_N:p\text{ prime}\}.
\]

Let `A_{D,S}(n)` be the existing `zetaRoughSquarefreeCoefficient`: the
original divisor-tail coefficient on rough squarefree composites, zero
elsewhere. Let `K_N(n)` be the original complex kernel with the exact
pole-isolating polynomial and ordinate of `rho`.

The new `actualFibre` is exactly

\[
F_{N,a}=u^{N+1}\sum_{a\mid n} A_{D_N,S_N}(n)K_N(n).
\]

These are complete, genuinely convergent arithmetic series. There is no
additional physical-window restriction in this theorem.

## Uniform total-variation bound

For every finite set `T` of primes outside `S_N` and at most `D_N^4`, Lean
proves

\[
\boxed{\quad\sum_{a\in T}|F_{N,a}|
\le C_\rho(1+N)\eta_\rho^N\longrightarrow0,\qquad
\eta_\rho=\frac{2u^{1/8}}{1+u^{1/8}}<1.\quad}
\]

The constant is independent of `N` and `T`. The norm is taken after the
complete signed arithmetic sum for each marked prime. This is not a bound
for the sum of the absolute values of individual integer terms.

The terminal theorems are `exists_actual_sum_norm_bound` and
`tendsto_actual_sum_norm` in namespace `RiemannGaussian.RoughPrimeIncidence`.
For arbitrary moving complex weights with `|w_N(a)|<=1`, the same theorem
therefore controls

\[
u^{N+1}\sum_n A_{D_N,S_N}(n)K_N(n)
\underbrace{\sum_{\substack{a\in T_N\\a\mid n}}w_N(a)}_{\text{exact incidence weight}}
\longrightarrow0.
\]

`hasSum_weight` proves the exact identity, including the sum interchange;
`tendsto_actual_incidence` proves this literal arithmetic decay. The sets and
complex weights may change at every moment order. No coefficient search or
unproved arithmetic cancellation premise is used.

## Why the enlarged prime range fits

For a marked prime `a` outside the original small-prime sieve, the exact
completion is

\[
\sum_{a\mid n} A_{D,S}(n)K_N(n)
=\sum_{W\subseteq S}(-1)^{|W|}H_{D,W\cup\{a\},N}
+\log(a)K_N(a),
\]

where `H` is the existing complete negative divisor prefix on squarefree
multiples of the indicated prime product. The last term is the full
ordinary-prime correction; it has not been dropped.

At any fixed Cauchy radius `0<r<1`, the squarefree intersection machinery
keeps the marked-prime weight

\[
w_r(a)=a^{-\tau}(1+a^{-\tau}),\qquad\tau=1-r/2>1/2.
\]

The sum of these corrected weights over selected primes through `X` is at
most `4 sqrt(X)`. The finite prime correction costs at most
`2 sqrt(X) log(X)` times the same radius-weighted kernel allowance. Thus
`exists_sum_norm_fibre_bound` gives the complete bound

\[
C_{y,r}D\,e^{4\sqrt R}\sqrt X(1+\log X)r^{-N}
\sum_{k\in\operatorname{supp}P}|P_k|r^{-k}.
\]

Keeping the exact factor four in the existing quadratic cutoff gives
`exp(4 sqrt(R_N)) <= (sqrt(q))^N`, proved in
`exp_sqrt_cutoff_bound`. With `X=D_N^4`, the exponential cost is therefore
at most `q^(7N/2)`. Source normalization leaves `u^(N/8)`.
Choosing `r=(1+u^(1/8))/2` produces the displayed strict geometric rate;
the logarithmic factor costs only `1+N`.

## Exact cancellation of the unbalanced semiprime arm

Now mark every retained prime through `D_N`, and let `k_N(n)` count those
which divide `n`. Subtract their complete incidence response from the
original carrier. The resulting coefficient is exactly

\[
\widetilde A_N(n)=(1-k_N(n))A_{D_N,S_N}(n).
\]

Every unbalanced semiprime `p*q` with `q<=D_N<p` contains exactly one such
prime unless it is already excluded by the original sieve. Its new
coefficient is therefore zero, identically. This is proved by
`compensatedCoefficient_unbalanced_semiprime_zero`. The existing cofactor
geometry then proves that above `D_N^3`, every remaining nonzero coefficient
admits two factors exceeding `D_N` (`compensatedCoefficient_balanced`).

The whole compensated head through `D_N^3` has the independent bound

\[
|\text{smallPart}_N|\le2C(P)(9/10)^N\longrightarrow0.
\]

The proof pays for every added mark: there are at most `D_N` of them, each
restricted head is covered by the earlier `(3/4)^N` small-product bound,
and `q<=6/5`. No cancellation premise for small products is needed.

Consequently the complete response

\[
\widetilde B_N=u^{N+1}
\sum_{\substack{n>D_N^3\\\exists a,b>D_N:\ n=ab}}
(1-k_N(n))A_{D_N,S_N}(n)K_N(n)
\longrightarrow -m_\rho
\]

retains the full multiplicity source. This sum counts each integer once;
the factorization condition is existential. `tendsto_balanced_source`
proves the limit, and `balancedPart_eq_source_sub_corrections` keeps the
exact complex identity. `exists_balanced_error_bound` proves at every order

\[
|\widetilde B_N-\text{original full rough response}_N|
\le C_\rho(1+N)\eta_\rho^N+2C(P)(9/10)^N\longrightarrow0.
\]

This removes the separate unbalanced arm from the new target by a proved
subtraction. It does not assert that the old unbalanced sum itself decays.

## What is still missing

With all weights equal to one, an integer containing two selected primes
appears twice. The union indicator would count it once. A signed estimate
for the incidence-weighted sum does not imply an estimate for that union.
The arithmetic terms also have complex phases, so no positivity comparison
allows the distinction to be ignored.

The new balanced coefficient therefore retains `1-k_N(n)` exactly. The
remaining sufficient target is an independent inequality
`Re(balancedPart_N)>=-1+epsilon`, for some fixed `epsilon>0`, on a cofinal
subsequence. `false_of_cofinal_balanced_bound` proves the conditional
contradiction; it does not prove that arithmetic premise. Arbitrary further
restrictions of these complete series also require their own error estimate.

This slice gives no additional zero exclusion. The proved all-height edge
width remains `1/(10 log(|t|+2))`. The complete RH contradiction is open.

The subsequent [all-divisor extension](zeta-rough-divisor-incidence.md)
controls every bounded squarefree-divisor family through `D_N^4`, including
higher prime intersections. It gives a separate exact Möbius-mask source
with a square and mixed logarithmic companion; the present `1-k_N` balanced
representation and its scope remain unchanged.
