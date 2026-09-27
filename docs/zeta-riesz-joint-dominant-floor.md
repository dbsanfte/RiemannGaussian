# Paying the 60.1% dominant-prime region in the joint floor

`ZetaRieszJointDominantFloor.Refined` lowers the independently paid
largest-prime threshold from `121/200 = 0.605` to `601/1000 = 0.601` on
`1/2 <= u <= 10001/20000`. It bounds a part of the **whole original core**.
This does not change the proved zero-free region.

For any finite subband `D` with an eligible selected prime satisfying

\[
\frac{601}{1000}\log n\le\log p\le L_N,
\]

`Refined.norm_scaled_sum_le` proves, for `N >= 320`,

\[
\left\|u^{N+1}\sum_{n\in D}
 (1-\theta_N(n))c_{L_N}(n)K_N(3/2+iy,n)\right\|
\le 2M_\sigma e^{-N/1000000},
\qquad \sigma=1+\frac1{262144}.
\]

Here `M_sigma` is the existing finite `zetaMoebiusLogMajorantMass sigma`,
not numerically evaluated. The estimate is uniform in real height, prime
count and additional finite label masks. It uses no zero hypothesis,
completed cofactor, prime-density approximation or rectangle selection.
The earlier `exp(-N/8000)` bound above `121/200` remains available unchanged.

The upper missing binomial tail now uses the rational tilt `103/100` and
cofactor share at most `399/1000`. Lean proves

\[
\log\frac{101197}{100000}-\frac{13}{32}\log\frac{103}{100}
\le-\frac1{9200}.
\]

After the source normalization and summable Dirichlet envelope this leaves
`exp(-N/1000000)`. The lower missing tail retains its physical constraint
`log p <= L_N` and the existing `exp(-N/2000)` saving. The common physical
kernel and coefficient arguments are shared by the two concrete tilts.

`Refined.re_core_ge_without_large` keeps the entire remaining core inside
one signed real observation, with only the displayed error subtracted.
`Refined.remaining_prime_log_lt` proves on the original dyadic schedule
that **every** prime factor of a nonzero remaining atom has log share
strictly below `601/1000`. Its eligibility follows from the actual masks.

## Both bounds in the same signed inequality

Let `S` be the core after the paid large-prime deletion, and choose `D`
inside `S` with every eligible selected prime share at most `293/500`.
Write `b_n=c_L(n)K_N(3/2+iy,n)`. The new theorem
`Refined.re_core_ge_joint_reduced` proves

\[
\operatorname{Re}(u^{N+1}\mathrm{coreResponse})\ge
\operatorname{Re}\left(u^{N+1}\left[
 \sum_{n\in D}b_n+\sum_{n\in S\setminus D}(1-\theta_N(n))b_n\right]\right)
-E_N,
\]

where

\[
E_N=M_\sigma\left(4U(N+1)r^N+2e^{-N/1000000}\right)\longrightarrow0,
\quad
r=U\frac{262144}{131071}e^{-1/8200}\le e^{-1/100000},
\quad U=\frac{10001}{20000}.
\]

The allocation factor therefore needs separate treatment only between
shares `0.586` and `0.601`. **The raw signed sum below `0.586` is still
unbounded**, including the balanced triples and higher-count partners.
This is a reduction of an allocation issue, not a bound on the total
remaining negative contribution or a measure of proximity to RH.
The required [joint cofinal floor](zeta-riesz-joint-floor.md)
`-79/1000-o(1)` remains open.

## Where scalar tuning stops

The [optional probe](../scripts/probe_riesz_joint_tilts.py) optimizes only
the same exponential-tilt/summable-envelope estimate. Its
[recorded output](riesz-joint-tilt-probe.json) predicts limiting share
boundaries about `0.58653135` and `0.60094175`. These floating boundaries
are not certified endpoints; the exact Lean results are the rationals above.

There are now also two **proved all-tilt obstructions**. At prime shares
59% and 60%, respectively, and at the upper source radius, Lean proves
for **every** real `q > 0` that

\[
\log\left(U\frac{262144}{131071}\right)
+\log(xq+1-x)-\frac{13}{32}\log q>\frac1{60000},
\qquad x=\frac{41}{100}\ \text{or}\ \frac25.
\]

The theorems are `fifty_nine_percent_all_tilts_grow` and
`sixty_percent_all_tilts_grow`. Weighted logarithm inequalities prove the
bound for the full tilt family, not just the chosen numerical optimizer.
Thus this scalar envelope cannot cover the transition by selecting a
better tilt. These are limitations of that estimate at `u=U`; they do
not say the actual tails grow or that joint signed cancellation is impossible.

## Quadratic literature check

Granville, Koukoulopoulos and Maynard's
[*Sieve weights and their smoothings*](https://dms.umontreal.ca/~andrew/PDF/sieveweights.pdf),
Theorem 1.1, studies even moments of smoothed Möbius divisor sums. That is
relevant to the hinge's structure, but does not itself give our linear
signed Mellin estimate with the current masks. The repo's existing
`SquarefreeEulerQuadratic.form_self_eq_complex_squares` is an exact
complex-bilinear diagonalization: its entries are complex squares, not
nonnegative squared norms. No positivity or independent core floor is
inferred from either fact, and no extra carrier representation was added.

## Additional radial savings

The [joint radial estimate](zeta-riesz-joint-radial-floor.md) now pays the
60% residual outside `1.984N < log n < 2.016N`, and pays removal of the
59% assigned part outside `1.974N < log n < 2.028N`. Its signed comparison
retains the old regions above and adds only an error tending to zero.
The central all-tilt barriers and the open joint floor are unchanged.
