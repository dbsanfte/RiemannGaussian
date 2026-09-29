# Joint bounds with the literal owner allocation

`ZetaRieszOwnerMaximal` proves an independent signed cutoff estimate that
allows the owner allocation and both retained period endpoints to depend on
the cofactor. It applies to arbitrary finite populations and has no prime-count
ceiling or zero hypothesis. The whole `-79/1000` floor and `3/2` ceiling for
`J+C` remain open.

## The exact allocation has bounded variation

The original unpaid orders are exactly

\[
\{\lfloor N/5\rfloor+2,\ldots,\lfloor13N/32\rfloor\}.
\]

For `N >= 32`, their binomial mass is a difference of two cumulative
binomial probabilities. Each cumulative probability is decreasing in the
cofactor share. Consequently, for **any** decreasing sequence of shares in
`[0,1]`, the retained owner weight

\[
v_N(x)=1-\sum_{k\in\mathrm{unpaidOrders}(N)}
  {N+1\choose k}x^k(1-x)^{N+1-k}
\]

has total variation at most `2`, independently of `N`, the number of prime
factors, and the number of periods. Its values lie in `[0,1]`.
`ownerWeight_variation_le_two` proves this; `ownerWeight_eq_fibre` identifies
it with the original unique-largest-prime allocation. No limiting share or
replacement allocation is used.

Finite Abel summation now gives

\[
\left|\sum_i v_N(x_i)z_i\right|\le3B
\quad\text{if every original complex partial sum has norm at most }B.
\]

`literal_owner_prime_partial_bound` applies this to the actual signed Riesz
coefficient and full complex prime kernel. **The raw prime partial-sum bound
is an explicit premise** of this bridge; it is not proved small here. Allowing
both endpoints of a retained interval to move gives the constant `6`.

## One arithmetic bound across the periods

Let `M=2^b` and let positive integer cutoffs satisfy
`|log R_i-log R_j| >= h |i-j|`, for a fixed `h>0`. Put

\[
M_R(n)=\sum_{d\mid n,\ d\le R}\mu(d),\qquad
A_n=\sum_{\ell(n)\le i<r(n)}v_N(x_{n,i})a_iM_{R_i}(n).
\]

The shares may depend on `n` and need only decrease **inside the selected
interval**. The interval may depend on `n` too. For any `S` contained in the
integer interval `(Y,X]`, `exists_owner_interval_mean_bound` proves

\[
\sum_{n\in S}A_n^2\le36(b+1)
 \left[E_h(X-Y)(b+1)\sum_{i<M}a_i^2+\mathcal B_b\right].
\]

`E_h>0` is proved to exist and remains unevaluated. The displayed finite error
`B_b` is a sum over the complete binary tree of period blocks. For each block
`I`, its contribution is exactly

\[
\left(\sum_{d\le\max_{i\in I}R_i}
 \left|\mu(d)\sum_{i\in I,\ d\le R_i}a_i\right|\right)^2.
\]

The signs are combined at each divisor **before** taking an absolute value.
Even its coarser bound is only
`(b+1)*(sum_i |a_i| R_i)^2`, by `dyadic_floor_cost_le`.
Thus the overall mean-square price is `36(b+1)^2`, not proportional to the
number `2^b` of periods. This follows by covering each prefix with one block
per binary level and applying the existing cross-cutoff estimate to the
blocks. It does not replace the arithmetic carrier.

For any common real weight `w(n)`, `exists_owner_interval_signed_bounds`
gives both `-K <= sum_n w(n) A_n <= K`, with `K` the square root of the
displayed mean bound times `sum_n w(n)^2`.
`exists_owner_slope_bounds` gives these same inequalities for the literal
`cutoffSlope`, retaining strict rounding `R_i < exp(D_i) <= R_i+1` and shares
`log(n)/T(n,i)`, with increasing radial lengths that may depend on `n`.

## Remaining quantitative work

Only the owner factor and interval endpoints have gained this dependence on
the cofactor. The base coefficients `a_i` and cutoff family `R_i` remain fixed
across the population. Arbitrary coefficients `a_i(n)`, noncontiguous prime
selection changes, the full prime-period weight energy, and the matching
signed Riesz cutoff corrections still require joint control. The exact
binary-block floor budget is not yet source-small. The mean bound does not
prove the raw prime partial-sum premise of the factor-three bridge.

No previously paid population is charged again. All earlier obstruction
theorems remain valid; a logarithmic saving cannot by itself defeat the
exponential absolute source envelope. No new zero exclusion is asserted.

The optional `scripts/probe_riesz_owner_modulation.py` retains the exact
allocation and samples the radial envelope through `N=8192`. It confirms the
expected bounded-variation behavior numerically but does not sample actual
prime populations or certify a source-scale bound. The constants `2`, `3`,
`6` and `36` above come from Lean. Reproduction data and source hashes are in
[`riesz-owner-maximal-audit.json`](riesz-owner-maximal-audit.json).
