# Explicit homogeneous moment descent

[`VinogradovDiagonalCost.explicit_relative_moment_bound`](../RiemannGaussian/VinogradovDiagonalCost.lean)
proves, for every integer `k >= 2` and every positive integer `P`,

\[
 \boxed{
 J_{(7k+1)k,k}(P)
 \le 2^{18k^6}
 P^{\,2(7k+1)k-k(k+1)/2+k^2/256}.}
\]

Here `J` is the existing homogeneous Vinogradov mean value: the actual
number of pairs of tuples in `{1,...,P}` with equal power sums through
degree `k`, equivalently their torus moment. There is no supplied moment
estimate, eventual threshold, or recursive constant in this endpoint.
Every small endpoint is included. This is an auxiliary estimate, not a
new zero-free region or a bound for the independent signed Riesz carrier.

The tuple order is **`(7k+1)k`**. The earlier quantitative Gaussian and
Dirichlet transport uses **`k(k+1)`**; this new coefficient cannot be
substituted into that transport without changing and checking its moment
order and all resulting exponents.

## Actual count and the diagonal branch

The starting point is the
[full unrestricted polynomial conditioning theorem](vinogradov-polynomial-systems.md).
Specialize its system to the monomials of degrees `1,...,k`, with type
`(0,1)`, and retain the original homogeneous tail. The mixed count is
exactly `J_{s+k,k}(P)`.

Set `M = floor(P^(1/k))`. The eligible packet prime satisfies `p > M`,
so `P < p^k`. Consequently the retained residue moment is exactly
diagonal, even though the maximizing polynomial system need not be the
original monomial system. The already proved exact diagonal identity
removes that system, leaving

\[
 J_{s+k,k}(P)
 \le 4R\,k!\,p^{\,2s+k(k-1)/2}P^k
 J_{s,k}(\lfloor P/p\rfloor).
\]

[`VinogradovDiagonalMoment.exists_diagonal_moment_step`](../RiemannGaussian/VinogradovDiagonalMoment.lean)
proves this for the literal tuple counts, with all packet and quotient
size conditions displayed. This branch needs no further increase in the
polynomial type. It does not assert that the general mixed-type descent
has been iterated.

## Exact exponent and all endpoints

Write `S_k = k(k+1)/2` and assume an existing bound
`J_{s,k}(X) <= C X^(2s-S_k+Delta)`, with `0 <= Delta <= k^2` and a
nonnegative exponent. The quotient and prime powers stay together until
their exponents cancel. The remaining prime exponent is exactly
`k^2-Delta`. At the root scale, the resulting defect is

\[
 \Delta' = \Delta(1-1/k).
\]

[`VinogradovDiagonalExponent`](../RiemannGaussian/VinogradovDiagonalExponent.lean)
proves this transition with the explicit packet cost. The packet has
`R=k^3` primes and the proved Bertrand endpoint `2^(k^3) M`; no dense
short prime packet is assumed.

For a fully specified all-endpoint statement, define

\[
 \begin{aligned}
 b_{k,s}&=\max\{2^k,4k^4,16s^2 2^{k^3},k+1\},\\
 H_{k,s}&=b_{k,s}^{\,k},\\
 D_k&=4k^3 k!\,2^{k^5}.
 \end{aligned}
\]

Above `H`, the literal integer root discharges the packet, repetition
and quotient conditions. Below it, counting all tuple pairs pays an
independent allowance `H^S_k`. The next coefficient is therefore

\[
 \boxed{C'=\max\{H_{k,s}^{S_k},D_k C\}.}
\]

The small-endpoint cost is a maximum with the recursive cost, so it is
not multiplied afresh into the preceding coefficient at every step.
[`VinogradovDiagonalThreshold.all_endpoint_defect_step`](../RiemannGaussian/VinogradovDiagonalThreshold.lean)
proves this inequality for every positive endpoint.

## Finite iteration and closed cost

The exact initial moment has `s_0=k`, `C_0=k!` and
`Delta_0=choose(k,2)`. The proved iteration is

\[
 \begin{aligned}
 s_n&=(n+1)k,\\
 \Delta_n&=\binom{k}{2}(1-1/k)^n,\\
 C_{n+1}&=\max\{H_{k,s_n}^{S_k},D_k C_n\}.
 \end{aligned}
\]

[`VinogradovDiagonalIteration.iterated_moment_bound`](../RiemannGaussian/VinogradovDiagonalIteration.lean)
proves the actual moment estimate at each finite stage. The elementary
bound `(1-1/k)^k <= 1/2` gives `Delta_(7k) <= k^2/256`.

The separate cost audit proves, for `s <= 8k^2`,

\[
 b_{k,s}\le2^{4k^3},\qquad
 H_{k,s}^{S_k}\le2^{4k^6},\qquad
 D_k\le2^{2k^5}.
\]

Monotonicity of the small-endpoint allowance gives
`C_n <= max(k!, H_(k,s_n)^S_k) D_k^n`. Hence
[`VinogradovDiagonalCost.coefficient_seven_degree_le`](../RiemannGaussian/VinogradovDiagonalCost.lean)
proves `C_(7k) <= 2^(18k^6)` and the terminal theorem follows.

## Scope and next quantitative obstruction

This is a direct diagonal consequence of the polynomial conditioning
method, motivated by the moment-order strategy in
[Ford, Section 3](https://arxiv.org/pdf/1910.08209). It is not a
formal reproduction of the sharper published moment constants, and no
historical novelty is claimed.

The [fixed-width packet continuation](vinogradov-narrow-packet.md) now
replaces the wide iterated-Bertrand packet by an actual packet in `(M,8M]`,
with every cardinality, threshold and discriminant condition proved. It
uses the existing Suzuki proper-prime-power estimate together with
Chebyshev bounds. At the same tuple order and defect, the new closed
coefficient is `(2^62*k^6)^(k^3)`.

That continuation also proves transport at the actual new tuple order.
The literal Dirichlet block has uniform coefficient five and saving
`1/(8192*k^2)` on its displayed height rectangle, with no moment premise
or unevaluated degree coefficient. Its
[all-scale continuation](vinogradov-near-one-growth.md) now proves
complete near-one zeta growth with explicit thresholds, including
continuous bands with a three-halves displacement exponent. Adaptive
height coverage, the VK zero detector, matching every benchmark and
an independent Riesz signed floor remain open. The proved zero-free
union and the explorer's default endpoints are unchanged.
