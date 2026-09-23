# Fixed-width prime packets and uniform Dirichlet coefficients

[`VinogradovShortDirichlet.block_bound`](../RiemannGaussian/VinogradovShortDirichlet.lean)
proves the actual original block estimate

```math
\left|\sum_{n=0}^{M^4-1}(z+n)^{-it}\right|\le5M^{4-\varepsilon_k},\qquad
\varepsilon_k=\begin{cases}
1/(1600k^2),&12\le k<48,\\
1/(512k^2),&48\le k.
\end{cases}
```

Its complete range is `k>=12`, `M>=(4*k+1)k`,
`M^(2k-2)<=t<=M^(2k)` and `M^4<=z<=2*M^4`, with integer `k,M`.
The coefficient five pays both actual moments, the entire Gaussian cost,
Taylor remainder and shift boundary. Partial blocks retain
`3*ell*M^(-epsilon_k)+2*M^2`; decreasing damping weights pay their actual
mass and only the initial weight at that boundary. Literal zeta damping
inherits the saving. No moment estimate or unevaluated degree cost is a
hypothesis.

[`VinogradovExponentialDefect`](../RiemannGaussian/VinogradovExponentialDefect.lean)
bounds the exact defect by `(k^2/2)*exp(-n/k)`.
[`VinogradovShortMoment`](../RiemannGaussian/VinogradovShortMoment.lean)
therefore proves defect `k^2/40` at order `(3k+1)k` and `k^2/100` at
order `(4k+1)k`, at every positive endpoint. Both have complete coefficient
`(2^41*k^6)^(k^3)`. The product of both coefficients and the full
variable-order Gaussian factor is at most `2^(2r^2)` for every actual
chosen order, giving multiplier two after the true root. The retained
frequency window supplies the stronger saving without extending its support.

The [all-scale continuation](vinogradov-near-one-growth.md) covers every
original dyadic block, and the [zero detector](vinogradov-zero-free.md)
proves a larger actual zero-free family. The older `1/(8192k^2)` saving
and its longer moment order remain proved; the following sections record
that fixed-width packet construction and its original transport.

## The shorter packet is proved from existing arithmetic

The previous
[diagonal descent](vinogradov-diagonal-descent.md) used `R` Bertrand
steps, with prime endpoint `2^R*M`. The new proof uses an existing input
from the Suzuki branch:
[`chebyshevPsi_sub_theta_le_eighteen_sqrt`](../RiemannGaussian/SuzukiProperPrimePowerWork.lean)
proves `psi(x)-theta(x) <= 18*sqrt(x)` for `x>=1`.

Combining that estimate with Mathlib's explicit Chebyshev lower bound for
`psi` and upper bound for `theta`,
[`VinogradovShortPacket.theta_eight_mul_sub`](../RiemannGaussian/VinogradovShortPacket.lean)
proves

\[
 \theta(8M)-\theta(M)\ge2M\qquad(M\ge4096).
\]

The elementary bound `log(8M)<=6*sqrt(M)` turns this into enough actual
primes for the exact finite selection:

\[
 \boxed{M\ge4096,\quad M\ge9R^2
 \quad\Longrightarrow\quad
 \exists\Pi\subset(M,8M],\ \#\Pi=R,\ \text{every }p\in\Pi\text{ prime}.}
\]

This is `exists_short_packet`. No prime-density assumption or external
unformalized prime estimate remains in it. The eightfold interval is
not asserted to be a packet in `(M,2M]`.

The generic `exists_conditioning_of_packet` interface retains the
packet's actual cardinality and upper endpoint. It requires its prime
product to exceed the full two-block discriminant budget. The same
proved packet then covers every retained solution, avoids the type
multiplier, and yields one prime carrying the original count. It does
not select unrelated primes separately for different sides of an equation.

## Every endpoint and every iteration cost

Use `R=2k^3` and the literal `M=floor(P^(1/k))`. Since `M+1<=M^2` for
`M>=2`, the strict two-block budget fits in `M^(2k^3)` without the earlier
`M>=2^k` requirement. All root-scale conditions are paid by

\[
 \begin{aligned}
 b_{k,s}&=\max\{4096,36k^6,128s^2,4k^4,k+1\},\\
 H_{k,s}&=b_{k,s}^{\,k},\\
 D_k&=8k^3k!\,8^{k^2}.
 \end{aligned}
\]

[`VinogradovNarrowThreshold.all_endpoint_defect_step`](../RiemannGaussian/VinogradovNarrowThreshold.lean)
proves the actual moment step at every positive integer endpoint with

\[
 \Delta'=\Delta(1-1/k),\qquad
 C'=\max\{H_{k,s}^{k(k+1)/2},D_kC\}.
\]

The independent small-endpoint reserve remains a maximum. The exact
orders and defects are the same as the preceding diagonal iteration;
the improved coefficients now come from the fixed-width packet.

At order `(7k+1)k`,
[`VinogradovNarrowCost.explicit_relative_moment_bound`](../RiemannGaussian/VinogradovNarrowCost.lean)
proves, for `k>=2` and every positive integer `P`,

\[
 \boxed{
 J_{(7k+1)k,k}(P)
 \le (2^{62}k^6)^{k^3}
 P^{\,2(7k+1)k-k(k+1)/2+k^2/256}.}
\]

The coefficient's logarithm has order `k^3 log k`; the earlier binary
coefficient had logarithm `18k^6 log 2`. The full cost proof includes
all small endpoints and uses `b_(k,s)<=8192k^6` for `s<=8k^2`, together
with `D_k<=2^(7k^2)`.

## The actual moment root pays the complete constants

The tuple order is retained as `r=(7k+1)k` throughout the new Gaussian
and product proofs. This does not substitute a new coefficient into the
older `k(k+1)` theorem.

At the new order, the full Gaussian cost is still at most `2^(9k^2)`.
The natural-number theorem `two_moments_gaussian_le` proves

\[
 \bigl((2^{62}k^6)^{k^3}\bigr)^2\,2^{9k^2}
 \le2^{2r^2}.
\]

Thus the exact `2r^2` moment root costs at most two. The net rectangle
saving, after paying both defects `k^2/256`, is at least
`1/(8192k^2)` after that root.
[`VinogradovNarrowResonance.polynomial_bound`](../RiemannGaussian/VinogradovNarrowResonance.lean)
therefore bounds the literal polynomial product by
`2*M^(2-1/(8192k^2))`. Its independent Taylor error gives coefficient
three for the original imaginary-power product.

For every partial block `0<=ell<=2M^4`, the full shift transfer proves

\[
 \left|\sum_{n=0}^{\ell-1}(z+n)^{-it}\right|
 \le 3\ell M^{-1/(8192k^2)}+2M^2.
\]

The full-block coefficient five follows. Abel summation also proves,
for every nonnegative decreasing weight family on `0,...,N` with
`N+1<=2M^4`,

\[
 \left|\sum_{n=0}^{N}w_n(z+n)^{-it}\right|
 \le3M^{-1/(8192k^2)}\sum_{n=0}^{N}w_n+2M^2w_0.
\]

`feature_block_bound` specializes this to the literal damped zeta
coefficients for every nonnegative real part. It retains the actual
weight mass and charges the endpoint only to its initial weight.

## Remaining route to a region

The [all-scale continuation](vinogradov-near-one-growth.md) now constructs
the integer block and degree parameters, pays every short and long scale,
and proves a complete near-one zeta-growth estimate with cubic-index
height exponent and an explicit starting height. It covers continuous
bands with a displacement-to-three-halves exponent. The
[complete zero-free continuation](vinogradov-zero-free.md) now pays the
joint schedule, original threshold and actual zero detector. Matching
published benchmark constants still requires sharper estimates.

The new eventual VK width does not prove the global Riesz signed floor
or RH, and no historical novelty is claimed. The fixed-height harmonic Type-II no-go
audit is unchanged; this growing-height rectangle is not its missing
arithmetic input. The new chain is a quantitative continuation of the
polynomial conditioning strategy motivated by
[Ford, Section 3](https://arxiv.org/pdf/1910.08209).
