# Explicit mean-value and Dirichlet-block costs

The local Lean chain now proves an unconditional high-moment bound with a
fully specified coefficient, then carries that coefficient into the original
Dirichlet blocks and the actual damped zeta coefficients. No homogeneous
moment estimate is assumed in these terminal theorems. The proved zero-free
region has not changed: the remaining issue is the size of these degree
costs, followed by the analytic transport to zeta and zero exclusion.

## Pay only the moment accuracy the Gaussian bound needs

For `u=k`, an exponent allowance `d=k²/q` gives the exact profile

\[
 \beta_j=k^2-j(1-1/k)k^2/q.
\]

After `2q` steps this is `-k²+2k`, and every earlier profile is at least
`-k²`. Thus `VinogradovRelativeProfile` proves that the single extension
`2k³` pays all descendant cutoffs, giving depth

\[
 T=(k+2k^3)^{2q}.
\]

This is polynomial in the degree for fixed `q`. The actual conditioned
moments, initial allowance and prime packet retain the profile coefficient
bound `(2k²)^(7k)` and the original source constant linearly. Their quotient
moment hypotheses are subsequently discharged by the finite descent below.

## All constants in the unconditional moment theorem

For integers `k>=4`, `1<=q<=k²`, define

\[
\begin{aligned}
 Q&=T+1,& R&=2Qk(k-1)+1,& L&=k(2k+1),\\
 E&=((2k^2)(2k^2-1)\cdots(2k^2-k+1))^{2k},\\
 B&=1+E(2k^2)^{7k},\\
 D&=\max\{2,2^R,4k^4,[2k(k-1)^{2k^2}]^2\},\\
 X_0&=(2^R D)^Q+1,& \varepsilon&=1/(2Q),\\
 A_0&=(2R)^2 B\,2^L(2^R)^{1/2},\\
 A_\infty&=\max\{1,A_0(2^Q)^L\},\\
 A&=\max\{A_\infty,X_0^\varepsilon\},\\
 m&=k(k-1)Q+1,& C_{k,q}&=A^m k!.
\end{aligned}
\]

These are the definitions in
[`VinogradovQuantitativeDescent`](../RiemannGaussian/VinogradovQuantitativeDescent.lean).
Its terminal `relative_moment_bound` proves

\[
 J_{k(k+1),k}(X)\le C_{k,q}
 X^{\frac32 k(k+1)+k^2/q}\qquad(X\in\mathbb N,\ X\ge1).
\]

The proof begins with the existing elementary factorial estimate. One
improvement pays the prime packet, padded quotient normalization, nearby
power-cutoff rounding and every smaller endpoint. The stopping count is
bounded by `m`; there is no existential coefficient or starting threshold
in this theorem. The coefficient is an explicit expression, not a claim
that it is numerically small or optimal.

## Actual polynomial, imaginary-power and damped blocks

At `q=128`, the full Gaussian degree gain pays **both** allowances `k²/128`
and still gives saving `delta_k=1/(256k²)` at the original moment root.
Set `r=k(k+1)` and

\[
 H_k=\left(C_{k,128}^2\,2^{9k^2}\right)^{1/(2r^2)}.
\]

[`VinogradovRelativeResonance.polynomial_bound`](../RiemannGaussian/VinogradovRelativeResonance.lean)
is unconditional. It includes the complete Gaussian resonance and smoothing
cost; every original polynomial phase and every positive subset of shifts
is supported. Its input moment is supplied by `relative_moment_bound`.

[`VinogradovQuantitativeDirichlet`](../RiemannGaussian/VinogradovQuantitativeDirichlet.lean)
then proves, for `k>=12`, `M>=k(k+1)`,

\[
 M^{2k-2}\le t\le M^{2k},\qquad M^4\le z\le2M^4,
\]

the actual partial-block bound

\[
 \left|\sum_{n=0}^{\ell-1}(z+n)^{-it}\right|
 \le (H_k+1)\ell M^{-\delta_k}+2M^2
 \qquad(0\le\ell\le2M^4),
\]

and the full-block bound

\[
 \left|\sum_{n=0}^{M^4-1}(z+n)^{-it}\right|
 \le (H_k+3)M^{4-\delta_k}.
\]

The Taylor remainder and the complete shift boundary are paid. The
`weighted_block_bound` theorem retains the actual total mass of every
nonnegative decreasing weight family, charging the boundary only to its
initial weight. `feature_block_bound` applies this to the literal zeta
coefficients at every nonnegative real part. The starting scale and all
coefficients are specified; no eventual moment or cancellation premise
remains. The older saving `1/(128k²)` with existential costs stays available.

## Cost audit and next literature target

The compiled `packet_square_power_le_momentMultiplier` proves

\[
 C_{k,q}\ge2^{Q^2}.
\]

This concerns **our chosen upper-bound allowance**, not a lower bound on the
mean value and not an obstruction to a better proof. At fixed `q=128` it
already identifies very rapid growth in the coefficient paid by this
descent. Merely replacing an existential coefficient by this expression
does not supply the small uniform constants required by the benchmark
argument. The block bound can exceed the trivial bound for a very large
range of scales.

[Bellotti, Section 2, Lemmas 2.1–2.5 and Theorem 2.7](https://arxiv.org/html/2306.10680v1#S2)
describes the relevant alternative: conditioning and differencing general
polynomial systems, followed by an increase in moment order `s -> s+k`.
The stated coefficients have much smaller degree growth. That section also
explains why oversized efficient-congruencing constants cannot be used in
Ford's argument merely because the exponent is optimal.

The polynomial-system continuation below proves those counting inequalities.
Its direct diagonal branch now gives an actual all-endpoint `s -> s+k`
iteration, including small endpoints and closed coefficients. The general
mixed-type iteration, sharper published moment estimates and their
all-scale transport, matching the benchmark constants, and enlarging the
proved union remain required by the full zero-free-region goal.

The polynomial-system continuation proves exact finite-difference type
preservation, the actual degree-modulus factorial count and the quantitative
L-to-next-K integral inequality, including boundary masks, the diagonal
case and fixed-shift selection. The actual nonsingular prime-dilated count
now feeds this inequality with an explicit factorial/prime-power cost and
unchanged endpoints. Low-degree tail conditioning also bounds the original
nonsingular count by d!*p^(2s-d) times one fixed residue-class count.
Endpoint deletion and exact binomial row transport now join these steps:
the original nonsingular count reaches the next polynomial type at the
required floor(Q/p) tail endpoint, with every cost proved. The attained
type-family maximum now pays repeated tuples on both sides while retaining
the fixed tail. One explicitly constructed eligible prime separates both
blocks and avoids T. The full unrestricted count reaches the conditioned
residue moment with coefficient 4*R*d!*m!*p^(2s-d+(r-d)*(r-d-1)/2), under
the displayed size conditions. This uses the proved Bertrand packet up to
2^R*M; the sharper short packet is not assumed. See
[the complete conditioning bound](vinogradov-polynomial-systems.md).

The subsequent
[explicit diagonal descent](vinogradov-diagonal-descent.md) proves
`J_{(7k+1)k,k}(P) <= 2^(18k^6)*P^(2(7k+1)k-k(k+1)/2+k^2/256)`
for every `k>=2` and positive integer `P`, without a moment premise. This
replaces the very large recursive construction at a different tuple order;
it does not substitute that coefficient into the earlier `k(k+1)`
Dirichlet theorem. The subsequent [fixed-width packet and uniform-coefficient
transport](vinogradov-narrow-packet.md) now discharges both obligations:
the coefficient is `(2^62*k^6)^(k^3)`, and the actual Dirichlet block has
coefficient five with saving `1/(8192*k^2)` on its proved rectangle.
The [all-scale continuation](vinogradov-near-one-growth.md) now proves
complete near-one zeta growth with explicit band-dependent thresholds.
Adaptive height coverage and the VK zero detector remain open.
