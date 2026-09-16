# Sharper cancellation costs for the original Riesz carrier

Lean now combines two independently proved improvements in the whole
original finite carrier: a quarter-sized profile allowance for composite
squarefree cofactors, and an exact factorial amplitude allowance beyond
the actual stationary points. The second estimate falls back to the prior
bound wherever its stationary test fails. Every original integer, including
the unmatched remainder, is accounted for.

The terminal theorem is
[`exists_actual_band_sharp_prime_pairs`](../RiemannGaussian/ZetaRieszSharpMatching.lean).
It proves an attained optimal disjoint saving with the new costs. It does
not prove that this saving is positive or large enough at source scale,
and gives no new zero-free region yet.

## Arithmetic cancellation inside the cofactor

For the Riesz profile and absolute divisor mass,

```math
R_L(n)=\sum_{d\mid n}\mu(d)\max(0,L-\log d),
\qquad M(n)=\sum_{d\mid n}|\mu(d)|,
```

the coupled four-hinge response to two prime insertions is exactly

```math
T(a,b,v)=\max\{0,\min\{a,b,v,a+b-v\}\}.
```

Its full Lipschitz constant is one. Separately bounding its four hinges
would pay four. Using the actual two-prime factorization and exact divisor
mass doubling, `riesz_cutoff_lipschitz_quarter` proves

```math
|R_L(n)-R_K(n)|\le\frac{|L-K|}{4}M(n)
```

for every squarefree n with at least two prime factors, uniformly in both
real cutoffs. Prime cofactors retain the preceding half-sized allowance.
The corresponding full complex prime-pair bounds retain all original band
and coprimality conditions; this is not merely a bound for an abstract tent.

## Keep the exact factorial amplitude

For each moment term the derivative keeps its growth and decay coupled:

```math
\frac{d}{dv}\left(v^{m+1}e^{-\sigma v}\right)
=v^m e^{-\sigma v}\bigl((m+1)-\sigma v\bigr).
```

On an interval beginning at A with m+1 at most sigma A, that term decreases.
For the entire fixed complex polynomial P the proved endpoint allowance is

```math
E_{L,P,N,\sigma}(A)=
\sum_{k\in\operatorname{supp}P}
\frac{|P_k|}{L(N+k)!}A^{N+k+1}e^{-\sigma A}.
```

It retains the exact factorials and the local pair endpoint A, rather than
using an exponential-series envelope or moving every pair to the global
cutoff. The real-line amplitude is bounded by E and its derivative by
sigma E beyond every stationary point. The exact complex coefficient
expansion and derivative are preserved before these norm estimates.
The full-phase two-amplitude sum consequently obeys

```math
|A_{\sigma+it}(x)+A_{\sigma+it}(y)|
\le E(A)\left(\sigma|x-y|
+2\left|\cos\left(\frac{t(x-y)}2\right)\right|\right).
```

`eventually_norm_logAmplitude_pair_above_length` verifies the stationary
conditions above the actual moving length for every sufficiently large
order, every fixed P and every height when 0 < u < exp(-1/2). The order
threshold may depend on u and P. This covers the narrower annulus regime;
it does not enlarge the proved source region or supply cancellation between
different pairs.

## Whole original support, with a verified fallback

Each candidate edge is defined by its actual integer indices, squarefree
nonunit gcd and prime quotients. The new `sharpPairCost` takes the smaller
of the old refined cost and the exact descending cost when the explicit
stationary test holds, and uses the old cost otherwise.
`sharpPairCost_bound` discharges its full analytical and arithmetic premises
for every candidate. `sharpPairCost_le_refined` proves pointwise nonincrease.
The whole-carrier statement requires no extra stationary hypothesis.

For the new cost C, let

```math
S(e)=\max\{|B(i)|+|B(j)|-C(e),0\}.
```

The finite maximum over all disjoint candidate families is attained, and

```math
\left|\sum_{n\in\mathcal B}B(n)\right|
\le\sum_{n\in\mathcal B}|B(n)|-\max_E\sum_{e\in E}S(e).
```

The exact complex partition into pairs and unmatched integers remains
available upstream. These bounds do not assert coverage, a positive
aggregate saving, or an asymptotic saving sufficient to beat the source.
A fixed fractional improvement need not remove the surviving exponential
allowance. The next obligation is quantitative control of the accumulated
pair costs and unmatched mass, or cancellation between those retained sums.

Small floating-point probes motivate the sharper estimates but are neither
certificates nor asymptotic results. They are not part of ordinary CI.
Default RH, zero-free and numerical-certificate endpoints remain unchanged.
No historical novelty claim is made for these identities or estimates.
