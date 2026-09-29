# One cutoff-crossing bound across counts and radial periods

Lean now bounds the affine cutoff error of the **literal allocated prime
sum** without fixing its number of prime factors, its share geometry or its
radial center. The bound applies on both sides. It does **not** yet bound the
whole signed carrier: two actual weighted prime moments and clipped-period
boundary contributions remain.

## The estimate

Write the existing Riesz response and its exact finite slope as

\[
 R_D(a)=\sum_{d\mid a}\mu(d)(D-\log d)_+,
 \qquad S_D(a)=\sum_{\substack{d\mid a\\\log d<D}}\mu(d).
\]

For \(|x|\le h\), subtract the affine part before taking absolute values:

\[
 \left|R_{D+x}(a)-R_D(a)-xS_D(a)\right|
 \le\sum_{d\mid a}(h-|D-\log d|)_+.
\]

Only divisors within one half-period of the cutoff are charged. The symmetric
second difference is exactly the same tent sum with each Möbius sign retained.
Reindexing the divisor incidences over **all integers** gives the checked bound

\[
 \boxed{\quad
 \sum_{1\le a\le X}\frac{|R_{D+h}(a)-2R_D(a)+R_{D-h}(a)|}{a}
 \le (1+\log X)h\left(e^{2h}-1+e^{h-D}\right).
 \quad}
\]

There is no prime-count ceiling and no squarefree hypothesis in this estimate.
The affine-error version holds on every masked cofactor subfamily. When
\(0<h\le1/16\) and \(D\ge h-\log h\), its cost is at most

\[
 \frac{23}{7}(1+\log X)h^2.
\]

This replaces a charge for every divisor choice by a charge for the divisors
actually crossed. It removes the exponential dependence on prime count from
this particular error term.

## Direct connection to the retained carrier

Let \(T=\log(pa)\). The signed weight used by the theorem is exactly

\[
 g_N(a,p)=\frac{(-1)^{\omega(a)+2}}{L}
 (1-\theta_N(pa))\frac{e^{-T/2}T^{N+1}}{N!p}\cos(yT).
\]

Both reflected responses remain in the literal coefficient:

\[
 \operatorname{Re}\bigl(c^{\rm residual}_{L,N}(pa)K_N(pa)\bigr)
 =\frac{g_N(a,p)}a
 \left[R_{T-L}(a)-R_{\log a-L}(a)\right].
\]

For every cofactor selection \(S\subseteq[1,X]\), retain its actual prime set
\(P(a)\), including any physical, ownership, count, radial or other masks.
The theorem requires squarefree cofactors with at least two factors and prime
\(p\nmid a\). It permits all such counts, without an upper ceiling. Put

\[
 M_0(a)=\sum_{p\in P(a)}g_N(a,p),\qquad
 M_1(a)=\sum_{p\in P(a)}g_N(a,p)(T-v).
\]

For \(|T-v|\le h\), the **literal signed sum** lies between \(M-E\) and
\(M+E\), where

\[
 M=\sum_{a\in S}\frac{
 [R_{v-L}(a)-R_{\log a-L}(a)]M_0(a)+S_{v-L}(a)M_1(a)}a,
\]

\[
 E=W(1+\log X)h\left(e^{2h}-1+e^{h-(v-L)}\right),
 \qquad \sum_{p\in P(a)}|g_N(a,p)|\le W.
\]

`owned_population_affine_bounds` identifies this with a literal union of
integers when the marked prime is the unique largest prime. No label is
counted twice. Close largest-prime pairs are allowed; an incomplete period
keeps its actual moments instead of receiving a free cancellation claim.
The allocation is inside \(g_N\), so it has not been replaced by a limiting
share or charged through a separate worst derivative estimate.

`radial_affine_error_le` sums arbitrary finite radial collections. If their
cutoffs are at least \(D_0\), the total crossing cost is bounded by

\[
 \left(\sum_j W_j\right)(1+\log X)h
       \left(e^{2h}-1+e^{h-D_0}\right).
\]

This is an actual combined inequality, but **the total weight budget and the
retained signed moments are not proved small at source scale**. For an
integer union across periods, use disjoint radial selections; the theorem
on an indexed collection retains any multiplicities in that collection.

## Numerical checks and their limits

The optional `probe_riesz_global_curvature.py` evaluates the all-integer
crossing majorant by divisor incidence. At radial center 50 and
\(h=\pi/54\), it gives approximately 0.07094, below the proved bound evaluated
as 0.36074. A coarse all-divisor comparison is approximately 146.9. These
are floating-point diagnostics, not certificates or asymptotic prime counts.

With `--literal`, the script also enumerates small finite uniquely owned
prime populations at orders 6, 8 and 10. It retains the exact rational
moving cutoff, all unpaid allocation orders, the phase and both responses,
and compares the direct sum with its two signed moments and crossing bound.
At order 10 it enumerates 493,241 distinct labels (490,738 triples and
2,503 four-prime labels). The direct crossing error is approximately
`1.3205e-5`, below the bound evaluated as `0.7775`; the reflected coefficient
identity agrees to roundoff below `7e-15`. The loose upper bound is a warning
against treating this probe as a source-scale estimate. These finite orders
do not establish an eventual endgame estimate.

The same diagnostic exposes cancellation that must remain joint: at order 10,
triples contribute approximately `+1.1835e-4` and four-prime labels
`-5.5492e-5`. The constant-moment total is `+7.9291e-5`, while the first-moment
total is `-2.9633e-5`. Taking their separate absolute values would erase both
savings. The exact local crossing-weight profile evaluates to `9.5953e-5`,
much smaller than the uniform-budget bound; this motivates preserving the
cofactor dependence of that budget in the next estimate. None of these
finite computations proves a uniform prime-density comparison.


The all-integer diagnostic grows roughly as a constant times \(v h^2\).
That observation does not suggest source-normalized decay by itself.
Multiplying a relative improvement by the old \((2u)^N\) envelope is still
insufficient. The next target is a joint estimate for the retained
\(M_0\) and \(M_1\), with their allocation and boundary correlations intact,
and a source-scale bound for the combined crossing cost. A complete-period
estimate cannot be added to favorable subperiod credits without subtracting
their exact signed overlap.

The response is also the classical truncated divisor sum
`Lambda_R(a)` with `R=exp(D)`. Goldston and Yıldırım, Theorem 5.1, prove
`sum_(a<=X) Lambda_R(a)^2 = X log R + O(X) + O(R^2)`.
That suggests a possible mean-square control of the retained cofactor
profile, but their statement does not include this carrier's allocation,
prime-phase weights or hard masks. It is not imported or used by the Lean
proof above, and it does not by itself discharge the source-scale estimate.
[Primary paper, §5](https://math.colgate.edu/~integers/d5/d5.pdf).

The independent whole floor \(-79/1000-o(1)\), the ceiling \(3/2+o(1)\), and
the RH contradiction remain open. No zero hypothesis is used in these new
finite inequalities; no new zero-free region is claimed.

- [Global crossing estimate](../RiemannGaussian/ZetaRieszGlobalCurvature.lean)
- [Literal prime sum and both signed bounds](../RiemannGaussian/ZetaRieszGlobalPrimePeriod.lean)
- [Optional quantitative probe](../scripts/probe_riesz_global_curvature.py)
- [Verification record](riesz-global-crossing-audit.json)
