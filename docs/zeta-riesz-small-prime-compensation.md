# Paying the entire small-prime triple head

[`ZetaRieszSmallPrimeCompensation`](../RiemannGaussian/ZetaRieszSmallPrimeCompensation.lean)
proves an actual joint signed inequality for the unchanged finite core.
It pays every squarefree three-prime label containing a prime at most
`N^2`, together with the previously paid balanced triple band. It uses
one positive four-prime supply, retaining unused credit and the complete
signed complement. The independent numerical floor remains open.

For a slab `2M <= log(n) < 2M+2`, write `E(N,M)` for the original radial
envelope `exp(-3M)*(2M)^N/N!`. The moment remains `N`, not `M`.
The small-prime selection keeps the actual support `S`, squarefreeness,
three distinct factors, and the inherited physical prime bound.
`small_triples_norm_upper` proves, when `log Q <= M/8`, `N <= 2M`, and
`L >= M > 0`,

\[
\left\|\sum_{n\in\mathrm{smallTriples}(S,M,Q)} f_N(n)\right\|
\le B(1+\log Q)\frac{e^{2M}}{M+1}E(N,M),
\qquad B=768(\log4)^3e^4.
\]

Here `f_N` is exactly `residualCoefficient * zetaPrimeLogKernel`, including
the original allocation and complex phase. The key arithmetic fact is
`abs_riesz_triple_le_marked_log`: the three-prime Riesz coefficient costs
the logarithm of **any** marked prime. Actual interval counts for the
other two primes retain `1/r` for the small prime. The proved Chebyshev
budget sums `log(r)/r` over all primes through `Q`. No signed PNT or Abel
transport, continuum prime density, or source completion is used.

The existing actual positive four-prime supply has lower bound

\[
\operatorname{Re}Y_M\ge c_y M\frac{e^{2M}}{M+1}E(N,M),\qquad c_y>0.
\]

For `Q=N^2` and `M` in the original radial core, the ratio of these proved
costs is `O_y(log N/N)`. `eventually_small_slabs_cost` allows an arbitrarily
small fixed fraction of this radial scale. This is **relative compensation**,
not a claim that the normalized small-prime sum decays separately.

`eventually_joint_slabs_spending` uses the same actual phased supply to
pay at most half its real part for a fixed balanced band and at most one
quarter for the small-prime triples. Distinct radial slabs use disjoint
integer supplies. The small-prime selection excludes already selected
balanced labels explicitly, so neither debit nor supply is counted twice.

`eventually_core_small_balanced_floor` then covers the entire original
radial support. Missing slab endpoints lie in the independently bounded
radial edges. For the original dyadic schedule, fixed `|y|>=16`, and
`1/2<u<=10001/20000`, it proves an eventual inequality of the form

\[
\operatorname{Re}(u^{N+1}\mathrm{coreResponse}_N)
\ge u^{N+1}\left(\operatorname{Re}W+
 (\operatorname{Re}X)_+ +(\operatorname{Re}Z)_+
 +\tfrac14\operatorname{Re}Y\right)-Cr^N,
\quad 0\le r<1.
\]

`X` contains the paid balanced slabs, `Z` the remaining paid small-prime
slabs, and `Y` the **one** positive four-prime supply. `W` contains everything
else after removing both full triple populations and that supply. The
width of the balanced band is a fixed positive existential constant;
the theorem does not pay every band of width at most `1/1000`. The eventual
threshold and supply constants are not numerically evaluated.

The terminal `eventually_compensated_core_floor` applies the
[exact four-prime](zeta-riesz-four-prime-reserve.md) and
[exact five-prime](zeta-riesz-five-prime-reserve.md) debit comparisons only
to `W`. It retains their positive parts and every other prime-count class
with its original sign. It does not charge the used four-prime supply again.

The remaining task is to bound that signed complement together with its
unspent credits. In particular, triples with every prime above `N^2`
outside the paid balanced band remain. There is no fixed count ceiling for
the whole core, and the divergent old absolute allowance is not revived.
The sufficient [cofinal joint floor](zeta-riesz-joint-floor.md) is still
`-79/1000-o(1)`; no zero exclusion or RH proof follows from this component
inequality alone.
