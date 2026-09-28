# Wider six-prime cancellation in both whole estimates

Both whole comparisons now pay a larger six-prime population and need one
fewer separate allocation error. The retained margin is unchanged, and
the complementary signed sum is smaller. The final numerical whole floor
and ceiling remain open.

## Actual population

Let `B(v)` be the five-prime cofactor set of
[`ZetaRieszBroadSixPeriod`](../RiemannGaussian/ZetaRieszBroadSixPeriod.lean):
`56v/125 < log(a) <= 3v/5`, with each prime divisor's logarithm at most
`39v/100`. The new cofactor set is exactly

\[
\left(B(v)\cup B(4v/5)\right)\cap
 \{a:\log a>41v/100\}.
\]

Overlapping cofactors are counted once. For each one, its unique largest
prime runs through the full original phase period

\[
v-\pi/|y|<\log(pa)\le v+\pi/|y|.
\]

This retains squarefreeness, every small cofactor prime, both coefficient
signs, the full complex phase, all original core masks and the original
allocation. Every prime's share is at most `591/1000` for the stated
large-`v` regime. The previous broad population is a proved subset; its
payment is **replaced**, never added a second time.

## The quantitative gain

[`ZetaRieszWideSixAllocation`](../RiemannGaussian/ZetaRieszWideSixAllocation.lean)
proves, for every finite eligible prime set `A`,

\[
0\le\operatorname{boundedShare}(A,N,n)
 \le6e^{-N/100000}
\]

on these six-prime labels. This rate is deliberately used **before source
scaling**. It does not beat the crude growing source envelope by itself.

The actual unsigned population mass is bounded by
`192*C1*m*V*h`, where `C1` is twice the preceding logarithmic cofactor
constant and `V` is at most the original radial weight. Only the allocated
fraction uses this norm estimate. Thus its relative cost is at most
`192*C1*6*exp(-N/100000)`, which tends to zero. The unallocated response
keeps the signed last-prime cancellation, with the exact moving Riesz
coefficient and its cutoff variation.

For every fixed `|y|>=54` and `epsilon>0`, eventually uniformly for
`2N<=v<=2N+1`, `cos(y*v)=-1`, `L>=67v/100`, and every finite `A`, Lean proves

\[
\left|\operatorname{Re}\sum_{n\in Z(v,y)}
 \operatorname{residualCoefficient}(A,L,N,n)K_N(3/2+iy,n)\right|
\le\epsilon\frac{\pi}{4|y|}\frac{e^{-v/2}v^N}{N!}.
\]

See `eventually_residual_population_small` in
[`ZetaRieszWideSixPeriod`](../RiemannGaussian/ZetaRieszWideSixPeriod.lean).
This is a genuine signed bound for the literal residual population,
including its allocation. It is **relative local o(radial), not
source-o(1)**. The starting order is existential and may depend on height
and precision.

## The same whole floor and ceiling

[`CheckRieszWideSixJoint.lean`](../scripts/CheckRieszWideSixJoint.lean)
uses this larger `Z` in both concrete comparisons, retaining the margin

\[
\left(\frac{\sqrt{N+1}}{16}-\frac18\right)G_N
\]

and every favorable signed observation. The exact unpaid rest is now
`S \ (P union I union H union Q union wideZ union D)`.
Only the preceding triple payment `Q` requires the separate geometric
`allocationBound`; the six-prime allocation is absorbed into its local
`m*V*h/100000` debit.
[`CheckRieszWideSixWhole.lean`](../scripts/CheckRieszWideSixWhole.lean)
retains all earlier second-reflection savings on precisely this rest.
The optional numerical-cover hypotheses are discharged with unchanged
cached assemblies. No exhaustive certificate rerun is involved.

Neither comparison assumes a zero or simplicity. Neither establishes the
final independent `-79/1000` whole floor or `3/2` ceiling. Other populations
and phase periods still require signed estimates. No zero exclusion or RH
claim follows from this slice.

## Numerical diagnostic

The optional
[`probe_riesz_wide_six_period.py`](../scripts/probe_riesz_wide_six_period.py)
uses the exact angular union corresponding to the new cofactor definition.
Four scrambled Sobol replicates place its coverage at about 92.5–92.7% of
the sampled negative one-large six-prime angular mass, versus 71.5–71.7%
for the preceding broad band. The samples exclude radial and phase
weights; these percentages are neither rigorous enclosures nor an
arithmetic certificate and are not spent in Lean. The proof is independent
of the probe. Its results are in
[`riesz-wide-six-period-probe.json`](riesz-wide-six-period-probe.json).
