# Zero exclusion from positive cosine modulation

Lean proves an unconditional eventual region for the actual zeta function:
there is a finite `T >= 1` such that every nontrivial zero
`rho=beta+i*t` with `abs(t)>=T` satisfies

\[
\frac{24}{125\log|t|}<\beta<1-\frac{24}{125\log|t|}.
\]

The terminal theorems are `exists_eventual_strip` and
`exists_eventual_nonvanishing` in
[GaussianFermiModulatedZeroFree.lean](../RiemannGaussian/GaussianFermiModulatedZeroFree.lean).
The latter proves literal `riemannZeta s != 0` on the corresponding
closed right edge. Every arithmetic and analytic antecedent is discharged.
**The finite height threshold is existential and unevaluated.** RH and
the independent signed prime estimate remain open.

## The preserved information

For every Gaussian width `B>0` and real modulation `delta`, keep

\[
g_{B,\delta}(u)=e^{-Bu^2}\frac{1+\cos(\delta u)}2,\qquad
H_{B,\delta}(x)=\int_0^\infty g_{B,\delta}(u)e^{-xu}\,du.
\]

The complete Fermi transform is an exact positive combination of the
three original evaluations at `z,z+i*delta,z-i*delta`, with weights
`1/2,1/4,1/4`. Both reflected-zero positivity and the actual full prime
sum retain their signs. The general identities apply to all admissible
original finite phase families; individual oscillatory prime terms are
not assumed nonnegative.

The two distinct horizontal partners of the selected right-half zero
contribute at least `m_rho*H_(B,delta)(sigma-beta)`. The complete averaged
constant pole is at most `H_(B,delta)(sigma-1)`. Combining its three
frequencies before bounding them is essential: separate inverse-square
estimates at the two tiny shifts lose this comparison. The original
outside allowance is unchanged because the positive averaging weights
sum to one.

See the [general modulation ledger](gaussian-fermi-cosine-modulation.md),
[actual arithmetic budget](../RiemannGaussian/GaussianFermiModulatedBudget.lean),
and [full source and coupled pole](../RiemannGaussian/GaussianFermiModulatedSource.lean).

## Exact integral estimates

At unit Gaussian width, let

\[
M_n(x)=\int_0^\infty u^n e^{-u^2-xu}\,du.
\]

[GaussianHalfLaplaceMoments.lean](../RiemannGaussian/GaussianHalfLaplaceMoments.lean)
proves absolute integrability, the boundary limit, and the exact identities

\[
2M_1(x)+xM_0(x)=1,\qquad
2M_{n+2}(x)+xM_{n+1}(x)=(n+1)M_n(x).
\]

The first identity retains the nonzero endpoint. The subsequent recurrence
keeps the alternating cosine coefficients signed throughout integration.
[CosineTaylorEnclosure.lean](../RiemannGaussian/CosineTaylorEnclosure.lean)
proves the global factorial remainder and the quartic and degree-twelve
upper bounds without a small-angle restriction.

The exact mass and dilation are

\[
H_{B,\delta}(0)=\frac{\sqrt{\pi/B}}4
  \left(1+e^{-\delta^2/(4B)}\right),\qquad
rH_{Br^2,\delta r}(xr)=H_{B,\delta}(x)\quad(r>0).
\]

The exponential tangent uses the actual modulated first moment. At
`delta=3/2`, its upper bound is `83/256`, improving the unmodulated `1/2`.
Together with exact exponential and pi bounds, this proves

\[
H_{1,3/2}(69/5000)\ge\frac{6911}{10000},\qquad
H_{1,3/2}(-9/16)\le\frac{2263}{2500}.
\]

The pole bound integrates the full degree-twelve cosine polynomial and
evaluates its moments through the recurrence. The remaining ordinary
Gaussian transform is bounded by `6279/5000` after completing the square
and integrating a quartic envelope over the displaced endpoint interval.
All remainders are included. These are kernel-checked integral inequalities,
not quadrature claims.

See [GaussianModulatedLaplace.lean](../RiemannGaussian/GaussianModulatedLaplace.lean)
and [GaussianModulatedLaplaceEnclosure.lean](../RiemannGaussian/GaussianModulatedLaplaceEnclosure.lean).

## The entire coefficient-class comparison

For every `0<=a0<=37/200`, `a1>=79/250`, `M<=61/100` and
`937/5000<=mu<=3/16`, Lean proves

\[
a_0H_{1,3/2}(-3\mu)+\frac M{12}+\frac1{20000}
\le a_1H_{1,3/2}\left(3\left(\frac{24}{125}-\mu\right)\right).
\]

The existing exact phase row satisfies this complete coarse class.
No new base phase coefficients are fitted. The frequency `3/2` selects
a concrete positive window to prove the exclusion; the preceding
modulation, dilation and moment identities remain general.

For an actual hypothetical zero write

\[
L=\log|t|,\quad H=50|t|,\quad
m=\frac3{16\log H},\quad B=\frac1{9L^2},\quad\delta=\frac1{2L}.
\]

The already proved `3/16` common-band theorem supplies the input margin
for every actual zero below `H`, including low zeros. For `L>=100000`,
the normalized margin `mu=L*m` lies in the displayed interval. At every
edge distance `d<=24/(125L)`, dilation yields

\[
a_0H_{B,\delta}(-m)+\frac{ML}4+\frac{3L}{20000}
\le a_1H_{B,\delta}(d-m).
\]

See `profile_surplus`, `scaled_profile_surplus` and
`exact_scaled_profile_surplus` in
[GaussianFermiModulatedProfile.lean](../RiemannGaussian/GaussianFermiModulatedProfile.lean).

## All remaining costs and the contradiction

Every original nonconstant phase has frequency between one and 24.
Its shifts by `abs(delta)<=1` remain at absolute height at least
`abs(t)/2` and at most `25*abs(t)`. The full pole cost is at most one,
and the gamma cost has leading coefficient `1/4` with a fixed remainder.
The constant mode uses the coupled pole bound above and a bounded gamma
cost. Summing every coefficient gives the complete upper cost

\[
a_0H_{B,\delta}(-m)+\frac{ML}4+9.
\]

The original uniform outside allowance eventually makes its full weighted
cost at most one. Selecting both horizontal partners retains their full
analytic multiplicity, which is at least one. Consequently a hypothetical
zero in the proposed region would require

\[
\frac{3L}{20000}\le10,
\]

contradicting `L>=100000`. See
[GaussianFermiModulatedHeight.lean](../RiemannGaussian/GaussianFermiModulatedHeight.lean)
and the [unconditional closing theorem](../RiemannGaussian/GaussianFermiModulatedZeroFree.lean).

The final threshold is the maximum of proved thresholds for the original
outside allowance, the common input band, the older global margin formula,
and `exp(100000)`. **`exp(100000)` alone is not a verified sufficient height.**
Horizontal reflection gives the other edge. The theorem
`exists_eventual_common_margin` then feeds the new coefficient back into
the entire bounded-height divisor for future comparisons.

## What remains open

This replaces the earlier coefficient `3/16` by `24/125`, a factor of
`128/125` in each eventual edge width. The edges still shrink like
`1/log|t|`; the remaining interior strip is not confined to the critical
line. The theorem gives no finite numerical height threshold or improved
finite zero count, and no best-published-region or historical novelty
claim is made.

The original global `zetaFermiZeroMargin` and the older squarefree-radius
transport retain their existing definitions. The
[subsequent general band transport](zero-free-region-transport.md) now uses
the new margin to prove a strictly larger actual squarefree Cauchy disc
and stronger decay for fixed marks. This does not bound the separate
factorial-moment prime heat independently. Its complex coefficients,
accumulated heat corrections and endpoints still need to be preserved.
That signed arithmetic estimate and RH remain open.
