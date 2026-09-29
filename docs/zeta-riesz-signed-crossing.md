# Signed cutoff crossings and the global error obstruction

Lean now sharpens both sides of the literal prime-period comparison by
preserving the sign of the cutoff correction. It also rules out the proposed
separate absolute-error payment: that cost is unbounded at source scale even
on one actual three-prime box per order. The combined signed sum is not
proved unbounded, and its whole floor and ceiling remain open.

## The sign retained in the new estimate

For a hinge at offset `z`, its exact affine remainder is

\[
b(z,x)=(z+x)_+-z_+-x\,\mathbf1_{z>0}.
\]

`hinge_error_nonneg` and the existing localization bound give

\[
0\le b(z,x)\le(h-|z|)_+,\qquad |x|\le h.
\]

Consequently the true signed multiplier `g*mu(d)` determines which side
needs a debit. Writing `M` for the existing constant and first signed prime
moments, `literal_signed_affine_bounds` proves

\[
M+E_-\le\operatorname{Re}S\le M+E_+,
\]

\[
E_- =\sum_{a,p,d\mid a}\frac{\min(g(a,p)\mu(d),0)}a
       (h-|v-L-\log d|)_+,
\qquad
E_+ =\sum_{a,p,d\mid a}\frac{\max(g(a,p)\mu(d),0)}a
       (h-|v-L-\log d|)_+.
\]

`S` is the original allocated residual prime sum. Its `g` retains count
parity, allocation, factorial weight, reciprocal prime and full cosine
phase. Both Riesz cutoffs stay in `M`. The estimate has no upper count or
share restriction. `radial_signed_affine_bounds` sums arbitrary finite
radial collections, including clipped periods, with their real moments.
Indexed repetitions are not silently identified with disjoint integer sets.

This is a genuine one-sided improvement over charging all crossings on both
sides. It is not a proof that `E_-`, `E_+` or `M` is source-small. Previously
paid favorable subperiods cannot be added again to a complete period.

## A concrete crossing that helps the floor

Take `N` large, the original moving length `L=L_N`, and a negative cosine
peak `2N<=v<=2N+1/2`. For fixed `|y|>=54`, put
`w=pi/(64|y|)`. The actual ordinary-prime windows are

\[
\begin{aligned}
L/2+3w&<\log p\le L/2+4w,\\
L/2-w&<\log q\le L/2,\\
v-L+w&<\log r\le v-L+2w.
\end{aligned}
\]

Lean proves `p>q>r`, squarefreeness, count three, unique largest-prime
ownership, and membership in the original core. The full product log lies
in `(v+3w,v+6w]`, inside the original phase period. Every prime log share
is below one half, so the original assigned fraction is eventually at
most one half, uniformly over the original selected-prime set.

For `a=q*r`, the exact response and its affine approximation differ by

\[
\mathcal R_{T-L}(a)-\mathcal R_{v-L}(a)
  -(T-v)\,\mathrm{cutoffSlope}(v-L,a)
=L-\log p-\log q\le-2w.
\]

The second, cofactor-dependent cutoff cancels exactly in this difference;
it was not discarded from the carrier. The negative cosine multiplies
this negative correction. `triple_crossingAtom_lower` therefore proves
the **positive** literal crossing correction is at least

\[
\frac w2\,\frac{e^{-3\log n/2}(\log n)^N}{N!}.
\]

This correction is part of the original signed atom and its affine
comparison. It is not an extra reserve that can be counted twice.

## The separate absolute budget cannot work

The proved fixed-width prime-count theorem supplies the number of these
labels. No phase-density approximation is used. Together with the exact
factorial normalization, `eventually_period_crossing_growth` proves

\[
\mathrm{absolutePeriodCrossing}(u,y,j,v)
\ge c_{u,y}\frac{(2u)^{N_j}}{(N_j+1)^4},\qquad c_{u,y}>0,
\]

eventually, for every negative peak in `[2N_j,2N_j+1/2]`, throughout
`1/2<u<=10001/20000`. The left side is the source-normalized absolute
crossing error on the **actual core period**, with canonical ownership and
the original allocation. `boxCrossing_eq_owned` prevents duplicate labels;
`tuple_mem_core` and `box_le_absolutePeriod` check the support bridge.

Because `2u>1`, `not_eventually_period_cost_bounded` rules out even a fixed
constant upper bound for all these period costs. This is stronger than
showing that a loose majorant diverges. It does not disprove an estimate
for the joint signed sum, nor an estimate for a smaller remaining set
after a separate, correctly accounted signed payment.

The next estimate must keep the constant moment, first moment and cutoff
correction coupled. The previous global nonowner allocation is still
source-`o(1)` and the owner variation bound remains valid. Neither the
whole `-79/1000-o(1)` floor nor the `3/2+o(1)` ceiling is proved. There is
no new zero exclusion or RH claim.

## Numerical diagnostic and proof audit

`scripts/probe_riesz_signed_crossing.py` is an optional smooth-density
diagnostic. It keeps the actual moving floor length through `N=8192`;
at larger orders it records an explicit bound on the sub-roundoff floor
correction. It uses every original unpaid factorial order and the original
allocation fraction. The logarithmic source rate is
`log(2u)`, about `0.000099995` at the radius ceiling. Large orders are
essential: a long initial decline does not imply cofinal decay.

The floating diagnostic is not a discrete certificate. The independent
Lean lower bound above establishes the obstruction without trusting it.

Sources:
[ZetaRieszSignedCrossing.lean](../RiemannGaussian/ZetaRieszSignedCrossing.lean),
[ZetaRieszCrossingGrowth.lean](../RiemannGaussian/ZetaRieszCrossingGrowth.lean).
[Source hashes, theorem list and diagnostic output](riesz-signed-crossing-audit.json).
