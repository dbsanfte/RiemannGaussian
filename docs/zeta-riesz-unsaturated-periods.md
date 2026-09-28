# Signed prime periods across the saturation boundary

Both whole `J+C` comparisons now include a wider part of the selected
7–55-prime sectors. The cofactor ceiling increases from `133v/200 = 0.665v`
to `7v/10 = 0.7v`. The complete prime period, unique-largest-prime condition,
original allocation and all core masks stay in place. The same combined
local debit `<1/90000` and growing credit are retained.

This crosses a genuine coefficient boundary. The old argument used
`log(a) <= L` to remove a second Riesz cutoff. The wider family needs the
exact formula

\[
 c_L(pa)=(-1)^{k+1}\frac{-\log(pa)}{L}
 \left[\mathcal R_{\log(pa)-L}(a)
       -\mathcal R_{\log a-L}(a)\right],
 \qquad \omega(a)=k.
\]

The second response is retained even when it is positive. It is constant
as the largest prime `p` varies, so it contributes **no additional cutoff
variation** along the phase period. The two responses together cost at
most twice the same count-dependent least-prime bound. That larger fixed
constant changes the eventual starting threshold, but not the arbitrarily
small signed local debit.

The original factorial-allocation derivative estimate also extends to
`log(a) <= 0.7v`. The denominator estimate remains

\[
 \frac{v}{L(v-\log a)}\le\frac5v,
 \qquad L\ge0.67v,
\]

because `5 * 0.67 * 0.3 > 1`. Thus every previous part of the finite-prime
inequality still applies. There is no completion, changed carrier, discarded
phase or independent norm estimate for the second response's prime sum.

## Nonempty arithmetic extension

`eventually_unsaturated_extra` constructs six distinct cofactor primes in
disjoint logarithmic intervals. Their product satisfies

\[
 0.6948v<\log a\le0.6984v.
\]

The seventh, largest prime is taken from the complete phase interval.
For every `0.693v <= L <= 0.6932v`, Lean proves the second Riesz response
strictly positive. In fact its cutoff is below the least-prime logarithm,
so it equals `log(a)-L`. These are actual primes and integers, not just
points in a continuous simplex. The new population therefore includes
labels outside the former cofactor ceiling with a genuinely active
unsaturated correction.

## Whole-sum use and limits

`CheckRieszFixedCountLocal`, `CheckRieszFixedCountJoint` and
`CheckRieszFixedCountWhole` use the widened population in both directions.
The floor retains favorable positive observations and the ceiling retains
favorable negative observations. The single global owner debit, all prior
six-prime costs and the growing margin `>=(N/16)*sourceCredit` remain on
the exact, now smaller unpaid complement.

This is still a relative local signed estimate, not a source-normalized
decay theorem. Constants depend on fixed prime count and height. Clipped
ownership periods, other share configurations, radial ranges and growing
counts remain. The independent whole floor `-79/1000-o(1)` and ceiling
`3/2+o(1)` are both open. No new zero exclusion is claimed.

The optional smooth-density probe now includes both cutoff terms. At
cofactor share `0.696`, its examples show strong cancellation despite a
nonzero correction. These computations guide the proof; they are not
prime-count certificates or assumptions used by Lean.

- [Exact response and signed estimate](../RiemannGaussian/ZetaRieszFixedCountPeriod.lean)
- [Actual unsaturated population](../RiemannGaussian/ZetaRieszFixedCountBand.lean)
- [Whole floor and ceiling](../scripts/CheckRieszFixedCountWhole.lean)
- [Underlying fixed-count mechanism](zeta-riesz-fixed-count-periods.md)
- [Optional numerical probe](../scripts/probe_riesz_fixed_count_period.py)
- [Proof audit](riesz-central-capacity-audit.json)
