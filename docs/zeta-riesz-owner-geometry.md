# Signed prime periods through the full separated-owner geometry

Both whole `J+C` estimates now cover the selected 7–55-prime populations
without the former `log(a) <= 0.7v` restriction. The numerical cofactor cap
used in the proof is `197v/200`; Lean proves that it follows automatically
from the retained largest-prime separation at every selected count.

The relative ownership gap of `v/200` is also replaced by the constant
`1/16`, enough to cover a full phase half-period because `|y| >= 54`.
Its normalized width therefore tends to zero. The remaining selection is exactly

\[
 a\text{ squarefree},\qquad \omega(a)=k,\qquad
 \frac{203}{500}v<\log a,\qquad
 \log q\le v-\frac1{16}-\log a\quad(q\mid a),
 \qquad 6\le k\le54.
\]

The owner prime still runs over its complete phase period

\[
 v-\frac{\pi}{|y|}-\log a<\log p
 \le v+\frac{\pi}{|y|}-\log a.
\]

No least-prime cutoff, coefficient-sign restriction, factorial-order deletion
or zero hypothesis is added. The original physical, core, count,
nondominant and allocation masks remain.

## Why the upper cap disappears

Summing the ownership inequalities over the squarefree cofactor gives

\[
 \log a\le k\left(v-\frac1{16}-\log a\right).
\]

For `k <= 54`, this implies

\[
 \log a\le\frac{54}{55}v<\frac{197}{200}v.
\]

`cofactor_cap_of_owner` and `mem_cofactors_iff_of_count_le` prove these
facts for actual integers. The counting cover adds no further restriction.

The allocation estimate is now

\[
 |\theta_N(pa)-\theta_N(p'a)|
 \le\frac{20(k+1)\sqrt{N+1}}{v}
       |\log(pa)-\log(p'a)|.
\]

It follows from the same exact binomial score variance as the narrower
estimate. The old `4(k+1)` theorem remains available on its former range.
Also,

\[
 \frac{v}{L(v-\log a)}\le\frac{100}{v},
 \qquad L\ge\frac{67}{100}v.
\]

Both signed responses remain in the coefficient:

\[
 c_L(pa)=(-1)^{k+1}\frac{-\log(pa)}L
 \left[\mathcal R_{\log(pa)-L}(a)-\mathcal R_{\log a-L}(a)\right].
\]

The second cutoff is constant along the prime fibre. Its amplitude is paid
together with the first response; it adds no variation cost.

With `B_k = responseConstant k` and the existing cofactor mass constants
`C_k, C'_k`, the relative local budget becomes

\[
 10000B_k\eta C_k+
 \frac{5000(k+1)B_k C_k+2000\,2^k C'_k}{\sqrt v}.
\]

For fixed count, choose `eta` first and then take the order sufficiently
large. The signed full-period sum still has arbitrarily small relative
local cost. No absolute value is taken on individual prime-phase atoms.

## Actual enlargement and whole-sum accounting

`eventually_near_balanced_extra` constructs six distinct cofactor primes
in disjoint logarithmic intervals near `0.14v`, followed by their unique
largest prime. Their actual product satisfies

\[
 \frac{21}{25}v<\log a\le\frac{2109}{2500}v
 \quad\text{(84% to 84.36%).}
\]

`eventually_thin_gap_extra` additionally constructs actual seven-prime
labels with `0.8544v < log(a) <= 0.85476v`. Every cofactor prime violates
the former `log(q) <= 199v/200-log(a)` restriction. These labels now fit the
same signed estimate with the constant-width separation.

Thus both the former cap and relative ownership gap are genuinely enlarged.
The earlier labels with a strictly positive unsaturated response remain
covered too.

All three cached `CheckRieszFixedCount*` applications compile with the wider
population. Counts 7–55 retain their combined debit `49/100000000` of the
local radial unit; with the previous six-prime payment the total stays
below `1/90000`. Both whole comparisons preserve:

- every favorable signed period observation;
- the growing margin of at least `(N/16)*sourceCredit`;
- the single global owner payment;
- all prior six-prime costs on the exact smaller unpaid complement.

The larger intermediate constants affect the eventual threshold, which
is not made effective. This is not source-normalized decay or a bound
uniform in a count growing with the order. Near-ties of the largest primes,
clipped ownership periods, radial ranges outside the covered saddle band,
and other prime counts remain. The independent whole floor
`-79/1000-o(1)` and ceiling `3/2+o(1)` are still open.

The optional smooth-density probe includes near-equal cofactor logarithms
at shares `0.74`, `0.80`, `0.84`, `0.89`, `0.855` and `0.8988`, with both exact Riesz responses,
the moving length and factorial allocation retained. Its small signed
ratios are diagnostic only; Lean uses no numerical probe as a premise.

- [Allocation variation](../RiemannGaussian/ZetaRieszAllocationVariation.lean)
- [Coverage and signed prime inequality](../RiemannGaussian/ZetaRieszFixedCountPeriod.lean)
- [Joint payment and actual added labels](../RiemannGaussian/ZetaRieszFixedCountBand.lean)
- [Whole floor and ceiling](../scripts/CheckRieszFixedCountWhole.lean)
- [Verification audit](riesz-central-capacity-audit.json)

The next objective is one combined prime-period estimate covering the remaining
share geometries, changing counts and radial periods. Further separate sector
extensions are not the target. Any completion must retain signed overlap with
previously credited populations; their favorable phase selections are not
entire prime periods. An aggregate curvature/hinge estimate is under investigation,
with no new global bound claimed.
