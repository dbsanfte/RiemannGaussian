# A global estimate for the joined signed main

The target remains an independent cofinal bound

\[
\operatorname{Re}P_N\le\frac{399}{5000}+o(1),
\qquad P_N=\mathrm{prefixPairDefect}(u,y,N).
\]

[`ZetaRieszJoinedPhaseRadius`](../RiemannGaussian/ZetaRieszJoinedPhaseRadius.lean)
now bounds **this whole literal signed main**, with the favorable credit and
remaining terms assembled. At every fixed \(54\le|y|\), there are
\(1/2<R_y<3/4\) and \(C_y>0\) such that, for all requested radii
\(1/2\le u\le10001/20000\) and \(N\ge65536\),

\[
\boxed{\|P_N\|\le26C_y^2(u/R_y)^N+E_N(u).}
\]

Here \(E_N\) consists of the **existing** whole-support completion budget
and one square-diagonal budget. Both tend to zero geometrically. Neither is
spent twice. The estimate has no exposed-zero, rightmost-zero or prime-density
transport hypothesis. It retains the literal masks through their already
proved whole-sum bridge; it does not complete a new masked cofactor.

The rate improves on the critical \(2u\) at every fixed height, because
\(R_y>1/2\). It need not be below one. The all-height absolute floor and the
multiple-zero ceiling remain open; no new zero exclusion is claimed.

## Why summing the correlated orders matters

The existing finite symmetric convolution and Selberg join give
`harmonicEvaluation (ordinaryArray u y) u N`, with its trace, both central
slots, logged successor slot, exact integer endpoints and moving length.
Order-zero logged moments remain included.

Actual zeta nonvanishing on the closed half-radius disk, compactness and
openness of analyticity give an independent analytic radius \(R_y>1/2\)
for \(-\zeta'/\zeta\). Cauchy bounds and the convergent proper-prime-power
correction give, simultaneously for every logged order,

\[
\|H_k^{\mathrm{ordinary}}(3/2+iy)\|\le C_yR_y^{-k}.
\]

In each quadratic slot the two logged indices have total order \(N-1\)
or \(N\). Bounding these **correlated total orders** gives
`norm_harmonicEvaluation_le_geometric`, with constant 26. It does not
replace two orders separately by a largest-order envelope. The direct
ordinary-prime bound also avoids assuming a bounded exposed moment array
merely to pay the proper-power correction.

`norm_prefix_sub_ordinary_le` transfers the already proved whole-symmetric
completion and square correction to this evaluator. The resulting
`norm_prefix_le_radius` is an independent bound for the existing retained
signed main, rather than another equality to an unpaid carrier.

## Global cancellation with the full actual-prime credit

Write \(B_N=\mathrm{exactSignCredit}(u,y,N)\). The preceding slice proved
\(B_N\ge c_{u,y}(2u)^N/(N+1)^3\) eventually, with \(c_{u,y}>0\).
Combining that actual-prime population estimate with the new whole-main
bound gives

\[
\|P_N\|\le
D_{u,y}(N+1)^3(2R_y)^{-N}B_N+E_N(u).
\]

Since \((2R_y)^{-1}<1\), the checked conclusions are

\[
\boxed{\frac{\|P_N\|}{B_N}\longrightarrow0,\qquad
\frac{\operatorname{Re}\mathrm{signedRest}_N}{B_N}\longrightarrow1.}
\]

`signed_rest_div_exact_credit_tendsto_one` states the second limit for
the **literal** complementary sum, using the exact existing ledger
\(\operatorname{Re}P_N=\operatorname{Re}\mathrm{signedRest}_N-B_N\).
The full credit, including its excess over the rational benchmark, remains
present. All retained populations are joined; there is no sector-by-sector
positive allowance.

This is quantitative relative cancellation across the whole support. It
does not bound the absolute remaining difference by 0.0798: a relatively
small difference between exponentially growing contributions can still
grow, or converge to a source-sized constant.

## Where the absolute cofinal bound follows

`prefix_tendsto_zero_of_radius` proves decay whenever \(u<R_y\).
`eventually_uniform_prefix_small` is uniform on any closed radius interval
whose endpoint is strictly below \(R_y\). Consequently every fixed height
has a nonempty, possibly very narrow interval starting at \(u=1/2\) on
which the independent 0.0798 bound holds.

There is also a concrete full-radius regression using the repo's existing
signed-pole zero-free region. Under

\[
54\le|y|,\qquad\log(|y|+3)\le1800,
\]

Lean proves an analytic disk of radius \(R=100011/200000\). The exact
denominator inequality has positive rational room \(7447/200\), and

\[
\frac{u}{R}\le\frac{100010}{100011}<1
\]

throughout the requested interval. Thus
`eventually_concrete_height_joint_floor` proves
\(\operatorname{Re}P_N<399/5000\) eventually, uniformly in that interval.

**These heights are already excluded in the candidate strip by existing
zero-free results.** This transfers existing coverage into the current
carrier; it is not progress into a previously unresolved zero strip.
Neither a numerical Cauchy constant nor a numerical entry order is supplied.
The height-local conclusion likewise does not establish a new zero region.

## The exact remaining obstruction

For heights/radii lacking a proved strict margin \(R_y>u\), this method
only supplies an improved exponential bound and the relative cancellation
limit. It does not settle the signed source-sized residue.

`radius_le_of_nonzero_ordinary_source` checks the limitation explicitly:
if the actual normalized ordinary-prime array tends to a nonzero source
and satisfies this Cauchy bound, then \(R_y\le u\). An exposed selected
zero cannot be norm-paid by silently choosing a radius past its pole.
The global relative cancellation theorem remains compatible with that
source, so it alone cannot give a contradiction.

The unchanged simple-mode source at the radius ceiling is approximately
\(0.07987179703494418\), above the required 0.0798. Their difference
\(0.00007179703494418\) is the **contradiction margin**, not measured unpaid
mass or a fraction of progress. The next endgame theorem still needs an
independent **one-sided estimate of the absolute joined residue** at the
uncovered heights. No fraction of that remaining margin has been certified.
The older positive-density, completion, mask-transfer and resonant-budget
no-gos all remain in force.

## Optional rate probe and focused validation

[`probe_riesz_joined_radius_rates.py`](../scripts/probe_riesz_joined_radius_rates.py)
audits the two exact rate factors and the unchanged source regression with
90-digit decimal arithmetic. It labels hypothetical radii as scenarios,
does not sample primes, and never treats an unknown constant as a certified
unit constant. It exposes the distinction between relative cancellation
and an absolute floor, especially at \(R=u\). Numerical outputs are not
used in the Lean proofs.

The strict leaf build and
[`CheckRieszJoinedPhaseRadius`](../scripts/CheckRieszJoinedPhaseRadius.lean)
check the namespace and transitive axioms, including private/generated
helpers. The scoped record is
[`riesz-joined-phase-radius-audit.json`](riesz-joined-phase-radius-audit.json).
All 247 earlier source/artifact pins were verified before the guide update;
old proof/probe snapshots are preserved. Work remains local, with no root
registration, wider gates, CI run, commit or push.
