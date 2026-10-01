# Signed owner-period costs at growing counts

This slice removes the fixed `log a <= .985 v` restriction from the
original signed owner-prime floor. It then joins every selected count,
dyadic owner-log shell and radial prime period in one budget. The numerical
`-79/1000` whole floor and the RH contradiction remain **open**.

The source is
[ZetaRieszTinyOwnerPeriodFloor.lean](../RiemannGaussian/ZetaRieszTinyOwnerPeriodFloor.lean);
the focused validation record is
[riesz-tiny-owner-period-audit.json](riesz-tiny-owner-period-audit.json).

## The principle extracted from the sector savings

The original owner allocation is summed before estimating the prime phase.
Both Riesz hinges, the factorial kernel and the phase remain in the actual
signed prime sum. A complete phase period cancels its constant response;
only the exact cutoff variation, factorial curvature and actual prime
endpoints are charged. The relevant denominator is the owner logarithm
`P0 = v - pi/y - log a`, rather than an assumed fixed fraction of `v`.

`owner_fibre_geometry`, `owner_atom_eq` and `owner_fibre_floor` establish
this directly for the original unique-largest-prime atom. The whole owner
fibre must lie in the original allocation set, and every cofactor prime
must remain below `P0`. Neither a fixed cofactor cap nor a count ceiling
is assumed. The unfavourable phase-grid orientation is retained.

## One price for counts, log ranges and radial periods

Suppose every cofactor prime logarithm lies in `[H,4H]`, with `H >= 5000`.
The already-checked actual prime mass is at most `M = 5 log 4`, and true
squarefreeness gives cofactor reciprocal mass at most `M^k/k!`.

The cap-free curvature price is at most `5/H^2`. The exact two-hinge
response is bounded using `log(minFac a) <= 4H`; its cutoff displacement
is only the actual half-period. Consequently the original signed count-k
population has the one-sided price

\[
-\frac{481(2M)^k}{H k!}\frac{\operatorname{amplitude}(N,v)}v.
\]

Summing every selected count yields

\[
-\frac{C}{H}\frac{\operatorname{amplitude}(N,v)}v,
\qquad C=481e^{2M}=504365056.
\]

This includes growing counts whose owner share tends to zero.
`owner_all_counts_floor` proves the signed bound; no prime-density
replacement or hypothetical-zero estimate enters it.

For dyadic log ranges `H_j = H_0 2^j`, the exact price satisfies

\[
\sum_j\frac1{H_j}\le\frac2{H_0}.
\]

`dyadic_shells_floor` and `radial_dyadic_shells_floor` therefore join all
selected counts, shells and radial periods with one coefficient `2C/H_0`
times the same radial units. The number of ranges causes no extra loss.
This is a proved signed inequality for original owner atoms, not a new
scalar carrier.

The comparable-log restriction is automatic on the current retained
single-layer geometry: the complete based block forces all cofactor
prime logarithms into `[P/2,P]`, including the base primes.
`retained_single_layer_shell_exists` covers these by a dyadic shell
whenever `P >= 2H_0`. The existing polynomial-owner payment gives a
natural increasing starting height on its disjoint complement.

## Compatibility with the existing positive supply

Taking `H_0 = 8 log(N+1)` makes the relative price tend to zero.
`eventually_period_shell_cost_paid` connects this price to the **same**
selected four-prime supply and scale used in the previous global ledger.
Eventually the price is at most `1/256` of that supply, with the old
phase-window and scale hypotheses retained. It does not choose an
unrelated new supply. After a compatible disjoint cover is established,
this can use half of the existing `1/128` reserve once.

## What remains unproved

The current `polynomialCentralRemaining` is unchanged. These estimates
have not yet supplied a disjoint complete-fibre cover for its entire
unpaid incidence population. A shell cover for labels is not by itself a
cover by whole prime periods. Clipped periods, selector boundaries, other
prime holes and wider-log geometries remain explicit. The earlier
all-count close-owner boundary payment remains available, but is not
silently spent here or identified with a different shell boundary.

The new price is relative to actual radial/supply units. It is **not**
source-scale decay and cannot be multiplied by a crude `(2u)^N` absolute
envelope to infer it. The large constant is intentionally coarse; an
effective starting order and a fraction of the global deficit are not
certified. All earlier credits still require a disjoint ledger.

The optional `scripts/probe_riesz_tiny_owner_period.py` checks cap-failing
large-count curvature parameters, finite exact squarefree symmetry and
dyadic reciprocal-price sums. It does not evaluate the literal retained
carrier or certify the floor. It is outside ordinary builds and CI.
