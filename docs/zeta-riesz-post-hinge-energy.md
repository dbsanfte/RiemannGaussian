# The whole joined floor's exact post-hinge energy price

This local slice tightens the price on the ENTIRE remaining signed energy.
It introduces neither a new carrier nor a positive whole-core majorant.
The original phase, masks, adverse cutoff selection, native funding overlaps,
supply witness and all previous geometric errors remain unchanged.
The independent signed-energy estimate and the floor remain open.

## An unconditional width bound

For the existing unit-log-corrected profile f, each literal step has

\[
 \Delta_k=f(k)-f(k+1)\le0,\qquad
 k\Delta_k^2\le-\Delta_k.
\]

`corrected_step_energy_le` proves the second inequality using the existing
exact bound |Delta_k|<=1/k. Telescoping includes the partial first hinge
interval and the final zero endpoint. For X>0 and L>=0 it gives

\[
 \mathrm{profileEnergy}\le(\log X-L)_+.
\]

`adverseProfileEnergy_post_hinge` gives the same cap on the ORIGINAL
whole-funded adverse subset. No label, bin or signed energy is discarded.

For every original core subset, including the funded union, its actual
cutoff endpoint X=max(1,sup S) satisfies log X<=203N/100. The actual moving
length retains its integer floor and added two. `length_lower_bound` gives

\[
 L_N\ge-2N\log u-2\log(N+1).
\]

For u<=10001/20000, `radius_log_le` proves log u<=-693/1000. Lean proves
log(N+1)<=N/2000 for every N>=65536. Consequently

\[
 L_N\ge277N/200,\qquad
 \mathrm{adverseProfileEnergy}\le129N/200.
\]

The order threshold 65536 applies to THIS profile cap only. It is not
an effective starting order for the independent arithmetic floor or for
the previously paid geometric error constants.

## Applied to the actual native whole-floor inequality

`eventually_joined_calibrated_floor` reuses the existing exact funding
witness and every previous error. Let E_N be `separatedEnergy` with the
original adverse cutoff selection. It proves

\[
 \Re[u^{N+1}\mathrm{joinedPhysical}]
 \ge-\sqrt{(129N/200)\max(E_N,0)}-e_N,
 \qquad e_N\to0.
\]

Diagonal, large-common-factor and nearby-label payments are retained once.
The paid, unpaid, radial-tail and supply sets still overlap according to
the original `rejoinedWeights`; no supply credit is spent a second time.
The comparison requires no exposed zero or unproved arithmetic hypothesis.

The price is smaller than the earlier universal 4(N+1) cap. It provides
a larger sufficient energy budget; it proves no cancellation bound on E_N.
Removing a negative paid cross family can still increase a finite remaining
energy, so no monotonicity in the original energy is asserted.

## The exact open numerical target

`cost_le_of_numeric_energy` proves the purely numerical implication

\[
 E_N\le\frac{3}{320(N+1)}
 \quad\Longrightarrow\quad
 \sqrt{\max(E_N,0)\,\mathrm{adverseProfileEnergy}}
 \le\frac{39}{500}=0.078.
\]

Combined with the checked native inequality, this sufficient energy bound
would give a floor -0.078-o(1), with strict room above the required -0.079.
`real_floor_of_numeric_energy` records the implication; its ENERGY PREMISE
IS OPEN. Neither the many-bin condition nor the decreasing separation of
the surviving total-log frequencies supplies that bound automatically.
The exact surviving pairs still have log(gcd(n,m))<=N/1000 and relative
distance>exp(-N/1000), with all counts, phases and funding weights joined.

## Numerical route selection and local validation

The optional `scripts/probe_riesz_post_hinge_budget.py` tests actual finite
integer divisor columns, original total-label phases and the exact rational
moving cutoff at orders4/5 and heights54/65/100. Allocation support is exactly
empty at those small orders. It checks the profile-width comparison and
the full signed prefix before testing a common-prefix-mean projection.
Native count56+ many-bin, physical, dyadic and funding-witness conditions
are not certified; these floats are not interval or cofinal certificates.

The common-mean projection is a diagnostic candidate, not a new theorem
used in the floor. Its variance/cost is computed before deciding whether
to build a larger projection framework. The earlier test with L=11N/8
retained over99.5% of the energy and increased the one-sided price in all
six cases. The native-length probe is recorded separately in the audit.
Neither test refutes a cancellation theorem for the actual unpaid carrier.

Focused direct/targeted Lean, ordinary-root import, all namespace linters
and all-public transitive axioms are recorded in
`riesz-post-hinge-energy-audit.json`. Probes stay outside ordinary CI.
No whole floor, ceiling, restricted contradiction or zero exclusion follows
until the remaining independent signed energy is numerically bounded.
