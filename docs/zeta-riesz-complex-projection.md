# Whole-carrier phase cancellation

`ZetaRieszComplexProjection.native_floor` proves a lower inequality for
the original source-scaled `joinedPhysical`, retaining its phase, allocation,
physical support, window and count masks. The proved count crop is included
in the error. No cofactor is completed or prime-count class estimated
separately.

Let `P_j` be the original source-scaled joined carrier and `Q_j` its
count-cropped core. For one common real tilt `v` in `[-4,4]`, first join all
labels and counts in each complete divisor-cutoff phase period, then measure
the negative part of its real contribution minus `v` times its imaginary
contribution. `nativeCost` is the least such cost. Compactness proves that a
minimizer exists; zero tilt is included, so the new cost never exceeds the
original complete-period price. The exact result is

\[
 \Re P_j\ \ge -\operatorname{nativeCost}_j-e_j,
 \qquad e_j=4|\Im P_j|+5\|Q_j-P_j\|.
\]

`tendsto_nativeError` proves `e_j -> 0` under the existing exposed-zero
hypotheses, for every analytic multiplicity. The whole source is real. This
does **not** assert that an adverse cutoff subset, prime-count class or
constructed finite population has vanishing imaginary part.

`native_floor_with_credit` retains the exact nonnegative directional credit
relative to the old adverse Cauchy price. Its companion cost comparison pays
the credit and the remaining cost together; it does not add a credit to an
already weakened carrier inequality. All old geometric pair payments remain
available, but their final signed energy budget is still unproved.

There is also a necessary safeguard: when the whole imaginary part is zero,
`negative_real_le_bestCost_of_im_eq_zero` proves that the new cost is at least
the actual negative real contribution. The selected source cannot be paid
to zero by this optimization. A cofinal bound
`nativeCost <= 399/5000` would close the relaxed simple-zero floor, as proved
by `false_of_cofinal_nativeCost`; that arithmetic premise is **open**. No
independent numerical floor, ceiling, zero exclusion or rate of progress
toward the remaining budget is certified here.

The optional `scripts/probe_riesz_complex_projection.py` joins every retained
squarefree label in two constructed probable-prime universes at native orders
256 and 640, using two seeds and heights 54, 65 and 100. In twelve tests, a
single bounded tilt after complete-period aggregation reduced the measured
one-sided price by approximately 0.079% to 36.717%. A coarser nine-direction
Cauchy test improved nine cases, with at most 43.533% reduction. An alternative
projection of the *full* positive-semidefinite energy was worse than the
original adverse-only price in all twelve cases and is set aside.
An additional one-seed test at order 1536 reduced complete-period prices
by approximately 0.009%, 25.583% and 27.602%, depending on the height.
This variation supplies no uniform arithmetic rate.

These are subset diagnostics with common amplitude rescaling, floating-point
arithmetic and harmonic/logarithmic interpolation. Every subset imaginary
correction is reported and checked against the unchanged literal finite sum;
including it can worsen a subset price. There is no population-density,
interval, growing-count or cofinal certificate, and the eventual `K/864` crop
is not applied at these small orders. The probe is outside ordinary builds
and CI. Reproduce it from `formal/` with:

```bash
../.venv/bin/python scripts/probe_riesz_complex_projection.py
```

Focused local validation and preservation hashes are recorded in
`docs/riesz-complex-projection-audit.json`. Published theorem endpoints and
README claims remain unchanged.
