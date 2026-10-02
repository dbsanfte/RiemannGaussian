# Geometry of the unpaid signed crossings

The native floor remains **open**. This detector extends the existing
unpaid-only probe with exact signed incidence tensors and unsigned hinge
boundaries. It searches arbitrary supplied log vectors without assigning
them a theorem-family name. The numerical rank findings are finite-input
model results, not a native population bound.

The backend is
[`riesz_hinge_geometry.py`](../scripts/riesz_hinge_geometry.py), with the
optional driver
[`probe_riesz_hinge_geometry.py`](../scripts/probe_riesz_hinge_geometry.py).
The underlying complete-cube cancellation and a signed pair floor criterion
are proved in
[`ZetaRieszSignedCubeGeometry.lean`](../RiemannGaussian/ZetaRieszSignedCubeGeometry.lean).
Receipts and source snapshots are in
[`riesz-hinge-geometry-audit.json`](riesz-hinge-geometry-audit.json).

## What is measured

For a cutoff `D` and positive cofactor logs `x_i`, the detector retains

```text
M0(D)   = sum_{sum_A x < D} (-1)^|A|,
M1_i(D) = sum_{sum_A x < D} (-1)^|A| * 1_{i in A},
M2_ij(D)= sum_{sum_A x < D} (-1)^|A| * 1_{i,j in A}.
```

All subsets and counts enter these sums. For the original two hinges
`D=L-log(owner)` and `E=L`, it evaluates the exact coefficient as

```text
D*M0(D)-E*M0(E) + sum_i x_i*g_i,
g_i = -M1_i(D)+M1_i(E).
```

The `g_i` are the local coordinate gradients at fixed cutoffs, away from
every unsigned subset boundary. Equal gradients identify directions that
redistribute cofactor log while preserving total log and the coefficient.
The incidence matrix `M2(D)-M2(E)` records which directions have common
signed subset membership. Its exact rational rank is a correlation feature;
it is **not** a Hessian, a positive covariance matrix, or a prime-energy
estimate. Null directions in that matrix alone are not transport theorems.

Strict and inclusive cutoff moments are computed separately. Their
difference retains all signed hinge-wall incidences. A separate exact
search keeps the nearest **unsigned** subset knot, even if its signed
coefficient cancels. A local affine neighborhood requires fixed cutoffs
and total cofactor displacement in the L1 norm strictly below that gap.
It does not control hard-mask or allocation derivatives.

## Why high-dimensional cancellation is accessible

A complete free cube has exact signed parity cancellation: a monomial
depending on fewer coordinates than the cube dimension sums to zero.
Thus all degree-zero, one and two signed incidence moments vanish on a
complete free cube of dimension greater than two. This is an algebraic
fact, with no prime-density assumption. The Lean theorem
`signedCube_polynomial_eq_zero` covers arbitrary complex coefficients.

The evaluator prunes such complete cubes jointly. It also discovers the
exact Boolean complement relation: a strict prefix above half the total
log is the complement of an inclusive reflected prefix below half, with
the actual parity and incidence transformation retained. No nearly-full
subset layer is discarded. An explicit work stack handles growing counts
without an interpreter recursion-depth cutoff.

The final Lean theorem `signedCube_real_floor_of_pairs` is a direct
one-sided criterion for the actual signed pair discrepancies. The weight,
phase and membership must all be inside the function being paired. An
unused coordinate of an unweighted polynomial does not license deleting
a coordinate of the literal weighted carrier.

## Findings on unpaid model geometry

At native index 1024, a 30-record scan rejects 12 paid configurations
before geometry work. Of the 18 surviving configurations, 15 have complete
tensors and unsigned boundary gaps; three generic 300-coordinate profiles
remain unresolved and unranked. The resolved models have `49..70` occupied
cofactor bins, beyond the paid ceiling 45.

Four resolved coefficients and tensors vanish. The other eleven have
incidence rank **one**, including three 300-coordinate active-hinge cases.
In those cases, 299 small-cofactor directions have the same gradient;
only the distinguished large cofactor has a different gradient. The
remaining response is collective rather than 299 independent responses.
This supports investigating the collective boundary before charging each
coordinate separately. It supplies no sign or density law for all native
cofactors.

Fifteen independent finite-input interventions move log between equal-gradient
coordinates, retain exact total log, and recheck the unpaid support before
evaluation. The coefficient remains exactly unchanged. The full phase and
radial factor therefore remain fixed in the log model; allocation enclosures
are recomputed rather than assumed invariant. Such same-count directions
do not create opposite-parity prime partners. Distinct real integers cannot
be inferred from an exact fixed-total virtual-log construction.

A second scan accepts eight arbitrary nonlattice unpaid profiles and rejects
seven paid profiles. All eight exceed the exact work budget and stay null
and unranked. No tensor rank, sign, or cancellation percentage is guessed
for them. These unresolved cases prevent a claim of generic rank-one geometry.

## Validation and remaining arithmetic work

The backend has 400 independent signed-tensor enumeration comparisons,
200 unsigned-knot comparisons and 40 complete two-hinge comparisons.
Tests include strict/inclusive equality, canceled signed walls with real
unsigned boundaries, state/storage exhaustion, a complete 300-coordinate
hierarchy and an exact 512-coordinate complement regression.
These tests validate finite-input arithmetic, not real-prime logarithm
intervals or Python correctness in Lean.

The five public Lean proofs pass focused strict compilation, targeted build,
ordinary root import, namespace lint and standard-axiom inspection.

Reproduce from `formal/`:

```sh
../.venv/bin/python scripts/probe_riesz_hinge_geometry.py \
  --counts 20 55 64 300 4000 --seeds 317 \
  --active-hinges --inner-regressions --self-test \
  --output .lake/riesz-hinge-geometry/unpaid-final.json

../.venv/bin/python scripts/probe_riesz_hinge_geometry.py \
  --inputs-json .lake/riesz-generic-pattern/arbitrary-inputs.json \
  --state-budget 4096 --moment-budget 200000 \
  --output .lake/riesz-hinge-geometry/arbitrary-unpaid.json
```

The existing centered transport theorem supplies an actual geometric
source price once native centered families and funding are proved; see
[`zeta-riesz-insertion-capacity.md`](zeta-riesz-insertion-capacity.md).
The missing obligations are still native partner inventory, global column
capacity, the original allocation/funding ledger and the signed unmatched
remainder. Neither low incidence rank nor a small model coefficient pays them.
Keep probes outside builds/CI and preserve the published endpoints.
