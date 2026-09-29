# Reduce the enlarged order-ten cost without moving its signed center

[`exists_core_quadratic_gain_bounds`](../RiemannGaussian/ZetaRieszCoordinateGain.lean)
and `exists_core_gain_bounds` improve both original whole-core bounds when
a common coordinate change reduces their cost. The
[proof audit](riesz-coordinate-gain-audit.json) separates the compiled
inequalities from the optional numerical search.

## Exact joint saving

For any admissible common coordinates, the signed center is exactly

```math
H=\sum_n\sum_p W(n,p)\,\alpha_X(F_p)\,M_2(n).
```

`center_eq_unrotated` proves this identity. Changing coordinates on both
weights and profiles does not change `H`. Thus, if `C` and `D` are two
costs computed with the same arithmetic constant, define

```math
G=\max(0,C-D).
```

The original quadratic enclosure and the further conditioned enclosure
both inherit the exact inequalities

```math
\max(-B_0,H-C+G)\le J\le\min(B_0,H+C-G).
```

This keeps the exact signed center, all original labels, prime counts,
factorial orders including zero and one, masks, allocation, full product
phase and physical cutoffs. `exists_partition_quadratic_gain_bounds`
adds the actual gains across disjoint populations with the same `E`:

```math
\sum_i H_i-\sum_i C_i+\sum_i G_i
\le J\le
\sum_i H_i+\sum_i C_i-\sum_i G_i.
```

There is no extra maximum-cost or family-cardinality factor. Counts remain
coupled within each population; the numerical attribution by prime count
is not a separate countwise bound.

## Exact coordinate recipes

For a rational parameter `t`, the coefficients

```math
c=\frac{1-t^2}{1+t^2},\qquad s=\frac{2t}{1+t^2}
```

satisfy `c²+s²=1`. `coordinates_rationalPair` and
`coordinates_rationalSequence` prove that every admissible finite recipe
preserves the original pairing. Every coordinate remains, including tiny
directions. `pair_energy` retains the signed cross terms when computing
the new cost.

The optional search also constructs a recipe starting at the identity.
Floating eigenvectors only guide its rational parameter choices. Lean
proves exact admissibility of any such recipe; the floating evaluation of
its logarithmic energies is **not** a numerical certificate.

## Enlarged order-ten test

The test fixes `u=10001/20000`, `y=54`, cofactor cap `6,484,203`, and
all `32,709,252` selected labels. It retains all coordinate directions
and the entire exterior profile energy, including its signed cross terms.
Each candidate is rescored from the original arrays.

| Coordinates | Quadratic cost before `sqrt(E)` |
|---|---:|
| Previous profile basis | 0.0038179766 |
| Rational rotations from that basis | 0.0034322872 |
| Balanced numerical candidate | 0.0034062020 |
| Rational recipe from identity | 0.0034062096 |

The last recipe reduces the diagnostic budget by about **10.8%** without
changing its signed center, approximately `-0.0000540593`. Most of the
reduction occurs among cofactors from one to four million, where labels
with five and six prime factors account for much of the cost.

Reproduce outside ordinary CI:

```sh
OPENBLAS_NUM_THREADS=4 ../.venv/bin/python \
  scripts/probe_riesz_order10_coordinates.py \
  --output /tmp/riesz-order10-coordinate-audit.json
```

The output includes the exact rational recipe parameters. The tracked
audit retains their counts and hashes rather than the large recipe arrays.

The population omits earlier nested core deletions; `E` remains
unevaluated. These finite floating values do not certify a whole-carrier
bound, an eventual rate, or a zero exclusion. The source-normalized signed
center and remaining large-order cost still need estimates strong enough
for the independent `-79/1000` floor and `3/2` ceiling.
