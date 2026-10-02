# Signed null directions in the whole floor

The native floor remains **open**. This slice proves an explicit credit
in the original `joinedPhysical` inequality and adds a detector for joint
signed-cost directions. **No native credit magnitude, cofinal cost bound,
restricted contradiction or new zero-free region has been established.**

The Lean source is
[`ZetaRieszSignedNullGain.lean`](../RiemannGaussian/ZetaRieszSignedNullGain.lean).
The optional backend and driver are
[`riesz_signed_block_geometry.py`](../scripts/riesz_signed_block_geometry.py)
and
[`probe_riesz_signed_block_geometry.py`](../scripts/probe_riesz_signed_block_geometry.py).
They are outside ordinary builds and CI. Receipts are in
[`riesz-signed-null-gain-audit.json`](riesz-signed-null-gain-audit.json).

## The arithmetic direction

The repository already proves that the cubic logarithmic divisor moment
vanishes for every squarefree label of prime count at least four. The new
finite profile retains its actual endpoint and divides by `(N+1)^2` for
conditioning. Its real and imaginary weighted correlations are therefore
exact null directions even with the original masks, phase and allocation.

Count three is left in the baseline population. It receives no cubic
correction: its third divisor moment need not vanish. Every other count is
joined before any cutoff group is clipped. Early cutoffs remain present.
Neither prime-partner inventory nor an assumed signed sieve estimate is
needed for this finite identity.

## The exact saving, including crossings

Let `T_b` be the full signed baseline contribution of cutoff group `b`,
and `V_b` its null correction. For a step `a`, Lean proves

```text
cost(T+aV) = cost(T) - a*sum_{T_b<0} V_b + crossingCost,

crossingCost = sum_{T_b<0} max(T_b+aV_b,0)
             + sum_{T_b>=0} max(-T_b-aV_b,0).
```

The correlation is signed; it is not a sum of absolute sector debits.
Original zero groups are included in the second sum. If the exact margin
test `|a V_b| <= |T_b|` holds in every group, the crossing cost is zero.
Otherwise its complete value stays in the credit.

After adjoining the cubic direction to the existing complex-null vector,
the credit is `max(oldCost-newCost,0)`. It cannot exceed the same old price.
The terminal theorem applies directly to the literal native carrier:

```text
Re(u^(N_j+1) joinedPhysical_j)
    >= -ComplexNullFloor.nativeCost + nativeCredit - nativeError.
```

The analytic error is exactly the former error. The cofinal hypothesis
`nativeCost-nativeCredit <= 399/5000` is still explicit and unproved.
Moving coefficients incur no new analytic error because the cubic identity
is exact at each finite endpoint. This credit is a reduction of the old
price, not a second use of earlier supply or head credits.

## Global cost geometry

The detector takes complete joined block totals and any exact zero-sum
direction matrix. It performs one joint bounded search, then recomputes
the proposed cost, correlation and every crossing with rational arithmetic.
It also searches each coordinate exactly and reports whether the joint
direction does better than every individual direction. Active-face rank
refers to the correction rows at cost kinks; it is not an arithmetic
orthogonality or positive covariance estimate.

A second certificate gives a lower bound for **all** vectors in the same
box. For `0<=h_b<=1` and `|a_i|<=B`, Lean proves

```text
cost(T+Va) >= -sum_b h_b*T_b - B*sum_i |sum_b h_b*V_bi|.
```

The last term pays every residual dual correlation. A floating optimizer
only proposes vectors; rounded rational primal and dual vectors are
checked independently. Equality of the resulting upper and lower bounds
certifies a finite-input optimum. A nonzero gap is retained as such.

The independent regressions verify 300 exact crossing identities, 22
rationally replayed optimizations, the genuine nonzero count-three cubic
moment, and the paid/incomplete/nonnull input guards. One unit example has
no saving in either coordinate alone but its joint direction reduces cost
from one to zero. Another leaves a certified unmatched cost of one. These
are optimizer and identity regressions, **not unpaid prime-population
measurements**.

No native block records have yet been supplied to the new driver. It skips
paid or unverified scopes before optimization and requires declared complete
groups. Those declarations and the arithmetic provenance of supplied blocks
are not independently validated by the Python program. A sampled cutoff
vector or synthetic null matrix must not be reported as the native cost.
The remaining task is to obtain and bound the complete arithmetic block
totals, or derive a usable analytic credit from them, with all previous
signed unmatched terms and funding retained.
