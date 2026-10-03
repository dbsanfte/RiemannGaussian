# A guaranteed saving in the joined signed floor

The independent numerical floor remains **open**. This local slice proves
a sharper, explicitly priced gain in the original `joinedPhysical`
inequality. It does not prove a fixed size for that gain, an eventual
`-399/5000` floor, a ceiling or a zero exclusion.

Source: [ZetaRieszQuantitativeNullStep.lean](../RiemannGaussian/ZetaRieszQuantitativeNullStep.lean).
The [audit](riesz-quantitative-null-step-audit.json) records focused Lean,
namespace lint and transitive standard-axiom checks. The
[optional probe](../scripts/probe_riesz_quantitative_null_step.py) runs
outside ordinary builds and CI.

## The signed estimate

Let `T_c` be the existing baseline contribution of a COMPLETE cutoff
period, and `V_c` its exact cubic null correction. All counts, labels and
incidences are assembled before these totals are formed. Define

```text
D = sum_{T_c<0} V_c,
Z = sum_{T_c=0} max(-V_c,0),
H = sum_{T_c!=0} V_c^2/(4*|T_c|).
```

Lean proves that every step `a>=0` satisfies

```text
cost(T) - cost(T+aV) >= a*(D-Z) - a^2*H.
```

Thus the mathematically defined step `a=max(D-Z,0)/(2H)` guarantees
`G=max(D-Z,0)^2/(4H)`. Both are defined as zero when `H=0`.
This is a bound on the actual signed cost, not a regression against an
energy proxy. Original zero blocks and every crossed block stay paid.

The existing cubic divisor identity makes the correction an exact null
on all count-four-and-higher squarefree labels. Count three stays in the
baseline. No factorial allocation, physical cutoff, radial window, owner
condition or phase has been changed.

## Paying near-zero margins without reciprocal blowup

The prime-universe probe found that an optimized baseline can have very
small block margins. Using `1/|T_c|` there makes the guarantee practically
zero even when a signed improvement is available.

For ANY nonnegative threshold `tau`, the new theorem instead uses

```text
Z_tau = sum_{|T_c|<=tau}
          (if T_c<0 then max(V_c,0) else max(-V_c,0)),
H_tau = sum_{|T_c|>tau} V_c^2/(4*|T_c|).
```

It proves the same crossing inequality with `Z_tau,H_tau`, giving
`G_tau=max(D-Z_tau,0)^2/(4H_tau)`. The near blocks have their full signed
linear crossing price; they are not omitted or declared negligible.
Threshold zero recovers `G` exactly. The threshold and orientation may be
chosen after joining the whole finite population.

The terminal compiled inequality is

```text
Re(u^(N_j+1) * joinedPhysical_j)
    >= -ComplexNullFloor.nativeCost_j + nativeThresholdGain_j
       - ComplexProjection.nativeError_j.
```

`nativeThresholdGain>=0` and it cannot exceed the SAME old native price.
The analytic error is unchanged. Trying both orientations yields their
maximum; their credits cannot be added. No additional paid sector or
source-scale rate has been assumed.

## Coherent prefixes

Let `M` be the common complex moment of the SAME higher-count population.
The cubic direction with coefficients `(a*Im M,a*Re M)` has increment

```text
a * (Im M * Re C(k) - Re M * Im C(k)) * cubicProfileDifference(k).
```

It vanishes exactly whenever that prefix correlation is collinear with
`M`. In particular cutoff one is killed without charging the size of `M`.
For positive height `y>=54`, every integer cutoff `k>=2` is in a positive
period. Hence the COMPLETE period-zero correction is exactly zero.
This statement is not asserted for negative heights by replacing `y`
with its absolute value.

## What the probe measures

The default command runs 2,000 exact rational crossing/gain regressions,
including zero-price and zero-block cases. An exact tiny-margin example
has thresholded guaranteed gain `1/5`, with its near-margin debit paid;
that identity is also checked in Lean. These are unit inputs, not primes.

```bash
../.venv/bin/python scripts/probe_riesz_quantitative_null_step.py
../.venv/bin/python scripts/probe_riesz_quantitative_null_step.py \
  --prime-probe --orders 256 640 --seeds 317 919 --heights 54 65 100
```

The second command enumerates all selected squarefree labels in two
constructed, disjoint prime universes for each batch. It retains the
literal core masks, source weight and allocation, sums every count and
cutoff period, and holds the baseline imaginary tilt fixed during the new
step. Every distinct absolute block margin is tested as a threshold.
All coherent integer prefixes are killed algebraically, not by a norm.
These small orders are below the eventual `K/864` count-cropping regime;
the probe retains the original count ceiling `K`. It does not test the
current asymptotically cropped native population at those early orders.

For the single phase-aligned cubic direction in twelve cases, the thresholded guarantee ranges from zero
to about 2.1% of the FINITE rescaled baseline cost. Four cases have zero
gain. The test shows why the inverse-margin bound needed sharpening and
why a universal positive gain must not be assumed.
The new [joint-null slice](zeta-riesz-joint-null-credit.md) recombines the
four log/log-square corrections with both cubic corrections; it proves a
stronger native inequality and diagnoses cancellation of their shared
near-period charges. Its finite results also supply no cofinal budget.

These prime universes are a small subpopulation, not the whole core or
a density sample. They use probable-prime tests, floating logs/phases,
amplitude rescaling and log interpolation for large cutoff edges. Their
absolute source scale and arithmetic coverage are not certified. No
native credit magnitude follows from their percentages.

There is also a precise test for an unprofitable direction. Lean proves
`crossingCost>=a*Z` for every `a>=0`. Therefore if `D<=Z`, NO positive step
on that line improves the cost. If the same condition holds for the
opposite direction, no real step on the line helps. This is a statement
about one direction, not an obstruction to the floor itself. Directions
must be joined before computing `Z`: two directions can cancel each
other's zero-block debits even when each line is individually unprofitable.
The exact unit regression exhibits that escape. The finite floating
probe cannot certify that its zero-gain cases meet the exact premise.

The remaining global task is to bound the joined arithmetic correlations
and crossing prices strongly enough that `nativeCost-G_tau<=399/5000`
cofinally. The many-bin, independent-insertion and masked-phase no-go
results all remain in force. This slice has not discharged that estimate.
