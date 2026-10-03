# Joint cancellation of the whole-floor crossing charges

The native numerical floor is **open**. This local slice proves a stronger
whole-carrier inequality by joining the existing complex log, log-square
and cubic null corrections before paying their cutoff crossings.
No fixed native saving, cofinal floor, ceiling or zero exclusion is proved.

The latest local pass replaces the quadratic crossing relaxation by the
actual signed crossing cost of the full joint step. Larger-order probes
also test whether the remaining cost is an optimizer artifact; their
exact rational duals cover all six real coefficients on the floating input
matrices. They do not establish a native or asymptotic rate.

Source: [ZetaRieszJointNullCredit.lean](../RiemannGaussian/ZetaRieszJointNullCredit.lean).
Receipts: [joint audit](riesz-joint-null-credit-audit.json).
It uses the [quantitative threshold crossing estimate](zeta-riesz-quantitative-null-step.md),
not a new carrier, prime completion or population mask.

## The combined native inequality

There are six exact null coefficients: real and imaginary coefficients of
the logarithm and squared logarithm, then real and imaginary coefficients
of the cube. The first four act on every original squarefree count-three
label and higher. The two cubic coefficients act only on count four and
higher. Count three is retained in the baseline. Every direction has zero
TOTAL finite sum, with all original cutoff endpoints included.

The old imaginary tilt is fixed. New coefficients incur no new analytic
error because they multiply exact finite nulls, even when the coefficients
move with the order. Lean proves

```text
Re(u^(N_j+1) * joinedPhysical_j)
    >= -ComplexNullFloor.nativeCost_j + nativeJointGain_j
       - ComplexProjection.nativeError_j.
```

The gain uses the actual joined adverse correlation and the full near/far
crossing price of ONE combined direction. It is nonnegative and bounded
above by the SAME native baseline cost. Restricting the six-vector to its
cubic plane recovers the preceding native cubic gain exactly. These are
alternative savings; neither their sum nor a second spend of earlier paid
sectors is licensed.

`false_of_cofinal_joint_gain` connects this inequality directly to the
existing simple-exposed-zero contradiction if

```text
nativeCost_j - nativeJointGain_j <= 399/5000
```

holds cofinally. That premise is still UNPROVED. The underlying source,
count crop, factorial allocation, phase, ownership and physical/radial masks
are unchanged. The larger correction space is not an RH proof.

## Pay the exact joint step

Let `D` be the signed adverse correlation of the whole joint direction and
`X` its exact crossing cost at step one. The new `jointCredit_eq` proves

```text
exactJointCredit = max(D-X,0)
                = max(baselineCost-actualJointCost,0).
```

Every original zero block and every crossed block remains in `X`. There is
no reciprocal-margin or near/far relaxation here. The proposed vector may
move arbitrarily with the order: it is still an exact finite null and the
original imaginary tilt is held fixed.

`thresholdGain_le_jointCredit` proves that this credit covers the preceding
threshold guarantee when evaluated at its SAME rescaled step. These are
alternative prices for one correction, not additive credits. Both are
capped by the original baseline cost.

The compiled `native_floor_with_joint_credit` gives

```text
Re(u^(N_j+1) * joinedPhysical_j)
    >= -ComplexNullFloor.nativeCost_j + nativeJointCredit_j
       - ComplexProjection.nativeError_j.
```

It preserves every original mask and exactly the same analytic error.
`nativeJointCredit_cubic` recovers the previous exact cubic credit.
`false_of_cofinal_joint_credit` connects this stronger inequality to the
existing simple-zero endpoint if its remaining native cost is cofinally
at most `399/5000`. That independent estimate is still OPEN.

The probe reports both absolute fitted profile coordinates and
`jointCorrectionParameters`. Only the latter is the displacement from the
old baseline used by `jointIncrement`: subtract the old four log/log-square
coordinates and keep the two new cubic coordinates. The old imaginary
tilt remains fixed. Confusing these two vectors would misprice the step.

## The exact shared-boundary cancellation

For baseline joined blocks `T_c`, a threshold `tau>=0` and two correction
blocks `V_c,W_c`, let `Z_tau(V)` be the already-proved near-block debit.
Lean proves exactly

```text
Z_tau(V) + Z_tau(W) - Z_tau(V+W)
  = (1/2) * sum_{|T_c|<=tau} (|V_c|+|W_c|-|V_c+W_c|)
  >= 0.
```

The absolute values occur only AFTER all original labels, counts and
cutoff contributions have been assembled into each block. They price a
null correction, not individual arithmetic atoms or the selected Fourier
resonance. The signed adverse correlation is exactly additive.

Opposite corrections on the SAME near-zero period therefore cancel
crossing charges. This can give a positive joint marginal even when each
individual direction has a negative marginal. The preceding single-line
no-improvement theorem remains true: the joined direction has a different,
smaller zero-face debit. This is not a way to omit zero blocks.

## Numerical test and its limits

The optional [probe](../scripts/probe_riesz_quantitative_null_step.py) now
tests the six corrections jointly on complete constructed prime universes.
It preserves the original finite-universe masks, weights and every cutoff
period. The imaginary tilt is held fixed throughout. It then recomputes the
actual cost, threshold guarantee and shared-boundary cancellation.

```bash
../.venv/bin/python scripts/probe_riesz_quantitative_null_step.py \
  --prime-probe --orders 256 640 --seeds 317 919 --heights 54 65 100
```

The twelve exploratory cases all have positive joint guarantees, including
the four cases where the phase-aligned cubic line had none. Their guaranteed
reductions are about 0.6% to 23.8% of their own finite rescaled baseline
costs; the recomputed proposed-step reductions are about 9.2% to 47.9%.
These floating percentages are NOT native bounds or certified credit sizes.

One diagnostic example, `N=256, seed=317, y=100`, has separately priced
signed marginals about `-170.21` and `-12.24`. Cancelling the shared near-block
charge restores about `203.91`, giving a positive joint marginal about
`21.47`. All values are in the common finite amplitude-rescaled units.
The exact cancellation identity is proved in Lean; these particular
arithmetic inputs and their floating values are not certified.

The universes are sparse subpopulations, not the full core or density
samples. Their primes are probable primes, phases/logs are floating,
large cutoff edges use log interpolation, and amplitudes are rescaled.
These early orders retain the original count ceiling `K`, not the eventual
`K/864` crop. No percentage transfers to the current cofinal native cost.
The default 2,000 rational regressions test the crossing inequalities on
unit inputs only; they also verify joint cancellation of a zero-face charge
of exactly two, with no saving in either individual coordinate.

The next mathematical estimate must control the actual joined arithmetic
correlations, shared near-block overlap and far crossing price at cofinal
orders. A constant-factor improvement on a finite population does not
control a growing native cost, and does not beat the previously audited
`(2u)^N` envelope. No such exponential or fixed source-scale bound is
inferred here. Every prior no-go remains in force.

## Rate and all-coefficient audit

The new optional flag runs exact rational primal/dual replay of the joined
matrix, treating each binary floating input as its exact rational value:

```bash
../.venv/bin/python scripts/probe_riesz_quantitative_null_step.py \
  --prime-probe --cost-audit --orders 256 640 1536 --seeds 317 \
  --heights 54 65 100 \
  --output .lake/riesz-joint-null-credit/exact-cost-rate.json
```

An exactly feasible dual `0<=h_c<=1` with
`sum_c h_c V_{i,c}=0` for each of the six columns bounds **every real
coefficient vector**, not just the optimizer proposal or a bounded search.
`signed_cost_lower_of_exact_dual` proves this signed inequality in Lean.
The script solves the small dual system over rational numbers, verifies
these equalities exactly, and recomputes its primal and dual costs exactly.
Its certificate is for those rationalized matrix inputs, not for the
uncertified prime logarithms/phases or for the native population.

All nine audited matrices have such an unrestricted dual. Their relative
primal/dual gaps are at most `8.9e-9`. The following remaining fractions use
the exact matrix dual lower bound divided by the finite baseline cost:

| Order | Height 54 | Height 65 | Height 100 |
|---:|---:|---:|---:|
| 256 | 0.788707 | 0.597429 | 0.886133 |
| 640 | 0.521482 | 0.606492 | 0.525348 |
| 1536 | 0.672367 | 0.529649 | 0.626831 |

Thus the leftover finite cost cannot be removed by searching further in
these six directions. From order 640 to 1536 the relative cost even rises
at two of the three heights. This does **not** rule out a later asymptotic
rate or cancellation with labels absent from these constructed universes.
There is no proved uniform exponential saving here.

At order 1536, exact crossing payment captures about 32.8%, 47.0% and 37.3%
of the finite baseline at those heights, compared with about 11.5%, 21.9%
and 14.7% for its quadratic threshold guarantee. The stronger theorem
retains this actual saving without charging a relaxation gap, but none of
these percentages is a native source-scale budget.

The positive-envelope comparison would require a relative exponential
saving faster than `log(2*radiusCeiling)=log(10001/10000)`, approximately
`9.9995e-5` per order. That is a test of that envelope-based route, not a
necessary condition for the actual floor. These changing finite inventories
and early count ceilings do not certify such a rate. The next advance must
bound the original native signed aggregate, using its arithmetic
correlations rather than claiming that coefficient optimization alone
solves the cofinal problem.
