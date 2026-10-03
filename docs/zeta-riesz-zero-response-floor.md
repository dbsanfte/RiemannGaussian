# Rebalance exact zero responses inside the whole floor

The current native cutoff cost can charge intermediate divisor responses
of labels whose **complete signed Riesz coefficient is zero**. This slice
uses an exact arithmetic gap test to identify such labels at every count,
then joins their zero-total increment with the existing whole-floor
corrections. Their coefficient may vary with order and have either sign.
There is no new source error or funding cost for this direction.

The module is
[ZetaRieszZeroResponseFloor](../RiemannGaussian/ZetaRieszZeroResponseFloor.lean).
The whole numerical floor remains open. The checked result is a direct
lower inequality for the same `joinedPhysical`, with an additional exact
signed direction in its price. No alternate carrier is introduced.

## A finite integer certificate for the zero coefficient

For a squarefree original label `n`, take a squarefree block `R | n` with
at least two prime factors. At the integer physical cutoff `X`, the test
`IntegerGap X n R` requires

$$
\forall d\mid n/R,\qquad X\le d\quad\text{or}\quad dR\le X.
$$

Every complete divisor block is then on an affine side of the hinge.
`riesz_zero_of_integerGap` invokes the existing all-rank signed block
identity from `ZetaRieszSmallCofactorCancellation` and proves

$$
\mathcal R_{\log X}(n)=0.
$$

This is not a new proof of the underlying gap cancellation. The new use
is to remove its artificial intermediate variation from the **current
native whole-floor price**. Integer comparisons supply the gap; a tiny
floating Riesz value is never used to classify a label as zero.

`physicalCutoff` is exactly
`(linearDampedCutoff u N_j + 2)^2`, and
`length_eq_log_physicalCutoff` checks its equality with the original
moving length. `zeroLabels` applies the test to the canonical two least
primes of each current native label. Their sizes have no polynomial cap.
The original core, near-critical count crop, squarefree and physical
predicates remain. The original factorial orders and full complex phase
are untouched.

## Why deletion alone is the wrong rule

A zero total does not imply small cutoff-period variation. Nor does its
removal always lower a price that already contains other null corrections.
The zero labels can help cancel those other corrections inside individual
periods.

`zeroIncrement` keeps the original all-prime allocation and bounded
imaginary tilt. `zeroLabels_complexPrefix` and `sum_zeroIncrement` prove
its complete complex response and real signed increment total are exactly
zero. Therefore a moving real coefficient `r_j` is allowed without any
growth condition:

$$
\sum_k r_j Z_j(k)=0.
$$

`zeroIncrement_zero_early` also proves that this direction vanishes before
the moving hinge. It introduces no early-cutoff debit. Coefficient one
deletes the zero-label base increment, coefficient zero retains it, and a
negative coefficient amplifies it. Every choice leaves the signed total
unchanged. The previous log, log-square, cubic and tangent directions are
joined with this one before the complete-period price is measured.

## The checked whole-floor inequality

Write `T_j` for the existing native increment with its chosen joint
corrections, `V_j` for the independently paid cubic-row increment, and
`Z_j` for the exact zero-response increment. Define

$$
D_j(r_j)=\operatorname{blockCost}(T_j-V_j-r_jZ_j).
$$

The signed paid-row budget `E_j = nativePaidBudget y j` is unchanged.
The owner allocation in `V_j` and the all-prime allocation in `T_j,Z_j`
remain distinct, exactly as in the previous paid-incidence ledger.
`eventually_joined_floor_zeroCleared` proves

$$
\operatorname{Re}\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
\ge -D_j(r_j)-E_j-\operatorname{nativeError}_j
\quad\text{eventually}.
$$

No zero hypothesis enters this arithmetic inequality. The range remains
`1/2 < u <= 10001/20000`, with fixed `|y| >= 54`. The previous count-crop,
endpoint and signed-row payments are charged once. Under the existing
exposed-zero hypotheses the reused `nativeError` tends to zero.

The alternative `zeroClearedPrice` keeps the old complete credited price:

$$
\mathcal D_j(r_j)=\min\left(
 \operatorname{nativePrunedPrice}_j,
 D_j(r_j)+E_j\right).
$$

`eventually_joined_floor_with_zero_response_credit` gives the same floor
with `-mathcal D_j-nativeError_j`. `zeroClearedPrice_zero` recovers the
previous price exactly, and `zeroClearedGain_nonneg` prevents a worse
floor. This is one price comparison, not two separately spendable credits.

`zeroCleared_saving_eq` measures the uncharged saving exactly:

$$
\operatorname{nativePrunedCost}_j-D_j(r_j)
=\frac12\left(
 \sum_c|\operatorname{blockTotal}_c(T_j-V_j)|
 -\sum_c|\operatorname{blockTotal}_c(T_j-V_j-r_jZ_j)|\right).
$$

These absolute values are taken only after every original count and signed
cutoff increment has been joined into a complete period. No individual
prime, divisor or count is assigned a positive main-term allowance.

The terminal `false_of_cofinal_zeroCleared_price` still requires the
independent numerical premise

$$
\mathcal D_j(r_j)\le 399/5000=0.0798\quad\text{cofinally}.
$$

That premise is unproved. Neither the floor, the ceiling, nor a zero
exclusion follows from this slice.

## Quantitative probe: preserve the helpful zero contributions

The optional [probe](../scripts/probe_riesz_zero_response_floor.py) reuses
the frozen factored-integer samples at orders `32,64`, seeds `317,919`,
and heights `54,65,100`. It retains the existing sampling importance
weights, original masks, allocation and phases. The exact integer test
identifies respectively `18,31,56,40` zero-response labels among
`145,126,170,157` selected labels.

Three comparisons are kept separate:

1. Before the earlier null credits, deleting the zero labels lowers the
   raw price in 11 of 12 cases. It raises it in one, so monotonicity fails.
2. With the earlier complex/cubic null fit held fixed, forced deletion
   raises the price in **all 12 cases**. It adds no funded saving. This
   rules out interpreting the raw improvements as additional credit.
3. Joining the new signed direction with all earlier null corrections,
   while keeping the imaginary tilt fixed, produces a further feasible
   numerical reduction in all 12 cases. For example at `N=64`, seed317,
   height54, the price changes from approximately `0.007343` to `0.006705`;
   fixed deletion instead costs about `0.012180`.

The last comparison is a floating finite-sample diagnostic, not a native
credit magnitude, rigorous upper bound, asymptotic saving or fraction of
the global deficit. These orders are not points of the cofinal native
schedule and do not use its count crop. Probable-prime decisions, sampling
weights, floating phases, large-edge interpolation and LP coefficients
are not certified. The exact gap test certifies only its integer
inequalities; the Lean theorem supplies their algebraic implication under
squarefreeness. The signed ledgers and variation identity are checked
numerically, without using underflow as cancellation.

The result suggests a concrete direction: preserve the useful zero-label
increments and rebalance them jointly. It does not supply the missing
cofinal price estimate. Rougher active crossings and all nonzero response
geometries still carry the arithmetic difficulty.

Validation is local: focused warning-as-error Lean/build, ordinary compiled
root plus explicit new module, namespace lint and transitive axiom audit.
No commit, push, full-root rebuild, wider CI, README or public endpoint
change is included. The probe stays outside ordinary builds and CI.
