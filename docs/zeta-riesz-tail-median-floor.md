# Resolve the signed crossing price on the same whole floor

[ZetaRieszTailMedianFloor](../RiemannGaussian/ZetaRieszTailMedianFloor.lean)
proves a stronger arithmetic floor for the existing `joinedPhysical`
carrier. It joins every count and complete cutoff period, forms the
existing literal null-feedback direction, and resolves its sign crossings
exactly. It does not prove the remaining cofinal numerical floor.

This continues the [whole signed feedback ledger](zeta-riesz-tail-feedback-floor.md).
No source carrier, arithmetic completion, support deletion, factorial
allocation restriction, prime-density transport or new phase is introduced.

## One rule for every count and period

Let `T_c` be the whole current signed period increment and `V_c` the
whole null-feedback direction, with `sum_c V_c=0`. For `V_c != 0`, put

$$
x_c=-T_c/V_c,\qquad w_c=|V_c|.
$$

For `V_c=0`, the weight is zero. An originally zero period with nonzero
direction has crossing root zero and retains its full weight. Its debit
is not ignored.

The exact existing `blockCost_eq` identity gives

$$
\operatorname{blockCost}(T+aV)
=\frac12\left(\sum_c |T_c+aV_c|-\sum_c T_c\right).
$$

Its variable part is the **joined** weighted displacement
`sum_c w_c * abs(a-x_c)`. A weighted median minimizes this over every
real `a`. `exists_weightedMedian` proves the finite median exists, even
with coincident roots or zero weights. `medianAdjusted_minimizes` applies
the resulting minimization to the original complete-period price.

This standard median principle applies simultaneously across all
counts, labels and periods. It chooses one step on the already assembled
direction; it fits no new per-label coefficient. The theorem optimizes
one line, **not** the whole space of null corrections or the actual
arithmetic remainder.

## Retain the actual signed saving

`medianCredit_eq_crossing` proves

$$
G=a_{\rm med}\,\operatorname{adverseCorrelation}(T,V)
-\operatorname{crossingCost}(T,V,a_{\rm med}).
$$

Every crossing is retained. `medianCredit_ge_feedbackCredit` proves
this actual rebate is at least every previously paid quadratic threshold
rebate **on the same current aggregate and direction**. There is no
native correlation-size assumption.

Two exact rational regressions are checked in Lean:

| Whole signed example | Previous guaranteed rebate | Exact median rebate |
| --- | ---: | ---: |
| `T=(-1,0,1)`, `V=(5,-1,-4)` | `16/41` | `4/5` |
| `T=(-1,0,1)`, joined `V=(3,0,-3)` | `1/2` | `1` |

`cost_medianIterate_add_credit_eq` telescopes only successive actual
rebates, repricing the changed aggregate each time. The original signed
sum is unchanged. `medianAccumulated_le_excess` also proves the limit of
this strategy: null corrections cannot remove the adverse part of that
unchanged total. Better step pricing alone is no proof of its arithmetic
size.

## The native signed inequality

`eventually_joined_floor_with_median` proves, on the same original native
dyadic sequence,

$$
\operatorname{Re}(u^{N_j+1}\operatorname{joinedPhysical}_j)
\ge -\operatorname{tailCost}_j+G_j
-\operatorname{nativePaidBudget}_j-\operatorname{nativeError}_j.
$$

Here `G_j` is the exact successive median rebate. The arithmetic
comparison uses `1/2<u<=10001/20000`, fixed `54<=abs(y)` and the actual
literal null identities; it needs no hypothetical zero. The known
exposed-zero hypotheses still make `nativeError` tend to zero.

The original full base, all masks, phases, factorial orders, previous
nulls, tangent direction and distinct paid owner rows remain. The same
owner budget and error are charged once. `medianPrice` retains the entire
previous `feedbackPrice` as a separate alternative; it never adds the
credits from different trajectories. Successive median and quadratic
trajectories are not asserted to dominate each other.

`eventually_joined_floor_with_canonical_median` uses the existing canonical
phase-aligned null column for **every** original native squarefree label,
with its existing inverse squared-period-norm weight. The original
nonzero arithmetic carrier retains its phase throughout.

The outstanding numerical arithmetic theorem is still

$$
\operatorname{canonicalMedianPrice}_j\le399/5000=0.0798
\quad\text{cofinally}.
$$

It is **unproved**. No whole numerical floor, multiplicity ceiling,
restricted zero exclusion or RH contradiction follows from this slice.

## Optional quantitative diagnostics

[probe_riesz_tail_median.py](../scripts/probe_riesz_tail_median.py) reads
only hash-verified frozen order32/64 importance-weighted samples, seeds
317/919 and heights54/65/100. It preserves the full base and all earlier
null coefficients and the imaginary tilt. It uses no new LP or per-label
fit. Every near/zero-row change, including floating SVD residuals, is
included in the full actual cost. These floating calculations are **not**
interval or Lean certificates.

After12 steps with joint near-row mixtures, all12 finite prices decrease;
their actual rebates are about **7.0%–72.4%** of the finite starting costs.
The extra correction-column audit retains only owner share `<60069/100000`
and second least prime `>N^3`, keeping the full base unchanged. All12
prices still decrease, by about **3.6%–31.8%**. These audited columns
remain only14/11/20/22 labels spanning counts4–6. The audit avoids two
known paid geometries; it is **not** a complete unpaid-mask inventory.
Other fixed-count supply ledgers are alternatives, not extra free credits.

A64-step scan still nearly plateaus in some cases. For example, order64,
seed317, height65 changes from about0.035612 to0.033115, while its unchanged
adverse signed total is about0.023743. Exact step resolution therefore
does not itself remove the remaining signed obstruction.

None of these sample orders is a native cofinal point. No eventual native
count crop, paid-owner budget or supply witness is applied to them. Prime
tests, phases, period edges and SVDs are uncertified. The percentages
measure neither native population coverage nor a fraction of the endgame
deficit. They provide no cofinal saving or price bound.

Validation is local: strict scoped Lean/build, the compiled ordinary root
plus the explicit new module, all namespace linters and standard transitive
axioms. The [scoped audit](riesz-tail-median-floor-audit.json) records source
and artifact hashes. No wider gates, README/explorer changes, commit or
push are included.
