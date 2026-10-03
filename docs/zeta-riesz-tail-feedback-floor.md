# A signed feedback rule for the whole native floor

The new [Lean module](../RiemannGaussian/ZetaRieszTailFeedbackFloor.lean)
turns complete affine-tail cancellation into an explicit, successive saving
in the **same** whole-floor price. It keeps the original carrier, counts,
phases, factorial allocations, masks and paid owner rows. The independent
cofinal numerical floor remains open.

This continues the [weighted-zero and closed-tail ledger](zeta-riesz-weighted-zero-floor.md).
It introduces no new source carrier or prime-density approximation.

## Read the joined signed aggregate, rather than fit each label

Let `t` be the current native cutoff increment, with all previous nulls
and the independently paid owner increment already included. Let `Z_i`
be complete affine-tail null corrections. Each has **exactly zero** sum
on the original integer cutoff axis, including the finite endpoint.

Write `T_c` and `Z_{i,c}` for complete-period sums. Define

$$
g_i=\sum_{c:T_c<0} Z_{i,c},\qquad
V=\sum_i w_i g_i Z_i,\qquad w_i\ge0.
$$

`adverseCorrelation_feedback_eq` proves the exact signed identity

$$
\sum_{c:T_c<0}V_c=\sum_i w_i g_i^2.
$$

All counts are joined before selecting the adverse periods. The same
rule covers arbitrary prime counts and rough prime sizes; no coefficient
or sign is fitted separately to a count sector.

The canonical choice uses one original label at a time, phase-aligned
**only inside its exact null correction**, with

$$
w_i=\left(\sum_c Z_{i,c}^2\right)^{-1}.
$$

A zero column receives weight zero. `canonicalPrice` therefore needs no
new per-label coefficient input. It computes every new coefficient from
the actual signed period correlations. The original nonzero base carrier
keeps its phase. This conditioning identity is not an energy or norm
estimate on that carrier.

The sum-of-squares identity is a familiar finite Gram calculation. Its
application here, using the literal closed divisor blocks in the current
native signed floor, is the new checked result.

## Pay the changed periods before claiming a gain

For any nonnegative threshold `tau`, retain the exact near-period debit
`D_tau` and the far-period crossing price `H_tau`. They are formed from
the **whole** direction `V`, after summing its columns:

$$
A_\tau=\max\left(\sum_i w_i g_i^2-D_\tau,0\right),\qquad
\lambda=\frac{A_\tau}{2H_\tau},\qquad
G_\tau=\frac{A_\tau^2}{4H_\tau}.
$$

Zero denominators give step/credit zero. The checked inequality is

$$
\operatorname{blockCost}(t+\lambda V)+G_\tau
\le\operatorname{blockCost}(t).
$$

This uses the existing near/far crossing estimate; it never drops a
zero or nearly zero period. `cost_iterate_add_credit_le` sums only the
successive credits, recalculating the full aggregate and its boundary
after every step. Columns may also be remixed at each step.

`nativeColumns_mix` proves that a finite real mixture of these columns
is still a literal closed-tail correction with the original complex
weight. If the mixture annihilates the near rows exactly,
`nearDebit_feedback_zero` proves their entire debit is zero. The next
lemma makes the full squared correlation available as credit. **This
does not assert that a useful cofinal native projection exists.** An
approximate projection must retain its actual residual debit.

Two exact rational regressions illustrate the boundary issue. Joined
feedback on a three-period example, retaining its originally zero
period, earns credit `16/41`. Mixing its columns to cancel that period
first raises the safe credit to `1/2`.

## The native arithmetic inequality

`eventually_joined_floor_with_feedback` proves

$$
\operatorname{Re}\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
\ge -\operatorname{tailCost}_j
      +\operatorname{accumulatedCredit}_j
      -\operatorname{nativePaidBudget}_j
      -\operatorname{nativeError}_j
\quad\text{eventually}.
$$

It needs the existing arithmetic range `1/2<u<=10001/20000`, fixed
`54<=abs(y)`, and nonnegative thresholds. It uses **no zero hypothesis**
to obtain that comparison. The existing exposed-zero hypotheses are
needed to make `nativeError` tend to zero.

The distinct all-prime and paid-owner allocations stay distinct. All
previous nulls, tangent corrections and paid boundaries are retained
and funded once. `feedbackPrice` keeps the entire old `tailPrice` as an
alternative and spends the successive credits only on their own funded
branch. Zero steps recover the previous price exactly.

The canonical version, `eventually_joined_floor_with_canonical_feedback`,
applies the same rule across **every** original native squarefree label.
It leaves no new label coefficient to search for.

`false_of_cofinal_feedback_price` still requires the independent premise

$$
\operatorname{feedbackPrice}_j\le399/5000=0.0798
\quad\text{cofinally}.
$$

That premise is **unproved**. This module does not establish the whole
floor, the multiplicity ceiling, a zero exclusion or an RH contradiction.

## Quantitative tests and their limits

Both optional probes keep the frozen order32/64 factored samples, seeds
317/919, heights54/65/100 and their original importance weights. They
join every count and cutoff period before pricing. They do not run in
ordinary builds or CI.

The [common-rule test](../scripts/probe_riesz_common_tail_rule.py) compares
constant, complex phase and small log-share feature families against
label-specific fits. Every earlier null direction and its coefficient
bound remains available. Training on one seed and replaying on the other
does **not** give uniform improvement. In-sample fitting gains are not
evidence of a common arithmetic coefficient formula.

The [feedback test](../scripts/probe_riesz_tail_feedback.py) uses the
explicit rule above without a new LP or per-label fit. It holds all
earlier null coefficients and the imaginary tilt fixed. After12 steps,
all12 costs decrease. The boundary-paid formula credits account for
about **3.9%–26.1% of those finite starting costs**.

With `--project-near`, the script also tries joint column mixtures that
reduce near-period responses. It charges **all** floating projection
residuals. After12 steps, all12 finite costs decrease; the formula credits
are about **3.9%–43.6% of their finite starting costs**. For example,

| Frozen population | Earlier price | After12 projected steps | Formula credit |
|---|---:|---:|---:|
| N32, seed317, y54 | 0.00817543 | 0.00237202 | 0.00356616 |
| N64, seed919, y65 | 0.02859080 | 0.02330157 | 0.00332452 |
| N64, seed317, y65 | 0.03561158 | 0.03315238 | 0.00140642 |

The longer unprojected128-step scan still improves all12, but some
sequences nearly plateau. A null correction cannot change the full
signed total; every price remains at least its adverse part. At N64,
seed317, y65, that unavoidable finite signed price is about0.02374284.
This is distinct from the excess price caused by local cutoff clipping.

An additional `--unpaid-column-audit` restricts **only the new correction
columns** to largest-prime share `<60069/100000` and second least prime
`>N^3`. These avoid two geometries already covered by eventual owner/cubic
payments. The base sum, its old nulls and every original label/count stay
unchanged. It does not assert those eventual payments at the sample orders,
and is not a complete inventory of all other paid sector masks.

Only `14,11,20,22` closed-tail labels remain in the four frozen populations;
they span counts4–6. All12 finite costs still decrease. Their boundary-paid
formula credits are about **1.8%–14.7% of the same whole finite starting
costs**. Thus the observed gain is not entirely confined to the two
previously covered geometries. The unrestricted4%–44% figures should not
be described as gains on the exclusively unpaid native population.

The generic native theorem already allows this exact restriction of its
column index set while retaining the full base. No arithmetic population
is deleted, completed or positively priced separately.

All of these are **finite, nonnative diagnostics**. Probable primality,
floating phases, period edges, LPs for the earlier seeds and SVD projections
are uncertified, as is the floating owner-share classifier. Neither the
native count crop nor its eventual paid-owner
budget is applied at these sample orders. The formula percentages do not
measure a fraction of the native endgame deficit. No native population
coverage, cofinal rate or numerical bound is proved by the tests.

The next actual estimate must control the remaining native signed
aggregate, or quantitatively control its correlations and crossing price
well enough to bound `feedbackPrice` cofinally. A better finite fit alone
does not close that arithmetic problem.

Validation remains local: warning-as-error Lean/build, the compiled
ordinary root plus the new module, namespace lint and transitive standard
axiom checks. No wider gates, README changes, commit or push are included.
