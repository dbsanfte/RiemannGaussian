# Stronger signed estimates for the same whole sum

The joint lower and upper comparisons now retain **47/8 of the central
credit**, after the unchanged positive-five and all-count owner payments.
The preceding comparisons retained 3/8. Every paid population, favorable
signed observation, and exact complementary sum is unchanged.

This is a proved improvement to the actual whole `J+C` comparisons. The
independent numerical floor `-79/1000-o(1)` and ceiling `3/2+o(1)` remain
open. There is no new zero exclusion.

## Recovering lost phase and radial margin

Write `g` for the number of mesh subdivisions; it is unrelated to zero
multiplicity. On the original grid of `8g` phase cells, the full triangular
minorant of cosine gives

```math
\sum_{i=0}^{8g-1}\max(0,\cos\theta_i)\ge2g,
\qquad
\sum_{i=0}^{8g-1}\max(0,-\cos\theta_i)\ge2g.
```

The old bound certified only `g`. No phase cell is removed. The proof pairs
the increasing and decreasing halves of the triangle and keeps the other
nonnegative terms.

The actual cell width satisfies `h<=1/100000`. For the original radial
factor `V(t)=exp(-t/2)t^N/N!`, the favorable and adverse cell factors obey

```math
\frac{99999}{100000}V(t)
\le\frac{e^{-(t+h)/2}t^N}{N!},
\qquad
\frac{e^{-t/2}(t+h)^N}{N!}
\le\frac{50001}{50000}V(t).
```

The respective old constants were `99/100` and `1001/1000`. We retain the
proved period-wide comparison `V0<=V(t)<=501V0/500`, the original phase
error `|y|h<=1/10000`, and the already certified angular credit/debit
`1309/10000` and `1261/10000`. Exact rational arithmetic then proves a
central period margin of `g*V0*h/125`, replacing `g*V0*h/500`.

All these statements are in
[ZetaRieszCentralSharpBudget.lean](../RiemannGaussian/ZetaRieszCentralSharpBudget.lean),
particularly `sum_positive_cos_lower`, `sum_negative_cos_lower`,
`original_central_period_budget_with_radial`, and its upper counterpart.
No numerical integration or new prime-count assertion enters this gain.

## Applying the gain to the actual joint sum

Use the previous central population `P`, the paid positive-five population
`B` selected from `S\P`, and the all-count owner population `D` selected
from `S\(P union B)`. Let `b,d` denote their literal complex sums and `R`
the exact remaining sum. The fixed positive-five cost is still
`g*V0*h/1000`, leaving `7g*V0*h/1000`. The unchanged radial witness pays six
copies of

```math
G_N=\frac{\pi u e^{-1}}{24000|y|}\frac{(2u)^N}{N+1}.
```

The owner population still costs at most `G_N/8` eventually. Consequently
the optional cached application proves

```math
\begin{gathered}
u^{N+1}\bigl(\operatorname{Re}R+
 \max(\operatorname{Re}b,0)+\max(\operatorname{Re}d,0)\bigr)
 +\frac{47}{8}G_N-e_j
 \le\operatorname{Re}\bigl(u^{N+1}(J+C)\bigr),\\
\operatorname{Re}\bigl(u^{N+1}(J+C)\bigr)
 \le u^{N+1}\bigl(\operatorname{Re}R+
 \min(\operatorname{Re}b,0)+\min(\operatorname{Re}d,0)\bigr)
 -\frac{47}{8}G_N+e_j,\qquad e_j\longrightarrow0.
\end{gathered}
```

The lower and upper comparisons have their respective original populations
and rests: they are **alternative budgets**, not supplies to add together.
They hold on the unchanged dyadic orders for `1/2<u<=10001/20000` and fixed
`|y|>=54`, without a zero hypothesis. The starting order is existential.

The terminal theorems are
`RieszCentralCapacityTransfer.eventually_joint_sharp_owner_floor` and
`RieszCentralCapacityTransfer.eventually_joint_sharp_owner_ceiling` in
[the cached application](../scripts/CheckRieszCentralCapacityTransfer.lean).
[The audit](riesz-central-capacity-audit.json) records the source hashes,
standard-axiom checks, and lint results. Exhaustive covers remain optional
and were not rerun.

Relative to the preceding comparisons the improvement is `11G_N/2` in
each direction, on the same signed rest. `G_N` grows for `u>1/2`; it is not
a vanishing error or an independently proved numerical bound on the whole
sum. The unresolved rest still includes smaller-owner labels, other radial
periods, and unselected prime-count/sign sectors. The next arithmetic task
is to pay the remaining positive-five population from this larger budget
without reusing any already spent credit.

The subsequent [small-prime boundary payment](zeta-riesz-positive-five-boundary.md)
now removes that boundary from the positive-five rest in the selected
period, preserving the same `47G_N/8` margin. The interior is still unpaid.
