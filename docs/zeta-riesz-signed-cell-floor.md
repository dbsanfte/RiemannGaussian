# Balanced cell cancellation and the retained cross-period imbalance

The independent `-79/1000-o(1)` floor is **open**. Many occupied prime-log
bins do not by themselves force distinct owner-period phases, weighted
dispersion or negative covariance. The earlier phase, correlation and rate
audits remain in force. This slice instead pays the balanced part of actual
inner-hinge cells, with no matching-existence or coverage assumption.

Proof: [ZetaRieszSignedCellFloor.lean](../RiemannGaussian/ZetaRieszSignedCellFloor.lean).
Focused checks: [proof audit](riesz-signed-cell-floor-audit.json).

## An actual signed estimate, without partner capacity

Let `F_N(n)` be the original fully allocated atom and `O_N(n)` its actual
unique-owner atom. Choose a subset `D` of the original support and a
reference `c(n)` in the same selected subset. Every label and its reference
must have the same **actual canonical owner** and second prime, and satisfy
the literal composite `InnerHinge` conditions. All physical, squarefree,
coprimality, original radial/count and allocation masks remain. No artificial
prime incidence is added and no cofactor is completed.

Write `b(n)` for the actual remaining composite cofactor. For
`abs(log n - log c(n)) <= exp(-N/1000)`, Lean proves

```
norm(u^(N+1) * [sum_D F_N(n)
 - sum_D mu(b(n))*mu(b(c(n)))*O_N(c(n))]) <= matchingBudget(N,y),

matchingBudget(N,y)
 = [168*radiusCeiling*(1+abs(y)) + 2*radiusCeiling*M(1+1/262144)]
     *(N+1)^3*exp(-N/1250) + ownerPaymentError(N) -> 0.
```

`global_owner_reference_error` pays the entire cell variation at source
scale; `original_cell_error` also includes the previous nonowner payment
once. Both are unconditional finite arithmetic estimates under the literal
support and gap conditions. The constants do not depend on prime count or
the number of occupied bins. A reference can be reused: its repeated norm
is never multiplied by cell cardinality in the error bound.

`logCell(N,n)=floor(log(n)/exp(-N/1000))` provides the actual geometric gap
for equal cells, proved in `same_logCell_gap`. This is a partition of existing
integer labels. It assumes no distribution or prime count inside a thin
interval, and it is not continuum transport or phase freezing.

## Keep every imbalance and radial period signed

After all cofactor counts have been joined, `sum_cofactor_cells` gives

```
sum_D mu(b(n))*mu(b(c(n)))*O_N(c(n))
 = sum_{i in image(c,D)}
      [sum_{n in D, c(n)=i} mu(b(n))] * mu(b(i))*O_N(i).
```

No absolute value or positive part is applied to the bracket or to an
individual period. A cell with actual imbalance zero contributes zero
reference channel (`reference_zero_of_cell_balance`). The nonzero
imbalances retain their reference phase and exact original owner allocation.
There is no assertion that those imbalances are small or favorable.

`floor_after_cells` plugs this inequality into the existing whole floor.
The original sum over `R\D`, this signed cell aggregate and the **same**
original supply debit remain joined. The geometric budget is subtracted
once. Neither matching capacity nor a new bilinear-cancellation hypothesis
is assumed. This pays balanced variation, not the unbounded signed main;
there is no new whole-population payment, numerical floor or zero exclusion.

## Complete-period numerical audit

The optional [probe](../scripts/probe_riesz_joined_period_cells.py) factors
every integer cofactor in its tested intervals. It retains all squarefree
composite cofactors, every observed count, the rounded moving Riesz length,
full original allocation, literal inner-hinge geometry and actual complex
product phase. Consecutive **complete total-log phase periods** are summed
before any magnitude is taken.

At order 80, the full integer interval contains 760,114 selected labels.
The joined energy divided by the sum of the individual period energies is

| Height | Complete periods | Joint/diagonal energy |
| ---: | ---: | ---: |
| 54 | 4 | 3.0521 |
| 65 | 5 | 3.9373 |
| 100 | 9 | 4.7809 |

Thus these actual finite cells exhibit substantial cancellation within a
period but **reinforcing** cross-period covariance. At order 64, one tested
height has negative covariance, while the other two have positive covariance.
The numerical result does not support automatic period orthogonality.

These examples have no cofactor prime above `binHead=5000`, fail the native
eventual length lower bound, and do not instantiate the unpaid count-56+
many-bin support, original dyadic schedule or funding witness. They are
finite diagnostics, not native many-bin counterexamples or asymptotic
certificates. Large fixed prime tests are probable-prime tests; floating
weights are not interval or Lean certificates. The probe is outside ordinary CI.

## Relevant literature and the actual rate gap

The [Matomäki–Radziwiłł paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf)
uses prime-factor ranges in mean-square estimates. Its frequency/interval
averaging cannot be substituted for the present fixed-height masked sum.
[Menon's 2026 refinement, Theorem 1.1 and Section 1.1](https://arxiv.org/html/2607.15574v1)
improves the short-interval mean square to logarithmic rates and treats
exceptional frequencies separately. Inserting `X=exp(c*N)` and
`h=X^theta` in its displayed bound gives logarithmic-over-polynomial rates
in `N`, not a fixed exponential saving. It does not discharge this carrier's
fixed-height, moving-order, nonmultiplicative mask obligations.

These are applicability observations, not formalized arithmetic inputs.
The existing rate audit proves even `exp(-C*log(N)^2)` cannot pay the old
positive `(2u)^N` envelope for fixed `u>1/2`. This is a limitation of that
envelope, not a no-go for the actual signed sum or for a one-sided floor.

## Remaining target

Control the **signed cell imbalances across all counts and radial periods,
jointly with the original supply debit**, plus the untouched non-inner-hinge
labels. Occupancy does not supply that covariance estimate. Balanced cell
variation is now paid without constructing a matching, but the independent
whole floor and RH contradiction remain open.
