# A direct all-count floor without the auxiliary supply debit

This slice applies the existing signed prefix estimate directly to the
original `coreResponse` and then transfers it to the existing
`joinedPhysical`. It introduces no new physical carrier. It preserves every
original count, allocation weight, physical mask and total-label phase.
The independent numerical floor is still open.

## Why use the original sum

The preceding funded comparison retains a fixed positive epsilon and the
relative tail and growing-count debits against a positive supply. Its
remaining signed energy includes that negative funding coefficient.
`ZetaRieszGlobalDebitAudit` already proves that the isolated supply tail
debit is unbounded at source scale. The combined funded carrier may still
cancel it; this is not a proof that its energy diverges.

The direct inequality avoids requiring such a cancellation in an auxiliary
comparison. It retains the signed fixed-count populations and the entire
original high-count tail in the same original core sum. It uses neither
their positive-part credits nor their relative supply allowances. Thus it
spends no credit twice and assumes no new payment of those populations.
It does not claim the direct energy is smaller than the funded energy.

## Checked direct inequality

Let S be the ORIGINAL `coreBand`, X=max(1,sup S), L its exact moving length,
f the existing unit-log-corrected profile and

\[
 w_n=u^{N+1}\operatorname{primeWeight}(A,L,y,N,n,1).
\]

There is no extra population coefficient q, epsilon or supply witness.
Let E_N be `nonOrbitEnergy` with these weights and the original adverse
cutoffs selected ONCE for this full signed sum. All count/count, period/period
and cofactor/cofactor cross terms remain in E_N unless already paid by the
diagonal, large-gcd, near-label or phase-band estimates.

`core_floor` and `joined_floor` prove, for N>=65536, u>0,
u<=10001/20000 and |y|>=3,

\[
 \Re[u^{N+1}\operatorname{joinedPhysical}]
 \ge-\sqrt{(129N/200)\max(E_N,0)}-e_N.
\]

The error is explicit:

\[
 e_N=D_N+G_N+V_N+O_{N,y}
   +\|u^{N+1}(\operatorname{coreResponse}-\operatorname{joinedPhysical})\|.
\]

Here the first four terms are exactly the earlier proved diagonal,
large-common-factor, nearby-label and phase-period geometric prices, all
with B=1. `joinedError_bound` gives the additional bridge bound

\[
 \|u^{N+1}(\operatorname{coreResponse}-\operatorname{joinedPhysical})\|
 \le2(19/20)^N M(1+1/256).
\]

`tendsto_joinedError` proves e_N->0 for fixed height on every cofinal
order schedule, with arbitrary moving original count cutoffs.
`eventually_joined_floor` applies the inequality on the original dyadic
schedule. No exposed-zero assumption is used in either estimate.
The order65536 certifies the profile cap, not an effective start for a
numerical floor or the unevaluated geometric constants.

## The arithmetic gap is unchanged

The independent estimate on this DIRECT E_N is open. The existing
sufficient numerical budget E_N<=3/[320(N+1)] would give a floor
-0.078-o(1), but this slice does not prove that premise. The earlier
funded-energy premise is a different statement: its weights and support
must not be substituted into the direct inequality.

This slice proves a cleaner unconditional signed comparison, not a new
signed-cancellation rate, a percentage of the floor gap, a -0.079 floor,
a restricted contradiction or a zero-free region. The next arithmetic
step must bound the combined actual signed core or its direct remaining
energy; another universal price calibration would not close the gap.

## Quantitative diagnostic and validation

`scripts/probe_riesz_direct_funding_cost.py` evaluates the explicit proved
lower-bound formula for the old isolated debit on the native dyadic orders.
At u=10001/20000 and y=54, the floating formula at order917504 is about
5.72e9 and at order1966080 about4.36e53. These are diagnostic evaluations of
the lower bound, NOT certified actual supplies at those finite orders:
the supply-capacity theorem has an unevaluated eventual threshold.
No signed carrier or energy value is computed. The probe stays outside CI.

Focused Lean, root import, namespace linters, all-public transitive axioms,
source hashes and preservation checks are recorded in
`riesz-direct-phase-floor-audit.json`. All prior no-go and payment theorems
remain unchanged. README and publication endpoints remain unchanged.
