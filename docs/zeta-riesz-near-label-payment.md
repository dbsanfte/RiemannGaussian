# Nearby actual-label correlations in the whole floor

This local slice continues the many-bin energy investigation on the exact
funded carrier. It pays another entire cross-correlation family; it does
not prove that bin occupancy forces cancellation, pay a whole label
population, or establish the numerical floor.

The original adverse cutoff selection, phase, allocation and funding
overlaps are retained. The previous large-gcd payment is not repeated.
Within its remaining smaller-gcd cross sum, split by

\[
 n\ne m,\qquad |n-m|\le e^{-N/1000}\min(n,m).
\]

`nearEnergy` contains these nearby pairs. `separatedEnergy` contains the
rest. `smallSharedEnergy_eq` is an exact partition using the SAME original
adverse cutoffs. Removing a negative paid family can increase a finite
remaining cost; no monotonic cost improvement is claimed.

## Literal capacity, rather than bin orthogonality

For every finite set of actual integer labels, a label n has at most
2 epsilon n distinct neighbours at relative distance epsilon.
`nearPair_card_le` proves this by a finite integer interval, excluding n.
No short-interval prime count is assumed.

`symmetric_pair_capacity` is a general finite symmetric-incidence bound:

\[
 \sum_{n,m:E(n,m)}a_na_m\le\sum_n\deg_E(n)a_n^2.
\]

Apply it to the actual reciprocal divisor weights. Writing
sigma=1+1/262144 and
M(sigma)=sum_n tau(n)^2 n^{-sigma}, the checked bound is

\[
 \sum_{n,m:\mathrm{near}}\frac{\tau(n)\tau(m)}{nm}
 \le 2\epsilon\,e^{\log X/262144}M(\sigma).
\]

M(sigma) is convergent by the existing divisor-square Dirichlet machinery.
This uses actual integer capacity and reciprocal weights; it applies to
all counts, all scale bins, and reinforcing as well as cancelling phases.

## Source-scale saving and the native ledger

For the original weights
w_n=u^{N+1}q_n primeWeight(A,L,y,N,n,1), with |q_n|<=B,
L>=1, u<=10001/20000 and log X<=3(N+1),
`weighted_nearEnergy_bound` proves

\[
 |\mathrm{nearEnergy}|\le
 K_B(N+1)^3 e^{-N/2000},\qquad
 K_B=32u_{\max}^2B^2M(\sigma)e^{3/262144}.
\]

The rate includes squared source growth (2u)^{2(N+1)}. It is not merely
an unnormalized pair-count discount. The resulting corrected-profile
price is

\[
 \mathrm{nearPrice}(B,N)=\sqrt{4K_B}(N+1)^2e^{-N/4000}\longrightarrow0.
\]

`eventually_joined_separated_floor` applies this once to the native
whole-floor ledger. The earlier diagonal/shared-factor errors remain.
The exact original unpaid, paid, radial-tail and supply sets, all their
funding overlaps, positive supply witness, debit
tailCost+epsilon+growingDebit and original physical/count support remain.
No exposed-zero or unproved arithmetic hypothesis is used in the payment.

The arithmetic target left OPEN is

\[
 \sqrt{\max(\mathrm{separatedEnergy},0)
              \,\mathrm{adverseProfileEnergy}}
 \le 79/1000+o(1).
\]

The remaining pairs have log(gcd(n,m))<=N/1000 and
|log n-log m|>exp(-N/1000)/2 (`separated_log_gap`). This frequency gap
DECREASES with N. It does not provide fixed-height orthogonality or a
large-sieve saving by itself. Many-bin occupancy does not replace a
quantitative estimate of this complete signed aggregate.

The older explicit positive supply credit cannot simply be added here:
the whole fixed-count sum already contains the same four-prime supply.
`rejoined_supply_sum` keeps that credit exactly once. A small relative
supply debit is not automatically source-o(1).

## Optional diagnostic and checks

`scripts/probe_riesz_near_label_energy.py` is outside ordinary CI/builds.
It computes complete actual finite Gram pairs at orders4/5 and heights
54/65/100, tests the capacity inequalities and exact signed partition,
and keeps the adverse selection unchanged. At these tiny orders the
literal exponential cutoff contains every smaller-gcd pair; this is NOT
cofinal evidence. A separate rational relative cutoff1/1000 is diagnostic
only and finds both signs in the separated aggregate. The tests use
L=11N/8 and exactly empty allocation support. Native dyadic, physical,
count56+ many-bin and supply-witness hypotheses are not certified; floats
are not interval certificates.

The fixed constants are not evaluated, and no effective starting order
is claimed. Focused Lean, root-import, namespace-lint and all-public-axiom
checks are recorded in `riesz-near-label-payment-audit.json`.
The independent floor, ceiling and restricted contradiction remain OPEN.
