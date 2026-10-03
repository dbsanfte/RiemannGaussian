# Joint quadratic transport of the retained prime correction

Local continuation from `194a361762f404a8f4473298b25d96fbae0bb56e`.
The independent cofinal floor remains open. This slice proves a direct
signed improvement of its current cost, with the arithmetic size of the
credit left explicit. No zero exclusion is claimed.

The checked leaf is
[`ZetaRieszPrimeHeadTransport.lean`](../RiemannGaussian/ZetaRieszPrimeHeadTransport.lean).
The focused audit is [`riesz-prime-head-transport-audit.json`](riesz-prime-head-transport-audit.json).

## Preserve the correction; change its cutoff placement exactly

Let $h_{p,q}$ denote `pairAmount`: the original source-normalized
ordinary-prime head atom. It retains the owner window, full original
39N/20..203N/100 cofactor window, phase, smooth owner allocation and sieve.
The independently paid contraction of the main window does not contract
the head. `nativeHead_eq_sum_pairAmount` joins every such pair.

For distinct primes define the actual divisor prefix

$$
\phi_{pq}(k)=1_{1\le k}-1_{p\le k}-1_{q\le k}+1_{pq\le k}
 =\sum_{d\mid pq,\ d\le k}\mu(d).
$$

`pair_cofactor_lt_owner` proves the original native pairs have $q<p$
for $N\ge64$. `native_pairOrbit_eq_divisors` therefore applies to the
literal head pairs, without averaging pair incidences.

The exact quadratic step has the signed total

$$
\sum_{k=1}^{X}\phi_{pq}(k)
 \frac{(\log k)^2-(\log(k+1))^2}{N+1}
 =\frac{2\log p\log q}{N+1},\qquad pq\le X.
$$

The terminal boundary cancels between all four divisor incidences; it
is not assumed zero. Consequently `pairIncrement` transports $h_{p,q}$
using this profile and has total exactly $h_{p,q}$.
`sum_quadraticHead` preserves the entire original signed head. The head is
not a vanishing marked two-prime weight.

The old and transported increments differ by `direction`, whose total is
zero. The common endpoint includes every actual pair product. Beyond the
old endpoint, the old main/head increments are exactly zero;
`blockCost_joinedIncrement` proves enlarging that endpoint does not change
the old central cost.

## Spend a joint signed credit in the whole floor

Let $T$ be the current complete-period increments of the central main
minus the same head, including all old native free logarithmic and tangent
profiles. Counts and divisor crossings are joined before clipping.

The crossing-square step gives `gain`, taking the better of both signed
orientations and retaining the exact zero-face debit. The theorem
`central_floor_with_gain` spends that nonnegative credit in the actual
central-minus-head lower bound. No small bound on its denominator or
positive native correlation is assumed.

The stronger finite-step update moves the head together with the existing
free main profiles. For old parameters $p$, new global parameters $r$
and one global head coefficient $b$, define

$$
v=T_r-T_p+b\,\mathrm{direction}.
$$

Its total is exactly zero (`sum_coupledDirection`). Write $B_c$ and $V_c$
for the whole period totals of $T_p$ and $v$. The exact crossing credit is

$$
C=\sum_{B_c<0}V_c,\qquad
X=\sum_c\begin{cases}
 \max(B_c+V_c,0),&B_c<0,\\
 \max(-B_c-V_c,0),&B_c\ge0,
\end{cases}
\qquad G=\max(C-X,0).
$$

All original zero periods are included in the second case. No inverse
small-margin estimate substitutes for $X$.
`coupledCredit_eq_cost_saving` identifies $G$ exactly with the positive
decrease in the whole period cost. `central_floor_with_coupled_credit`
then proves, independently of any zeta-zero hypothesis,

$$
\operatorname{Re}S_j-H_j\ge-\operatorname{cost}$T_p$+G.
$$

`eventually_joined_floor_coupled` spends this inequality in the current
`joinedPhysical` floor, retaining the same high-owner, allocation, radial
and native-error budgets once. The arithmetic target remains the cofinal
bound on **cost minus the joint credit**, not a separate norm of the head.
The credit's required native size is not proved by this slice.

## Optional numerical evidence and its limits

`scripts/probe_riesz_joint_head_transport.py` is outside builds and CI.
It exhausts small toy squarefree labels at $N=6,7$, heights 54,65,100,
and both the original and contracted radial windows. The toy length is

$$
L=-2N\log u,
$$

not the native moving integer length or native dyadic schedule. The full
native deletion masks are not modeled, and no eventual budget is applied
at these orders. Every tested main retains all its counts together; the
same full prime head is retained in both windows.

The quadratic direction, optimized jointly with the original four free
profiles using one coefficient per direction, reduces the finite cost in
all eleven tests with a numerically nonzero baseline. Savings range from
about 0.1% to 48.1%; the uncontracted $N=7,y=65$ case saves about 30.4%.
These are percentages of finite toy costs, not of the global floor deficit.
An already-zero baseline is preserved instead of reporting roundoff as a
relative saving. The probe checks the exact signed correlation-minus-
crossing identity in floating arithmetic, not by interval certification.

The probe also evaluates the mathematically defined crossing-square step.
The joined log-minus-hinge increment is computed using its exact
piecewise formula, so the analytically zero region below $L$ is not
polluted by subtractive roundoff. Near-zero optimized blocks are not
rounded away. The direct finite-step identity avoids the inverse-margin
cost of those blocks. Total-label and two-direction alternatives in the
probe are exploratory; only the quadratic transport is formalized here.

Strict leaf validation, the targeted leaf build, all namespace linters
and the all-declaration standard-axiom audit are recorded in the focused
report. Older proofs, audit snapshots, compiled ordinary root, public
endpoints and concurrent semiprime work remain unchanged. No root
registration, wider gate, commit or push is performed.
