# Combine prime periods before the cutoff energy

Lean now bounds the original retained carrier over a separated family of
complete prime periods **before** taking the quadratic mean. The new cost
uses one maximum partial-tail amplitude across the family. The original
factorial allocation, every order, both Riesz hinges and the full correlated
cofactor phase remain literal.

Source: [`ZetaRieszJointPeriodEnergy.lean`](../RiemannGaussian/ZetaRieszJointPeriodEnergy.lean).
The [audit](riesz-joint-period-energy-audit.json) records the compiled endpoints
and optional numerical checks. This extends the
[retained factorial estimate](zeta-riesz-retained-factorial.md).
Both whole-carrier thresholds remain open.

## The joint inequality

Let prime intervals have disjoint interiors $[a_i,b_i]$ inside $[a,b]$,
where $a\ge0$. For each finite interval population, let $c_{i,p}$ be its
real signed coefficients and $x_{i,p}\in[a_i,b_i]$. Write

\[
T_i(t)=\sum_p c_{i,p}1_{(L-x_{i,p},L]}(t),\qquad
M_i=\sum_p c_{i,p}.
\]

At a fixed cutoff $t$, at most one interval is partially active. Every other
interval contributes its complete signed moment or zero. If each partial
tail is bounded by $B$, Lean proves

\[
\left|\sum_i T_i(t)\right|\le\sum_i|M_i|+B.
\]

On the common strip of length $a$, the response is exactly $\sum_i M_i$.
Applying this to the original two-hinge profile $f$ gives

\[
\sum_{k=1}^R k\,[f(k)-f(k+1)]^2
\le a\left(\sum_iM_i\right)^2
 +(b-a)\left(\sum_i|M_i|+B\right)^2.
\]

`joint_tail_bound` and `joint_profile_energy` prove these statements, with
exact half-open endpoint conventions. The total full moment stays signed
inside its square. The partial-tail price is a maximum, not a sum of
individual response norms. The remaining absolute moment sum is visible.

## Actual factorial prime periods

For $|y|\ge54$, put $h=2\pi/|y|$. Each actual prime interval is
$e^{a_i}<p\le e^{a_i+h}$, with $a_i\ge5000$. For factorial order $j$ let

\[
W_{i,j}=e^{-a_i/2}(a_i+h)^j,\qquad
s_{i,j}=\left|\frac j{a_i}-\frac12\right|+\frac{jh}{a_i^2},
\qquad B_i^0=\frac2{|y|a_i}+\frac4{a_i^2}.
\]

The checked numerical caps are

\[
C_{i,j}=\frac{4W_{i,j}}{a_i^2}+W_{i,j}s_{i,j}hB_i^0,
\qquad
B_{i,j}=W_{i,j}(1+s_{i,j}h)B_i^0.
\]

All prime-discrepancy and amplitude hypotheses are discharged. For the
nonempty finite index set $I$, the new `factorialJointEnergy` is

\[
Q_j=a\left(\sum_{i\in I}C_{i,j}\right)^2
 +(b-a)\left(\sum_{i\in I}C_{i,j}+\max_{i\in I}B_{i,j}\right)^2.
\]

It is an explicit finite numerical expression. For the *combined* response,
`exists_joint_factorial_mean` proves a squarefree mean bounded by $EXQ_j$,
with one proved but **unevaluated** $E>0$ and arbitrary cofactor phase $c(n)$.
The phase rotation is performed on the whole sum, not separately on its
periods. Reciprocal cofactor weights on $M<n\le2M$ also have their complete
energy paid.

## Original-carrier endpoint

`exists_literal_joint_period_bounds` applies directly to

\[
J=\Re\sum_{n\in S}\sum_{i\in I}\sum_{p\in P_i}
 \operatorname{residualCoefficient}(A,L,N,pn)
 \operatorname{zetaPrimeLogKernel}(N,3/2+iy,pn).
\]

For one common squarefree cofactor selection $S\subset(M,2M]$, with at
least two cofactor prime factors, it gives $-K\le J\le K$, where

\[
K=\frac{\sqrt E}{LN!}e^{-\log M/2}
 \sum_{j=0}^{N+1}{N+1\choose j}(\log(2M))^{N+1-j}\sqrt{Q_j}.
\]

Here $L>0$, $M\ge1$, all $P_i\subseteq A$, and every selected prime is
coprime to every selected cofactor. The proof uses the exact nonnegative
retained coefficients from `ZetaRieszRetainedFactorial`; they are independent
of the marked prime and hence allow the periods to be combined first.
All orders, including zero and one, and every squarefree count from three
upwards remain. No zero or simplicity hypothesis is used.

The new bound is an alternative to the earlier sum of individual square-root
budgets. It is not claimed to dominate that bound for every configuration.
For the tested central factorial blocks it is smaller: at $N=262144$,
order $j=144180$, and 256 neighbouring periods, the new numerical cost is
about $0.513$ of the separate-period cost. This is a floating diagnostic,
not an additional theorem or a whole-carrier estimate.

The optional
[`probe_riesz_joint_period_energy.py`](../scripts/probe_riesz_joint_period_energy.py)
also checks the general signed-tail inequality on actual primes at log
endpoint 10. In its 16-period, phase-zero case the actual joint energy is
about $0.0472$ of the squared sum of individual norms. These small-prime
checks are below the quantitative theorem's $a_i\ge5000$ threshold and do
not test those numerical Chebyshev constants. The script stays outside CI.

The same probe now evaluates the **entire factorial-order sum**, not only
one order. In a smooth central-saddle diagnostic with largest share $0.55$,
$u=10001/20000$ and 16 complete periods, the source-normalized numerical
budget, omitting the unknown $\sqrt E$, is approximately

| $N$ | Joint budget | Joint / separate budget |
| --- | ---: | ---: |
| 16384 | $4.87\times10^{-7}$ | 0.933 |
| 65536 | $4.42\times10^{-6}$ | 0.809 |
| 262144 | $1.09\times10^2$ | 0.618 |
| 1048576 | $1.26\times10^{35}$ | 0.454 |

Every order is included in the floating calculation; very small binomial
probabilities can underflow. The probe treats $\log(2M)$ as a real saddle
parameter and uses the smooth length $-2N\log u$, rather than the exact
integer cutoff. These are values of an upper-bound expression, not lower
bounds for the carrier, an asymptotic impossibility theorem, or an actual
prime computation at those heights. The gain from combining periods does
not eliminate the large positive complete-moment caps in this diagnostic.

## What remains

The cofactor population must be common to the combined intervals. Periods
must remain complete and separated; cofactor-dependent prime holes, moving
ownership, physical masks and clipped endpoints are not silently filled.
Any use on uniquely owned integers needs its exact incidence accounting.
Credits already inside a combined period cannot be added again.

This slice reduces a price for summing periods separately. It does not prove
that the complete-moment contribution, factorial-order aggregation or final
source-normalized cost is small. The central-saddle obstruction to the
earlier separate-period budget remains valid. Neither the independent
$-79/1000-o(1)$ floor nor the $3/2+o(1)$ ceiling is proved, and no new zero
exclusion is claimed.
