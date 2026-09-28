# Paying the positive-five small-prime boundary in the whole sum

The actual whole `J+C` floor and ceiling now pay an additional population
from their signed rests, while preserving every previous payment and the
full `47*sourceCredit/8` margin. The new population consists of positive
squarefree five-prime labels in the selected central phase period whose
largest prime has log share below `119/200` and which have a prime of log
share at most `1/100000000`.

The two independent numerical endgame bounds, `-79/1000-o(1)` below and
`3/2+o(1)` above, remain open. This payment neither proves that the whole
rest is small nor excludes a zero.

The subsequent [factorial refinement](zeta-riesz-saddle-joint-credit.md)
keeps this payment and the same rest while increasing the explicit reserve
to `(12*sqrt(N+1)-1/8)*sourceCredit`.

## Literal arithmetic estimate

Write `delta=1/100000000`, and let `t<log(n)<=t+h` be an original phase
cell, with `h<=1/100000` and `69t/100<=L<=7t/10`. On the new population,
positivity of the exact five-prime coefficient implies that the three
cofactor primes other than the marked small prime all have logarithm
greater than `9t/100`. They also have a uniform upper logarithmic bound.
Thus only one cofactor can approach the small-prime boundary.

The marked prime retains its logarithmic weight. The proof combines:

- the coefficient bound `norm(coefficient)<=2*log(r)`;
- the literal Chebyshev bound `sum log(r)/r<=10*delta*t`;
- three finite reciprocal-prime sums, each at most `5`;
- the exact cofactor-dependent last-prime interval, costing at most `3h/t`.

These bounds give a cost at most `7500*delta*V(t,h)*h`, hence

```math
\sum_{n\in H(t)}\left|\operatorname{residualCoefficient}(n)
             K_N(n)\right|
\le \frac1{10000}V(t,h)h,
\qquad V(t,h)=\frac{e^{-t/2}(t+h)^N}{N!}.
```

The theorem is `ZetaRieszPositiveFiveBoundary.eventually_norm_mass` in
[the ordinary library](../RiemannGaussian/ZetaRieszPositiveFiveBoundary.lean).
It retains the original allocation factor, phase and arbitrary support
mask. Its starting order is existential; the explicit threshold used by
one elementary part of the proof is not a threshold for the whole theorem.

`eventually_period_norm_mass` pays all `8g` original phase cells at cost
`g*V0*h/1200`, where `g` is the phase mesh count, not zero multiplicity.
`remaining_prime_log_gt` shows that positive-five labels left in this
period after the payment have every prime log share strictly above
`1/100000000`, provided their largest share is below `119/200`.

## Whole-sum application and spending

Keep the previous central population `P`, positive-five population `B`,
and owner population `D` unchanged. Select the new boundary `H` only from
`S \ (P union B union D)`. In particular, the owner payment is not redefined
or spent twice. Let `b,d,h0` denote the literal complex sums over `B,D,H`,
and let `R` be the exact sum over the remaining labels.

The sharper central margin pays both five-prime costs:

```math
\frac{gV_0h}{125}-\frac{gV_0h}{1000}-\frac{gV_0h}{1200}
=\frac{37gV_0h}{6000}.
```

This still pays six copies of the existing source credit `G_N`. The
unchanged owner debit costs `G_N/8`. The cached optional application proves

```math
\begin{gathered}
u^{N+1}\bigl(\operatorname{Re}R+
 \max(\operatorname{Re}b,0)+\max(\operatorname{Re}h_0,0)+
 \max(\operatorname{Re}d,0)\bigr)+\frac{47}{8}G_N-e_j
 \le \operatorname{Re}\bigl(u^{N+1}(J+C)\bigr),\\
\operatorname{Re}\bigl(u^{N+1}(J+C)\bigr)
 \le u^{N+1}\bigl(\operatorname{Re}R+
 \min(\operatorname{Re}b,0)+\min(\operatorname{Re}h_0,0)+
 \min(\operatorname{Re}d,0)\bigr)-\frac{47}{8}G_N+e_j,
\qquad e_j\longrightarrow0.
\end{gathered}
```

As before, the lower and upper comparisons use their respective original
central populations and are alternative budgets. They are not additive.
They hold on the original dyadic orders for `1/2<u<=10001/20000` and fixed
`abs(y)>=54`, without a zero hypothesis.

On the same payment ledger, replacing the previous rest `R+h0` by this
formula raises the lower comparison by `u^(N+1)*max(-Re(h0),0)` and lowers
the upper comparison by `u^(N+1)*max(Re(h0),0)`. The old reserve is intact.
This is a bound on an actual previously unpaid population, not a completed
surrogate or a source-decay assertion.

The terminal declarations are
`RieszCentralCapacityTransfer.eventually_joint_boundary_floor` and
`RieszCentralCapacityTransfer.eventually_joint_boundary_ceiling` in
[the cached application](../scripts/CheckRieszCentralCapacityTransfer.lean).
The [audit](riesz-central-capacity-audit.json) records its exact source
hashes, standard-axiom checks and lint result. Exhaustive covers remain
optional and were not rerun.

The remaining arithmetic task includes the positive-five interior with
all shares above this cutoff, other phase periods and the other unselected
counts and signs. Numerical integration suggests a usable cost for the
positive-five interior, but it is not a certified literal-prime bound.

The [subsequent interior-debit slice](zeta-riesz-positive-five-interior.md)
sharpens these same local and period costs to `3/40000` and `g/1600`,
spending the 25 percent reduction in both whole-sum comparisons.
The preceding theorems remain as corollaries.
