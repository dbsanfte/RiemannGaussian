# Complete prime periods with the original factorial allocation

Lean now bounds both signed sides of the **original** finite
`residualCoefficient * zetaPrimeLogKernel` carrier on complete prime periods.
The factorial kernel, `1-boundedShare`, both Riesz hinges, the actual product
phase, and every factorial order are retained. An explicit binomial-variance
calculation sums the order cost. There is no upper prime-count restriction.

The result extends the [joint prime-tail energy](zeta-riesz-prime-tail-energy.md).
It does **not** close the whole-carrier floor or ceiling. Cofactor-dependent
holes and the total source-normalized cost still need control. In particular,
the new polynomial savings do not remove the central saddle's exponential
source growth. The mean constant is proved but **unevaluated**.

Sources:
[`ZetaRieszWeightedPrimeTail.lean`](../RiemannGaussian/ZetaRieszWeightedPrimeTail.lean)
and [`ZetaRieszRetainedFactorial.lean`](../RiemannGaussian/ZetaRieszRetainedFactorial.lean).
The [audit](riesz-retained-factorial-audit.json) records the endpoints and
optional numerical diagnostics.

## Exact allocation before the signed inequality

For a squarefree cofactor $n$ with at least two prime factors, put $m=N+1$.
Lean constructs coefficients $B_j(n)$, independent of the marked prime $p$,
such that for every eligible prime $p\nmid n$,

\[
(1-\operatorname{boundedShare}(A,N,pn))\log(pn)^m
 =\sum_{j=0}^{m} B_j(n)(\log p)^j,
\qquad
0\le B_j(n)\le {m\choose j}(\log n)^{m-j}.
\]

`unassigned_multinomial` identifies the left side with precisely those
multinomial allocations not assigned to a selected majority-prime incidence.
Such incidences are disjoint. `exists_retained_coefficients` sums the
remaining allocations with marked-prime order $j$. No low orders are removed;
the original eligible-prime set and `unpaidOrders` definition are unchanged.

Exact squarefree reflection then expresses the real carrier atom through

\[
-\frac{1}{LN!}\sum_{j=0}^{m}
 \frac{e^{-\log n/2}B_j(n)}{n}
 \frac{e^{-\log p/2}(\log p)^j}{p}
 \cos(y(\log p+\log n))
 \left(\mathcal R_L(n)-\mathcal R_{L-\log p}(n)\right).
\]

Both cutoffs and the full phase stay inside the same signed prime sum.
The coefficients' positivity is used only after that cancellation is bounded.

## Varying amplitudes and their joint cutoff cost

Let $a\ge5000$, $|y|\ge54$, $h=2\pi/|y|$, and
$P=\{p\text{ prime}:e^a<p\le e^{a+h}\}$.
For a real amplitude $G$ with $|G|\le W$ and Lipschitz constant $D$ on
$[a,a+h]$, exact finite Abel summation gives

\[
\left|\sum_{p\in P}\frac{G(\log p)\cos(y(\log p+c))}{p}\right|
\le \frac{4W}{a^2}+DhB,
\qquad B=\frac{2}{|y|a}+\frac4{a^2}.
\]

All partial tails are bounded by $(W+Dh)B$. Integrating the **combined signed
tail** before squaring pays the full moment and every Riesz crossing by

\[
Q(a,y,W,D)
 =a\left(\frac{4W}{a^2}+DhB\right)^2
   +h\left((W+Dh)B\right)^2.
\]

This is `amplitudeEnergy`. The existing quantitative prime theorem discharges
all prime-discrepancy premises. It is a finite arithmetic inequality, not a
source-scale prime-density substitution. On every squarefree cofactor shell
$M<n\le2M$, the reciprocal cofactor energy is also paid, uniformly in the
correlated phase $c(n)=\log n$.

For the literal factorial amplitude $G_j(t)=e^{-t/2}t^j$, Lean proves

\[
W_j=e^{-a/2}(a+h)^j,\qquad
D_j=W_js_j,\qquad
s_j=\left|\frac ja-\frac12\right|+\frac{jh}{a^2}.
\]

These bounds hold for every $j$, including zero and one.

## The order sum has an explicit budget

Write $b=\log(2M)$, $T=a+h+b$, $x=(a+h)/T$, and $m=N+1$. Put

\[
C=\frac{4\sqrt a}{a^2}+\sqrt h B,\qquad
D=(\sqrt a+\sqrt h)hB,\qquad
V=\frac{\sqrt{mx(1-x)}}a
  +\left|\frac{mx}a-\frac12\right|+\frac{mh}{a^2}.
\]

The compiled theorem `factorial_order_budget` gives

\[
\sum_{j=0}^{m}{m\choose j}b^{m-j}\sqrt{Q(a,y,W_j,D_j)}
\le e^{-a/2}T^m(C+DV).
\]

The key improvement is the variance term $\sqrt{mx(1-x)}$, instead of the
maximum deviation of a factorial order. This comes from Cauchy--Schwarz
against the exact complete binomial distribution, including all orders.

Consequently, for every squarefree selection $S\subset(M,2M]$ with at least
two cofactor primes, the original joint sum

\[
J=\Re\sum_{n\in S}\sum_{p\in P}
 \operatorname{residualCoefficient}(A,L,N,pn)
 \operatorname{zetaPrimeLogKernel}(N,3/2+iy,pn)
\]

satisfies $-K\le J\le K$, where

\[
K=\frac{\sqrt E}{LN!}\,e^{-\log M/2}e^{-a/2}T^m(C+DV).
\]

Here $L>0$, $M\ge1$, $P\subseteq A$, and every selected $p$ is coprime to
every selected $n$. One proved $E>0$ works for all parameters. This is
`exists_literal_summed_period_bounds`; `summedPeriodCost` is $K/\sqrt E$.
`exists_literal_family_bounds` sums these explicit costs for arbitrary finite
radial/share families with a common $A,N,y,L$. There is no extra multiplier
for the number of periods, orders or prime counts.

## Scope and remaining obstruction

The period must be complete for each selected cofactor. Arbitrary subsets of
cofactors are allowed; cofactor-dependent deleted primes inside a period are
not. The theorem does not silently fill ownership, window, physical-cutoff,
coprimality or already-paid-sector holes. A use on the whole carrier needs an
exact, appropriately disjoint incidence partition and payment of its clipped
boundaries. Credits from inside a complete period cannot be added again.

The optional script
[`probe_riesz_retained_factorial.py`](../scripts/probe_riesz_retained_factorial.py)
checks 15 exact integer-log coefficient regressions and evaluates the order
budget numerically at $N=16384,65536,262144$. At the central saddle and share
$0.55$, its averaged cost is about $0.1333$, $0.0487$, and $0.0188$ times the
maximum-score cost. These are floating diagnostics, not additional theorems.

The same diagnostic keeps the source normalization visible: at $u=0.50005$,
the central single-period upper budget eventually grows in the tested range,
reaching about $15.7$ before the unknown $\sqrt E$ at $N=262144$. This is a
limitation of the bound, not a lower bound on the signed arithmetic sum or an
asymptotic impossibility theorem. This saddle diagnostic uses the smooth
length $L=-2N\log u$ and a real cofactor-log endpoint; it does not evaluate
the literal integer cutoff defining the repository's moving length.
Global cancellation still has work to do.

Both independent whole-carrier targets, the $-79/1000-o(1)$ floor and
$3/2+o(1)$ ceiling, remain open. No zero hypothesis or simplicity assumption
enters these new estimates; no new zero exclusion is claimed.
