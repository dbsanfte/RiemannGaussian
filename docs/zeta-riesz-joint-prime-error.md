# A sharper error for the retained signed prime moments

Lean now improves the **arithmetic discrepancy** of a joined prime interval
from an inverse square to an inverse cube of its lowest prime logarithm.
The comparison keeps the entire signed smooth integral. The theorem is
eventual, with a proved but **unevaluated** starting point.

Source: [`ZetaRieszJointPrimeError.lean`](../RiemannGaussian/ZetaRieszJointPrimeError.lean).
The [audit](riesz-joint-prime-error-audit.json) records the compiled endpoints
and optional numerical diagnostics. Both whole-carrier inequalities remain
open.

## Actual primes, stronger error

The existing complete smoothed prime formula already supplies exponential
decay in the square root of logarithmic time. Retaining that rate first gives

\[
\left|V(t)-\left(e^t-1-t\log(2\pi)\right)\right|\le e^t/t^6
\]

eventually. Monotone desmoothing at the exact step $h=1/t^2$ pays both moving
endpoints and the linear completion term. The resulting actual Chebyshev
estimates are

\[
|\psi(e^t)-e^t|\le4e^t/t^2,
\qquad |\theta(e^t)-e^t|\le5e^t/t^2.
\]

The second inequality includes the complete proper-prime-power allowance.
There is no unproved prime-error, exposed-zero or simplicity hypothesis.
The existing explicit-start bound remains available independently; this
sharper rate does **not** claim that its threshold is 5000.

If the literal test kernel satisfies
$|f(x)|\le W/(x\log x)$ and
$|f'(x)|\le D/(x^2\log x)$ on $e^a\le x\le e^b$, the finite Abel theorem gives

\[
\left|\sum_{e^a<p\le e^b}f(p)\log p
 -\int_{e^a}^{e^b}f(x)\,dx\right|
\le \frac{5\,[2W+D(b-a)]}{a^3}
\]

for all sufficiently large $a$, uniformly over these test kernels and
endpoints. Its exact identity has only the two exterior boundary terms.
Artificial interior endpoints do not acquire separate absolute costs.
The integral stays signed and retains its exact reciprocal logarithm.

## All factorial orders and the original allocation

For $G_j(t)=e^{-t/2}t^j$, Lean proves the global maximum

\[
|G_j(t)|\le e^{-j}(2j)^j\quad(t\ge0),
\]

including $j=0$, using $0^0=1$. Therefore the interval amplitude can use

\[
W_j=\min\{e^{-a/2}b^j,\ e^{-j}(2j)^j\},\qquad
S_j=\left|j/a-1/2\right|+j(b-a)/a^2.
\]

This avoids an unnecessarily large endpoint-product bound on wide intervals.
With arbitrary phase shift $c$ and any real height $y$, the actual prime
moment differs from its smooth integral by at most

\[
\mathcal E_j(a,b,y)=
\frac{5W_j[2+(S_j+|y|+2)(b-a)]}{a^3}.
\]

`eventually_retained_interval_error` then uses the **exact** nonnegative
allocation coefficients $B_{n,j}$ already proved for squarefree cofactors:

\[
(1-\theta_A(N,pn))(\log p+\log n)^{N+1}
 =\sum_{j=0}^{N+1}B_{n,j}(\log p)^j,
\quad 0\le B_{n,j}\le {N+1\choose j}(\log n)^{N+1-j}.
\]

For arbitrary signed weights $w_n$, it bounds the difference between the
literal retained prime moment and the **joint signed** sum of its smooth
moments by

\[
\sum_{n\in S}|w_n|e^{-\log n/2}
 \sum_{j=0}^{N+1}{N+1\choose j}(\log n)^{N+1-j}
 \mathcal E_j(a,b,y).
\]

The left side keeps $1-\theta_A$, the full factorial amplitude and
$\cos(y\log(pn))$. Every order, including zero and one, is retained.
Cofactors may have any number of prime factors from two upwards. Every
selected prime must belong to the original eligible set and be coprime to
every selected cofactor. The prime interval is common to this cofactor
population and may have clipped exterior endpoints.

This is a theorem for the **retained prime moments**. It does not include
the prime-dependent Riesz cutoff response in that moment comparison, prove
its coupled smooth contribution small, fill prime holes, or discharge the
whole `residualCoefficient*zetaPrimeLogKernel` carrier. Unique incidence
accounting and already-paid-sector exclusions still have to be respected.

## Quantitative diagnostic and remaining work

The optional [probe](../scripts/probe_riesz_joint_prime_error.py) compares
the old and new **arithmetic error formulas for the same smooth comparison**,
with all factorial orders included. For 16 central periods, the new/old
ratios are approximately $6.36\cdot10^{-4}$ at $N=16384$ and
$3.98\cdot10^{-5}$ at $N=262144$. This is a floating evaluation; the theorem's
starting point is unevaluated, so these values do not certify applicability
at those finite endpoints. Small actual-prime tests are also explicitly
outside the established eventual range. The probe is never a CI gate.

Even the improved positive error formula grows after source normalization
in the sufficiently large tested central examples. Thus this extra inverse
logarithm is not by itself a source-scale decay theorem. The remaining
task is to control the joined **signed smooth moments and Riesz cutoff
correlations**, then pay their actual masks and total aggregation with
disjoint accounting. The independent $-79/1000-o(1)$ floor and
$3/2+o(1)$ ceiling both remain open. No new zero-free region or RH claim
is made.
