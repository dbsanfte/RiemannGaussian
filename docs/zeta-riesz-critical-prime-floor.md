# Least-prime critical shells in the balanced floor

Local continuation from `194a361762f404a8f4473298b25d96fbae0bb56e`.
The independent cofinal floor remains open. This slice proves an exact
arithmetic classification and spends its favorable signed contribution
in the current balanced-minus-head inequality. It does not certify the
size of the remaining adverse sum.

The checked leaf is
[`ZetaRieszCriticalPrimeFloor.lean`](../RiemannGaussian/ZetaRieszCriticalPrimeFloor.lean).
The focused report is
[`riesz-critical-prime-floor-audit.json`](riesz-critical-prime-floor-audit.json).

## Pair the actual least primes, preserving every divisor sign

Write a squarefree label as $n=rqb$, with $r<q$ prime and every prime of
$b$ at least $q$. The condition `Gap L r (q*b)` says that no divisor of
$qb$ has logarithm strictly between $L-\log r$ and $L$. Both endpoints,
and the empty divisor, are retained in its exact definition.

On this gap, the two least-prime pairings give

$$
\mathcal R_L(rqb)=\log r\sum_{d\in\mathcal D}\mu(d),\qquad
\mathcal D=\{d\mid b:L-\log r-\log q<\log d\le L-\log r\}.
$$

`riesz_eq_signed_critical_shell` proves this identity on the original
finite cofactor. It joins every subset rank before evaluating the sum;
there is no completion, prime density, fitted count weight, or phase
assumption.

`criticalDivisors_eq_singleton` proves a stronger classification. If
$2\log n<3L$ and any prime $p$ belongs to $\mathcal D$, then
$\mathcal D=\{p\}$. Every other critical divisor, including every
composite one, is excluded. The gap forces $\log q+\log p\ge L$.
Another critical divisor either contains $p$, contradicting the shell's
upper endpoint, or is coprime to $p$, contradicting the total-log budget.
Consequently

$$
\mathcal R_L(n)=-\log r,\qquad
c_L(n)=\frac{\log n\log r}{L}.
$$

This is a coefficient identity, not a sign assertion for its complex
phase. Total prime-count parity does not determine this sign.

## What the native geometry permits

`native_budget` discharges $2\log n<3L$ on every native central label
for $N\ge65536$, using the existing $L\ge277N/200$ lower bound and
$\log n\le2029N/1000$ upper bound.

`native_primeCritical_count_le_four` prevents overstating this payment:
on the actual balanced population, this prime-critical gap has at most
four prime factors. The owner bound $\log p<51N/50$ forces
$\log q>73N/200$. At count at least five, the remaining cofactor has
at least two additional prime factors of size at least $q$, so
$\log n>423N/200$, contradicting the central upper endpoint. Native
counts are already at least three. Thus the prime-critical gap covers
counts three and four, not the higher-count active crossings or
composite-critical shells.

`favorableLabels` selects precisely these original central labels whose
original kernel has nonnegative real part. `favorable_sum_nonneg` pays
their entire source-normalized signed sum independently of any zero
hypothesis. The full phase and all original central masks remain.
`central_joint_floor_of_favorable` spends this payment in the whole
balanced-minus-head lower inequality. The **same full signed
ordinary-prime head** is retained on both sides. No monotonicity of a
clipped period cost is assumed and no credit is spent twice.

The adverse phase part, active least-prime crossings, composite-critical
shells, and their joint correlation with the head still need a
quantitative signed estimate. This slice proves no cofinal allowance
$\le399/5000$, ceiling, contradiction, zero exclusion, or RH result.

## Optional numerical audit

`scripts/probe_riesz_balanced_critical_shell.py` exhausts the earlier toy
population at $N=6,7,8$, heights $54,65,100$, and both radial windows.
It retains the full complex phase and same full head, and passes all
18 regressions against the frozen independent signature probe.
Integer tests use the exact divisor cutoff
$X=\lfloor(20000/10001)^{2N}\rfloor$.

At $N=8$ the original toy window contains 704,598 labels: 300,813 active
least-prime crossings, 172,515 zero-gap responses, 204,353 prime-critical
gap responses, 11,165 single-composite critical gaps, and 15,752 other
nonzero critical gaps. Every prime-critical shell observed is a
singleton. At height 65 that population contributes about
$-1.02135\cdot10^{-4}$ to the main, while the joined main-minus-head is
about $-5.41040\cdot10^{-5}$. The signs are exploratory floating
measurements, not interval-certified native bounds.

The toy uses $L=-2N\log u$, not the native moving integer length or
dyadic schedule; it omits full native deletion masks and applies no
eventual payment at these small orders. These numbers are not fractions
of the native floor deficit. Earlier profile-optimization probes also
show that much of their residual cost is the genuinely negative signed
total, which an exact null direction cannot change.

The least-weight critical-shell pattern has a classical analogue in
[Pakianathan and Winfree's threshold-complex theorem](https://journals.tubitak.gov.tr/math/vol37/iss3/14/).
That analogy supplies no independent arithmetic cancellation rate; the
proof here uses literal divisor geometry, without a homology framework
or a claim that this closes the RH-strength estimate.

Focused strict Lean, the targeted leaf build, compiled ordinary-root
namespace lint and all-declaration standard-axiom checks are recorded in
the report. All previous snapshots, concurrent semiprime work and public
endpoints are preserved. This slice is local only.
