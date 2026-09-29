# Joint signed cutoff energy

The new bound applies to the original finite prime sum. It retains the
constant moment, first moment and signed cutoff correction together, and
does not charge the separately divergent absolute crossing sum. Its remaining
profile energy is explicit and is **not yet small enough at source scale**.
The whole floor and ceiling remain open.

The source is
[`ZetaRieszSignedCutoffEnergy.lean`](../RiemannGaussian/ZetaRieszSignedCutoffEnergy.lean).
The [machine-readable audit](riesz-signed-cutoff-energy-audit.json) records the
scope, theorem names, verification and optional diagnostic.

## The quantitative gain

Write (M_k(n)=\sum_{d\mid n,\ d\le k}\mu(d)). One proved but unevaluated
constant (E>0) satisfies, for every finite squarefree (S\subset(1,X])
and every **signed** profile (b),

\[
 \sum_{n\in S}\left(\sum_{k=1}^R b_k M_k(n)\right)^2
 \le E X\sum_{k=1}^R k b_k^2.
\]

There is no prime-count ceiling, cutoff separation assumption, or remainder
from integer rounding. The proof uses the inverse-square logarithmic Gram
bound, a weighted Schur estimate with row cost four, and exact complementary
cutoffs ((n-1)/k) above the square-root transition.

Finite Abel summation applies this to arbitrary divisor weights (f), with

\[
 b_k=f(k)-f(k+1),\qquad f(R+1)=0.
\]

Unlike the earlier positive-mixture estimate, the new cost permits summing
opposite prime contributions **inside** each (b_k) before squaring. There
is no monotonicity assumption on (f). The corresponding two-sided weighted
inequality is `exists_joint_profile_bounds`.

## The literal carrier and moving boundaries

For the original `signedPrimeWeight` (g(a,p)), the exact profile on a
selected squarefree composite cofactor is

\[
 f_a(d)=-\frac{\mu(a)}a\sum_{p\in P(a)}g(a,p)
 \bigl((L-\log d)_+-(L-\log p-\log d)_+\bigr).
\]

The defined `primeProfile` extends the sign as ((-1)^{\omega(a)}) to
unselected labels and vanishes past (X). This extension agrees exactly
with the displayed expression on the selected squarefree population.
The cofactor selection stays in the arithmetic mean; it is not completed.
The original factorial kernel, allocation `1-boundedShare`, full cosine,
both cutoffs, coprimality and arbitrary selected prime sets are unchanged.

With (b_a(i)=f_a(i)-f_a(i+1)), the terminal theorem proves

\[
 -K\le \operatorname{Re}\sum_{a\in S}\sum_{p\in P(a)}
   \mathrm{residualCoefficient}(pa)\,\mathrm{kernel}(pa)\le K,
\]

\[
 K=\sqrt E\sum_{q=1}^X q
   \sqrt{\sum_{i=1}^R i\bigl(b_q(i)-b_{q+1}(i)\bigr)^2}.
\]

Take any integer (R) with (e^L<R+1). This is a proved bound, with no
unproved arithmetic estimate in its hypotheses. The prime sums remain inside
the cutoff and cofactor differences. Their moving endpoints, interior holes,
and the exterior endpoint at (X+1) are included. Every finite radial
selection may be included in (P(a)) before applying the theorem. If separate
selections overlap, their incidence multiplicities must still be handled in
the original ledger; no additional positive credit is free.

## What the finite probe says

`scripts/probe_riesz_signed_cutoff_energy.py` is an optional floating diagnostic using
actual finite primes, exact integer divisor signs, the original allocation
formula, the moving length, (1.95N<\log n\le2.03N), unique largest-prime
ownership, the nondominant mask and the full phase at height 54. It reports a
broader squarefree population and, separately, its subpopulation with every
prime above (N^2). These are small finite orders, not an asymptotic test or a
certificate for the Lean constant.

| Order | Cofactor ceiling | Signed/unsigned profile energy | Normalized variation cost, before (\sqrt E) |
|---:|---:|---:|---:|
| 6 | 4,096 | 0.14618 | 14.13 |
| 8 | 65,536 | 0.011878 | 71.13 |

At order 8, 285,908 actual prime/cofactor atoms and 38,971 divisor-crossing
incidences are included; 25,344 atoms satisfy the additional all-primes
physical lower cutoff. A separate direct evaluation of 256 original atoms
agrees with the reflected profile to floating precision.

The signed energy detects substantial cancellation. The general variation
bound across cofactors is nevertheless too expensive in this test. It is
therefore **not** a successful whole-floor estimate, and it is not evidence
that the actual signed sum diverges. The next quantitative task is to exploit
the correlated moving boundaries without paying their full variation. The
existing separate-crossing and generic source-envelope no-go results remain
in force. No zero hypothesis, new zero exclusion, or RH claim enters this
slice.
