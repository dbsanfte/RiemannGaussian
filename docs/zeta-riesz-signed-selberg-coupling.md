# Signed Selberg coupling and the actual cutoff

Local numerical and literature investigation, 2026-10-03. No new arithmetic
bound, Lean theorem, floor, ceiling or zero exclusion is proved in this pass.

The preceding `ZetaRieszLowCountSelbergAudit` rules out paying the Selberg
completion defect by absolute value. The present probe leaves that defect
inside the signed sum on the **same live low-count labels and complete phase
periods**. It tests

\[
B_N=S_N+D_N,
\qquad
D_N=\sum_n\bigl(b_N(n)-b_{\rm Sel}(n)\bigr)W_N(n),
\]

where `b_N` is the existing joined coefficient, `W_N` includes the original
factorial weight and `exp(-iy log n)`, and

\[
b_{\rm Sel}(p)=-\log p,
\qquad
b_{\rm Sel}(pq)=-\frac{2\log p\log q}{\log(pq)}.
\]

No defect norm, positive-period price or separate population allowance is
spent. Floating-point reconstruction checks are numerical regressions, not
proofs of a native or cofinal estimate.

## The finite signed test does not establish a uniform cancellation rule

The optional `scripts/probe_riesz_signed_selberg_coupling.py` evaluates
orders 6, 7, 8 and the held-out order 9 at heights
54, 65, 100, 142, 400, 1600 and 51200. It runs both the older ideal-cutoff
model and the actual damped cutoff: **56 evaluations in total**. All phases
remain attached to their literal prime or distinct-prime-product labels.
The original head and unallocated correction remain distinct.

The normalized Selberg prime/pair contributions have strong finite
opposition. Their median real complete-period correlations range from
approximately -0.912 to -0.985. This does not imply that the masked defect
also opposes Selberg. For the ideal model, the corresponding median
Selberg/defect correlations at orders 6 through 9 are

\[
-0.708,\quad +0.361,\quad -0.049,\quad +0.139.
\]

For the actual damped cutoff they are

\[
-0.581,\quad -0.812,\quad -0.703,\quad -0.866.
\]

Even in the latter samples, the total signed Selberg and defect contributions
do not always have opposite signs. These small-order values neither prove
nor refute eventual cancellation with the native weights.

## A cutoff calibration prevents a misleading extrapolation

Lean uses the floor-dependent physical cutoff

\[
\boxed{
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,
\qquad X_N=(D_N+2)^2,
\qquad L_N=\log X_N.
}
\]

The old toy evaluator explicitly uses the ideal length `-2N log u` and its
older physical support. The new `--actual-length` mode instead computes
`D_N` by exact integer division at `u=10001/20000`, reweights the same label
superset at `L_N`, and retains the strict upper physical-prime cutoff `p<X_N`.
The old support contains the actual toy support at these four orders.

The distinction changes the coefficient geometry qualitatively. Consider
only the log profile `log p=0.99N`, `log q=1.01N`, `T=2N`; this is a
**continuous coefficient calibration, not an enumeration of actual primes**.
The larger log lies below the `1.02N` owner threshold, so both head and
correction are absent. Its exact four-hinge coefficient gives the following
floating-point calibration:

| Order | Actual `L_N/(2N)` | Actual Selberg defect divided by `T` |
| --- | ---: | ---: |
| 6 | 0.399649 | -0.500050 |
| 8 | 0.425150 | -0.500050 |
| 9 | 0.441144 | -0.500050 |
| 256, first native order | 0.671371 | +0.010461 |
| 640 | 0.682949 | +0.035711 |
| 8192 | 0.691947 | +0.054753 |
| 90112 | 0.692921 | +0.056783 |

The ideal model gives approximately `+0.057047` at every listed order.
At the enumerable actual orders, both large-prime head and correction
populations are empty; those samples therefore cannot validate their native
joint cancellation. At native-sized orders the coefficient calibration
returns to the positive balanced-defect geometry already proved in
`ZetaRieszLowCountSelbergAudit`. The calibration itself proves no signed
prime-sum estimate.

Preserve the older probes and their explicitly ideal conventions. Future
detector results must distinguish the actual damped cutoff from that model
before claiming a pattern relevant to the eventual floor.

## What the literature supplies, and what remains missing

Friedlander and Iwaniec's [*Asymptotic sieve for primes*](https://arxiv.org/pdf/math/9811186)
starts from nonnegative weights and imposes a separate bilinear cancellation
hypothesis `(B)`, in addition to divisor-distribution estimates. Its Theorem 1
assumes that hypothesis; it does not prove it for arbitrary weights. The
discussion on pages 1044–1045 explicitly separates this parity-breaking input
from the usual distribution assumptions.

The present factorial, allocation and owner masks, with the fixed complex
logarithmic character, do not come with a verification of `(B)`. Rewriting
them into an asymptotic-sieve framework would leave a real estimate to prove.
No such hypothesis is introduced into Lean or treated as an arithmetic
payment here. This literature audit finds no ready-made bound for the
literal joined signed quantity; it does not rule out a more specific signed
argument.

The remaining target is unchanged:

\[
\boxed{
\mathrm{lowCountPeriods}(u,y,j)\le399/5000+o(1)
\quad\text{cofinally}.
}
\]

The whole floor and the independent multiplicity ceiling `42/25` remain
open. Numerical correlation is not a fraction of the remaining source gap.

## Validation and local evidence

The two ideal runs preserve nine frozen complex complete-period results.
All four runs check `B_N=S_N+D_N` on labels and complete periods, and compare
the joined complex result with the older evaluator on the same reweighted
data. An independent check reconstructs the full Möbius divisor sum for
768 sampled actual-cutoff labels at orders 6, 7 and 8; its maximum coefficient
difference is below `4e-15`.

These are floating-point numerical checks, not interval or Lean
certificates. All 24 reported source pins were verified. No Lean source is
changed, so the prior strict/linter/standard-axiom audit is preserved rather
than presented as a new theorem check. No wider checks, commits, pushes,
root registration or public frontier updates are run. Concurrent semiprime
work is preserved. The focused immutable evidence record is
`docs/riesz-signed-selberg-coupling-audit.json`; the probe remains outside CI.
