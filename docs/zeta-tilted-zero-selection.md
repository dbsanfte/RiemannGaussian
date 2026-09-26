# Tilted zero selection: an attained maximum and its limit

**This is a zero-selection theorem and a narrowly scoped mode audit. It
does not bound the retained prime sum or establish a new zero exclusion.**
The unchanged target remains the source-normalized difference
`lowerThresholdPacket` (counts 3–55) minus `shortOverflowPacket` (counts
3–13), with both factorial boundaries, the full phase and every mask.

## What is now proved for actual zeros

[`ZetaTiltedZeroSelection`](../RiemannGaussian/ZetaTiltedZeroSelection.lean)
constructs an upper-half-plane zero maximizing

\[
f_a(\rho)=\Re\rho-a\Im\rho,\qquad a>0.
\]

If an initial upper zero lies above a target, a sufficiently small slope
preserves that inequality. The maximum is attained: every competitor of
positive score lies in a finite height window. Avoiding finitely many
slopes makes the maximum unique. The theorem
`exists_unique_upper_max` proves this for genuine nontrivial zeta zeros;
it does **not** assume a globally rightmost zero or infer simplicity.

Put \(u=3/2-\Re\rho\), and move the evaluation point to

\[
c_a=\frac32+i(\Im\rho-au),\qquad v=c_a-\rho=u-iau.
\]

The exact signed identity is

\[
\Re\bigl(\overline v(c_a-\tau)\bigr)
=|v|^2+u\bigl(f_a(\rho)-f_a(\tau)\bigr).
\]

For nonnegative shares summing to one, the same identity retains the
weighted score differences **before** a norm is taken. It proves
\(|\sum q_j(c_a-\tau_j)|\ge |v|\), strictly if a positively weighted
competitor has strictly smaller score. Thus a selected upper zero supplies
a separating line for all upper modes without a rightmost-zero assumption.
This theorem alone does not transfer the old source ledger to the shifted
evaluation height or handle the pole, lower modes, or hard least-prime mask.

## Why distant modes still matter

The geometric control is only over the upper divisor. Consider synthetic
points at real part \(\beta+\delta\) and heights
\(\pm G,\ \pm(G+2y)\), where \(y=\Im c_a\). For sufficiently large
\(G\), both upper competitors lose the tilted score to \(\beta+i\gamma\).
The two points at heights \(-G\) and \(G+2y\) nevertheless have denominators

\[
d+i\eta,\quad d-i\eta,\qquad d=u-\delta,\quad\eta=G+y.
\]

`remote_upper_scores` and `remote_pair_denominators` prove these statements
exactly. Both nodes can be arbitrarily far outside a local analytic disk.
Their least-coordinate moment, after summing its two ordered chambers,
is still

\[
(2u)^h M_h=\frac{(u/d)^h}{d^2+\eta^2}.
\]

`remote_minimum_tendsto` proves divergence when \(0<\delta<u\), for every
fixed \(G\). Distance supplies a small constant, not an eventual saving.
**This integral omits the full joined Riesz/count cancellation. Its growth
does not prove growth of that response, nor the existence of these zeros.**

The optional [probe](../scripts/probe_riesz_tilted_selection.py) uses exact
rational geometry and ball evaluation of this already-proved formula; it
performs no quadrature. Its [report](riesz-tilted-selection-probe.json)
includes conjugation and functional-equation symmetries, while treating all
points as synthetic. With \(\beta=0.999951\), \(\gamma=100\),
\(a=10^{-9}\), \(\delta=10^{-6}\), and \(G=10^6\), the rate is
\(\log(u/d)\approx1.9998060\times10^{-6}\):

| Moment order h | Normalized two-chamber moment |
| --- | ---: |
| 1,000,000 | `7.3861e-12` |
| 10,000,000 | `4.8413e-4` |
| 20,000,000 | `2.3443e5` |

These values illustrate delayed growth of this exact model integral only.
They are not evidence about the population of actual zeta zeros.

Reproduce outside CI using the optional ball environment:

```sh
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_tilted_selection.py \
  --output docs/riesz-tilted-selection-probe.json
```

The new selection theorem resolves attainment and coupled separation for
upper modes. It leaves the actual signed target unchanged: the lower and
upper factorial faces, all retained counts and the masked remainder must
still be estimated jointly. Local analyticity alone cannot justify dropping
remote modes after the least-prime projection. The older radial, phase
transfer, allocation, and diverging-allowance audits remain in force.
