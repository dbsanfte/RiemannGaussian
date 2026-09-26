# Refining the coupled phase diagnostic

The retained arithmetic target is unchanged:
`u^(N+1) * (lowerThresholdPacket - shortOverflowPacket)`, with counts
3–55 and 3–13, respectively. **No bound for that prime sum or its
complementary carrier is proved here.**

## The moderate-order result also needs refinement

The earlier finite ball calculation at `N=65536` used eight beta nodes.
Its rounding enclosure near `-0.00557338` did not include quadrature error.
The new [phase audit](riesz-beta-phase-65536-probe.json) checks those nodes
against a separate analytic ball integral. This is the exact upper-face
beta distribution, at `T=(N+1)/(10001/20000)`, tested with
`exp(i*k*(3/500)*T*(r-E r))`:

| Harmonic k | Eight-node error | 32-node error | 128-node error |
| --- | ---: | ---: | ---: |
| 6 | `0.07217` | `4.57e-20` | `<1.1e-42` |
| 10 | `0.96277` | `2.26e-8` | `<3.4e-44` |
| 12 | `0.37075` | `5.02e-5` | `<3.6e-43` |
| 24 | `0.04749` | `0.01331` | `1.907e-17` |

Refinement is not monotone: 64 nodes give error about `0.27362` for
harmonic 24. The reference integrates on 18 standard deviations and
encloses the omitted beta mass by less than `2.12e-60`. Forwarding the
analytic branch flag and enforcing narrow reference balls remain mandatory.
The [million-order regression](riesz-beta-phase-probe.json) was rerun too.

These are enclosures for individual phase moments. They neither bound
the coupled varying amplitude nor prove that its old value is wrong by
any particular amount. They rule out treating that old quadrature as
resolved. A small rounding ball is not a continuum error estimate.

## A faster, independently checked probability evaluator

The optional [binomial helper](../scripts/riesz_binomial_balls.py) starts
with an exact integer binomial coefficient and sums the smaller positive
tail. Successive probability ratios decrease. After any retained term,
the entire remaining tail is at most

\[
\text{current term}\;\frac{r}{1-r},\qquad 0\le r<1.
\]

The computation checks this inequality's ratio premise and adds the
geometric remainder to its output ball. It also retains all rounding
errors. Its [independent test](../scripts/test_riesz_binomial_balls.py)
uses exact rational probabilities for small cases, Arb's separate
incomplete-beta evaluator for large cases, and a parameter ball straddling
the mean. The [audit](riesz-binomial-balls-audit.json) records those checks.

[`probe_riesz_joined_refinement.py`](../scripts/probe_riesz_joined_refinement.py)
uses this evaluator in the existing coupled expression. All masks and
normalizations of that **numerical model** remain unchanged. At grid 128,
eight beta nodes, 48 radial nodes and 256 owner nodes, both evaluators
enclose the same value, approximately `-0.005589620774028708`. The measured
runtime changed from 122 seconds to 44 seconds. That comparison validates
the replacement evaluator, not the quadrature.

Both 128-beta-node runs have finished. The
[combined report](riesz-joined-refinement-probe.json) preserves the complete
output balls, frozen input hashes, count allowances and timings:

| Cutoff grid | Beta nodes | Joined finite expression |
| ---: | ---: | ---: |
| 128 | 8 | `-0.00558962077402870791` |
| 128 | 128 | `-0.00558902293985005846` |
| 256 | 128 | `-0.00557573982899972697` |

The beta refinement changes this expression by approximately `5.97834e-7`;
the grid refinement changes it by `1.32831e-5`, about 22 times as much.
Neither refinement makes the finite model value vanish. These differences
are observed changes, **not estimates of the remaining errors**. No limiting
sign, eventual growth, packet bound or arithmetic conclusion follows.

The lower face changes from `3.33e-20` to `2.68e-24` between the two finer
grids. Its small magnitude does not certify that component either. The
upper face supplies the displayed negative joined value after subtraction.
The grid-256 run bounds its *omitted lattice count classes* by less than
`3.17e-17`; this does not bound the lattice-to-continuum error. The two runs
took about 1007 and 1790 seconds and checked that all frozen inputs remained
unchanged before writing their reports.
The 64-node run with the old evaluator was deliberately stopped after
the new evaluator passed the independent comparison; it produced no final
result. There are no pending runs in this refinement pass. The next numerical
estimate must control the cutoff lattice/interpolation and the full coupled
quadrature, including its amplitude. Increasing arithmetic precision or
declaring a limit from this table does not discharge either error. The
actual-prime transfer and independent complementary floor remain open after
any successful continuum calculation.

## An analytic budget for individual phase modes

The optional [phase-budget probe](../scripts/probe_riesz_phase_budget.py)
adds a sufficient test, not just agreement between resolutions. For
`R ~ Beta(a,b)`, let `gamma_q` be the squared norm of the monic degree-`q`
orthogonal polynomial. The classical
[Gauss remainder formula](https://dlmf.nist.gov/3.5.E19), applied separately
to the real and imaginary parts, gives the safe bound

\[
\left|\mathbb E e^{i\omega R}-Q_q(e^{i\omega R})\right|
\le \frac{2\gamma_q|\omega|^{2q}}{(2q)!}.
\]

For this beta probability measure the Jacobi recurrence gives

\[
\gamma_q=\prod_{j=1}^{q}
\frac{j(j+a-1)(j+b-1)(j+a+b-2)}
 {(2j+a+b-2)^2(2j+a+b-3)(2j+a+b-1)}.
\]

The [report](riesz-phase-budget-probe.json) evaluates this expression with
ball arithmetic. The normalization passes 68 exact rational checks against
an independent factorial formula and the variance identity. Enlarging the
previous numerical phase values by these budgets is consistent with all
50 independently integrated reference comparisons. This checks those
computations; it is not a formalization of Gaussian quadrature in Lean.

Using the full radial endpoint `T<=203N/100`, the first node counts giving
this conservative budget below `1e-30` are:

| N | Lower-face stress harmonic 54 | Upper-face stress harmonic 12 |
| --- | ---: | ---: |
| 65536 | 291 | 85 |
| 262144 | 956 | 207 |
| 1048576 | 3595 | 654 |

These are sufficient node counts for the stated **single Fourier modes**;
they are neither necessary counts nor a prescription that certifies the
coupled probe. The full amplitude includes Riesz hinges, owner weights and
moving interpolation cells. Its derivative bounds and accumulated Fourier
weights have not been estimated. In particular the 128-node coupled run
does not yet carry a full quadrature error bound. The table prevents us
from mistaking a fixed node count for a uniform large-order guarantee.

Run outside ordinary CI:

```sh
.lake/riesz-ball-venv/bin/python scripts/test_riesz_binomial_balls.py
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_phase_budget.py \
  --output /tmp/riesz-phase-budget.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_beta_phase.py \
  --order 65536 --nodes 8 16 32 64 128 --harmonics 2 6 10 12 24 \
  --bits 1024 --sigma-span 18 --output /tmp/riesz-phase-65536.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_joined_refinement.py \
  --order 65536 --grid 256 --tnodes 48 --rnodes 128 --pnodes 256 \
  --bits 384 --workers 4 --output /tmp/riesz-joined-refinement.json
```

The refinement wrapper freezes source hashes before computation and checks
them again before writing a report. Do not edit those inputs during a run.
No exhaustive numerical-certificate workflow is invoked by these probes.

The subsequent [continuous-renewal audit](zeta-riesz-continuous-renewal-audit.md)
computes fixed-geometry responses independently of the cutoff lattice. It
also isolates a large, exact `H-I(H)` interpolation discrepancy introduced
by splitting off the one-cofactor head. That artifact must be resolved
before using high-order coupled probes to diagnose the arithmetic target.
