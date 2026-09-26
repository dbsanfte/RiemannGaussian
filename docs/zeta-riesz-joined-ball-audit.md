# Phase quadrature in the joined cutoff model

The retained arithmetic target is unchanged:

\[
u^{N+1}\left(\mathrm{lowerThresholdPacket}_{3..55}
             -\mathrm{shortOverflowPacket}_{3..13}\right).
\]

**There is still no bound for that signed sum, no complementary arithmetic
floor, and no new zero exclusion.** This audit identifies a numerical error
that prevents the large-order synthetic calculation from deciding its own
growth or decay. It adds no Lean theorem and makes no arithmetic transport.

## An independently checked failure of the phase quadrature

The original upper factorial face uses

\[
R\sim\operatorname{Beta}(h+1,N-h+1),\qquad h=\lfloor N/25\rfloor-1.
\]

At `N=1048576`, set `u=10001/20000`, `T=(N+1)/u`, and test

\[
\mathbb E\exp\left(i k\frac3{500}T(R-\mathbb E R)\right).
\]

These are basic frequencies of the existing synthetic close-mode diagnostic.
They are not an identification of the complete response with a single
Fourier moment. The independent
[phase probe](../scripts/probe_riesz_beta_phase.py) integrates each moment
with complex ball arithmetic, verifies analyticity of the logarithms used
in the integrand, and includes both omitted tails. The integrated interval
is sixteen standard deviations on either side of the mean. The combined
tail mass is less than `2.381e-55`; the phase has unit modulus there.
The separate zero-frequency check encloses the exact mass one.

The [report](riesz-beta-phase-probe.json) records the reference enclosures
and the fixed-node quadrature errors. For example:

| Harmonic | Quadrature nodes | Absolute error, approximately |
| --- | --- | --- |
| 2 | 12 | `0.06816` |
| 6 | 12 | `0.90931` |
| 10 | 64 | `5.12e-13` |
| 10 | 128 | `0.37033` |
| 10 | 256 | `9.35e-16` |
| 10 | 512 | less than `2e-44` |

The sixth reference moment has norm below `3e-43`, yet the 12-node rule
returns a value of norm about `0.909`. At the tenth harmonic, increasing
the node count from 64 to 128 makes the error much worse. This is phase
aliasing, not floating-point roundoff. Neither extra precision nor agreement
between a few resolutions is a sufficient quadrature check.
The 512-node rule passes all five reported individual-moment comparisons
at the reference integration's accuracy. This resolves these regression
tests, not the varying-amplitude coupled integral. The reference rejects
both non-finite balls and finite enclosures too wide to support its claims.

The corresponding million-order coupled run was stopped as unresolved.
Its partially accumulated values are not evidence of a growing source.
These tests do not establish the full response's error or its sign either:
that requires retaining its varying amplitudes and all correlated weights.

## What the coupled ball diagnostic does and does not enclose

The optional [coupled probe](../scripts/probe_riesz_joined_balls.py) keeps
the original two factorial faces, the owner-order band, the full conjugate
phase, the exact integer-floor moving length and the radial core interval.
It computes the finite Euler series and signed convolution in ball
arithmetic. Direct trigonometric evaluation avoids interval wrapping from
repeated complex rotations. An explicit lattice composition allowance
accounts for counts beyond 55 and 13 on the two respective faces.

It also replaces the one-cofactor term by its analytic value before
interpolation. Both boundary rules are calibrated to their common owner
marginal. The elementary identity used for that calibration is

\[
\int_0^{1-p}
 \frac{r^h(1-r)^{N-h}}{B(h+1,N-h+1)}
 \binom{N-h}{j}\left(\frac p{1-r}\right)^j
 \left(1-\frac p{1-r}\right)^{N-h-j}\,dr
 =\binom{N+1}{j}p^j(1-p)^{N+1-j},
\]

for `0<p<1` and `j+h<=N`. Expand the powers, substitute
`r=(1-p)v`, and evaluate the beta integral to obtain it. This marginal
formula is not a newly formalized Lean theorem. The already compiled
`ZetaRieszJoinedHeadCancellation.constant_head_integral` proves the
corresponding exact cancellation of every cutoff-independent complex head
for the original rectangle. Calibrating this one moment does not bound
other quadrature errors.

A [384-bit finite calculation](riesz-joined-balls-probe.json) at `N=65536`, cutoff grid 512 and quadrature
orders `(48,8,256)` gives approximately `-0.00557338434`. This agrees with
the older diagnostic at that scale but **is not an enclosure of the
continuum integral**. Its tiny rounding ball excludes neither lattice error
nor unresolved phase integration. The physical prime measure and its
remaining masks are not represented by the synthetic density.

## Reproduction

Keep these optional diagnostics out of ordinary CI and the numerical
zero-count certificate workflow:

```sh
python3 -m venv .lake/riesz-ball-venv
.lake/riesz-ball-venv/bin/python -m pip install -r scripts/requirements-riesz-balls.txt
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_beta_phase.py \
  --nodes 12 64 128 256 512 --bits 2048 \
  --output docs/riesz-beta-phase-probe.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_joined_balls.py \
  --workers 4 --output docs/riesz-joined-balls-probe.json
```

The separate coupled diagnostic is available for finite-expression tests;
its output explicitly leaves grid, interpolation and quadrature errors open.
It must not be reported as a certificate or used to decide eventual growth
without resolving those errors. Python-FLINT's
[complex integration documentation](https://python-flint.readthedocs.io/en/latest/acb.html)
explains the required analyticity checks in ball quadrature.

The next useful numerical calculation must integrate oscillatory phase
components reliably while retaining their amplitudes, both boundaries and
the count sum. Even a successful continuum calculation would still leave
the literal signed prime-sum estimate and the complementary floor unproved.

The subsequent [moderate-order refinement audit](zeta-riesz-phase-refinement.md)
shows that the old eight-node rule at `N=65536` also fails individual phase
tests. Its independently enclosed errors include `0.96277` at harmonic ten.
A faster positive-term binomial evaluator reproduces the old finite result;
the finer coupled integrations are tracked in that note. This supplies no
continuum or arithmetic bound.
