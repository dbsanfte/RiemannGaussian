# Coupled continuous Riesz audit

The target remains the literal signed difference

\[
u^{N+1}(\mathrm{lowerThresholdPacket}_{3..55}
        -\mathrm{shortOverflowPacket}_{3..13}).
\]

**This pass does not prove its arithmetic bound or the complementary floor.**
It tests the synthetic modes `0, 1/40000 +/- (3/500)i`, with multiplicities
`1,3,3`. No claim is made that these are zeta zeros. Every previous Lean
no-go remains in force. Numerical evidence of decay at finite orders would
not by itself exclude delayed growth.

The preceding [continuous renewal audit](zeta-riesz-continuous-renewal-audit.md)
removed the cutoff lattice and diagnosed the error from splitting the
one-cofactor head before interpolation. The new optional
[coupled driver](../scripts/probe_riesz_joined_continuous_balls.py) uses that
continuous response *before* the outer integrations. It keeps the moving
integer-floor length, radial core `39N/20..203N/100`, both original factorial
beta faces, and the conditional owner-order band. It performs no head split
and discards no low factorial allocations.

## What the numerical balls enclose

The interval-parameter projection retains the common affine breakpoint
identities in the same `s,d` parameters. It includes the empty-cofactor
boundary and splits every convolution at its density-polynomial boundaries.
Its [regressions](riesz-continuous-projection-audit.json) compare against
the original fixed-geometry evaluator, include interval inputs and an
independent count-by-count subset integral.

Two optimizations have explicit numerical allowances:

- A completed density polynomial may be shortened only after adding
  `sum |c_j| h^j` for every removed Taylor coefficient to its uniform error.
  These are numerical Taylor coefficients, not prime-count truncations.
- A negligible quadrature summand may be replaced by a zero-centered ball
  containing its full norm envelope. One envelope uses the already-summed
  continuous densities; a second uses the unsigned simplex volume.

The driver rejects a non-finite or overly wide final ball. It separately
reports a simplex allowance for model cofactor counts above 54 and 12.
Input hashes are checked before and after every run, and complete row
checkpoints are retained locally. A two-row `--benchmark` is explicitly
labelled and is **not** a coupled integral.

These budgets enclose response evaluation, roundoff and skipped numerical
terms. **They do not enclose the outer quadrature error or justify transfer
to ordinary primes.** The optional probes stay outside ordinary CI and the
numerical certificate workflow.

## Completed coupled refinements

The [completed-run report](riesz-coupled-continuous-probe.json) verifies the
frozen sources and every expected row of each checkpoint. At `N=65536`:

| Radial rule | Radial / beta / owner nodes | Joined finite quadrature |
| --- | --- | ---: |
| Ordinary Legendre | `12 / 32 / 128` | `-0.0154946800869143` |
| Ordinary Legendre | `24 / 32 / 128` | `-0.00557131130141336` |
| Finite-window gamma | `24 / 32 / 128` | `-0.00557135860389366` |
| Ordinary Legendre | `24 / 96 / 192` | `-0.00557131133102910` |

The response-evaluation radii are below `6e-22`; the separate omitted model
count allowance is below `1.18e-17` for these runs. Neither includes outer
quadrature error. The change of about `0.00992337` is a diagnostic
discrepancy, not an error estimate or evidence about eventual growth. The
independent radial test below explains why the 12-node value is unreliable.
Changing the radial measure to the exact finite-window gamma rule changes
the 24-node result by about `4.73e-8`. This comparison is a diagnostic too;
agreement of two rules is not an enclosure of their common integration error.
The independent beta/owner refinement from `32/128` to `96/192` changes
the ordinary 24-node radial result by about `2.96e-11`. All four runs have
finished; their row checkpoints and frozen inputs pass the report checks.

The complete count response is evaluated on both factorial boundaries before
the subtraction. In the completed gamma run, the lower-boundary finite sum
is enclosed by a zero-centered ball of radius `4.55e-23`; the upper boundary
is approximately `+0.0055713586`. Thus the observed surviving model response
comes from the upper boundary. This is a statement about that run, not a
claim that the lower arithmetic packet is zero or that separate boundary
allowances are valid asymptotically.

## An independent radial phase check

Small mass error does not imply small phase error. At `N=65536`, the
12-node radial rule approximates the core gamma mass to about `6.4e-6`,
but its error on the moment of `exp((3/500)i*T)` is about `0.16445`.
The true moment has norm only `0.00888924`.

The [radial report](riesz-radial-phase-probe.json) computes these moments
independently of the count recurrence. For `a=u-g-i*f`, it uses

\[
\int_A^B \frac{u^{N+1}e^{-uT}T^N}{N!}e^{(g+if)T}\,dT
=\left(\frac ua\right)^{N+1}
  \left[Q_N(aA)-Q_N(aB)\right],
\qquad
Q_N(z)=e^{-z}\sum_{k=0}^N\frac{z^k}{k!}.
\]

The finite sum is evaluated backwards. Once `k<|z|`, the omitted terms
have decreasing ratios and their entire tail is bounded by
`|term_k|*k/(|z|-k)`. Complex ball arithmetic retains all earlier terms.
Fifteen small-order complex checks agree with a separate incomplete-gamma
implementation; the two large-order real cases agree as well.

For the tested frequency `f=3/500` and growth `g=1/40000`, the moment has
norm approximately `0.235259`. Its ordinary radial Legendre errors are:

| Nodes | Enclosed error, approximately |
| ---: | ---: |
| 12 | `4.33836` |
| 24 | `4.76499e-6` |
| 48 | `7.59429e-27` |

These are enclosures for individual moments, not for the whole
varying-amplitude response.

## Quadrature adapted to the exact factorial density

The optional [gamma-weighted driver](../scripts/probe_riesz_gamma_coupled.py)
reuses the same response and masks. Only the prepared radial quadrature
changes. Both finite-window endpoints are retained.

Put `a=N+1`, `X=(uT-a)/sqrt(a)` and let `f_X` be its gamma density. The
finite-window moments satisfy the exact integration-by-parts recurrence

\[
M_{k+1}=kM_{k-1}+\frac{k}{\sqrt a}M_k
-\left[(1+x/\sqrt a)x^k f_X(x)\right]_{x_-}^{x_+}.
\]

The [rule implementation](../scripts/riesz_radial_gamma.py) forms its
Stieltjes recurrence in centered coordinates, brackets each Gaussian root,
computes positive Christoffel weights, and checks moments through degree
`2q-1`. It rejects insufficient precision rather than accepting an
unproved positive norm. In the same tested phase/growth moment, 24
gamma-weighted nodes have error about `2.73e-20`; 32 have error about
`7.19e-34`. No assertion about the full integrand's quadrature error follows
just from these tests.

## A large upper-boundary response remains

The independent [million-order point report](riesz-continuous-upper-million.json)
evaluates `N=1048576`, `T=(N+1)/u`, owner share `11/20`, and cutoff share
`1/25`. The complete continuous response is about `1.29209e9`, with no
lattice or split-head interpolation. Its cofactor total allows at most
eleven cofactor primes, so it does not use the omitted high-count tail.

This contrasts with the lower-boundary point near cutoff `1/99`, whose
response is about `5.95e-19`. It neither proves growth of the coupled sum
nor supports bounding its two boundaries separately. The radial and share
phases and the signed boundary difference remain essential.

## Exact chamber calculation prompted by the audit

The [minimum-collision audit](zeta-riesz-minimum-collision-audit.md#summed-balanced-cones)
now proves the summed orthant cone for every balanced opposite-frequency
family. After its fixed-total Jacobian, its value is

\[
\frac{a}{(a^2+\eta^2)^m}>0\qquad(a>0,\;2m\text{ legs}).
\]

For the 12- and 48-cofactor candidates, the grouped factorial normal slopes
are exactly `1/1045` and `1/4465`. The Riesz factors have opposite signs,
but the original boundary subtraction reverses one of them: both signed
cone factors are negative. Lean proves this on `0.693<=L/T<=0.694`.

This rules out cancellation **between those two reduced cone factors**.
It does not prove that they survive in the full coupled response: replacing
the actual varying integrand by its cone asymptotic, controlling the
remaining corners, and summing the other count/mode assignments are still
unproved. There is no arithmetic-transfer or retained-prime-sum bound here.

## Literature applicability

Gorodetsky retains an explicit zeta-zero correction and a prime-power
correction in the smooth-number approximation. Lemma 4.1 gives a truncated
complex explicit formula; Corollary 4.4 states derivative bounds only through
order five. Theorem 2.13 assumes a global zero-free strip.
[Source: §§2.3, 2.6 and 4.1](https://arxiv.org/html/2211.08973v3).

Our applicability conclusion is limited: the explicit formula is a possible
input for a transfer retaining the zero corrections, but the displayed
estimates do not bound our growing factorial order and correlated masks.
The existing [finite Euler-quotient work](zeta-riesz-euler-correction-deletion.md)
already supplies the relevant algebra. Rebuilding that quotient or replacing
its correction by one would not close the present signed estimate. No new
literature assumption is added to the Lean chain.

## Reproduction

```sh
.lake/riesz-ball-venv/bin/python scripts/test_riesz_continuous_projection.py \
  --output /tmp/riesz-projection.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_radial_phase.py \
  --output /tmp/riesz-radial-phase.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_gamma_coupled.py \
  --tnodes 24 --rnodes 32 --pnodes 128 --degree 96 --bits 512 --workers 4 \
  --output /tmp/riesz-gamma-coupled.json
```

No numerical result here is a Lean certificate, an independent signed
arithmetic estimate, or a zero exclusion.
