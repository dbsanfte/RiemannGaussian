# Source-unit calibration of the joined-pair detector

This pass supplies **no arithmetic floor saving**. The target is still the
independent cofinal bound `Re prefixPairDefect <=399/5000+o(1)`. The existing
all-multiplicity implication remains conditional. No new zero exclusion,
carrier, prime-density approximation, or physical-mask payment is claimed.

The numerical follow-up tests two possible explanations for the stalled
detector: another missing cancellation in the collected factorial slots,
and insufficient resolution in source units. It finds no additional slot
cancellation. It quantifies how a conservative sampling-based check becomes
poorly conditioned, without proving a minimum cost for every possible
numerical method. Exact identities can evade that cost and remain the useful
purpose of numerical discovery.

## Exact algebra before numerical calibration

Write `K=floor(13N/32)` and use the already-defined complete logged array
`a_k=u^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+i*y)`. The existing evaluator is

```math
\begin{aligned}
H_N(a)={}&\frac1N\sum_{k=0}^{N-1}a_k a_{N-1-k}
+\sum_{k=K+1}^{N-K}\frac{a_{k-1}a_{N-k}}{N+1-k}\\
&-\frac{N+1}{uL_N}\sum_{k=1}^{N+1-K}
  \frac{a_{k-1}a_{N+1-k}}{N+2-k}.
\end{aligned}
```

The optional producer recollects the original central slot, successor slot,
logged prefix, and full Selberg trace using exact rational coefficients.
It matches both swapped order incidences and checks equality to the above
joined evaluator at orders `32,64,256,640,1536,8192`. The two total logged
orders are `N-1` and `N`. Every surviving collected coefficient is nonzero:
positive in the first total order and negative in the second. This does not
exclude further cancellation using a newly proved relation between actual
prime moments; it excludes a missed zero in this finite coefficient table.

Logged orders zero and one are retained. Equal-order entries are counted
once after collection. They are not extra prime-square labels: the previously
paid whole square correction is neither added nor spent again.

An independent checker evaluates the original four-slot factorial quadratic
and the joined logged evaluator at 130 digits for twelve finite genuine-prime
cases. These cases have orders at most 64 and do not estimate the exhaustive
literal carrier. They verify normalization and phases only.

## A declared reference model, not prime transport

For calibration only, set `g=2u` and write a synthetic array as
`a_k=g^(k+1)*phi_k`, with `|phi_k|<=1`. This is **not** asserted to be the
exact unsigned ordinary-prime moment mass. No actual prime measure is
transported to this model.

Define the two exact positive coefficient masses

```math
P_N=1+\mathsf H_{N-K}-\mathsf H_K,\qquad
Q_N=\frac{N+1}{uL_N}(\mathsf H_{N+1}-\mathsf H_K).
```

The reference absolute price is

```math
A_N=g^{N+1}(P_N+gQ_N).
```

If every reference phase-coordinate estimate has error at most `epsilon`
and estimated coordinate norm at most one, product expansion gives the
sufficient whole-evaluator error price `A_N*(2epsilon+epsilon^2)`. This is
used solely to calibrate a conservative interval/Monte Carlo method; it is
not a new positive majorant proposed for closing the floor.

At the radius ceiling the known hypothetical simple-zero source is
`0.0798717970349441779...`. Its difference from `0.0798` is
`0.0000717970349441779...`, the unchanged **contradiction margin**, not
observed unpaid arithmetic mass. Allocating one quarter of that margin to
the reference numerical error gives:

| Order | Reference absolute price | Sufficient reference phase accuracy |
| ---: | ---: | ---: |
| 65536 | `1.8800e3` | `4.7737e-9` |
| 425984 | `8.4604e18` | `1.0608e-24` |
| 1048576 | `9.2227e45` | `9.7310e-52` |

These are model tolerances, **not estimates of actual prime errors** or
necessary lower bounds for all algorithms. Direct signed interval evaluation,
an exact identity, or a valid variance-aware method may be much sharper.

The optional report also computes a deliberately conservative sufficient
confidence cost for bounded IID complex marks, with failure probability
`0.05` and a union over `N+2` coordinates. Applying the bounded-sum inequality
to both real coordinates gives
`n>=4*log(80*(N+2))/epsilon^2`; the report does not apply this probability
model to the cached prime draws. The underlying inequality is
[Hoeffding, Theorem 2 (1963)](https://www.cs.rpi.edu/academics/courses/spring06/random/hoefding.pdf).

Synthetic constant-array perturbations on either side of the target verify
that the stated precision resolves the declared model. They use no actual
prime arrays, exposed-zero assumption, numerical first-crossing certificate,
or bound on a remaining arithmetic population.

## What the frozen genuine-prime samples cover

The producer reads the existing frozen caches without rerunning them:

- 2080 distinct FLINT-proved primes, 50 boxes, and 48256 Cartesian incidences;
- orders 256, 640, and 1536; none reaches the formal threshold 65536;
- shared-prime Cartesian incidences are not independent observations;
- neither cache exhausts the ordinary-prime population at any native order.

At the two uncovered test heights, `10^10000` and `10^20000`, every sampled
prime is smaller than the height. Thus these samples are before the eventual
fixed-height integer-spacing regime. This repeats the existing coverage
warning with exact cache counts; it is not a new obstruction to a cofinal
theorem and is not a bound on consecutive prime gaps.

High precision in evaluating a sampled phase does not supply either
population coverage or source-scale statistical precision. The current
detector remains useful for discovering candidate exact relations. It cannot
be promoted to a cofinal floor certificate by increasing the number of
Cartesian pair products or by reporting a small normalized sample mean.

## Local artifacts and next arithmetic target

Run the optional producer and independent checker from `formal/`:

```sh
../.venv/bin/python scripts/probe_riesz_pair_source_resolution.py \
  --output .lake/riesz-pair-source-resolution/scan.json
../.venv/bin/python scripts/check_riesz_pair_source_resolution.py \
  --input .lake/riesz-pair-source-resolution/scan.json \
  --output .lake/riesz-pair-source-resolution/validation.json
```

No Lean source, root import, public endpoint, README, explorer metadata,
semiprime work, CI workflow, commit, or remote was changed by this pass.
The snapshots are pinned by
[`riesz-pair-source-resolution-audit.json`](riesz-pair-source-resolution-audit.json).

The next mathematical result must constrain the actual ordinary-prime
moments **jointly** strongly enough to bound this same `H_N`/literal prefix.
There is currently no proved constraint with that strength. Further generic
phase statistics, endpoint cancellation, or the exposed-zero source limit
do not establish it. The goal remains open.
