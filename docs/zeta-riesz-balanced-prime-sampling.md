# Actual-prime sampling: no balanced-pair floor credit

Local diagnostic, 2026-10-03, at `194a361762f404a8f4473298b25d96fbae0bb56e`.
The required signed bound `Re literalPairDefect <= 399/5000 + o(1)` is
**still open**. This experiment proves no quantitative saving against it.

The optional [sampler](../scripts/probe_riesz_balanced_prime_sampling.py)
examines actual prime pairs, rather than a continuous prime-density model.
Its final acceptance check uses FLINT's proved-primality routine
([FLINT documentation](https://flintlib.org/doc/fmpz.html)); the accepted
integers are not accompanied by Lean primality certificates. `python-flint`
0.9.0 is an optional analysis dependency, with no build or CI registration.

For each of two seeds, the experiment draws 128 primes from each of
`N < log p <= N+1` and `N+1 < log q <= N+2` at `N=256`, and 32 per
interval at `N=640`: 640 accepted primes in total, sampled with replacement.
Every sampled prime exceeds `N^16`. Both owner masks are false on this
box, so their absence is a literal support fact. Distinctness, squarefreeness,
the contracted radial window, full phase and actual moving length are retained.
No eventual native payment is applied at these early orders.

Writing `T=log p+log q` and `L=log((floor(u^(-N)/(N+1))+2)^2)`, the actual
balanced coefficient is

\[
\Delta_N(p,q)=-\frac{T(T-L)}L+
 \frac{2\log p\log q}{T},\qquad u=\frac{10001}{20000}.
\]

The report retains `u^(N+1) Delta_N exp(-3T/2) T^N/N! exp(-iyT)`.
It removes only a common positive scalar for the relative diagnostics;
it restores that scalar for the finite-box population estimates.
The radial variable is never frozen at `2N`.

## What the test found

At heights 54, 100 and the exact integer `10^1800`, all **12** two-marginal
bootstrap intervals contain zero. The heights are not asserted to be zero
ordinates. The very large height is a numerical phase check, not an
asymptotic regime. The two samples at `N=640`, height 54 illustrate the
lack of a stable sign:

| Seed | Signed real / positive sampled mass | Empirical bootstrap interval |
| --- | ---: | --- |
| 731 | -0.032395 | [-0.11474, 0.04244] |
| 732 | 0.000061 | [-0.04960, 0.05971] |

The corresponding source-scaled finite-box estimates are about
`-4.51e-8` and `4.52e-11`. These are estimates for **one early box**,
not the whole retained pair aggregate, and not bounds. Their uncertainty
also contains both signs. A rank-one decomposition of the sampled weight
matrix is a floating diagnostic only; it supplies no prime-phase theorem.

The Cartesian products share their primes: 32-by-32 pairs do not provide
1,024 independent observations. The bootstrap therefore resamples the
two prime marginals separately. Prime-count uncertainty is also retained.
Since sampling stops at `r` accepted primes after `T_trials` odd draws,
the count estimator uses `(r-1)/(T_trials-1)`, not the biased stopped ratio
`r/T_trials`. For ideal independent Bernoulli trials of success rate `theta`,

\[
\mathbb E\frac{r-1}{T_{\rm trials}-1}
 =\theta^r\sum_{k\ge0}\binom{k+r-2}{r-2}(1-\theta)^k
 =\theta.
\]

This explains the estimator; neither the pseudorandom generator nor the
bootstrap is a formal probability or confidence certificate. The proposal
population consists of the literal odd integers in each box; no PNT density
is used for these count estimates.

## Verification and decision

Independent Arb evaluations checked the exact product logarithm, moving
coefficient and normalized factorial weight at eight sample atoms, and
the full phase at all three heights. Six negative-binomial distributions
checked the stopped-count calibration numerically. The report marks the
sample SVD upper estimate as floating, not deterministic certification.
All these are diagnostic checks, not Lean inequalities.

Run the optional experiment with:

```sh
../.venv/bin/python scripts/probe_riesz_balanced_prime_sampling.py --bootstraps 500
```

The final report and accepted prime integers are in
`.lake/riesz-balanced-prime-sampling/result.json` and `result.primes.json`.
Use `--reuse-samples` to recompute the analysis without repeating primality
checks. The [audit](riesz-balanced-prime-sampling-audit.json) pins the final
script, raw samples and report and records the focused checks.

**Decision:** stop enlarging this sampling experiment without a mechanism
that can be proved for the cofinal aggregate. Credit against `0.0798` is
exactly zero. The existing selected source `0.079871797034944...` and
contradiction margin `0.000071797034944...` are unchanged. This margin is
the difference between the hypothetical source and the desired independent
upper bound; it is not a measured remaining error or distance to completion.
No new Lean representation, floor,
ceiling, zero exclusion or RH claim is introduced.
