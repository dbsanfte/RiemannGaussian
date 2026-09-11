# Centered interval counts for the complete squarefree matrix

The local continuation proves an arithmetic estimate on every integer
interval for all bounded complex divisor-weight families. It subtracts
the exact density before estimating the error. This closes a counting
interface for the complete squarefree sequence; the independent signed
ordinary-prime-tail bound needed for RH remains open.

## Actual coefficient and density

For a finite prime set `S`, a divisor cutoff `D`, and complex families
`w,v`, the coefficient is the existing literal arithmetic sequence

```text
c(n) = 1[n squarefree and no prime in S divides n]
       * (sum_(d<=D,d|n) w(d)) * (sum_(e<=D,e|n) v(e)).
```

Both factors are complex sums. The new theorem does not replace their
product by a squared norm. Equal real Möbius families recover the
original squared divisor mask.

`SquarefreeCounting.finiteCount_eq_floor_sum` proves exact inclusion and
exclusion for square divisibility, including primes shared with a mark.
`finiteCount_sub_density_eq` subtracts the corresponding signed rational
density, leaving the full signed sum of integer-quotient remainders.

The density of the complete marked squarefree sequence is defined as
the infimum of its decreasing finite sieve densities. Theorems
`finiteDensity_tendsto` and `count_div_tendsto` identify it with both the
finite-sieve limit and the actual asymptotic counting density. This slice
does not identify it with a closed Euler-product expression.

The rough marked density keeps the signed sum over all subsets of `S`.
The full density `delta` then retains the entire ordered matrix

```text
delta = sum_(d,e<=D) w(d) v(e) markedDensity(S,lcm(d,e)).
```

`RoughSquarefreeCounting.familyCount_centered_eq` preserves the exact
centered matrix before any norm is taken. Impossible squarefree marks
and marks divisible by an excluded prime vanish in the original count
and its density.

## Uniform estimates

For every fixed real `sigma` with `1/2 < sigma <= 1`, every prime set
`S` contained in the primes through `R`, and every pair of complex
families with `norm(w(d)), norm(v(d)) <= 1` through `D`, the theorem
`familyCount_centered_bound` proves

```text
norm(sum_(1<=n<=X) c(n) - delta*X)
  <= C_sigma * D * exp(4*sqrt(R)) * X^sigma.
```

Here `X` is a natural number and the explicitly defined positive
`C_sigma = familyCountingCost sigma` is independent of `X,D,R,S,w,v`.
The useful asymptotic range is `1/2 < sigma < 1`.

For all natural endpoints `A <= B`, `familyInterval_centered_bound`
proves

```text
norm(sum_(A<n<=B) c(n) - delta*(B-A))
  <= C_sigma * D * exp(4*sqrt(R)) * (B^sigma + A^sigma).
```

The linear divisor cost uses the existing factor-sensitive lcm estimate.
It does not pay separately for all `D^2` pairs. The preceding theorem
`familyCount_centered_lcm_bound` also retains the full weighted lcm
budget for arbitrary finite divisor sets and arbitrary complex weights.

The square-sieve error is uniform over all finite square exclusions,
so its limit removes every prime square. The estimate uses the
small-argument floor remainder, not just its bound by one. No prime
number theorem, RH hypothesis, or unknown cancellation estimate is
used to prove these counting bounds.

## Meaning for the remaining tail

The [actual-prime window audit](../../research-audits/prime-phase-window-evidence-2026-09-11/README.md)
showed why complete signed moment decay does not give a source-scale
norm bound on every raw interval. The present theorems establish a
centered interval estimate for the complete squarefree matrix instead.

This is not yet the centered Type II estimate for the ordinary-prime
error. The arbitrary coefficients here weight the bounded divisor
families; a bilinear factor-variable estimate has additional quantifiers.
Removing ordinary primes from this controlled complete sequence still
exposes the unresolved prime tail. No new zero-free region or RH proof
follows from this counting slice alone.

## Local verification

The two modules are imported by the root library. Local verification
includes strict direct compilation, focused and full builds, declaration
lint, terminal-theorem axiom checks, the compiled-environment status
audit, and source and whitespace scans. Remote CI is checked separately on the exact commit.
