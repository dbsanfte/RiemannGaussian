# Explicit joint prime-period costs

The actual prime sums now have a numerical cancellation bound that is uniform
in the number of cofactor primes and the position of a complete radial period.
Both the independent whole `-79/1000` floor and `3/2` ceiling remain open.

Write `a` for the lowest prime logarithm and `H_X = sum_{p<=X} 1/p` for the
literal reciprocal prime mass. For `a >= 5000` and `|y| >= 54`, Lean proves

```text
|sum_{exp(a)<p<=exp(a+2*pi/|y|)} cos(y*(log p+c))/p| <= 4/a^2.
```

If the period is centered at a cosine extremum, its first signed moment
with the additional factor `log p-a-pi/|y|` is at most `1/a^2`. These are
bounds for ordinary primes, with exact natural floors at both endpoints.
There is no prime-error hypothesis or hypothetical-zero assumption.

The proof uses the existing checked estimate
`|theta(exp t)-exp t| <= (41/100)*exp(t)/t` for `t >= 5000`.
Finite Abel summation keeps the signed smooth integral and both endpoints
before bounding the error. It does not assert a source-scale PNT transport
for the former parity packet.

## Correlated weights and clipped intervals

More generally, let `F` have a continuous derivative `G`, with `|F|<=W`
and `|G|<=V` on the total-log interval `[a+c,b+c]`. The proved inequality is

```text
|sum_p F(log p+c)/p - integral_[a+c,b+c] F(t) dt / a|
 <= [W*(b-a)^2 + (41/100)*(2W+(V+2W)*(b-a))]/a^2.
```

This retains the full profile in the integral. In particular, a common
total-log profile gives a common signed numerator across cofactor labels;
its reciprocal prime logarithm is exactly the type of correlated weight
handled by the preceding owner/density estimates.

For a clipped cosine interval the numerator is explicitly
`[sin(y*(b+c))-sin(y*(a+c))]/y`. It is not set to zero. Consequently a
complete-period bound cannot be reused after deleting already-paid sectors
inside the period. Every resulting hole still has its endpoint contribution.

## Every cofactor count, together

Let `S` be any squarefree subset of `M<n<=2M`, let `|w(n)|<=W/n`, and let
the lower prime logarithm `a(n)` dominate every prime-factor logarithm of
`n`. Actual prime incidence counting gives

```text
sum_S |w(n)|/a(n)^2 <= 2W*(H_(2M)^2+H_(2M))/log(M)^2.
```

Combining this with the complete-period estimate gives

```text
|sum_n w(n) * sum_p cos(y*(log p+log n))/p|
 <= 8W*(H_(2M)^2+H_(2M))/log(M)^2.
```

The cofactor phase and arbitrary signed cofactor weights remain. No maximum
prime count or exponential count-dependent constant is used. Every constant
displayed here is numerical; the preceding mean-bound constant `E_h` does
not enter this particular estimate. The already-proved logarithmic bound
for `H_X` makes the cost `O(W*(log log M)^2/log(M)^2)`.

An arbitrary finite family of radial periods obeys the same inequality with
`sum_j W_j` in place of `W`. Their actual amplitude budgets still have to be
bounded. This does not replace that sum by a source-small quantity.

## What is still unpaid

The terminal all-count estimate has cofactor weights constant within each
prime period. The literal carrier also contains a prime-dependent factorial
weight, original allocation, both Riesz cutoffs and paid-sector exclusions.
The smooth-profile theorem retains such a profile when its differentiability
and numerical variation bounds have been proved; it does not discharge
them automatically, and a Riesz hinge requires its boundary treatment.

The next quantitative task is to bound those literal weighted moments and
their matching signed cutoff correction together, preserving every paid
sector. Neither a new zero exclusion nor a whole-carrier bound is claimed.

## Verification and diagnostic

The proof is in
[`ZetaRieszQuantitativePrimePeriod.lean`](../RiemannGaussian/ZetaRieszQuantitativePrimePeriod.lean).
The corresponding record is
[`riesz-quantitative-prime-period-audit.json`](riesz-quantitative-prime-period-audit.json).

`scripts/probe_riesz_prime_period_cost.py` is an optional floating-point
experiment with literal primes below twelve million. Those primes are
**below the rigorous logarithmic starting point 5000**. It illustrates the
signed zeroth/first moments and the importance of clipped endpoint terms;
it does not validate the theorem's large-range start or certify a carrier
estimate. It is not run by ordinary CI.
