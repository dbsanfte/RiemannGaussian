# A signed allocation saving for the whole matching floor

The independent `-79/1000-o(1)` floor is still **open**. The new result pays
one error component geometrically across counts and radial periods: the
owner-allocation mismatch in an admissible, negatively oriented pair. It
does not prove native partner coverage or bound the remaining joined pair
gaps and signed unmatched population.

The proofs are in
[`ZetaRieszOwnerPairFloor.lean`](../RiemannGaussian/ZetaRieszOwnerPairFloor.lean).
They keep the original residual coefficient, factorial kernel, complex
phase and signed funding multipliers. No completed carrier replaces them.

## Why the allocation change should stay signed

Write the owner weight at cofactor share `x` as

```
A_N(x) = 1 - sum_(N/5+2 <= k <= 13N/32) mass(N+1,k,x).
```

This is the exact original integer order interval. Its upper cumulative
mass is decreasing in `x`. Its lower cumulative mass is small throughout
the remaining owner geometry:

```
lowerMass(N+1,N/5+1,x) <= 2 exp(-N/25),     3/8 <= x <= 1.
A_N(x) <= A_N(x') + 2 exp(-N/25),           x <= x' <= 1.
```

The first inequality uses a rational binomial tilt `1/2`, not a numerical
tail calculation. `remaining_owner_share_gt` proves that every squarefree
count3+ core label left by the existing `60069/100000` owner crop has
cofactor share greater than `3/8`. This is not a new restriction on that
remaining population.

For the original unallocated weighted complex atoms `F,G`, assume
`Re F <= 0` and the stated share ordering. Joining before pricing gives

```
Re(A_N(x) F + A_N(x') G)
  >= -norm(F+G) - 2 exp(-N/25) norm(F).
```

Increasing the weight on the opposite-parity partner can be favorable.
Pricing `abs(A_N(x')-A_N(x))` would throw away that direction. The theorem
instead charges only the lower tail. Both original signed funding
coefficients stay in `F,G`; their difference is not assumed small.

## One global exponential price

Let `D` be any finite set of original labels, `norm(w(n)) <= B`, `L>0`
and `0 <= u <= 10001/20000`. Independently of the height, counts and radial
periods, `total_lower_tail_price` proves

```
u^(N+1) 2 exp(-N/25)
  sum_(n in D) norm(w(n) coefficient(L,n) K_N(3/2+i*y,n))
 <= 2 radiusCeiling B exp(-N/50) M(1+1/262144).
```

Here `M` is the existing finite Möbius-log majorant mass. Its value is not
numerically evaluated. The exponential rate beats source growth at the
full requested radius; every fixed polynomial envelope is also allowed.

For the **same original funded ledger**, the population weights are

```
1_H + a*1_P + b*1_T - (tailCost + epsilon + growingDebit)*1_Y.
```

All overlaps remain. With `0 <= a,b <= 1` and fixed `epsilon`, their
norms are eventually bounded by `4+abs(epsilon)`.
`tendsto_funded_lower_tail_price` then proves decay of the actual total
funded lower-tail cost, allowing moving masks, cutoffs and heights. This
does not infer an absolute supply-charge bound from a relative debit.

## The lower inequality for the original carrier

`matching_original_floor` applies to a disjoint matching `E` on the
original supported labels `S`. Each matched label must be squarefree,
count3+, in the original literal window, and have its eligible canonical
owner. Pair orientation and ordered cofactor shares are explicit.

It proves, schematically,

```
u^(N+1) Re(sum_(n in S) originalWeightedAtom(n))
 >= -u^(N+1) sum_(e in E) norm(F(e.1)+F(e.2))
    - C_B exp(-N/50)
    - B*existingNonownerError(N)
    + u^(N+1) Re(sum_(n in S \ matchedVertices(E)) originalWeightedAtom(n)).
```

The existing nonowner payment is used once on matched labels. Unmatched
labels retain their **original** residual coefficient and signed weights.
There is no separate divisor-count allowance or absolute allocation
variation. The native matching and the numerical bound on its joined
pair gaps are not assumed proved by this inequality.

## What many bins do and do not provide

An actual insertion `p -> p'*r` with `p'<=p` increases the cofactor share.
If `log r<=binHead(N)`, `small_insertion_bins_eq` proves that every occupied
cofactor bin is unchanged. This makes small-prime insertion compatible
with the many-bin condition at the bin level. `manybin_owner_eligible`
also proves that any occupied cofactor bin puts the canonical owner of
an original central label in the original allocation's prime set.
Canonical ownership after insertion,
squarefreeness, inner-hinge inequalities, count limits, funding and native
support still have to hold for each pair.

The current whole core has an upper physical prime cutoff. The `N^2`
threshold controls allocation eligibility; it does **not** forbid every
small cofactor prime. The old fixed parity packet had an additional
all-leg rough-prime mask. The previous probe note conflated these scopes;
that note and its scope flags are corrected.

Bin occupancy is not a weighted dispersion estimate. The existing
coherence and rate audits remain valid. To finish the floor with this
principle, the remaining tasks are:

1. Prove enough supported, disjoint opposite-parity partners at the native
   growing counts, with the required negative-first orientation.
2. Bound their total joined **unallocated** mismatch with the actual
   phases and original funding retained.
3. Bound the signed unmatched and supply contribution in the same ledger.

Only the allocation-tail error in this list's matching mechanism is now
paid. No new whole population, fixed power saving for the full carrier,
floor, ceiling or zero exclusion is claimed.

## Numerical regression and local checks

The optional probe runs with

```
../.venv/bin/python scripts/probe_riesz_owner_pair_floor.py \
  --output .lake/riesz-owner-pair-probe.json
```

It retains rounded native moving length, allocation, full phase and
original signed multipliers on finite count4/5 through12/13 labels.
There are 70 negative-first test cases. Every equal-funding owner pair
tested has nonnegative real part. Unequal funding remains an obstruction.
Tiny raw differences at high orders can lie below the 120-digit numerical
resolution; no floating residual is an interval certificate. These samples
do not certify the native count56+ many-bin population or dyadic/funding
coverage. The script is not in the ordinary build or CI.

All twenty public proofs receive focused warning-as-error Lean, targeted
build, working root-import, fourteen namespace-linter and transitive
standard-axiom checks. See
[`riesz-owner-pair-floor-audit.json`](riesz-owner-pair-floor-audit.json) for
the exact validation results. Wider publication checks, commits, generated
assets and public explorer/README changes remain deferred.
