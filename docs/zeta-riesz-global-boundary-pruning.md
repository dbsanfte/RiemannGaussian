# All balanced completion-mask failures are now paid together

The completed bulk theorem left a joined boundary consisting of ordinary
primes, semiprimes, rejected count/owner/physical/deletion labels, and the
same signed head. `ZetaRieszGlobalBoundaryPruning` independently pays the
ENTIRE balanced part of those rejected labels by one geometric bound.
It does not estimate the remaining raw high owners or prime terms.

## Exact zero and full-population count saving

The current central window is `1.971N < log n <= 2.029N`. The native moving
length eventually satisfies `L >= 5N/4`, so every central label is below
`X^2`, where `X=(linearDampedCutoff u N+2)^2` and `L=log X` exactly.

If a prime divisor `p` fails the upper physical mask, `p>=X`. The existing
`nonzero_extreme_below_square_is_semiprime` theorem then forces any nonzero
original coefficient to have total prime count at most two. Therefore the
completed coefficient is **exactly zero** for every such squarefree central
label of count at least three. This is not a small-prime/phase estimate.
Ordinary primes and semiprimes keep their nonzero completion boundaries.

Next suppose all primes obey the physical bound and

```text
omega(n) < countCeiling(j),
log(largestPrime n) < 51N/50.
```

The existing `window_mem_originalMask` theorem places the label in every
original deletion mask. Its owner logarithm is too small for either the
cancelling-sector share `>=21/32` or the dominant-prime share `>=13/20`.
Thus `balanced_mem_native_central` proves actual membership in the EXACT
native central population, not a replacement rough-label population.

Consequently every rejected balanced label below the count ceiling is
an exact zero. Every remaining rejected balanced label has high count.
`eventually_balanced_failures_bound` applies the existing arbitrary-support
high-count theorem directly to those literal failures. It gives, uniformly
in all heights,

```text
norm(sourceScaled completed sum over ALL balanced failures)
 <= (203/50)*radiusCeiling*(N+1)*exp(-N/10000000)
 -> 0.
```

The eventual count theorem has an unevaluated start, including `j>=1024`;
no finite native threshold or small constant is asserted. The new payment
is for the COMPLETION count tail. It does not reuse a previously funded
native count difference as a free credit, or delete orders zero and one.

## Spent in the same whole signed floor ledger

Define `rawHighLabels` to contain **every** squarefree central label of
count at least three with `log(largestPrime n)>=51N/50`. All prime counts
and all original unallocated coefficients remain. The set has no physical,
count, deletion, nondominant or old allocation restriction. Physical
failures may remain as exact zero slots. This set is independent of `u`;
its coefficients and moving length still depend on `u`.

It is a literal subset of the rejected population, because the native
central labels have the opposite strict owner condition. The checked
finite difference is exactly the balanced failures:

```text
joinedBoundary - prunedBoundary = completed sum over balancedFailures,
prunedBoundary = P1 + P2 + rawHigh + SAME full head.
```

Every physical/deletion/count failure of the balanced population has thus
been paid jointly. `eventually_native_pruned_bound` spends the payment in
the actual native carrier:

```text
abs(nativeScaledCore.re + prunedBoundary.re)
 <= nativeBoundaryBudget + countAllowance
 -> 0.
```

The resulting independent one-sided inequality is

```text
nativeScaledCore.re >= -prunedBoundary.re - nativePrunedBudget.
```

There are no residual unestimated balanced mask failures in this formula.
Raw high-owner labels retain their full original coefficient; the old
allocated high-owner theorem does not pay them. The head retains its
original `1.95..2.03` radial support. Prime and semiprime terms retain the
contracted central support. No cofactor completion or independent phase
replacement is performed.

The remaining floor task is the independent signed aggregate upper bound
`prunedBoundary.re <= 399/5000+o(1)`. The raw high-owner response, ordinary
prime response, semiprime response and unchanged head must still be
controlled together. None is declared small. The whole floor, ceiling
`42/25`, restricted contradiction, zero exclusion and RH remain open.

## Exact-divisor numerical diagnostic

The optional `probe_riesz_global_boundary_pruning.py` uses the actual
native order `N=256`, rational floor cutoff, squared physical threshold
and corresponding length. It constructs central squarefree labels of
counts 3 through 12 with a prime just beyond that physical threshold.
Every divisor cutoff is tested using integers. The Riesz response is
represented as an integer linear combination of `log X` and individual
prime logs, before inserting the phase or taking a norm. All ten classes
have identically zero log profiles. Semiprime and ordinary-prime controls
inside the central window retain the respective responses `log q` and
`log X`. The original ordinary-prime coefficient is deleted; its restored
completed coefficient is kept.

These are exploratory SymPy primes, not Lean primality certificates. The
probe does not assert low-count native membership at this early dyadic
order, invoke an eventual count budget there, or certify a floor. The
universal statements and exact masks are proved in Lean. The probe remains
outside builds/CI, with earlier toy and negative audits preserved.

Focused validation: strict leaf, targeted build, frozen compiled ordinary
root with explicit leaf, all14 namespace linters and transitive standard-
axiom checks on every compiled declaration. No root registration, public
endpoint changes, wider checks, subagents, commits or pushes are performed.
