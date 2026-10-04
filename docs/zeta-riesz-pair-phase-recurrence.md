# Genuine-prime phase recurrence: the height and order limits differ

This pass supplies **no arithmetic floor saving**. The independent target
is still the cofinal fixed-height bound
`Re prefixPairDefect <=399/5000+o(1)`. The result rules out a uniform
relative phase contraction at a fixed order; it does not refute that target.

The leaf is
[`ZetaRieszPairPhaseRecurrence.lean`](../RiemannGaussian/ZetaRieszPairPhaseRecurrence.lean).
It preserves the existing evaluator, actual ordinary primes, signed
central/successor/logged/trace combination, integer cutoffs and moving length.
No selected-zero hypothesis, prime-density approximation or new carrier is
introduced.

## Exact recurrence, including the complete prime population

Lean proves there is one integer sequence `H(n) -> infinity` such that

\[
\exp(-iH(n)\log m)\longrightarrow1
\quad\text{for every fixed integer }m.
\]

The proof takes a convergent subsequence of square-indexed points in the
countable compact unit torus. Differences of consecutive square indices
are unbounded, and their phase ratios converge to one. This does not require
linear independence of prime logarithms and is not merely a sampled-prime
counterexample.

At each fixed factorial order, the ordinary-prime series is absolutely
convergent. Tannery's theorem therefore passes this pointwise recurrence to
the **entire** ordinary-prime moment. Write `Q_N(u,y)` for the existing
`harmonicEvaluation (ordinaryArray u y) u N`, with all its original slots.
Then the same recurrence sequence gives

\[
Q_N(u,y+H(n))\longrightarrow Q_N(u,y)
\quad\text{for every fixed }N,u,y.
\]

`exists_arbitrarily_high_joined_approx` and
`arbitrarily_high_joined_signed_lower` consequently prove

\[
\forall\varepsilon>0\ \forall Y\ \exists h\ge Y:
\qquad\Re Q_N(u,h)>\Re Q_N(u,y)-\varepsilon.
\]

If the starting real value is positive, `not_uniform_joined_relative_contraction`
rules out every strict multiplicative contraction uniformly above a height
threshold at this fixed order. It does **not** assert that the starting value
is positive at every order, or exceeds `399/5000`.

The existing `finitePrefixPairDefect` also recurs exactly. That is the finite
whole symmetric pair evaluator. We do not infer recurrence of the literal
height-dependent complete-period mask from it, nor apply separate complete-leg
limits to a hard-share projection. No completion budget is spent anew.

## Independent numerical regression on genuine primes

The optional probe reads eight frozen FLINT-proved primes from
`1536-balanced-731`; it reruns no primality search or old detector.
LLL constructs a height with `log(height) ~=4501.04075` and certifies its
integer lattice relations exactly. The prime phases are within
`1.486e-244` of one.

All 28 distinct unordered pairs retain the exact moving length and binomial
factorial prefixes. Their joined prefix-minus-Selberg coefficients are
positive. The pairs lie strictly inside the original radial window with a
unit margin, have balanced log shares and primes above the stronger
polynomial rough threshold. The unit margin also funds complete-period
membership by the existing geometric theorem. This is not an audit of an
entire growing prime population.

The signed finite response returns to its zero-height value with relative
error `1.372e-244`. That zero-height source-scaled value is only
`1.2724e-1321`: this population is **not** a counterexample to the floor
constant and supplies no positive or negative cofinal credit. Its order
1536 is below the formal payment threshold 65536.

The independent checker imports no producer. It evaluates the giant-height
phases directly, replays every integer lattice relation, and computes the
product phase again from the literal product logarithm. It then reconstructs
the original four factorial slots and **one** whole square correction.
Their relative discrepancy from the direct unordered pair sum is below
`3.23e-349`. The stored Arb balls are checked against higher-precision
mpmath values; these numerical checks are not Lean certificates.

```bash
../.venv/bin/python scripts/probe_riesz_pair_phase_recurrence.py \
  --output .lake/riesz-pair-phase-recurrence/scan.json
../.venv/bin/python scripts/check_riesz_pair_phase_recurrence.py \
  --input .lake/riesz-pair-phase-recurrence/scan.json \
  --output .lake/riesz-pair-phase-recurrence/validation.json
```

## Consequence for the floor investigation

The required order limit is **at a fixed height**. The recurrence theorem
instead changes height with the chosen finite population/order. These limits
cannot be interchanged. In particular, this result neither contradicts the
fixed-height cofinal target nor proves that its literal support is paid.

Do not promote finite phase features, primality or a favorable phase sample
to a height-uniform contraction. Numerical discovery must keep the fixed
height while increasing the genuinely covered prime/order population, or
derive an exact arithmetic identity valid before such limits. The earlier
source-resolution audit still governs population error and source units.

The focused leaf build, namespace lint and transitive axiom audit pass with
only standard axioms. The leaf is not root-registered. Prior proof/probe
snapshots and concurrent semiprime work remain unchanged; wider gates,
commits and pushes are not part of this slice. The `399/5000` estimate and
zero exclusion remain open.
