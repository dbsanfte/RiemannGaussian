# Executed knot fusion and factor-correlated coverage

26 October 2026. The guaranteed classical all-semiprime sixth-exponent
goal remains active and open. This pass produces exact finite identities
and a safe arithmetic interval filter. **It does not improve the acquisition
exponent.** The current native query still costs
`soft O(k + sqrt(k m)) = soft O(k^(5/4))` at `m = Theta(k^(3/2))`,
where `k = Theta(N^(1/6))`. This is the bound for this particular route,
not a claim to improve the known general deterministic fifth-exponent bound.

## What was executed

- [Fermionic fusion](fermionic-fusion.md): the acquired knot norm becomes a
  polynomial domain-wall partition function with certified unit extra
  factors. No roots of an unknown polynomial are requested: the supplied
  roots are the recentered native rows. A direct two-channel calculation
  retains the exact fusion correction. Conditional on a collision, that
  correction vanishes even when the projected channel and pivot are units.
  Discarding it is therefore not a valid algebraic simplification. This is
  a test of the specified transfer, not an attained catalogue example or a
  theorem excluding all knot fusion. [Independent review](fermionic-review.md).
- [Finite Racah transform](bispectral-fusion.md): an explicit self-dual
  parameter choice has unit denominators and an invertible finite transform
  on its legal grid. Clearing its terminal singularity gives exactly
  `T_m(qX) = q^m (q^(m+3);q)_m C_m(X+q/X)`.
  The scalar prefactor is cheaply computable; the remaining factor is the
  original long kernel. A legal endpoint formula is derived, but its
  off-grid initialization is not acquired. [Independent review](bispectral-review.md).
- [Factor-correlated cover](factor-correlated-cover.md): an adaptation of
  Lenstra's Euclidean construction acquires soft(k) descriptors directly
  from `PQ=N`, with explicit conic phases and common-index swapped rows.
  This avoids independent factor-size bins. Its literal interval list
  nevertheless has total width `Omega(k^(5/2))`, even under integer clock
  reanchoring and label deduplication.
- [Safe discriminant filter](first-odd-filter-addendum.md): the exact
  inequality `(AP+BQ)^2 >= 4ABN` shortens odd-stage intervals in soft(k)
  acquisition work and preserves coverage. The filtered first-odd widths
  are `mu0*(1-sqrt(g/k))^2 + O(1)`, with `mu0=sqrt(N/k^3)`.
  A positive fraction of tags still has width `Theta(k^(3/2))`.
  This is a constant-factor improvement, not a rate improvement.
  [Independent arithmetic review](factor-cover-review.md).

[Additional literature screening](literature-triage.md) records the recent
arborescent TQFT implementation and the periodic-knot papers, including the
hypotheses still missing from a native application. Previously audited
cyclic-resultant results are identified as prior work.

## The concrete remaining work

The fusion route needs an initialized evaluation of its retained correction
over the acquired root family, preserving zeros and costing
`soft O(L + sqrt(m))`. A small auxiliary module alone does not pay for its
scalar amplitude.

The arithmetic alternative now has explicit integer conics

    w^2 = D0 + 2*tau*z + k^2*z^2

over a softly linear list of acquired intervals. A sufficient advance is
to find a valid factor-producing square point in soft(k) total work, or to
acquire a coverage-preserving selection with total interval width soft(k^2).
The current batch evaluator would then cost soft(k). Checking every
candidate for squareness does not meet that bound. The existence of only
two proper prime factors is not by itself an algorithm for finding the
corresponding points.

## Validation and scope

The reports were checked against primary formulas and independently reviewed
for finite-ring legality, normalization, coverage and paid costs. The root
review also rederived the Euclidean phase and checked Lenstra's actual
sign-change lemma. The recentered-root and conditional-collision wording
corrections are incorporated in the archived fermionic report. The Racah
report includes the review's scaled-variable/terminal-recurrence caveat.

This is paper research, not a new Lean theorem or an implemented faster
factoring algorithm. No numerical campaign, generated-asset rebuild,
commit or push was performed. Prior evidence and the existing journal and
agent-guide prefixes are preserved; validation details and file hashes are
recorded in `review.json` and `manifest.json`.
