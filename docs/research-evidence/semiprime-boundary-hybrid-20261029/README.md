# Acquired boundary hybrid, 2026-10-29

The original-binary factoring program now executes the deterministic boundary
partition and sorted-record contraction described in the supplied research
note. The new recursion returns exactly the previous complete coefficient words
and factor bytes. Its leaf report has a uniform leading exponent of one half
on the original scheduled family. The complete primitive-machine bit-time
theorem remains open.

This work starts after publication commit
[`07968f5ea0bff8caf39973599280e6321211c682`](https://github.com/dbsanfte/RiemannGaussian/commit/07968f5ea0bff8caf39973599280e6321211c682)
was pushed. The [supplied note](source-note/RESEARCH.txt), prototype, validation
and eighteen original source pins are preserved exactly by the
[source-note manifest](source-note-manifest.json). The prior
[publication packet](../semiprime-publication-20261029/) is unchanged.

## Installed algorithm and checked gains

The entry is [`SemiprimeD1HybridAlgorithm.factor`](../../../RiemannGaussian/SemiprimeD1HybridAlgorithm.lean).
Each public prefix acquires its original root and uses the closed hybrid
recursion. Both inactive and exhausted-fuel calls execute the checked boundary
leaf. Its validity scan is paid; malformed inputs use the paid previous leaf.
The fast path acquires its own colouring and reads the literal local tables.
Full jets, isolated scalar vertices, repeated parallel incidences and precision
zero are retained.

For a loopless occurrence graph with `M` edges and maximum degree `Delta`, Lean
proves the actual acquired width satisfies

```math
W\le (1/2+1/K)M+\sqrt{(2K-1)M\Delta/2}
 \le M/2+3(M^2\Delta)^{1/3}.
```

The colour count comes from the executable first-success integer cube test.
The conditional expectation enumerates at most four endpoint colours per term;
its polynomial acquisition bound includes every vertex, candidate and ordered
edge pair. Disjoint-edge covariance cancels exactly. Diagonal and parallel
occurrences remain in the shared-endpoint bound.

The actual sequential record sort, forward join, full-jet multiplication and
equal-key reduction have one exponential record factor. A fixed polynomial in
the original graph dimensions and complete current coefficient context bounds
the entire native retained leaf report by `P * (2^W + 1)`. Canonical input table
storage is acquired once and absorbed using the actual incident-width bound.
No free lookup or product of two exponentially large catalogues is assumed.

Writing `L = s / sqrt(logarithm s)`, the scheduled original family satisfies,
for every fixed positive `epsilon` and sufficiently large original scale,

```math
\mathrm{leafReport}\le 2^{(1/2+\epsilon)L}.
```

The threshold is uniform over that family. A manually truncated zero-fuel root
need not be a scheduled small leaf; the zero-fuel rate theorem retains the
original depth/fuel condition. Correctness holds for arbitrary supplied fuel.

The independent recursion analysis uses the actual factor-sixteen child shrink
and the geometric sum `8/7`. Its leading natural-exponential call-count
coefficient is `393216/7`, exactly `4/7` of the former `98304`. This tightens an
upper bound on the same executed tree. The whole-report cubic call reserve is
retained; this ratio is not a claimed runtime speedup or a stronger asymptotic
factoring class.

## Proof interfaces

- [`BoundaryLeafValue`](../../../RiemannGaussian/SemiprimeD1BoundaryLeafValue.lean):
  actual acquired boundary semantics and exact canonical bytes; the checked
  wrapper needs positive axes alone.
- [`HybridCorrectness`](../../../RiemannGaussian/SemiprimeD1HybridCorrectness.lean):
  exact recursive words, original prefix counts and complete binary factor
  output for every semiprime, including squares.
- [`BoundaryWidth`](../../../RiemannGaussian/SemiprimeD1BoundaryWidth.lean) and
  [`PartitionWidthRate`](../../../RiemannGaussian/SemiprimeD1BoundaryPartitionWidthRate.lean):
  closed averaging, variance, mean and acquired cube-root width bounds.
- [`BoundaryLeafPolynomial`](../../../RiemannGaussian/SemiprimeD1BoundaryLeafPolynomial.lean)
  and [`BoundaryLeafOriginalRate`](../../../RiemannGaussian/SemiprimeD1BoundaryLeafOriginalRate.lean):
  actual native report, fixed polynomial domination and original-family leaf rate.
- [`PartitionReachRate`](../../../RiemannGaussian/SemiprimeD1BoundaryPartitionReachRate.lean):
  actual reached stopped calls and scheduled fuel exhaustion, including empty
  graphs.
- [`HybridRecursiveCounter`](../../../RiemannGaussian/SemiprimeD1HybridRecursiveCounter.lean)
  and [`HybridPublicReport`](../../../RiemannGaussian/SemiprimeD1HybridPublicReport.lean):
  the changed program's own additive child reports, actual chronological prefix
  queries, unchanged physical decoder and explicit report composition.
- [`HybridOriginalCounterBudget`](../../../RiemannGaussian/SemiprimeD1HybridOriginalCounterBudget.lean)
  and [`HybridOriginalRate`](../../../RiemannGaussian/SemiprimeD1HybridOriginalRate.lean):
  a closed budget for the changed recursive counter and its actual public
  retained report, with fixed constants before all original inputs. The
  whole-counter reserve remains conservative; the sharper half-leaf rate is
  proved separately.
- [`HybridCallReport`](../../../RiemannGaussian/SemiprimeD1HybridCallReport.lean):
  tighter call analysis and its original **WordTape** report endpoint. Its
  existing public-rate theorem must not be relabelled as a theorem about the
  changed hybrid's clock.

## Validation and scope

Focused warning-as-error Lean compilation, complete scoped declaration linting
and transitive-axiom audits cover the new modules. Exact executable comparisons
exercise full mixed jets, zero precision, empty/isolated/parallel networks,
malformed fallback, and both recursive stopping cases with their own clock
formulas. The [independent review](independent-integration-review.md) records
exact reviewed hashes and the distinction between native reports and primitive
machine time. The complementary
[public-rate review](new-public-rate-independent-review.md) checks the changed
whole-program report joins. [Focused records](focused-validation/manifest.json)
retain their source versions; the
[combined Lean checkpoint](combined-lean-checkpoint.json) records the fresh
ordinary build, whole-project lint and compiled environment audit. All 26
[local publication gates](fresh-publication/validation.json) passed, including
actual browser/rendering checks. Commit-hook and exact-SHA remote CI/Pages
outcomes remain separate until complete; the inventory refresh itself never
runs Lean.

The target remains deterministic factoring of every original binary semiprime
within `2^(C*ell/sqrt(log(ell+2))) * (ell+1)^d`, with fixed constants before the
input. This packet improves and installs its native algorithm. Full source,
control, memory, addressing and report-erasure lowering to one primitive bit
machine remains a separate open theorem. No stronger complexity class or new
factoring record is claimed.
