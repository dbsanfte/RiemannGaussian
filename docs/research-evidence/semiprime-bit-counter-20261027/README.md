# Actual bit arithmetic and native counter heights

Status: **PROGRESS; the uniform guaranteed factoring bit-time theorem is still
open.** This packet extends the shared-summary route obtained from the ETH paper.
It does not improve the older native long-residue query's soft-K^(5/4) bound.

The source Lean proof of fixed-width SAT/counting was already independently
checked at its pinned endpoint and dependency closure. It is a foundation for
this work, not a theorem that automatically supplies growing-scope tensor
contraction or factoring. The relevant source is
[the fixed-width primitive-machine theorem](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean).

## What is proved in this slice

- Actual rational bit operations now perform reduction, exact division and
  copying; their cubic width bound includes unreduced intermediates. Dot products
  derive every intermediate fit from common-denominator representations.
- The actual constructed rows supply height bounds for corrected local inputs,
  full Taylor packets, signed partial accumulators, group/fibre prefixes, local
  truth subtotals and partially formed interpolation leaves. These bounds do not
  rely on cancellation in the final count.
- The Hermite backend constructs its cardinal arrays and cardinal-at-zero values,
  performs cached inversion/quotient evaluation, and sums actual node reports.
  All nodes share a proved denominator; prefixes have explicit polynomial bit
  bounds. Acquiring the input packet arrays remains separate.
- Actual bit checkers now evaluate every original and equality vertex of the
  public multiplication graph, with a proved polynomial backend clock. A separate
  constructive preparation argument pays public descriptors, gathers, syntax,
  allocation and flat-tape access.
- The scheduled source-constructed public counter now counts exactly the ordinary
  ordered nontrivial factor pairs of N whenever the source-layout guard holds.
  This supplies the semantic composition without a count or coverage oracle.

These are whole-family statements with explicit hypotheses. Small execution
controls are diagnostics only. None is presented as a complete factoring
runtime theorem.

## Complete runtime candidate and review

The [candidate composition](full-bit-composition-candidate.md) retains the
previous operation envelope

`poly(n) * Cq * Y * 2^h * 2^w`,

where n is the public Boolean edge count, Cq the bounded signed-support menu,
Y the summary box, h the largest head group and w the largest local scope.
The actual graph has n=Theta(L), w=O(L^(3/4)), L=bitLength(N). The scheduled
nonpolynomial factors give `2^O(L*(loglog L)^2/sqrt(log L))`, hence a candidate
`N^o(1)` bound if the complete execution correspondences are closed.

The [independent adversarial audit](full-bit-independent-audit.md) corrected the height claim for partial
sorted-pivot Gaussian scratch rows: they need a larger polynomial bound than
completed basis rows. It also made the local truth-leaf l1 bound explicit.
Neither correction changes the candidate exponent. The reference implementation
streams summaries and fibre scans and retains polynomial state; no full fibre
or signature table is assumed.

The remaining issue is execution composition: explicit finite enumeration and
row construction, the actual acquired H arrays and their prefixes, primitive
rational/control/storage operations, and all-input fallback/recovery must be
joined in one proved execution. The detailed [frontier](research-frontier.md)
sets the next acceptance condition. An arithmetic ledger or a collection of
component clocks does not satisfy it.

## Evidence

The packet contains eleven new Lean modules, independent strict compilations,
ordinary-root scoped 15-linter checks, and transitive axiom checks for every
generated declaration. The exact counts and source/object hashes are in
`verification.json`; `manifest.json` seals the archived files. No proof
placeholders, native decision shortcuts, or custom axioms are admitted.

Independent reports cover [rational operations](review-rational-dot-bits.md),
[Hermite reconstruction](review-hermite-array.md), [public counting and native
height expressions](review-public-count-heights.md), and [actual entry
evaluation](review-entry-bits.md). Existing sources/evidence and concurrent work
are preserved. No commit or push was performed in this slice.
