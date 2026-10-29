# Exact all-prefix sixteen-feature incidence histogram

NEW canonical `SemiprimeSourceIncidenceHistogram.lean` proves the original padded incidence sum equals a scalar derived from sixteen sparse histograms of the actual port list. It does not assume a matrix, histogram answer, full pair tensor, count oracle, normalization, or canonical prefix phase. Existing sources and previous scratch origins were not edited.

## Pointwise features

For a positive complete-menu size L and actual remaining keys A, write P(a,c) for the existing conditional whole-word equality probability. The module defines a scaled kernel K=L P. It has value L on a repeated key, 1 on a distinct pair with any free endpoint, and L times the actual fixed-word equality indicator otherwise.

For each key a there are four features:

| f | coefficient | per-key mask | equality key |
|---|---:|---|---|
| 0 | 1 | 1 | constant |
| 1 | L−1 | a free | actual variable key a |
| 2 | L | a fixed | actual fixed whole-word label |
| 3 | −1 | a fixed | constant |

`kernel_expansion` proves pointwise

```
K(a,c)=Σf coefficient(f) * [key_f(a)=key_f(c)] * mask_f(a)*mask_f(c).
```

The diagonal feature is keyed by the actual variable, not its colour; this preserves aliases, loops and parallel ports. In a fixed loop the constant and negative correction cancel, leaving L. In a free loop the first two terms total L. Distinct free pairs have only the constant term; distinct fixed pairs have their actual whole-word bucket term. These statements do not depend on canonical prefix order.

`kernel_potential` ties K to the previously proved actual conditional potential, with only known positive integer L cleared. The signed coefficient −1 is retained honestly; it is not discarded under a positivity heuristic.

## Joint sparse grouping

For arbitrary actual port list xs and owner/factor key functions, each feature pair (f,g) derives

```
jointKey(i) = (key_f(owner i), key_g(factor i)),
jointWeight(i) = mask_f(owner i)*mask_g(factor i).
```

`featureWeight_zero_one` and `jointWeight_zero_one` prove all masks are literal zero or one. `eligiblePorts` filters xs by jointWeight=1, preserving order and every repeated occurrence. `histogram_filtered` proves

```
S_fg = Σk∈derived keys of eligiblePorts (multiplicity k in eligiblePorts)².
```

Thus S_fg is the ordinary collision square-count histogram of an actually derived filtered list. `histogram_keys_bound` bounds sparse keys by xs.length. Filtering cannot increase the record count. There is no need to read labels of omitted free ports for fixed-label features in an implementation.

`feature_grouping` applies the root's already checked weighted pair-grouping identity to the product of the two feature kernels. `pairs_sum` commutes the finite feature sums with the original ordered occurrence-pair sum. `kernel_pairs` proves that the double kernel pair sum equals

```
histogramSum L xs remaining omega owner factor
  =Σf∈Fin4 Σg∈Fin4 coefficient(f)*coefficient(g)*S_fg.
```

It works for arbitrary lists, including duplicate ports and empty lists; no incidence deduplication or dense owner×factor matrix is performed.

## Exact original evaluator endpoint

`padded_kernel` identifies the existing `SourceScoreCountsPadding.paddedLocal` incidence term with L² K_owner K_factor. Its hypotheses are the same positive actual group count, original duplicate-free remaining key list and four original namespace inequalities as the frozen exact incidence formula.

The main theorem is

```
original_incidence_pairs xs owner factor r Q hr remaining env hn hcross
```

with `hcross : forall i in xs, forall j in xs, owner i != factor j`. Its left side is the rational embedding of the actual original ordered pair sum of paddedLocal values on xs×xs. Its right side is

```
L² * histogramSum L xs remaining (denote env) owner factor,
L=r^Q.
```

Every source owner key is a complete-index code of a Sum.inl, and every factor key is a code of a Sum.inr; the frozen `SourceIncidenceNamespaces.indexCode_cross` discharges hcross for the original family. This is not a new source promise. Skein's separate original-score-list bridge composes the theorem with the actually compiled original incidence lane; this module itself does not acquire the obsolete quadratic descriptor list at runtime.

The theorem allows arbitrary actual defaults, fixed words, overrides and remaining order. A free key's cached default is never used as a fixed anchor. Remaining Nodup holds for every original sequential range. r=1, Q=0 and empty ports are covered. r>0 is explicit and agrees with the original source preparation. Q=0 has a singleton empty-word alphabet; no coordinate is introduced. The result does not assume n,M or either score weight is positive.

## Constructive paid successor and honest boundary

The mathematical histogram definition is a literal derived sum of bucket squares. Evaluating that definition by rescanning every bucket could take quadratic work; this module does NOT mislabel that implementation near-linear. Its purpose is to provide the exact semantic target for the concurrently built deterministic physical trie.

A concrete sixteen-pass acquisition avoids even enumerating final distinct keys: for each eligible port, obtain its key, bump its trie frequency from k to k+1 and update the collision accumulator by 2k+1. The invariant is accumulator=Σfrequencies². Each pass has at most M original records and at most M nonzero bins; no original M² pair list is acquired. Actual Boolean key scans/copies, trie-node visits, compact counter increments, accumulator arithmetic and mask/descriptor reads still require their executed reports. No unit-cost hashing is permitted.

Each S_fg is at most M². For L≥1 every coefficient has absolute value ≤L, so signed sixteen-term prefix magnitude is at most 16 L² M² and the final L²-padded magnitude at most 16 L⁴ M². The actual final incidence count is at most L⁴ M². These observations provide a concrete original-input size target for the physical word layer, not an additional Fits premise in this proof. The numerical prefix bounds and physical producer are not claimed proved by this module.

The original full primitive public clock remains open. The positive result here is an exact original all-prefix representation that removes the requirement to acquire M² incidence descriptors and supports sixteen actual sparse passes; it is not a value-equality substitution for an older execution clock.

## Verification

Canonical strict compilation uses autoImplicit=false and warningAsError=true. The ordinary-root fifteen linters and all-generated-declaration axiom scan pass: 36 declarations, 25 theorems, only propext/Classical.choice/Quot.sound. A separate output-path strict recompile and source/object pins appear in `incidence-histogram-verification.json`.
