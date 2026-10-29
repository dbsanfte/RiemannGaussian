/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramHeadBounds
import RiemannGaussian.SemiprimeSourceHistogramHeadAggregate

/-! # Original source semantics of the actual physical head histogram
The acquired prefix, compact candidate bank, row dictionary and original finite
vertex cache discharge every key/label relation internally. Word functions and
quadratic semantic collision sums below are never runtime inputs or routines.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramHeadOriginal
open SemiprimeBitArithmetic SemiprimeSourceHistogramHeadBits
open SemiprimeSourceHistogramHeadRefinement
open SemiprimeSourceHistogramHeadAggregate

/-- Proof-side original environment of the actual selected reverse ID prefix. -/
def originalEnv (r Q : ℕ) [NeZero r] (fixed : List (List Bool)) :
    SemiprimeMaterializedScoreEnvironment.Environment r Q :=
  SemiprimeMaterializedScoreEnvironment.baseEnvironment
    (SemiprimeSourceWordBankSemantics.decode r Q [])
    (fixed.map (SemiprimeSourceWordBankSemantics.decode r Q))

private theorem fixed_filter (n k s : ℕ) :
    (List.finRange n).filter (fun v => !(SemiprimeSourceHistogramFeatureBits.active k s v.val))=
      fixedVertices n (List.range' k s) := by
  unfold fixedVertices
  congr 1
  funext v
  by_cases hm : v.val∈List.range' k s <;>
    simp [SemiprimeSourceHistogramFeatureBits.active_value,hm]

private theorem free_filter (n k s : ℕ) :
    (List.finRange n).filter (fun v => SemiprimeSourceHistogramFeatureBits.active k s v.val)=
      freeVertices n (List.range' k s) := by
  unfold freeVertices
  congr 1
  funext v
  exact SemiprimeSourceHistogramFeatureBits.active_value k s v.val

/-- The actual physical collision accumulator equals the derived original C,
not an advised or separately enumerated quadratic answer. -/
theorem collision_original (n r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) (k s : ℕ) :
    bitValue (acquire (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s
      (verticesWith (List.finRange n)).value).histogram.bits=
        collisionCount n r Q (List.range' k s) (originalEnv r Q fixed) := by
  change bitValue (SemiprimeSourceHistogramSquares.acquire
    (produce (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s
      (verticesWith (List.finRange n)).value).keys).bits = _
  rw [SemiprimeSourceHistogramSquares.acquire_value,
    produce_original_keys r Q fixed hf k s (List.finRange n),fixed_filter]
  have hp : (fixedVertices n (List.range' k s)).flatMap
      (fun v => (List.finRange Q).map (headKey r Q fixed v.val))=
      (headOccurrences n Q (List.range' k s)).map
        (fun p => headKey r Q fixed p.1.val p.2) := by
    simp only [headOccurrences,List.product,List.map_flatMap,List.map_map,Function.comp_def]
  rw [hp]
  apply collision_map_iff
  intro a _ b _
  have he := headKey_eq_iff r Q fixed a.1.val b.1.val a.2 b.2
  simpa only [colourKey,originalEnv,
    SemiprimeSourceHistogramDictRefinement.labels_original] using he

/-- Actual physical fixed-vertex counter equals the original source fixed list. -/
theorem fixed_original (n r Q : ℕ) (fixed : List (List Bool)) (k s : ℕ) :
    bitValue (acquire (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s
      (verticesWith (List.finRange n)).value).head.fixed=
        (fixedVertices n (List.range' k s)).length := by
  change bitValue (produce _ _ _ _ _).fixed = _
  rw [SemiprimeSourceHistogramHeadBounds.original_fixed_count,fixed_filter]

/-- Actual physical free-vertex counter equals the original source free list. -/
theorem free_original (n r Q : ℕ) (fixed : List (List Bool)) (k s : ℕ) :
    bitValue (acquire (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s
      (verticesWith (List.finRange n)).value).head.free=
        (freeVertices n (List.range' k s)).length := by
  change bitValue (produce _ _ _ _ _).free = _
  rw [SemiprimeSourceHistogramHeadBounds.original_free_count,free_filter]

end RiemannGaussian.SemiprimeSourceHistogramHeadOriginal
