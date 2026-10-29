/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramQuery
import RiemannGaussian.SemiprimeSourceHistogramHeadOriginal
import RiemannGaussian.SemiprimeSourceScoreCancellation

/-! # Original score acquired by sparse physical histograms
The quadratic original compiler and finite count evaluator occur only in the
specification. The executed query acquires its keys and collision counts from
the original sparse input. Both lanes and every original integer weight agree.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceHistogramQueryCorrectness
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeRationalBits

/-- Proof-side original count specification, including every repeated term.
This definition is never called by the physical histogram query. -/
def originalCounts (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (fixed : List (List Bool)) (s : ℕ) : SemiprimeSourceScoreCountsObjective.Counts :=
  let old := SemiprimeSourceWordIdMetadata.acquire n F Q arity
  (SemiprimeSourceScoreCountsObjective.evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
    (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst old.indices old.terms).value
    (List.range' fixed.length s)
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed)).value

/-- All sixteen actually acquired incidence histograms recover the ORIGINAL
integer count lane for every original selected prefix. -/
theorem incidence_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (SemiprimeSourceHistogramQuery.incidenceWith
      (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie fixed.length s).word.value=
        ((originalCounts n F r Q arity owner fixed s).incidence:ℚ) := by
  rw [SemiprimeSourceHistogramQuery.incidence_original n F r Q lam arity owner fixed s hf]
  have h := (SemiprimeSourceHistogramAcquiredSums.acquired_original_lanes
    n F r Q arity owner (NeZero.pos r) (List.range' fixed.length s)
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed) (List.nodup_range')).1
  simp only [SemiprimeSourceHistogramPortKeys.indexCode_inl,
    SemiprimeSourceHistogramPortKeys.indexCode_inr,
    SemiprimeSourceHistogramHeadOriginal.originalEnv,
    SemiprimeSourceHistogramDictRefinement.labels_original] at h
  exact h.symm

/-- The actual head state and physical counters recover the positive original
head formula. The signed subtraction is justified even when the free count is zero. -/
theorem head_total (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (SemiprimeSourceHistogramQuery.headWith
      (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie fixed.length s).word.value=
        (SemiprimeSourceHistogramHeadAggregate.total n r Q (List.range' fixed.length s)
          (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed):ℚ) := by
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  have hp := SemiprimeSourceHistogramScales.acquire_values r Q lam cache.data.records cache.data.metadata.vertices
  have hA : bitValue cache.scales.fourth=(r^Q)^4 := hp.2.2.1
  have hG : bitValue cache.scales.head=r^(4*Q-1) := hp.2.2.2.1
  change (SemiprimeSourceHistogramQuery.headWith cache _ _ _).word.value=_
  unfold SemiprimeSourceHistogramQuery.headWith
  rw [SemiprimeSourceHistogramSetup.rows_actual,
    SemiprimeSourceHistogramSetup.vertices_actual]
  let data := SemiprimeSourceHistogramHeadBits.acquire
    (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
    (SemiprimeSourceHistogramPrefix.acquire fixed).trie fixed.length s
    (SemiprimeSourceHistogramHeadBits.verticesWith (List.finRange n)).value
  let C : RationalReport :=
    ⟨(SemiprimeSourceHistogramArithmetic.fromState data.histogram).word,data.clock+3⟩
  have hC : SemiprimeSourceHistogramArithmetic.DenOne C.word :=
    SemiprimeSourceHistogramArithmetic.fromState_den data.histogram
  have hCv : C.word.value=(bitValue data.histogram.bits:ℚ) :=
    SemiprimeSourceHistogramArithmetic.fromState_value data.histogram
  change (SemiprimeSourceHistogramArithmetic.head cache.scales
    ⟨cache.coordinateCount,0⟩ ⟨data.head.fixed,0⟩ ⟨data.head.free,0⟩ C).word.value=_
  rw [SemiprimeSourceHistogramArithmetic.head_value _ _ _ _ C hC]
  rw [hCv]
  change (bitValue cache.scales.fourth:ℚ)*
      ((bitValue data.histogram.bits:ℚ)+(bitValue cache.coordinateCount:ℚ)*(bitValue data.head.free:ℚ))+
      (bitValue cache.scales.head:ℚ)*(bitValue cache.coordinateCount:ℚ)*
        (2*(bitValue data.head.fixed:ℚ)*(bitValue data.head.free:ℚ)+
          (bitValue data.head.free:ℚ)^2-(bitValue data.head.free:ℚ))=_
  dsimp only [data]
  rw [hA,hG,SemiprimeSourceHistogramSetup.coordinate_value,
    SemiprimeSourceHistogramHeadOriginal.collision_original n r Q fixed hf,
    SemiprimeSourceHistogramHeadOriginal.fixed_original,
    SemiprimeSourceHistogramHeadOriginal.free_original]
  let f := (SemiprimeSourceHistogramHeadAggregate.freeVertices n (List.range' fixed.length s)).length
  have hoff : (f:ℚ)*((f-1:ℕ):ℚ)=(f:ℚ)^2-(f:ℚ) := by
    have h := congrArg (fun z : ℕ => (z:ℚ))
      (SemiprimeSourceHistogramHeadAggregate.free_offdiag f)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] at h
    linarith
  unfold SemiprimeSourceHistogramHeadAggregate.total
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [hoff]
  dsimp only [f]
  ring

/-- The head query returns the ORIGINAL count, including zero dimensions. -/
theorem head_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (SemiprimeSourceHistogramQuery.headWith
      (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie fixed.length s).word.value=
        ((originalCounts n F r Q arity owner fixed s).head:ℚ) := by
  rw [head_total n F r Q lam arity owner fixed s hf]
  congr 1
  exact (SemiprimeSourceHistogramHeadAggregate.original_head_lane n F r Q arity owner
    (List.range' fixed.length s) (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed)
    (List.nodup_range')).symm

/-- The full executed query equals the original scheduled integer objective.
No positivity of n, M, either lane or either integer weight is required. -/
theorem score_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (SemiprimeSourceHistogramQuery.score
      (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner) fixed s).word.value=
      (SemiprimeSourceScoreCancellation.weight (∑ e,arity e) n lam (r^(2*Q))
        (originalCounts n F r Q arity owner fixed s).incidence
        (originalCounts n F r Q arity owner fixed s).head:ℚ) := by
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  have hp := SemiprimeSourceHistogramScales.acquire_values r Q lam cache.data.records cache.data.metadata.vertices
  have hn : cache.data.metadata.vertices.length=n := by
    rw [SemiprimeSourceHistogramSetup.metadata_actual]
    exact (SemiprimeSourceHistogramMetadata.sizes n F Q arity).1
  have hM : cache.data.records.length=∑ e,arity e :=
    SemiprimeSourceHistogramPortKeys.acquireOriginal_length n F Q arity owner
  have hI : bitValue cache.scales.weights.incidence=n^2*lam^2*(r^Q)^4 := by
    have h : bitValue cache.scales.weights.incidence=
        cache.data.metadata.vertices.length^2*lam^2*(r^Q)^4 := hp.2.2.2.2.1
    simpa only [hn] using h
  have hH : bitValue cache.scales.weights.head=4*(∑ e,arity e)^2 := by
    have h : bitValue cache.scales.weights.head=4*cache.data.records.length^2 := hp.2.2.2.2.2
    simpa only [hM] using h
  change (SemiprimeSourceHistogramQuery.scoreWith cache dict fixed.length s).word.value=_
  rw [SemiprimeSourceHistogramQuery.scoreWith,
    SemiprimeSourceHistogramArithmetic.weighted_value _ _ _
      (SemiprimeSourceHistogramQuery.incidence_den cache dict fixed.length s)
      (SemiprimeSourceHistogramQuery.head_den cache dict fixed.length s),hI,hH,
    incidence_original n F r Q lam arity owner fixed s hf,
    head_original n F r Q lam arity owner fixed s hf]
  simp only [SemiprimeSourceScoreCancellation.weight,
    SemiprimeSourceScoreCancellation.bank_square,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]

end RiemannGaussian.SemiprimeSourceHistogramQueryCorrectness
