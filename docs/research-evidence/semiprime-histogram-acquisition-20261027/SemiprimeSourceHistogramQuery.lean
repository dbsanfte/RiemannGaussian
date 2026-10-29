/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramSetup
import RiemannGaussian.SemiprimeSourceHistogramArithmetic
import RiemannGaussian.SemiprimeSourceHistogramDictRefinement
import RiemannGaussian.SemiprimeSourceHistogramAcquiredSums

/-! # Executed original-source histogram score query
The original cache supplies actual graph keys, rows and arithmetic constants.
One actual prefix dictionary feeds all sixteen incidence histograms and the
single joint coordinate/colour head histogram. No score-pair list is built.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeSourceHistogramQuery
open scoped BigOperators
open SemiprimeRationalBits SemiprimeBitArithmetic
open SemiprimeSourceHistogramSetup (Cache)
open SemiprimeSourceHistogramTrie (Trie)
open SemiprimeSourceIncidenceHistogram (Feature)
open SemiprimeSourceHistogramArithmetic (DenOne)

/-- Execute all sixteen sparse physical incidence histograms from the actual cache. -/
def incidenceWith {n F Q : ℕ} {arity : Fin F → ℕ}
    (cache : Cache n F Q arity) (dict : Trie) (k s : ℕ) : RationalReport :=
  SemiprimeSourceHistogramArithmetic.incidence cache.scales
    (fun f g => SemiprimeSourceHistogramFeatureBits.acquire dict k s f g cache.data.records)

/-- Acquire fixed colour keys, actual fixed/free counters and one head histogram. -/
def headWith {n F Q : ℕ} {arity : Fin F → ℕ}
    (cache : Cache n F Q arity) (dict : Trie) (k s : ℕ) : RationalReport :=
  let data := SemiprimeSourceHistogramHeadBits.acquire cache.rows dict k s cache.vertices
  let C := SemiprimeSourceHistogramArithmetic.fromState data.histogram
  let count : RationalReport := ⟨C.word,data.clock+3⟩
  SemiprimeSourceHistogramArithmetic.head cache.scales
    ⟨cache.coordinateCount,0⟩ ⟨data.head.fixed,0⟩ ⟨data.head.free,0⟩ count

/-- Both actual lanes execute and are weighted using original acquired constants. -/
def scoreWith {n F Q : ℕ} {arity : Fin F → ℕ}
    (cache : Cache n F Q arity) (dict : Trie) (k s : ℕ) : RationalReport :=
  let I := incidenceWith cache dict k s
  let H := headWith cache dict k s
  SemiprimeSourceHistogramArithmetic.weighted cache.scales I H

/-- Acquire the concrete prefix once and retain both score and prefix reports.
The native input-list length traversal is explicitly charged. -/
def score {n F Q : ℕ} {arity : Fin F → ℕ}
    (cache : Cache n F Q arity) (fixed : List (List Bool)) (s : ℕ) : RationalReport :=
  let pfx := SemiprimeSourceHistogramPrefix.acquire fixed
  let out := scoreWith cache pfx.trie fixed.length s
  ⟨out.word,pfx.clock+out.clock+fixed.length+7⟩

/-- Standalone original-input query, with all setup data and reports acquired. -/
def indexed (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (fixed : List (List Bool)) (s : ℕ) : RationalReport :=
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let out := score cache fixed s
  ⟨out.word,cache.clock+out.clock+3⟩

/-- No query branch performs rational reduction or produces a zero denominator. -/
theorem incidence_den {n F Q : ℕ} {arity : Fin F → ℕ}
    (cache : Cache n F Q arity) (dict : Trie) (k s : ℕ) :
    DenOne (incidenceWith cache dict k s).word :=
  SemiprimeSourceHistogramArithmetic.incidence_den _ _

/-- Head arithmetic consumes the actual state without encoding a native count. -/
theorem head_den {n F Q : ℕ} {arity : Fin F → ℕ}
    (cache : Cache n F Q arity) (dict : Trie) (k s : ℕ) :
    DenOne (headWith cache dict k s).word := by
  apply SemiprimeSourceHistogramArithmetic.head_den
  exact SemiprimeSourceHistogramArithmetic.fromState_den _

/-- The actual combined score always has denominator one. -/
theorem scoreWith_den {n F Q : ℕ} {arity : Fin F → ℕ}
    (cache : Cache n F Q arity) (dict : Trie) (k s : ℕ) :
    DenOne (scoreWith cache dict k s).word :=
  SemiprimeSourceHistogramArithmetic.weighted_den _ _ _
    (incidence_den cache dict k s) (head_den cache dict k s)

/-- Validity follows structurally, without a score-value or Fits answer. -/
theorem score_valid {n F Q : ℕ} {arity : Fin F → ℕ}
    (cache : Cache n F Q arity) (fixed : List (List Bool)) (s : ℕ) :
    (score cache fixed s).word.Valid :=
  SemiprimeSourceHistogramArithmetic.den_valid _
    (scoreWith_den cache (SemiprimeSourceHistogramPrefix.acquire fixed).trie fixed.length s)

/-- The original acquired graph and prefix discharge every dictionary/key
interface of the actual sixteen-feature query, with no histogram advice. -/
theorem incidence_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
    let data := SemiprimeSourceHistogramMetadata.acquire n F Q arity
    (incidenceWith cache (SemiprimeSourceHistogramPrefix.acquire fixed).trie fixed.length s).word.value=
      ((r^Q:ℕ):ℚ)^2*SemiprimeSourceIncidenceHistogram.histogramSum ((r^Q:ℕ):ℚ)
        data.incidences (List.range' fixed.length s)
        (SemiprimeSourceHistogramDictRefinement.labels r Q fixed)
        (fun i => (owner i).val) (fun i => n+i.1.val) := by
  classical
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let data := SemiprimeSourceHistogramMetadata.acquire n F Q arity
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  have hd := SemiprimeSourceHistogramDictRefinement.dict_rep r Q fixed (n+F) hf
  have hrecords : cache.data.records=
      (SemiprimeSourceHistogramPortKeys.acquirePorts owner data.incidences).value :=
    SemiprimeSourceHistogramSetup.records_actual n F r Q lam arity owner
  have hfeature (f g : Feature) :
      (bitValue (SemiprimeSourceHistogramFeatureBits.acquire dict fixed.length s f g cache.data.records).bits:ℚ)=
        SemiprimeSourceIncidenceHistogram.histogram data.incidences (List.range' fixed.length s)
          (SemiprimeSourceHistogramDictRefinement.labels r Q fixed)
          (fun i => (owner i).val) (fun i => n+i.1.val) f g := by
    rw [hrecords]
    exact SemiprimeSourceHistogramFeatureBits.acquirePorts_histogram_value owner data.incidences
      dict (SemiprimeSourceHistogramDictRefinement.labels r Q fixed) hd fixed.length s f g
  have hp := SemiprimeSourceHistogramScales.acquire_values r Q lam cache.data.records cache.data.metadata.vertices
  have hL : bitValue cache.scales.alphabet=r^Q := hp.1
  have hL2 : bitValue cache.scales.square=(r^Q)^2 := hp.2.1
  change (incidenceWith cache dict fixed.length s).word.value=_
  rw [incidenceWith,SemiprimeSourceHistogramArithmetic.incidence_value,hL,hL2,Nat.cast_pow]
  unfold SemiprimeSourceIncidenceHistogram.histogramSum
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro g _
  rw [hfeature f g]

end RiemannGaussian.SemiprimeSourceHistogramQuery
