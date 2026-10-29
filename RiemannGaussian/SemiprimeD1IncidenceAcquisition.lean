/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IncidenceSearchBudget
import RiemannGaussian.SemiprimeD1SelectedCollision

/-! # Retained D1 selection cache and actual selected-pair frequency state
No cache, selected labels, dictionary, keys or frequencies are supplied. A single
original setup feeds selection, one selected-prefix dictionary, cached port-key
reads, and one physical square/frequency trie acquisition.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1IncidenceAcquisition
open SemiprimeMaterializedWords SemiprimeRationalBits
open SemiprimeSourceHistogramPortKeys SemiprimeSourceHistogramFeatureBits
open SemiprimeSourceHistogramTrie
open SemiprimeD1CollisionOriginal

/-- Actual once-acquired cache, selected byte IDs and complete retained report. -/
structure Selection (n F a : ℕ) (arity : Fin F→ℕ) where
  /-- Original sparse setup, shared by subsequent selected-key acquisition. -/
  cache : SemiprimeSourceHistogramSetup.Cache n F a arity
  /-- Actual original-menu selected IDs. -/
  ids : List (List Bool)
  /-- Setup and every original incidence-query/comparison/copy report. -/
  clock : ℕ

/-- Cache-retaining execution of exactly the frozen incidence-only selector. -/
def select (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Selection n F a arity :=
  let cache := SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner
  let N := cache.data.metadata.indices.length
  let result := SemiprimeSourceChoiceBits.run [] cache.rows.source.bank.ids.tail
    (fun tokens fixed => SemiprimeD1IncidenceSearch.query cache fixed tokens.length) N []
  ⟨cache,result.value,cache.clock+result.work+N+4⟩

/-- The retained cache is acquired from the original graph, never provided. -/
theorem select_cache (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (select n F r a arity owner).cache=SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner := rfl

/-- Exact selected IDs, including every original tie. -/
theorem select_ids (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (select n F r a arity owner).ids=(SemiprimeD1IncidenceSearch.run n F r a arity owner).value := rfl

/-- Retaining the cache changes no acquired report. -/
theorem select_clock (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (select n F r a arity owner).clock=(SemiprimeD1IncidenceSearch.run n F r a arity owner).work := rfl

/-- Literal selected keys are retained for later packet/slot construction. -/
structure Acquired (n F a : ℕ) (arity : Fin F→ℕ) where
  /-- The single original setup and its actual selected IDs/report. -/
  selection : Selection n F a arity
  /-- Actual cached physical pair-key stream, with one entry per original port. -/
  keys : List (List Bool)
  /-- Actual acquired frequency trie/collision total with ALL producer clocks. -/
  state : SemiprimeSourceHistogramSquares.State

/-- Select once, acquire the selected prefix once, read each cached port pair once,
then run the physical frequency-square fold once. No semantic Word data executes. -/
def acquire (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Acquired n F a arity :=
  let selected := select n F r a arity owner
  let dict := SemiprimeSourceHistogramPrefix.acquire selected.ids
  let generated := produce dict.trie selected.ids.length 0 2 2 selected.cache.data.records
  let hist := SemiprimeSourceHistogramSquares.acquire generated.value
  let state := ⟨hist.trie,hist.bits,
    selected.clock+dict.clock+generated.work+hist.clock+selected.ids.length+13⟩
  ⟨selected,generated.value,state⟩

/-- The physical frequency state is acquired on precisely the returned keys. -/
theorem acquire_good (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    SemiprimeSourceHistogramSquares.Good (acquire n F r a arity owner).keys
      (acquire n F r a arity owner).state :=
  SemiprimeSourceHistogramSquares.acquire_good _

/-- No selection or prefix/key/frequency producer report is discarded. -/
theorem acquire_retains_selection (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeD1IncidenceSearch.run n F r a arity owner).work≤
      (acquire n F r a arity owner).state.clock := by
  change (select n F r a arity owner).clock≤_
  unfold acquire
  dsimp only
  omega

/-- Original physical pair-key interpretation, used only for specification. -/
def originalKey (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) : List Bool :=
  jointBytes (SemiprimeSourceHistogramPrefix.acquire
    (SemiprimeD1IncidenceSearch.run n F r a arity owner).value).trie 2 2 (record owner i).value

/-- With no free coordinates every original port survives both eligibility masks. -/
theorem eligible_fixed (k code : ℕ) : eligible k 0 2 code=true := by
  have hact : active k 0 code=false := by
    unfold active
    have h : ¬(k≤code ∧ code<k+0) := by omega
    exact decide_eq_false h
  have h20 : (2:SemiprimeSourceIncidenceHistogram.Feature)≠0 := by decide
  have h21 : (2:SemiprimeSourceIncidenceHistogram.Feature)≠1 := by decide
  simp only [eligible,h20,h21,ite_false,hact,Bool.not_false]

/-- Returned keys are the actual original ordered ports, not an advised bucket list. -/
theorem keys_original (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).keys=
      (ports n F a arity).map (originalKey n F r a arity owner) := by
  change (produce _ _ _ _ _ _).value=_
  rw [produce_value]
  simp only [eligible_fixed,Bool.and_self,List.filter_true]
  rw [select_cache,SemiprimeSourceHistogramSetup.records_actual,acquirePorts_value,List.map_map]
  simp only [select_ids,Function.comp_def,ports]
  rfl

/-- Every original single cached record has its internally derived representation. -/
theorem record_rep {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : (e : Fin F)×Fin (arity e)) :
    RecordRep (n+F) (record owner i).value := by
  apply acquirePorts_rep owner [i]
  rw [acquirePorts_value]
  simp

/-- Actual acquired bytes agree exactly iff the selected original pair labels do.
Dictionary representation and valid selected menu IDs are discharged internally. -/
theorem originalKey_eq_iff (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i j : (e : Fin F)×Fin (arity e)) :
    originalKey n F r a arity owner i=originalKey n F r a arity owner j ↔
      SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner i=
      SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner j := by
  have hv := SemiprimeD1IncidenceSearch.run_valid n F r a arity owner
  let fixed := (SemiprimeD1IncidenceSearch.run n F r a arity owner).value
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  let labels := SemiprimeSourceHistogramDictRefinement.labels r a fixed
  have hd := SemiprimeSourceHistogramDictRefinement.dict_rep r a fixed (n+F) hv
  have h := joint_eq_iff dict labels (n+F) hd 2 2
    (record owner i).value (record owner j).value (record_rep owner i) (record_rep owner j)
  have h21 : (2:SemiprimeSourceIncidenceHistogram.Feature)≠1 := by decide
  simp only [SemiprimeSourceIncidenceHistogram.jointKey,SemiprimeSourceIncidenceHistogram.featureKey,
    h21,ite_false,ite_true,Prod.mk.injEq,Sum.inr.injEq] at h
  change _ ↔ labels (owner i).val=labels (owner j).val ∧
    labels (n+i.1.val)=labels (n+j.1.val) at h
  simpa only [originalKey,SemiprimeD1SelectedCollision.selectedLabel,
    SemiprimeSourceHistogramHeadOriginal.originalEnv,
    SemiprimeSourceHistogramDictRefinement.labels_original,Prod.mk.injEq] using h

/-- Actual physical key frequencies are exactly original selected-label loads. -/
theorem count_originalKey (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) :
    ((acquire n F r a arity owner).keys.count (originalKey n F r a arity owner i))=
      SemiprimeSourceHistogramGrouping.multiplicity
        (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner)
        (ports n F a arity) (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner i) := by
  rw [keys_original,←SemiprimeSourceHistogramSquares.row_count]
  simp only [List.map_map,Function.comp_def,originalKey_eq_iff]
  exact SemiprimeSourceHistogramGrouping.indicator_sum _ _ _

/-- Finite physical frequency cap transfer; absent raw byte keys have zero load.
The actual original degree/numeric endpoint discharges hload separately. -/
theorem countCap_of_load (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (K : ℕ)
    (hload : ∀ label,SemiprimeSourceHistogramGrouping.multiplicity
      (SemiprimeD1SelectedCollision.selectedLabel n F r a arity owner)
      (ports n F a arity) label≤K) :
    SemiprimeSourceHistogramTrieBounds.CountCap (acquire n F r a arity owner).state.trie K := by
  intro key
  rw [(acquire_good n F r a arity owner).1 key]
  by_cases hk : key∈(acquire n F r a arity owner).keys
  · rw [keys_original] at hk
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    rw [count_originalKey]
    exact hload _
  · have hz : (acquire n F r a arity owner).keys.count key=0 := List.count_eq_zero_of_not_mem hk
    rw [hz]
    exact Nat.zero_le _

/-- The whole original report is the selector plus one prefix and feature-square fold.
No duplicate selected-key producer or semantic decoding is charged instead. -/
theorem acquire_clock (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).state.clock=
      (SemiprimeD1IncidenceSearch.run n F r a arity owner).work+
      (SemiprimeSourceHistogramPrefix.acquire (SemiprimeD1IncidenceSearch.run n F r a arity owner).value).clock+
      (SemiprimeSourceHistogramFeatureBits.acquire
        (SemiprimeSourceHistogramPrefix.acquire (SemiprimeD1IncidenceSearch.run n F r a arity owner).value).trie
        (SemiprimeD1IncidenceSearch.run n F r a arity owner).value.length 0 2 2
        (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner).data.records).clock+
      (SemiprimeD1IncidenceSearch.run n F r a arity owner).value.length+10 := by
  simp only [acquire,SemiprimeSourceHistogramFeatureBits.acquire,select_ids,select_cache,select_clock]
  omega

end RiemannGaussian.SemiprimeD1IncidenceAcquisition
