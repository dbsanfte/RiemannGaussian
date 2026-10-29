/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IncidenceAcquisition
import RiemannGaussian.SemiprimeD1SelectedLoadBounds

/-! # Original-data report and persistent-state bounds for D1 acquisition
No prefix, key width, frequency, report or cache advice is supplied. Persistent
trie size is distinguished from the still-open full auxiliary machine heap.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1IncidenceAcquisitionBounds
open scoped BigOperators
open SemiprimeD1IncidenceAcquisition SemiprimeD1CollisionOriginal
open SemiprimeSourceHistogramPortKeys SemiprimeSourceHistogramFeatureBits
open SemiprimeSourceHistogramTrie SemiprimeSourceHistogramTrieBounds

/-- Original setup, all selection queries, one final prefix and selected-key trie. -/
def budget (n F r a M : ℕ) : ℕ :=
  SemiprimeSourceHistogramSearchBudget.budget n F r a 0 M (r^a)+
    SemiprimeSourceHistogramQueryBounds.prefixBudget (r^a) (n+F)+
    SemiprimeSourceHistogramFeatureBitsBounds.budget (n+F) (r^a) M+n+F+10

/-- Actual selected original pair-key state retains every producer report. -/
theorem acquire_work (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).state.clock≤budget n F r a (∑e,arity e) := by
  let fixed := (SemiprimeD1IncidenceSearch.run n F r a arity owner).value
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  have hv := SemiprimeD1IncidenceSearch.run_valid n F r a arity owner
  have hp := SemiprimeSourceHistogramQueryBounds.prefix_clock r a fixed hv
  rw [SemiprimeD1IncidenceSearch.run_length] at hp
  have hf := SemiprimeSourceHistogramFeatureBitsBounds.acquirePorts_clock owner
    (ports n F a arity) dict fixed.length 0 2 2 (r^a)
    (SemiprimeSourceHistogramPrefix.stored_compact fixed)
    (SemiprimeSourceHistogramDictRefinement.count_cap r a fixed hv)
  have hM : (ports n F a arity).length=∑e,arity e :=
    (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1
  rw [hM] at hf
  have hs := SemiprimeD1IncidenceSearchBudget.run_work n F r a arity owner
  rw [SemiprimeD1IncidenceAcquisition.acquire_clock,SemiprimeD1IncidenceSearch.run_length]
  rw [SemiprimeSourceHistogramSetup.records_actual]
  dsimp only [fixed,dict] at hp hf
  rw [SemiprimeD1IncidenceSearch.run_length] at hf
  dsimp only [ports] at hf
  unfold budget
  omega

/-- Every actual pair key has original logarithmic variable/palette width. -/
theorem key_length (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ∀ key∈(acquire n F r a arity owner).keys,
      key.length≤3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+1 := by
  let fixed := (select n F r a arity owner).ids
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  have hv : SemiprimeSourceWordIdControl.InMenu
      (SemiprimeSourceCompactWordBank.acquire r a).ids fixed :=
    SemiprimeD1IncidenceSearch.run_valid n F r a arity owner
  have hc := SemiprimeSourceHistogramPrefix.stored_compact fixed
  have hp := SemiprimeSourceHistogramDictRefinement.count_cap r a fixed hv
  change ∀key∈(produce dict fixed.length 0 2 2
    (select n F r a arity owner).cache.data.records).value,_
  rw [select_cache,SemiprimeSourceHistogramSetup.records_actual]
  exact SemiprimeSourceHistogramFeatureBitsBounds.produce_key_length dict fixed.length 0 2 2
    (SemiprimeSourceHistogramPortKeys.acquirePorts owner (ports n F a arity)).value
    (n+F) (r^a) (acquirePorts_rep owner _) hc hp

/-- Exact persistent-node bound from the actual acquired pair-key stream.
This is not a theorem about all recursion frames or machine addresses. -/
theorem nodes_bound (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    nodes (acquire n F r a arity owner).state.trie≤
      (∑e,arity e)*(3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+2) := by
  have h := SemiprimeSourceHistogramSquaresBounds.acquire_nodes
    (acquire n F r a arity owner).keys
    (3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+1)
    (key_length n F r a arity owner)
  have hl : (acquire n F r a arity owner).keys.length=∑e,arity e := by
    rw [keys_original,List.length_map]
    exact (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1
  rw [hl] at h
  exact h

/-- The actual final stream contains exactly one key per original incidence. -/
theorem keys_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).keys.length=∑e,arity e := by
  rw [keys_original,List.length_map]
  exact (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1

/-- Every actual stored frequency payload has original logarithmic width.
This unconditional cap suffices for the physical maximum's copy/compare clock. -/
theorem stored_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (key : List Bool) :
    (stored (acquire n F r a arity owner).state.trie key).length≤
      Nat.clog 2 ((∑e,arity e)+1) := by
  have hg := acquire_good n F r a arity owner
  have hc := SemiprimeSourceCompactBits.compact_length_clog _ (hg.2.2.1 key)
  have hv : (acquire n F r a arity owner).keys.count key≤∑e,arity e := by
    calc
      _ ≤ (acquire n F r a arity owner).keys.length := List.count_le_length
      _ = _ := keys_length n F r a arity owner
  have he : SemiprimeBitArithmetic.bitValue (stored (acquire n F r a arity owner).state.trie key)=
      (acquire n F r a arity owner).keys.count key := hg.1 key
  rw [he] at hc
  exact hc.trans (Nat.clog_mono_right 2 (Nat.add_le_add_right hv 1))

/-- Actual original graph guarantees the floor cap for EVERY raw trie key.
All semantic label/load premises are discharged by the acquired greedy selector;
only original degree and D.3 numerical hypotheses remain. -/
theorem original_countCap (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (owner i).val)
        (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val)
        (ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a arity).length) :
    CountCap (acquire n F r a arity owner).state.trie
      (2*(ports n F a arity).length/r^(2*a)) := by
  apply countCap_of_load n F r a arity owner
  intro label
  apply (Nat.le_div_iff_mul_le (pow_pos (NeZero.pos r) (2*a))).mpr
  simpa only [Nat.mul_comm] using
    SemiprimeD1SelectedLoadBounds.selected_load_nat_le n F r a arity owner Δ ho hf hsmall label

end RiemannGaussian.SemiprimeD1IncidenceAcquisitionBounds
