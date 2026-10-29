/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyMeaning
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyExecution
import RiemannGaussian.SemiprimeD1IncidenceAcquisition
/-! # Original selected-incidence frequency maximum from the literal acquired raw-key vector -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyOriginal
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeD1StackSourceKeyFrequencyMeaning SemiprimeD1StackSourceKeyFrequencyExecution
attribute [local irreducible] SemiprimeD1IncidenceAcquisition.acquire
/-- Original raw-key bytes remain available for later packet rows; no sentinel replaces them in the retained source. -/
theorem source_retained (keys:List (List Bool)) :(done keys).data (aux .source)=SemiprimeD1TensorTapeCodec.vectorBits keys :=rfl
/-- Every actual retained override, including older duplicate records, remains in the physical dictionary. -/
theorem dictionary_retained (keys:List (List Bool)) :(done keys).data (aux .dictionary)=dictionary (acquire keys).rows :=rfl
/-- All18 additional words are actually empty after whole acquisition. -/
theorem work_clear (keys:List (List Bool)) (k:Stack)
    (hk:k≠aux .source ∧ k≠aux .dictionary ∧ k≠aux .maximum) :(done keys).data k=[] :=by
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> first | rfl | exact (hk.1 rfl).elim | exact (hk.2.1 rfl).elim | exact (hk.2.2 rfl).elim
/-- Actual first-match dictionary read is exactly the raw byte-key multiplicity, even for empty or high-zero keys. -/
theorem frequency_original (keys:List (List Bool)) (raw:List Bool) :
    SemiprimeBitArithmetic.bitValue (read (acquire keys).rows raw)=keys.count raw :=(acquire_good keys).counts raw
/-- Entire stopped maximum word is the compact original maximum, not just an output width or mathematical upper bound. -/
theorem output_original (keys:List (List Bool)) :
    (done keys).data (aux .maximum)=(SemiprimeD1CounterMaximum.maxState (SemiprimeSourceHistogramSquares.acquire keys)).bits :=
  maximum_original keys
/-- A source state with the original acquired count semantics has the SAME maximum bytes regardless of its retained producer clock. -/
theorem maximum_of_good (keys:List (List Bool)) (old:SemiprimeSourceHistogramSquares.State)
    (ho:SemiprimeSourceHistogramSquares.Good keys old) :
    (acquire keys).maximum=(SemiprimeD1CounterMaximum.maxState old).bits :=by
  have hn:=acquire_good keys
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hn.compact
    (SemiprimeD1CounterMaximum.maximumTrie_compact old.trie ho.2.2.1)
  apply Nat.le_antisymm
  · rcases hn.attained with hz|⟨q,hq⟩
    · rw [hz];exact Nat.zero_le _
    · rw [hq,←ho.1 q]
      exact SemiprimeD1CounterMaximum.lookup_le_maximum old.trie q
  · exact SemiprimeD1CounterMaximum.maximumTrie_le old.trie _ (fun q=>by
      rw [ho.1 q]
      exact hn.dominates q)
/-- Exact complete original selected-incidence maximum follows internally from the original source's acquired keys/counts. -/
theorem incidence_output_original (n F r a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    (done (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys).data (aux .maximum)=
      (SemiprimeD1CounterMaximum.maxState (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).state).bits :=
  maximum_of_good _ _ (SemiprimeD1IncidenceAcquisition.acquire_good n F r a arity owner)
/-- Same actual21-role source and own whole trace, with exact retained raw vector and entire old maximum. -/
theorem source_run_original (keys:List (List Bool)) :∃t≤ runBound keys,
    SemiprimeD1StackCalls.run program t (source keys)=some (done keys) ∧
      (done keys).data (aux .maximum)=(SemiprimeD1CounterMaximum.maxState (SemiprimeSourceHistogramSquares.acquire keys)).bits ∧
      (done keys).data (aux .source)=SemiprimeD1TensorTapeCodec.vectorBits keys :=by
  obtain ⟨t,ht,hr⟩:=source_run keys
  exact ⟨t,ht,hr,output_original keys,source_retained keys⟩
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyOriginal
