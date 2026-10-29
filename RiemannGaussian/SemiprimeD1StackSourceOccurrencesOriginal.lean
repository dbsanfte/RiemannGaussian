/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesBounds
/-! # Literal original-network occurrence namespace acquisition
Every original factor/local-slot occurrence supplies its compact owner ordinal
and disjoint n+factor ordinal. Empty factors advance the factor ordinal; repeated
owner values stay separate. All numeric metadata come from the actual two-input
source; original N-only composition is a separate caller obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesOriginal
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeD1StackSourceOccurrencesExecution SemiprimeD1StackSourceOccurrencesBounds
open SemiprimeBitArithmetic (bitValue)
/-- Exact original canonical pair order, one entry for every original local occurrence. -/
def originalPairsFrom (n:Nat) :Nat→List (List (Fin n))→List (List Bool×List Bool)
  | _,[]=>[]
  | f,row::rows=>row.map (fun v=>(Keys.numberKey v.val,Keys.numberKey (n+f)))++originalPairsFrom n (f+1) rows
/-- Every actual padded owner word normalizes to its exact original compact ordinal. -/
theorem original_owner_key (n:Nat) (v:Fin n) :
    normal (Owner.ownerWord n v.val)=Keys.numberKey v.val :=by
  rw [normal_key,Owner.ownerWord_value n v.val (Nat.le_of_lt v.isLt)]
/-- Exact original factor/local-slot order agrees with the actual normalizing physical-key specification. -/
theorem original_pairs_from (n f:Nat) (rows:List (List (Fin n))) :
    pairsFrom n f (rows.map (fun row=>row.map (fun v=>Owner.ownerWord n v.val)))=originalPairsFrom n f rows :=by
  induction rows generalizing f with
  | nil=>rfl
  | cons row rows ih=>
    simp only [List.map_cons,pairsFrom,originalPairsFrom]
    have hr:(row.map (fun v=>Owner.ownerWord n v.val)).map (fun word=>(normal word,Keys.numberKey (n+f)))=
        row.map (fun v=>(Keys.numberKey v.val,Keys.numberKey (n+f))):=by
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      rw [Function.comp_apply,original_owner_key]
    rw [hr,ih]
/-- Whole actual key stream has exactly the original owner/factor ordinal pairs, including empty-factor gaps. -/
theorem original_pairs (net:SemiprimeD1TensorNetwork.Network) :
    pairs net.leftCount (originalRows net)=originalPairsFrom net.leftCount 0 net.rows :=
  original_pairs_from _ _ _
/-- Original owner/factor namespaces cannot alias after actual compact normalization. -/
theorem namespaces_disjoint (n F:Nat) (v:Fin n) (f:Fin F) :
    Keys.numberKey v.val≠Keys.numberKey (n+f.val) :=by
  intro h
  have hv:=congrArg bitValue h
  simp only [Keys.numberKey_value] at hv
  have hn:=v.isLt
  omega
/-- Every original factor key lies in exactly the acquired n..n+F namespace. -/
theorem factor_range (n F:Nat) (f:Fin F) :
    n≤bitValue (Keys.numberKey (n+f.val)) ∧ bitValue (Keys.numberKey (n+f.val))<n+F :=by
  rw [Keys.numberKey_value]
  have hf:=f.isLt
  omega
/-- Genuine source final bank on the original actual row-word ABI. -/
def originalDone (net:SemiprimeD1TensorNetwork.Network) :C.State Stack Label :=done net.leftCount (originalRows net)
/-- Exact original acquired-row input is retained literally. -/
theorem rows_retained (net:SemiprimeD1TensorNetwork.Network) :
    (originalDone net).data .rows=SemiprimeD1StackNetworkRowsEncoding.originalTape net :=rfl
/-- Original n markers are retained literally, without a binary-n answer operand. -/
theorem n_retained (net:SemiprimeD1TensorNetwork.Network) :
    (originalDone net).data .number=List.replicate net.leftCount true :=rfl
/-- Every original factor, including zero-port rows, physically pushes exactly one F marker. -/
theorem factor_count (net:SemiprimeD1TensorNetwork.Network) :
    (originalDone net).data .factors=List.replicate net.rows.length true :=by
  change List.replicate (originalRows net).length true=_
  simp only [originalRows,List.length_map]
/-- Every original local occurrence pushes one actual M marker, preserving repeated owner entries. -/
theorem occurrence_count (net:SemiprimeD1TensorNetwork.Network) :
    (originalDone net).data .occurrences=List.replicate net.rows.flatten.length true :=by
  change List.replicate ((originalRows net).map List.length).sum true=_
  simp only [originalRows,List.map_map,Function.comp_def,List.length_map,List.length_flatten]
/-- Complete exact original dictionary/stream bytes, with one final false and no supplied record list. -/
theorem output_original (net:SemiprimeD1TensorNetwork.Network) :
    (originalDone net).data .output=SemiprimeD1StackOwnerLookup.records (originalPairsFrom net.leftCount 0 net.rows) [] :=by
  change tape net.leftCount (originalRows net)=_
  rw [tape,original_pairs]
/-- Source inputs are precisely actual original row bytes and acquired unary n, not an owner/arity/getter interface. -/
theorem source_original (net:SemiprimeD1TensorNetwork.Network) :
    ∃q≤1000000*((SemiprimeD1StackNetworkRowsEncoding.originalTape net).length+net.leftCount+1)^2,
      SemiprimeD1StackCalls.run program q
        (initial (SemiprimeD1StackNetworkRowsEncoding.originalTape net) (List.replicate net.leftCount true))=
          some (originalDone net) ∧
      (originalDone net).data .output=SemiprimeD1StackOwnerLookup.records (originalPairsFrom net.leftCount 0 net.rows) [] ∧
      (originalDone net).data .factors=List.replicate net.rows.length true ∧
      (originalDone net).data .occurrences=List.replicate net.rows.flatten.length true :=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded net.leftCount (originalRows net)
  refine ⟨q,?_,?_,output_original net,factor_count net,occurrence_count net⟩
  · simpa only [polynomial,inputSize,original_input] using hq
  · simpa only [source,original_input,originalDone] using hr
/-- Genuine fixed finite-machine certificate for the entire original row-input family. -/
noncomputable def originalInTime (net:SemiprimeD1TensorNetwork.Network) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (SemiprimeD1StackNetworkRowsEncoding.originalTape net) (List.replicate net.leftCount true)))
      (some (SemiprimeD1StackCalls.configuration (originalDone net)))
      (polynomial net.leftCount (originalRows net)) :=by
  simpa only [source,original_input,originalDone] using sourceInTime net.leftCount (originalRows net)
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesOriginal
