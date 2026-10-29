/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsBounds
import RiemannGaussian.SemiprimeD1StackNetworkRowsOrder
/-! # Actual whole original-network owner rows and n/F/M acquisition
ALL original well-formed networks discharge the physical lookup contracts.
Runtime input remains only the old complete vertex records and unary left
count; the global N-only producer/controller join is separate work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsOriginal
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsExecution
open SemiprimeD1StackNetworkRowsEncoding SemiprimeD1StackNetworkRowsOrder
open SemiprimeD1StackNetworkRowsLoop SemiprimeD1StackNetworkRowsBounds
namespace Net
export SemiprimeD1TensorNetwork (Network WellFormed vertices)
end Net
/-- Every physically parsed original factor port has the unique actual-index singleton and allocated owner width. -/
theorem original_contract (net:Net.Network) (hw:Net.WellFormed net) :
    ∀v∈net.right.toList,∀p∈v.ports,
      SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows net.left.toList)=[ownerAt net p] ∧
        (ownerAt net p).length≤net.left.toList.length+1 :=by
  intro v hv p hp
  have h:=right_port_lt net hw v hv p hp
  exact ⟨original_singleton net hw p h,by rw [ownerAt_length net p h,Vector.length_toList]⟩
/-- The two physical inputs are EXACTold original vertex bytes and the acquired unary left count. -/
theorem initial_original (net:Net.Network) :
    source net.left.toList net.right.toList=
      initial (SemiprimeD1StackVertexProduct.records (Net.vertices net)) (List.replicate net.leftCount true) :=by
  unfold source inputTape
  rw [SemiprimeD1StackNetworkOwnerIndexOriginal.input_original,Vector.length_toList]
/-- Same-program final bank for the entire original family; no routing/rows function is a runtime argument. -/
def originalDone (net:Net.Network) :C.State Stack Label :=done net.left.toList net.right.toList (ownerAt net)
/-- Exact old literal row order, repetitions and empty rows, with n+1-bit binary owner fields. -/
theorem output_original (net:Net.Network) (hw:Net.WellFormed net) :
    (originalDone net).data (aux .output)=originalTape net :=by
  change rowsTape (resolvedRows net)=_
  exact rowsTape_original net hw
/-- Every original index/source/factor-suffix/catalogue cache word survives the whole physical row producer. -/
theorem index_retained (net:Net.Network) (k:I.Stack) :
    (originalDone net).data (indexStack k)=
      SemiprimeD1StackNetworkOwnerIndexExecution.result net.left.toList
        (SemiprimeD1StackVertexProduct.records net.right.toList) k :=rfl
/-- Actual n metadata is retained directly from the acquired count input. -/
theorem left_count (net:Net.Network) :
    (originalDone net).data (indexStack .leftCount)=List.replicate net.leftCount true :=by
  rw [index_retained]
  simpa only [SemiprimeD1StackNetworkOwnerIndexExecution.done,Vector.length_toList] using SemiprimeD1StackNetworkOwnerIndexExecution.count_retained net.left.toList
    (SemiprimeD1StackVertexProduct.records net.right.toList)
/-- Every original factor, including zero-port factors, physically pushes one marker. -/
theorem factor_count (net:Net.Network) :
    (originalDone net).data (aux .factors)=List.replicate net.rows.length true :=by
  change List.replicate net.right.toList.length true=_
  rw [Vector.length_toList]
/-- Every original local occurrence physically pushes one marker; repeated owners remain separate. -/
theorem occurrence_count (net:Net.Network) (hw:Net.WellFormed net) :
    (originalDone net).data (aux .occurrences)=List.replicate net.rows.flatten.length true :=by
  change List.replicate (occurrences net.right.toList) true=_
  rw [occurrences,SemiprimeD1StackNetworkRowsOrder.occurrence_count net hw]
/-- Original right-record suffix remains exactly intact in the included index bank. -/
theorem factors_retained (net:Net.Network) :
    (originalDone net).data (indexStack .reader)=SemiprimeD1StackVertexProduct.records net.right.toList :=by
  rw [index_retained]
  simpa only [SemiprimeD1StackNetworkOwnerIndexExecution.done] using
    SemiprimeD1StackNetworkOwnerIndexExecution.suffix_retained net.left.toList
      (SemiprimeD1StackVertexProduct.records net.right.toList)
/-- All private fibre roles, including the allocated unused query shadow, are EMPTY at whole halt. -/
theorem fibre_clear (net:Net.Network) (k:F.Stack) :
    (originalDone net).data (.inr (.inl k))=[] :=rfl
/-- Whole original-family source pays the fixed physical-input polynomial and returns exact old rows/n/F/M. -/
theorem source_original (net:Net.Network) (hw:Net.WellFormed net) :
    ∃q≤10000000000*((SemiprimeD1StackVertexProduct.records (Net.vertices net)).length+net.leftCount+1)^3,
      SemiprimeD1StackCalls.run program q
        (initial (SemiprimeD1StackVertexProduct.records (Net.vertices net)) (List.replicate net.leftCount true))=
          some (originalDone net) ∧
      (originalDone net).data (aux .output)=originalTape net ∧
      (originalDone net).data (indexStack .leftCount)=List.replicate net.leftCount true ∧
      (originalDone net).data (aux .factors)=List.replicate net.rows.length true ∧
      (originalDone net).data (aux .occurrences)=List.replicate net.rows.flatten.length true :=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded net.left.toList net.right.toList (ownerAt net) (original_contract net hw)
  refine ⟨q,?_,?_,output_original net hw,left_count net,factor_count net,occurrence_count net hw⟩
  · simpa only [polynomial,inputSize,inputTape,SemiprimeD1StackNetworkOwnerIndexOriginal.input_original,
      Vector.length_toList] using hq
  · simpa only [initial_original,originalDone] using hr
/-- Genuine compiled finite-machine time certificate for ALL original well-formed network tapes. -/
noncomputable def originalInTime (net:Net.Network) (hw:Net.WellFormed net) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (SemiprimeD1StackVertexProduct.records (Net.vertices net)) (List.replicate net.leftCount true)))
      (some (SemiprimeD1StackCalls.configuration (originalDone net)))
      (polynomial net.left.toList net.right.toList) :=by
  rw [←initial_original]
  exact rowsInTime _ _ _ (original_contract net hw)
/-- Actual-cache ready source gives the SAMEoriginal output/n/F/M and retains every index word, without rerunning Index17. -/
theorem ready_original (net:Net.Network) (hw:Net.WellFormed net) :
    ∃q ≤ polynomial net.left.toList net.right.toList,
      SemiprimeD1StackCalls.run program q (ready net.left.toList net.right.toList)=some (originalDone net) ∧
      (originalDone net).data (aux .output)=originalTape net ∧
      (originalDone net).data (indexStack .leftCount)=List.replicate net.leftCount true ∧
      (originalDone net).data (aux .factors)=List.replicate net.rows.length true ∧
      (originalDone net).data (aux .occurrences)=List.replicate net.rows.flatten.length true :=by
  obtain ⟨q,hq,hr⟩:=ready_run_bounded net.left.toList net.right.toList (ownerAt net) (original_contract net hw)
  exact ⟨q,hq,hr,output_original net hw,left_count net,factor_count net,occurrence_count net hw⟩
end RiemannGaussian.SemiprimeD1StackNetworkRowsOriginal
