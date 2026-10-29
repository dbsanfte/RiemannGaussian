/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexBounds
/-! # Original network records supply their exact actual owner-index catalogue
The only runtime inputs are the literal complete vertex records and the actual
unary left count. Exact singleton owner lookup is derived for EVERY original
well-formed network and occurrence. No owner/arity function is an operand.
The remaining right-row/packing consumer must physically parse the retained
factor suffix and use this actual catalogue; full factoring remains open.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexOriginal
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexEncoding
open SemiprimeD1StackNetworkOwnerIndexExecution SemiprimeD1StackNetworkOwnerIndexBounds
namespace Net
export SemiprimeD1TensorNetwork (Network WellFormed vertices scope)
export SemiprimeD1TensorNetworkLayout (leftGroup)
end Net
namespace R
export SemiprimeD1StackVertexProduct (records)
end R
/-- Literal physical input is the old complete original cached network tape, owners before factors. -/
theorem input_original (net:Net.Network) :
    inputTape net.left.toList (R.records net.right.toList)=R.records (Net.vertices net) :=
  (SemiprimeD1StackNetworkOwnerIndexLoop.records_split net.left.toList net.right.toList).symm
/-- Exact same two-input entry, with the bounded original left count and no derived graph/lookup answer. -/
theorem initial_original (net:Net.Network) :
    source net.left.toList (R.records net.right.toList)=
      initial (R.records (Net.vertices net)) (List.replicate net.leftCount true) :=by
  unfold source
  rw [input_original,Vector.length_toList]
/-- Actual catalogue retains the exact original left-vertex and local-port order for the whole network. -/
theorem output_original (net:Net.Network) :
    (done net.left.toList (R.records net.right.toList)).data .output=
      SemiprimeD1StackOwnerLookup.records (ownerPairs net.leftCount 0 net.left.toList) [] :=by
  rw [output_records]
  simp only [pairs,Vector.length_toList]
/-- The exact physically acquired catalogue has ONE matching original owner at every original occurrence. -/
theorem original_owner_fibre (net:Net.Network) (hw:Net.WellFormed net) (p:Fin (Net.scope net.rows)) :
    SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p.val)
      (pairs net.left.toList)=[ownerWord net.leftCount (Net.leftGroup net.rows p).val] :=by
  simpa only [pairs,Vector.length_toList] using original_fibre net hw p
/-- Exact first-match owner readout also follows from the same original acquired catalogue. -/
theorem original_owner_lookup (net:Net.Network) (hw:Net.WellFormed net) (p:Fin (Net.scope net.rows)) :
    (SemiprimeD1StackOwnerLookup.result (SemiprimeD1StackUnaryDivmod.unary p.val)
      (pairs net.left.toList) []).1=ownerWord net.leftCount (Net.leftGroup net.rows p).val :=by
  simpa only [pairs,Vector.length_toList] using original_lookup net hw p []
/-- One uniform actual source bound before ALL original network record tapes and left counts. -/
theorem source_original (net:Net.Network) :
    ∃q ≤10000*((R.records (Net.vertices net)).length+net.leftCount+1)^2,
      SemiprimeD1StackCalls.run program q
        (initial (R.records (Net.vertices net)) (List.replicate net.leftCount true))=
          some (done net.left.toList (R.records net.right.toList)) ∧
      (done net.left.toList (R.records net.right.toList)).data .output=
        SemiprimeD1StackOwnerLookup.records (ownerPairs net.leftCount 0 net.left.toList) [] ∧
      (done net.left.toList (R.records net.right.toList)).data .reader=R.records net.right.toList :=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded net.left.toList (R.records net.right.toList)
  refine ⟨q,?_,?_,output_original net,suffix_retained _ _⟩
  · simpa only [polynomial,inputSize,input_original,Vector.length_toList] using hq
  · simpa only [initial_original] using hr
/-- The real complete factor suffix survives for a subsequent physical factor-row producer. -/
theorem factors_retained (net:Net.Network) :
    (done net.left.toList (R.records net.right.toList)).data .reader=R.records net.right.toList :=
  suffix_retained _ _
/-- Original physical record/count configuration has a genuine fixed finite-machine time certificate. -/
noncomputable def originalInTime (net:Net.Network) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (R.records (Net.vertices net)) (List.replicate net.leftCount true)))
      (some (SemiprimeD1StackCalls.configuration (done net.left.toList (R.records net.right.toList))))
      (polynomial net.left.toList (R.records net.right.toList)) :=by
  rw [←initial_original]
  exact machineBounded _ _
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexOriginal
