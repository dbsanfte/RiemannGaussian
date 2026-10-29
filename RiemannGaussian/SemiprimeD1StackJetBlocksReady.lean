/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksFinish
/-! # Same literal block program on the caller's actually acquired old context
The context argument describes the entire existing physical cache. Its rank
word is read by real copies; no rank number occurs in runtime control.+-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksReady
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksPrimitives SemiprimeD1StackJetBlocksView
open SemiprimeD1StackJetBlocksEncoding SemiprimeD1StackJetBlocksInner SemiprimeD1StackJetBlocksLoop
open SemiprimeD1StackJetBlocksFinish SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Existing context bank, actual q markers and actual physical coefficient vector. -/
def ready (context:X.Stack→List Bool) (q:Nat) (words:List (List Bool)) :C.State Stack Label :=
  ⟨some (ctl .ready),none,none,data context (vectorBits words) (List.replicate q true) [] [] [] [] [] [] [],[]⟩
/-- Whole clean halt, preserving every actual context/source/q word. -/
def done (context:X.Stack→List Bool) (rank q:Nat) (words:List (List Bool)) :C.State Stack Label :=
  ⟨none,none,none,result context (vectorBits words) (List.replicate q true) (tape rank q words),[]⟩
/-- Own literal ready-source allowance, including all copy/loop/output/trailing-drain/halt work. -/
def readyBound (rank q:Nat) (words:List (List Bool)) :Nat :=
  5*q+5*(vectorBits words).length+8+loopBudget rank q words+
    2*(Codec.payload ((chunks rank q words).map vectorBits)).length+
    (vectorBits (words.drop (q*rank))).length+6
/-- Both actual inputs are copied once, preserving them for the complete caller. -/
theorem setup_trace (context:X.Stack→List Bool) (q:Nat) (words:List (List Bool)) :
    Runs program (5*q+5*(vectorBits words).length+8) (ctl .ready) (ready context q words).data
      (ctl .outer) (data context (vectorBits words) (List.replicate q true) (List.replicate q true)
        (vectorBits words) [] [] [] [] []) :=by
  have h0:=copy_call .blocks .ready .copyVector rfl (ready context q words).data
    (List.replicate q true) [] rfl rfl rfl
  simp only [List.length_replicate,List.append_nil] at h0
  change Runs program (5*q+4) _ _ _ (Function.update
    (data context (vectorBits words) (List.replicate q true) [] [] [] [] [] [] []) (aux .todo) (List.replicate q true)) at h0
  rw [data_todo] at h0
  have h1:=copy_call .vector .copyVector .outer rfl
    (data context (vectorBits words) (List.replicate q true) (List.replicate q true) [] [] [] [] [] [])
    (vectorBits words) [] rfl rfl rfl
  simp only [List.append_nil] at h1
  change Runs program (5*(vectorBits words).length+4) _ _ _ (Function.update
    (data context (vectorBits words) (List.replicate q true) (List.replicate q true) [] [] [] [] [] [])
    (aux .reader) (vectorBits words)) at h1
  rw [data_reader] at h1
  have h:=join h0 h1
  convert h using 1
  omega
/-- All actual ready-entry work, through physical cleanup and immediately before the real halt. -/
theorem ready_trace (context:X.Stack→List Bool) (rank q:Nat)
    (hr:context X.rankCache=List.replicate rank true) (words:List (List Bool)) :
    ∃t,t+1≤readyBound rank q words ∧ Runs program t (ctl .ready) (ready context q words).data
      (ctl .done) (done context rank q words).data :=by
  have h0:=setup_trace context q words
  obtain ⟨a,ha,h1⟩:=blocks_run context (vectorBits words) (List.replicate q true) [] rank q hr words
  simp only [List.append_nil] at h1
  have h2:=finish_run context (vectorBits words) (List.replicate q true)
    (vectorBits (words.drop (q*rank))) (Codec.payload ((chunks rank q words).map vectorBits)).reverse
  simp only [List.length_reverse,List.reverse_reverse,Codec.payload_vector] at h2
  have h:=join (join h0 h1) h2
  refine ⟨(5*q+5*(vectorBits words).length+8)+a+
      (2*(Codec.payload ((chunks rank q words).map vectorBits)).length+
        (vectorBits (words.drop (q*rank))).length+5),?_,h⟩
  unfold readyBound
  omega
/-- The SAMEliteral ready program halts at the EXACTnative ascending block vector. -/
theorem ready_run (context:X.Stack→List Bool) (rank q:Nat)
    (hr:context X.rankCache=List.replicate rank true) (words:List (List Bool)) :
    ∃t≤readyBound rank q words,SemiprimeD1StackCalls.run program t (ready context q words)=
      some (done context rank q words) :=by
  obtain ⟨t,ht,h⟩:=ready_trace context rank q hr words
  obtain ⟨out,ho,ha⟩:=h [] (ready context q words) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (done context rank q words).data [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,ho,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackJetBlocksReady
