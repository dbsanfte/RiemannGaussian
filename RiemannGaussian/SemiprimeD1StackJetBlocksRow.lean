/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksInner
/-! # Complete actual coefficient-block vector, chronological log and cleanup
The final inner reversal, whole-row logger and real row drain preserve every
context/source word and every subsequent unread coefficient field.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksRow
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksPrimitives SemiprimeD1StackJetBlocksView
open SemiprimeD1StackJetBlocksEncoding SemiprimeD1StackJetBlocksInner SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Real completed block framing/reversal/logging and cleanup, with an own physical-row-byte cap. -/
theorem finish_row (context:X.Stack→List Bool) (coefficients blocks todo reader history:List Bool) (words:List (List Bool)) :
    ∃q≤15*(Codec.payload words).length+37,Runs program q (ctl .rowSeed)
      (data context coefficients blocks todo reader [] [] (Codec.payload words).reverse [] history)
      (ctl .outer) (data context coefficients blocks todo reader [] [] [] []
        ((Codec.chunk (vectorBits words)).reverse++history)) :=by
  let hist:=(Codec.payload words).reverse
  let row:=vectorBits words
  let b0:=data context coefficients blocks todo reader [] [] hist [] history
  let b1:=data context coefficients blocks todo reader [] [] hist [false] history
  let b2:=data context coefficients blocks todo reader [] [] [] row history
  let b3:=data context coefficients blocks todo reader [] [] [] row ((Codec.chunk row).reverse++history)
  have h0:=push_run .rowSeed (ctl .rowReverse) (aux .row) false b0 rfl
  change Runs program 1 _ b0 _ (Function.update b0 (aux .row) [false]) at h0
  rw [show Function.update b0 (aux .row) [false]=b1 from data_row _ _ _ _ _ _ _ _ _ _ _] at h0
  have h1:=reverse_call .row .rowReverse .logRow rfl b1 hist [false] rfl rfl
  have hrow:hist.reverse++[false]=row:=by
    dsimp only [hist,row]
    rw [List.reverse_reverse,Codec.payload_vector]
  rw [hrow] at h1
  have he1:Function.update (Function.update b1 (reverseStack .row 0) []) (reverseStack .row 1) row=b2:=by
    change Function.update (Function.update
      (data context coefficients blocks todo reader [] [] hist [false] history)
      (aux .rowHistory) []) (aux .row) row=
      data context coefficients blocks todo reader [] [] [] row history
    rw [data_rowHistory,data_row]
  rw [he1] at h1
  obtain ⟨a,ha,h2⟩:=body_call b2 row history rfl rfl rfl
  change Runs program a _ b2 _ (Function.update b2 (aux .history) ((Codec.chunk row).reverse++history)) at h2
  rw [show Function.update b2 (aux .history) ((Codec.chunk row).reverse++history)=b3 from data_history _ _ _ _ _ _ _ _ _ _ _] at h2
  have h3:=drain_loop .clearRow (ctl .outer) (aux .row) rfl b3 row rfl
  rw [show Function.update b3 (aux .row) []=
    data context coefficients blocks todo reader [] [] [] [] ((Codec.chunk row).reverse++history) from data_row _ _ _ _ _ _ _ _ _ _ _] at h3
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨1+(2*hist.length+3)+a+(row.length+1),?_,h⟩
  have hr:row.length=(Codec.payload words).length+1:=by
    have he:=congrArg List.length (Codec.payload_vector words)
    simp only [List.length_append,List.length_cons,List.length_nil] at he
    dsimp only [row]
    omega
  have hh:hist.length=(Codec.payload words).length:=List.length_reverse
  rw [hr] at ha ⊢
  rw [hh]
  omega
/-- One actual retained-rank copy, complete sequential/default coefficient scan and whole block log. -/
theorem block_run (context:X.Stack→List Bool) (coefficients blocks todo history:List Bool) (rank:Nat)
    (hr:context X.rankCache=List.replicate rank true) (words:List (List Bool)) :
    ∃q≤100*wordMass (padded rank words)+100*(rank+1),Runs program q (ctl .copyRank)
      (data context coefficients blocks todo (vectorBits words) [] [] [] [] history)
      (ctl .outer) (data context coefficients blocks todo (vectorBits (words.drop rank)) [] [] [] []
        ((Codec.chunk (vectorBits (padded rank words))).reverse++history)) :=by
  let bank:=data context coefficients blocks todo (vectorBits words) [] [] [] [] history
  have h0:=copy_call .rank .copyRank .inner rfl bank (List.replicate rank true) [] hr rfl rfl
  simp only [List.append_nil] at h0
  change Runs program (5*(List.replicate rank true).length+4) _ bank _ (Function.update bank (aux .rankTodo) (List.replicate rank true)) at h0
  rw [show Function.update bank (aux .rankTodo) (List.replicate rank true)=
      data context coefficients blocks todo (vectorBits words) (List.replicate rank true) [] [] [] history from data_rankTodo _ _ _ _ _ _ _ _ _ _ _] at h0
  have h1:=inner_run context coefficients blocks todo [] history rank words
  simp only [List.append_nil] at h1
  obtain ⟨a,ha,h2⟩:=finish_row context coefficients blocks todo (vectorBits (words.drop rank)) history (padded rank words)
  have h:=join (join h0 h1) h2
  refine ⟨(5*(List.replicate rank true).length+4)+innerClock rank words+a,?_,h⟩
  have hi:=innerClock_le rank words
  have hp:=Codec.payload_length (padded rank words)
  change (Codec.payload (padded rank words)).length=2*wordMass (padded rank words)+2*(padded rank words).length at hp
  rw [padded_length] at hp
  rw [hp] at ha
  simp only [List.length_replicate]
  omega
end RiemannGaussian.SemiprimeD1StackJetBlocksRow
