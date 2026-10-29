/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryRows
/-! # Paid remaining-path cleanup and complete coefficient-vector reversal -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryFinish
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryView SemiprimeD1StackChildTableEntryPrimitives
open SemiprimeD1StackChildTableEntryScalar SemiprimeD1StackChildTableEntryFields SemiprimeD1StackChildTableEntryRows
open SemiprimeD1StackProcedureTrace
/-- Actual complete successful bank preserves both full context banks, all original operands and the paid parent-entry copy. -/
def finishBank (old child:J.Stack→List Bool) (assignment table order entry output:List Bool):Stack→List Bool:=
  bank old child (G.contents [] assignment [] [] [] []) (T.contents [] [] [] [] []) (scalarBank [] [])
    (words {parentTable:=table,order:=order,parentEntry:=entry,output:=output,success:=[true]})
/-- Real cleanup of gathered path residue changes no assignment or gather helper word. -/
theorem gather_path (assignment path xs:List Bool):
    Function.update (G.contents [] assignment [] [] [] path) .output xs=G.contents [] assignment [] [] [] xs:=by
  funext k;cases k <;> rfl
local notation "ctl"=>Label.local
/-- Actual path drain, false sentinel, final real reverse and true-success push; final halt is paid by the whole source. -/
theorem finish_run (old child:J.Stack→List Bool) (assignment path table order entry hist:List Bool):
    Runs program (path.length+2*hist.length+6) (ctl .clearPath)
      (state old child assignment path table order entry [] [] [] hist) (ctl .done)
      (finishBank old child assignment table order entry (hist.reverse++[false])):=by
  let w:=loopWords table order entry [] [] hist
  have h0:=drain_loop .clearPath (ctl .seedOutput) (gather .output) rfl
    (view old child assignment path [] w) path rfl
  dsimp only [view] at h0
  rw [update_gather,gather_path] at h0
  have h1:=push_run .seedOutput (ctl .reverseOutput) (aux .output) false
    (view old child assignment [] [] w) rfl
  dsimp only [view] at h1
  rw [update_aux,words_update] at h1
  let w1:Words:={w with output:=[false]}
  have h2:=reverse_call true .reverseOutput .accept rfl (view old child assignment [] [] w1) hist [false] rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view old child assignment [] [] w1)
    (aux .history) []) (aux .output) (hist.reverse++[false])) at h2
  dsimp only [view] at h2
  rw [update_aux,words_update,update_aux,words_update] at h2
  let w2:Words:={w with history:=[],output:=hist.reverse++[false]}
  have h3:=push_run .accept (ctl .done) (aux .success) true (view old child assignment [] [] w2) rfl
  dsimp only [view] at h3
  rw [update_aux,words_update] at h3
  have h:=join (join (join h0 h1) h2) h3
  convert h using 1 <;> first | rfl | omega
end RiemannGaussian.SemiprimeD1StackChildTableEntryFinish
