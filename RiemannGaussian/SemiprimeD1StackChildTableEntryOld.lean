/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryRows
/-! # Entire original-coefficient loop, preserving every coordinate and its order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryOld
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryView SemiprimeD1StackChildTableEntryPrimitives
open SemiprimeD1StackChildTableEntryScalar SemiprimeD1StackChildTableEntryFields SemiprimeD1StackChildTableEntryRows
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
local notation "ctl"=>Label.local
/-- Exact sum of actual old-coefficient row costs and the three final physical EOF checks. -/
def budget (p:List Bool):List (List Bool)→Nat
  | []=>3
  | word::rest=>rowTime word p+budget p rest
/-- Actual vector terminator pop, actual inputEOF peek and actual exhausted-old-rank peek. -/
theorem empty_run (old child:J.Stack→List Bool) (assignment path table order entry remaining hist:List Bool):
    Runs program 3 (ctl .header) (state old child assignment path table order entry [false] [] remaining hist)
      (ctl .zeros) (state old child assignment path table order entry [] [] remaining hist):=by
  let w:=loopWords table order entry [] remaining hist
  have h0:=pop_run .header (ctl .abort) (ctl .inputEOF) (ctl .parse) (tree .output)
    (view old child assignment path [false] w) [false] rfl rfl
  change Runs program 1 _ _ _ (Function.update (view old child assignment path [false] w) (treeAllocation .output) []) at h0
  dsimp only [view] at h0
  rw [update_tree,tree_reader] at h0
  have h1:=peek_run .inputEOF (ctl .oldEOF) (ctl .abort) (ctl .abort) (tree .output)
    (view old child assignment path [] w) [] rfl rfl
  have h2:=peek_run .oldEOF (ctl .zeros) (ctl .abort) (ctl .abort) (aux .oldRemaining)
    (view old child assignment path [] w) [] rfl rfl
  exact join (join h0 h1) h2
/-- Every old coordinate is parsed and individually reduced; no aggregate lift or coefficient truncation occurs. -/
theorem old_run (old child:J.Stack→List Bool) (assignment path table order entry hist p:List Bool)
    (ws:List (List Bool)) (zeros:Nat) (hp:child J.precisionBits=p):
    Runs program (budget p ws) (ctl .header)
      (state old child assignment path table order entry (vectorBits ws) (unary ws.length) (unary (ws.length+zeros)) hist)
      (ctl .zeros) (state old child assignment path table order entry [] [] (unary zeros)
        ((history (ws.map (fun word=>SR.result word p))).reverse++hist)):=by
  induction ws generalizing hist with
  | nil=>simpa only [budget,List.map_nil,history,List.flatMap_nil,List.reverse_nil,List.nil_append,vectorBits,List.length_nil,Nat.zero_add,unary,List.replicate_zero] using
      empty_run old child assignment path table order entry (unary zeros) hist
  | cons word ws ih=>
    have h0:=row_run old child assignment path table order entry word (vectorBits ws) (unary ws.length)
      (unary (ws.length+zeros)) hist p hp
    have h1:=ih ((row (SR.result word p)).reverse++hist)
    have he:unary ((word::ws).length+zeros)=true::unary (ws.length+zeros):=by
      rw [show (word::ws).length+zeros=(ws.length+zeros)+1 by simp only [List.length_cons];omega]
      rfl
    rw [he]
    have h:=join h0 h1
    simpa only [budget,List.map_cons,history,List.flatMap_cons,List.reverse_append,List.append_assoc,vectorBits,List.length_cons,unary,List.replicate_succ] using h
end RiemannGaussian.SemiprimeD1StackChildTableEntryOld
