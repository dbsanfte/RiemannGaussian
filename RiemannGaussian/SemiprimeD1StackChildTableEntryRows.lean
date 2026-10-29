/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryFields
/-! # Complete one-old-coefficient replay on physically acquired rank markers -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryRows
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryView SemiprimeD1StackChildTableEntryPrimitives
open SemiprimeD1StackChildTableEntryScalar SemiprimeD1StackChildTableEntryFields
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- All actual loop helpers are empty apart from retained sources, acquired counters and reverse chronological log. -/
def loopWords (table order entry oldRemaining remaining hist:List Bool):Words:=
  {parentTable:=table,order:=order,parentEntry:=entry,oldRemaining:=oldRemaining,remaining:=remaining,history:=hist}
/-- Whole actual61-word loop boundary, including every original context cache word. -/
def state (old child:J.Stack→List Bool) (assignment path table order entry reader oldRemaining remaining hist:List Bool):Stack→List Bool:=
  view old child assignment path reader (loopWords table order entry oldRemaining remaining hist)
/-- Actual header/parser/two-counter/scalar step, without an index or rank supplied to code. -/
def rowTime (word p:List Bool):Nat:=8*word.length+11+scalarTime word p
local notation "ctl"=>Label.local
/-- Both acquired rank counters are REALLY popped once for each REALLY parsed parent coefficient, followed by its own literal modular reduction. -/
theorem row_run (old child:J.Stack→List Bool) (assignment path table order entry word tail oldTail newTail hist p:List Bool)
    (hp:child J.precisionBits=p):
    Runs program (rowTime word p) (ctl .header)
      (state old child assignment path table order entry (true::frame word tail) (true::oldTail) (true::newTail) hist)
      (ctl .header)
      (state old child assignment path table order entry tail oldTail newTail ((row (SR.result word p)).reverse++hist)):=by
  let w0:=loopWords table order entry (true::oldTail) (true::newTail) hist
  have h0:=pop_run .header (ctl .abort) (ctl .inputEOF) (ctl .parse) (tree .output)
    (view old child assignment path (true::frame word tail) w0) (true::frame word tail) rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (view old child assignment path (true::frame word tail) w0) (treeAllocation .output) (frame word tail)) at h0
  dsimp only [view] at h0
  rw [update_tree,tree_reader] at h0
  have h1:=field_read old child assignment path word tail w0
  let w1:Words:={w0 with coefficient:=word}
  have h2:=pop_run .oldCount (ctl .abort) (ctl .abort) (ctl .newCount) (aux .oldRemaining)
    (view old child assignment path tail w1) (true::oldTail) rfl rfl
  change Runs program 1 _ _ _ (Function.update (view old child assignment path tail w1) (aux .oldRemaining) oldTail) at h2
  dsimp only [view] at h2
  rw [update_aux,words_update] at h2
  let w2:Words:={w1 with oldRemaining:=oldTail}
  have h3:=pop_run .newCount (ctl .abort) (ctl .abort) (ctl (.precision false)) (aux .remaining)
    (view old child assignment path tail w2) (true::newTail) rfl rfl
  change Runs program 1 _ _ _ (Function.update (view old child assignment path tail w2) (aux .remaining) newTail) at h3
  dsimp only [view] at h3
  rw [update_aux,words_update] at h3
  have h4:=scalar_run false word p old child (G.contents [] assignment [] [] [] path)
    (T.contents [] [] [] [] tail) (loopWords table order entry oldTail newTail hist) hp
  have h:=join (join (join (join h0 h1) h2) h3) h4
  unfold rowTime
  convert h using 1 <;> first | rfl | omega
end RiemannGaussian.SemiprimeD1StackChildTableEntryRows
