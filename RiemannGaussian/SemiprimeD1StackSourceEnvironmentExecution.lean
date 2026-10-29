/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentPrefix
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentLookup
/-! # Complete physical prefix acquisition and retained-cache operation entries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentExecution
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentPrimitives
open SemiprimeD1StackSourceEnvironmentEncoding SemiprimeD1StackSourceEnvironmentView
open SemiprimeD1StackSourceEnvironmentReverse SemiprimeD1StackSourceEnvironmentPrefix
open SemiprimeD1StackSourceEnvironmentLookup SemiprimeD1StackSourceEnvironmentExtend
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Literal one-word source; the retained encoded selected prefix is newest first. -/
def source (ids:List (List Bool)) :C.State Stack Label :=initial (vectorBits ids)
/-- All25words after physical whole-prefix acquisition, including the retained unnormalized input vector. -/
def result (ids:List (List Bool)) :Stack→List Bool :=
  view (dictionary ids) (variableKey ids.length) [] [] (vectorBits ids) [] [] [] [] []
/-- Complete actual clean halt, without supplied prefix count/key/dictionary/environment. -/
def done (ids:List (List Bool)) :C.State Stack Label :=⟨none,none,none,result ids,[]⟩
/-- Own actual sum of initialization, realcopy, field-order reversal/transfer, real extension returns and final halt. -/
def timeBound (ids:List (List Bool)) :Nat :=
  5*(vectorBits ids).length+8+reverseClock ids+
    (4*(vectorBits ids.reverse).length+6)+oldClock 0 ids.reverse+1
/-- Actual initialize call/return, preserving prefix copy and reversed-vector false seed. -/
theorem prepare_trace (pfx:List Bool) :
    Runs program (5*pfx.length+8) (ctl .acquire) (initial pfx).data
      (ctl .readNew) (view [false] [] [] [] pfx pfx [false] [] [] []) :=by
  change Runs program _ _ (input pfx) _ _
  rw [input_eq]
  have h0:=push_run .initialize (ctl .resume) (aux .dictionary) false (view [] [] [] [] pfx [] [] [] [] []) rfl
  change Runs program 1 _ _ _ (Function.update (view [] [] [] [] pfx [] [] [] [] []) (aux .dictionary) [false]) at h0
  rw [view_dictionary] at h0
  have h1:=local_call .acquire .initialize .copyPrefix rfl 1 _ _ h0
  have h2:=copy_call .prefix .copyPrefix .seedReverse rfl (view [false] [] [] [] pfx [] [] [] [] []) pfx [] rfl rfl rfl
  simp only [List.append_nil] at h2
  change Runs program _ _ _ _ (Function.update (view [false] [] [] [] pfx [] [] [] [] []) (aux .reader) pfx) at h2
  rw [view_reader] at h2
  have h3:=push_run .seedReverse (ctl .readNew) (aux .reversedPrefix) false (view [false] [] [] [] pfx pfx [] [] [] []) rfl
  change Runs program 1 _ _ _ (Function.update (view [false] [] [] [] pfx pfx [] [] [] []) (aux .reversedPrefix) [false]) at h3
  rw [view_reversedPrefix] at h3
  have h:=join (join h1 h2) h3
  have he:(1+2)+(5*pfx.length+4)+1=5*pfx.length+8:=by omega
  simpa only [he] using h
/-- The complete actual source interprets a newest-first prefix by physically processing its fields oldest first. -/
theorem source_trace (ids:List (List Bool)) :
    ∃q,q+1≤timeBound ids ∧ Runs program q (ctl .acquire) (source ids).data (ctl .done) (result ids) :=by
  have h0:=prepare_trace (vectorBits ids)
  have h1:=reverse_loop [false] [] [] (vectorBits ids) [] [] [] ids []
  simp only [List.append_nil] at h1
  have h2:=transfer_stream [false] [] [] (vectorBits ids) (vectorBits ids.reverse) [] [] []
  obtain ⟨q,hq,h3⟩:=old_loop [] ids.reverse [] (vectorBits ids) [] [] []
  simp only [List.reverse_reverse,List.append_nil] at h3
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,h⟩
  change q≤oldClock 0 ids.reverse at hq
  unfold timeBound
  omega
/-- Whole physical source includes its actual final halt and clears all flags/return frames. -/
theorem source_run (ids:List (List Bool)) :
    ∃q≤timeBound ids,SemiprimeD1StackCalls.run program q (source ids)=some (done ids) :=by
  obtain ⟨q,hq,hr⟩:=source_trace ids
  obtain ⟨finish,hf,hAt⟩:=hr [] (source ids) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result ids) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Exact retained-cache lookup source; no computed answer/found flag is loaded. -/
def lookupReady (ids:List (List Bool)) (chosen q pfx:List Bool) :C.State Stack Label :=
  ⟨some (ctl .lookup),none,none,view (dictionary ids) (variableKey ids.length) chosen q pfx [] [] [] [] [],[]⟩
/-- Exact physical lookup result, with presence separate from the compact ID and with the unread scan fully cleared. -/
def lookupDone (ids:List (List Bool)) (chosen q pfx:List Bool) :C.State Stack Label :=
  ⟨none,none,none,view (dictionary ids) (variableKey ids.length) chosen q pfx [] []
    [decide (SemiprimeBitArithmetic.bitValue q < ids.length)] []
    (if SemiprimeBitArithmetic.bitValue q < ids.length then SemiprimeSourceHistogramPrefix.expected ids (SemiprimeBitArithmetic.bitValue q) else []),[]⟩
/-- Same-program preserving query source has its own paid copy/scan/drain/marker/final-halt budget. -/
theorem lookup_run (ids:List (List Bool)) (chosen q pfx:List Bool) :
    ∃t≤201*(q.length+1)*((dictionary ids).length+1),
      SemiprimeD1StackCalls.run program t (lookupReady ids chosen q pfx)=some (lookupDone ids chosen q pfx) :=by
  obtain ⟨t,ht,hr⟩:=lookup_trace ids chosen q pfx
  obtain ⟨finish,hf,hAt⟩:=hr [] (lookupReady ids chosen q pfx) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl _ [] finish hAt
  refine ⟨t+1,?_,?_⟩
  · nlinarith
  · rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
    exact hh
/-- The actual return instruction cleanly halts an operation whose own real caller-frame stack is empty. -/
theorem return_run (data:Stack→List Bool) (target:C.State Stack Label) (h:At (ctl .resume) data [] target) :
    SemiprimeD1StackCalls.run program 1 target=some (⟨none,none,none,data,[]⟩:C.State Stack Label) :=by
  change SemiprimeD1StackCalls.step program target=some _
  simp only [SemiprimeD1StackCalls.step,h.1,Option.map_some,program,SemiprimeD1StackCalls.execute,h.2.1,h.2.2]
/-- Literal extension entry reuses the acquired cache and the actual caller's selected ID. -/
def extendReady (ids:List (List Bool)) (chosen q pfx:List Bool) :C.State Stack Label :=
  ⟨some (ctl .extend),none,none,view (dictionary ids) (variableKey ids.length) chosen q pfx [] [] [] [] [],[]⟩
/-- Whole retained cache after one actual chosen-ID extension, preserving the original chosen/query/prefix words. -/
def extendDone (ids:List (List Bool)) (chosen q pfx:List Bool) :C.State Stack Label :=
  ⟨none,none,none,view (dictionary (chosen::ids)) (variableKey (chosen::ids).length) chosen q pfx [] [] [] [] [],[]⟩
/-- Same literal extension entry acquires its key from the actual compact counter and pays the real return/halt. -/
theorem extend_run (ids:List (List Bool)) (chosen q pfx:List Bool) :
    ∃t≤101*(chosen.length+(variableKey ids.length).length+1),
      SemiprimeD1StackCalls.run program t (extendReady ids chosen q pfx)=some (extendDone ids chosen q pfx) :=by
  obtain ⟨t,ht,hr⟩:=extend_trace (extendReady ids chosen q pfx).data (dictionary ids) (variableKey ids.length)
    chosen rfl rfl rfl (view_clear _ _ _ _ _ _ _ _ _ _)
  dsimp only [extendReady] at hr
  rw [view_dictionary,view_nextKey,←dictionary_cons,←variableKey_succ] at hr
  obtain ⟨finish,hf,hAt⟩:=hr [] (extendReady ids chosen q pfx) ⟨rfl,rfl,rfl⟩
  have hh:=return_run _ finish hAt
  refine ⟨t+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Literal empty-cache initialization entry, preserving the caller's actual selected/query/prefix words. -/
def initializeReady (chosen q pfx:List Bool) :C.State Stack Label :=
  ⟨some (ctl .initialize),none,none,view [] [] chosen q pfx [] [] [] [] [],[]⟩
/-- Actual one-false dictionary and empty compact next key acquired by initialization. -/
def initializeDone (chosen q pfx:List Bool) :C.State Stack Label :=
  ⟨none,none,none,view [false] [] chosen q pfx [] [] [] [] [],[]⟩
/-- Initialization physically writes the empty dictionary terminal and executes its actual return. -/
theorem initialize_run (chosen q pfx:List Bool) :
    SemiprimeD1StackCalls.run program 2 (initializeReady chosen q pfx)=some (initializeDone chosen q pfx) :=by
  have h0:=push_run .initialize (ctl .resume) (aux .dictionary) false (initializeReady chosen q pfx).data rfl
  change Runs program 1 _ _ _ (Function.update (view [] [] chosen q pfx [] [] [] [] []) (aux .dictionary) [false]) at h0
  rw [view_dictionary] at h0
  obtain ⟨finish,hf,hAt⟩:=h0 [] (initializeReady chosen q pfx) ⟨rfl,rfl,rfl⟩
  have hh:=return_run _ finish hAt
  change SemiprimeD1StackCalls.run program (1+1) _=_
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentExecution
