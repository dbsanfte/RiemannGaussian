/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseCalls
import RiemannGaussian.SemiprimeD1StackCachePhaseGuard
/-! # Whole actual cached-phase source, with its own component/copy clock
Logical histories describe actual heap bytes and allocator-issued references.
Modes describe the physical child tape; no solver or native mode traversal is
an instruction operand. Every source/copy/component transition is paid below.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseExecution
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseNewCache SemiprimeD1StackCachePhaseOldCache
open SemiprimeD1StackCachePhasePrimitives SemiprimeD1StackCachePhaseCalls SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhaseGuard SemiprimeD1StackProcedureTrace
open SemiprimeD1StackJetFoldWords (Modes modeTape sumWords)
local notation "ctl" => Label.local
/-- Literal physical heap encoding of the actual stopped phase records. -/
def heap (banks:List (Fresh.Stack→List Bool)) :List Bool :=
  SemiprimeD1StackHeapAllocate.heapBytes (SemiprimeD1StackFreshBankRestoreExecution.records banks)
/-- The actual allocator's retained chronological allocation count. -/
def counter (banks:List (Fresh.Stack→List Bool)) :List Bool :=List.replicate banks.length true
/-- Actual allocator-issued ordinal markers, never a decoded address opcode. -/
def reference (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) :List Bool :=List.replicate i.val true
/-- Only four physical operand words enter the actual whole source. -/
def source (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes) :C.State Stack Label :=
  initial (heap banks) (counter banks) (reference banks i) (modeTape modes)
/-- The complete95-role result of the actual included restore. -/
def restored (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) :Restore.Stack→List Bool :=
  (SemiprimeD1StackFreshBankRestoreExecution.target banks i).data
/-- Exact111-role ordered-fold result, including its physically retained child tape. -/
def folded (axes:List Nat) (q:Nat) (newP:List Bool) (modes:Modes) :Fold.Stack→List Bool :=
  (SemiprimeD1StackJetFoldExecution.done (q::axes) newP modes).data
/-- Exact actual raw coefficient words of that stopped fold, used only as proof notation. -/
def coefficients (axes:List Nat) (q:Nat) (newP:List Bool) (modes:Modes) :List (List Bool) :=
  sumWords (SemiprimeD1StackJetFoldContext.context (q::axes) newP) modes
/-- Complete actual clean accepted target, preserving all238 allocated data roles. -/
def result (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) :Stack→List Bool :=
  data (restored banks i) (folded axes q newP modes)
    (SemiprimeD1StackJetBlocksReady.done (SemiprimeD1StackJetBlocksExecution.contextResult axes p)
      axes.prod q (coefficients axes q newP modes)).data []
/-- Real whole-source accepted halt; no workspace is silently reset. -/
def done (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) :C.State Stack Label :=
  ⟨none,none,none,result banks i axes p q newP modes,[]⟩
/-- Own source clock pays three actual component calls, ten actual copies, guard and halt. -/
def timeBound (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (_p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) :Nat :=
  SemiprimeD1StackFreshBankRestoreExecution.runBound banks i+newCopyTime (restored banks i)+
    SemiprimeD1StackJetFoldBounds.runBound (q::axes) newP modes+
    oldCopyTime (restored banks i) (folded axes q newP modes)+
    SemiprimeD1StackJetBlocksReady.readyBound axes.prod q (coefficients axes q newP modes)+5
/-- Full accepted trace through three actual sources and all ten paid physical cache copies. -/
theorem source_trace (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (hp:∀r∈axes,0<r) (p:List Bool) (q:Nat) (hq:0<q) (newP:List Bool) (modes:Modes)
    (hv:ValidCache banks[i.val] axes p q newP) :
    ∃t,t+1≤timeBound banks i axes p q newP modes ∧ Runs program t (ctl .start) (source banks i modes).data
      (ctl .done) (result banks i axes p q newP modes) :=by
  have hpositive:∀r∈q::axes,0<r:=by
    intro r hr
    rcases List.mem_cons.mp hr with he|he
    · exact he ▸ hq
    · exact hp r he
  obtain ⟨a,ha,h0⟩:=restore_call banks i (Fold.initial [] [] (modeTape modes)).data (fun _=>[]) []
  have hflag:data (restored banks i) (Fold.initial [] [] (modeTape modes)).data (fun _=>[]) [] phaseValid=[true]:=hv.guard
  have h1:=guard_run (data (restored banks i) (Fold.initial [] [] (modeTape modes)).data (fun _=>[]) []) true hflag
  change Runs program 1 (ctl .check) _ (ctl (.copy .newAxes)) _ at h1
  have h2:=new_cache_run (restored banks i) (modeTape modes) (fun _=>[])
  have hready:foldReady (restored banks i) (modeTape modes)=
      (SemiprimeD1StackJetFoldContext.ready (q::axes) newP (modeTape modes)).data:=
    foldReady_actual banks[i.val] axes p q newP hv (heap banks) (counter banks) (reference banks i) (modeTape modes)
  rw [hready] at h2
  obtain ⟨b,hb,h3⟩:=fold_call (q::axes) hpositive newP modes (restored banks i) (fun _=>[]) []
  have h4:=old_cache_run (restored banks i) (folded axes q newP modes)
  have hcoeff:folded axes q newP modes Fold.output=SemiprimeD1TensorTapeCodec.vectorBits (coefficients axes q newP modes):=
    SemiprimeD1StackJetFoldExecution.output_words (q::axes) newP modes
  have hblock:blockReady (restored banks i) (folded axes q newP modes)=
      (SemiprimeD1StackJetBlocksReady.ready (SemiprimeD1StackJetBlocksExecution.contextResult axes p) q
        (coefficients axes q newP modes)).data:=
    blockReady_actual banks[i.val] axes p q newP hv (heap banks) (counter banks) (reference banks i)
      (folded axes q newP modes) (coefficients axes q newP modes) hcoeff
  rw [hblock] at h4
  obtain ⟨c,hc,h5⟩:=blocks_call (SemiprimeD1StackJetBlocksExecution.contextResult axes p)
    axes.prod q rfl (coefficients axes q newP modes) (restored banks i) (folded axes q newP modes) []
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  refine ⟨a+1+newCopyTime (restored banks i)+b+oldCopyTime (restored banks i) (folded axes q newP modes)+c,?_,h⟩
  unfold timeBound
  omega
/-- Whole accepted physical four-input execution, through the real halt with all238 roles intact. -/
theorem source_run (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (hp:∀r∈axes,0<r) (p:List Bool) (q:Nat) (hq:0<q) (newP:List Bool) (modes:Modes)
    (hv:ValidCache banks[i.val] axes p q newP) :
    ∃t≤timeBound banks i axes p q newP modes,SemiprimeD1StackCalls.run program t (source banks i modes)=
      some (done banks i axes p q newP modes) :=by
  obtain ⟨t,ht,h⟩:=source_trace banks i axes hp p q hq newP modes hv
  obtain ⟨out,ho,ha⟩:=h [] (source banks i modes) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result banks i axes p q newP modes) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,ho,Option.bind_some];exact hh⟩
/-- Genuine compiled consumer certificate, retaining its SAMEactual whole-program clock. -/
noncomputable def sourceInTime (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (hp:∀r∈axes,0<r) (p:List Bool) (q:Nat) (hq:0<q) (newP:List Bool) (modes:Modes)
    (hv:ValidCache banks[i.val] axes p q newP) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source banks i modes))
      (some (SemiprimeD1StackCalls.configuration (done banks i axes p q newP modes)))
      (timeBound banks i axes p q newP modes) :=by
  let h:=source_run banks i axes hp p q hq newP modes hv
  apply SemiprimeD1StackCalls.evalsCorrect (restoreStack Restore.originalInput)
    (blockStack (Blocks.aux .output)) (ctl .start) program
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackCachePhaseExecution
