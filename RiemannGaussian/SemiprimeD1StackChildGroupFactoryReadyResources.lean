/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyRetention
/-! # Whole actual retained258 source: fixed own polynomial and every real return
All143 acquired producer words,115 source allocations and seven empty displaced
inputs are counted. This is genuine compiled READY configuration execution;
producer acquisition and a literal N-only caller remain explicit separate work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyResources
namespace R
export SemiprimeD1StackChildGroupFactoryReady
  (Stack Header initial sourceInputs program machine factory environment)
end R
namespace C
export SemiprimeD1StackCalls (State run)
end C
namespace E
export SemiprimeD1StackChildGroupFactoryExecution (done)
end E
namespace V
export SemiprimeD1StackChildGroupFactoryTraceBounds (Valid inputBytes prefix_le)
end V
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end P
namespace W
export SemiprimeD1StackChildGroupFactoryWiring (Label entry)
end W
/-- Actual complete physical bank sum; arbitrary retained producer caches are paid. -/
def mass (words:R.Stack→List Bool):Nat:=∑k,(words k).length
/-- Every actual byte of ALL258 allocations and all thirteen source operands is charged. -/
def size (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header):Nat:=
  mass (R.initial s p iv h).data+V.inputBytes (R.sourceInputs s p iv h)+1
/-- Fixed coefficient/degree precede all source banks and headers. -/
def runBound (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header):Nat:=10^75*(size s p iv h+1)^12
private theorem word_le_sum {K:Type} [Fintype K] (words:K→List Bool) (k:K):
    (words k).length ≤ ∑j,(words j).length:=
  Finset.single_le_sum (f:=fun j:K=>(words j).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- Each retained/private/shadow initial tape is bounded by the full actual physical size. -/
theorem initial_word_le (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header):
    ∀k,((R.initial s p iv h).data k).length ≤ size s p iv h:=by
  intro k
  have hw:=word_le_sum (R.initial s p iv h).data k
  change _ ≤ mass (R.initial s p iv h).data at hw
  exact hw.trans (by dsimp only [size];omega)
/-- Core's SAME actual bound fits a fixed monomial of the entire retained physical byte size. -/
theorem core_bound_le (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header):
    SemiprimeD1StackChildGroupFactoryBounds.runBound (R.sourceInputs s p iv h) ≤ runBound s p iv h:=by
  have hi:V.inputBytes (R.sourceInputs s p iv h) ≤ size s p iv h:=by dsimp only [size];omega
  have hc:SemiprimeD1StackChildGroupFactoryForwardBounds.capacity (R.sourceInputs s p iv h)+1 ≤ 9*(size s p iv h+1):=by
    dsimp only [SemiprimeD1StackChildGroupFactoryForwardBounds.capacity]
    omega
  have hp:=Nat.pow_le_pow_left hc 12
  dsimp only [SemiprimeD1StackChildGroupFactoryBounds.runBound,runBound]
  calc
    _ ≤ 10^60*(9*(size s p iv h+1))^12:=Nat.mul_le_mul_left _ hp
    _ ≤ 10^75*(size s p iv h+1)^12:=by ring_nf;omega
/-- Whole actual retained258 run, with exact core output and all foreign fields retained. -/
theorem source_run (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header)
    (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid (R.sourceInputs s p iv h) a coordinate ids packets fields):
    ∃t ≤ runBound s p iv h,∃finish,C.run R.program t (R.initial s p iv h)=some finish ∧
      SemiprimeD1StackChildGroupFactoryReadyTrace.Rel R.factory (R.initial s p iv h).data
        (E.done (R.sourceInputs s p iv h) a coordinate ids packets fields) finish:=by
  obtain ⟨t,ht,finish,hr,hrel⟩:=SemiprimeD1StackChildGroupFactoryReadyExecution.source_run s p iv h a coordinate ids packets fields
    hv.id_members hv.environment hv.catalogue hv.colour hv.count hv.pairs hv.placements hv.domain hv.packet_tape
  exact ⟨t,ht.trans ((SemiprimeD1StackChildGroupFactoryBounds.timeBound_le _ _ _ _ _ _ hv).trans
    (core_bound_le s p iv h)),finish,hr,hrel⟩
/-- All258 actual data words plus the actual saved return cells. -/
def cells (out:C.State R.Stack W.Label):Nat:=mass out.data+out.frames.length
/-- EVERY successful ready prefix has the same fixed whole-source time bound. -/
theorem prefix_time (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header)
    (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid (R.sourceInputs s p iv h) a coordinate ids packets fields)
    (fuel:Nat) (out:C.State R.Stack W.Label) (hr:C.run R.program fuel (R.initial s p iv h)=some out):
    fuel ≤ runBound s p iv h:=by
  obtain ⟨t,ht,finish,hfinish,hrel⟩:=source_run s p iv h a coordinate ids packets fields hv
  exact (V.prefix_le R.program _ _ _ t fuel hfinish (SemiprimeD1StackChildGroupFactoryReadyExecution.stopped hrel).1 hr).trans ht
/-- EVERY successful ready prefix counts ALL258 tapes and genuine caller returns. -/
theorem prefix_cells (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header)
    (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid (R.sourceInputs s p iv h) a coordinate ids packets fields)
    (fuel:Nat) (out:C.State R.Stack W.Label) (hr:C.run R.program fuel (R.initial s p iv h)=some out):
    cells out ≤ 10^78*(size s p iv h+1)^12:=by
  have ht:=prefix_time s p iv h a coordinate ids packets fields hv fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound R.program fuel (size s p iv h) (R.initial s p iv h) out
    (initial_word_le s p iv h) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound R.program fuel (R.initial s p iv h) out hr
  have hm:=SemiprimeD1StackChildGroupFactoryFinishBounds.finite_word_sum out.data (size s p iv h+fuel) hd
  rw [SemiprimeD1StackChildGroupFactoryReady.stack_card] at hm
  change out.frames.length ≤ 0+fuel at hf
  have hp:size s p iv h+1 ≤ (size s p iv h+1)^12:=Nat.le_pow (by decide:0<(12:Nat))
  dsimp only [cells,mass,runBound] at *
  omega
/-- Genuine compiled machine execution from its honest READY physical configuration. -/
theorem compiled_source (s:SemiprimeD1StackChildGroupFactoryReady.S.Stack→List Bool)
    (p:SemiprimeD1StackChildGroupFactoryReady.P.Stack→List Bool)
    (iv:SemiprimeD1StackChildGroupFactoryReady.I.Stack→List Bool) (h:R.Header)
    (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid (R.sourceInputs s p iv h) a coordinate ids packets fields):
    ∃finish:C.State R.Stack W.Label,finish.pc=none ∧
      Nonempty (StateTransition.EvalsToInTime R.machine.step
        (SemiprimeD1StackCalls.configuration (R.initial s p iv h))
        (some (SemiprimeD1StackCalls.configuration finish)) (runBound s p iv h)) ∧
      SemiprimeD1StackChildGroupFactoryReadyTrace.Rel R.factory (R.initial s p iv h).data
        (E.done (R.sourceInputs s p iv h) a coordinate ids packets fields) finish:=by
  obtain ⟨t,ht,finish,hr,hrel⟩:=source_run s p iv h a coordinate ids packets fields hv
  refine ⟨finish,(SemiprimeD1StackChildGroupFactoryReadyExecution.stopped hrel).1,⟨?_⟩,hrel⟩
  apply SemiprimeD1StackCalls.evalsCorrect R.environment
    (R.factory (SemiprimeD1StackChildGroupFactoryRoles.aux .output)) W.entry R.program
  exact ⟨⟨t,hr⟩,ht⟩
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyResources
