/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryView
/-! # Actual dictionary-copy, complete lookup and unread-tail drain
Raw equality is obtained by the preceding real sentinel procedure. Neither a
lookup answer nor a prepared count is a runtime operand of this fragment.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryRead
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
namespace Map
export SemiprimeD1StackOwnerLookup (Stack initial done records result program)
end Map
local notation "ctl"=>Label.local
/-- Fixed caller continuation after an actual complete dictionary read. -/
def next : Read → Control | .classes=>.copyOldIndex | .seen=>.readSeen
/-- Every actual lookup address is a separate physical word in the complete59-role source. -/
theorem lookup_injective:Function.Injective lookupStack:=
  frequency_injective.comp SemiprimeD1StackSourceKeyFrequency.lookup_injective
/-- Complete real eleven-role lookup, including actual first-match payload, unread suffix and its real caller return. -/
theorem lookup_call (what:Read) (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool)
    (q:List Bool) (rows:List (List Bool×List Bool))
    (hi:∀k,view f r o (lookupStack k)=(Map.initial q (Map.records rows [])).data k):
    ∃t ≤ SemiprimeD1StackOwnerLookupBounds.runBound q rows+1,
      Runs SemiprimeD1StackPacketInventory.program t (ctl (.lookup what)) (view f r o)
        (ctl (.clearLookupReader what))
        (view {f with lookupReader:=(Map.result q rows []).2,oldCount:=(Map.result q rows []).1} r o) :=by
  let start:=Map.initial q (Map.records rows [])
  let stop:=Map.done q rows []
  have hin:Link.DataRel lookupStack (view f r o) start.data (view f r o):=⟨hi,fun _ _=>rfl⟩
  have h0:=Link.data_update lookupStack lookup_injective (view f r o) start.data (view f r o) hin
    (.inr .reader) (Map.result q rows []).2
  have h1:=Link.data_update lookupStack lookup_injective (view f r o) _ _ h0
    (.inr .output) (Map.result q rows []).1
  have he:Function.update (Function.update start.data (.inr .reader) (Map.result q rows []).2)
      (.inr .output) (Map.result q rows []).1=stop.data:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h1
  change Link.DataRel lookupStack (view f r o) stop.data
    (Function.update (Function.update (view f r o) (frequencyStack (F.lookupStack (.inr .reader))) (Map.result q rows []).2)
      (frequencyStack (F.lookupStack (.inr .output))) (Map.result q rows []).1) at h1
  rw [update_lookupReader,update_oldCount] at h1
  refine ⟨SemiprimeD1StackOwnerLookupExecution.loopTime q rows+2,?_,?_⟩
  · have h:=SemiprimeD1StackOwnerLookupBounds.time_le q rows;omega
  · exact SemiprimeD1StackProcedureCallsTrace.included_call SemiprimeD1StackPacketInventory.program lookupStack
      Label.lookupCode lookup_injective Map.program .loop (fun _=>rfl) (ctl (.lookup what))
      (ctl (.clearLookupReader what)) rfl (SemiprimeD1StackOwnerLookupExecution.loopTime q rows+1)
      start stop (view f r o) _ rfl rfl rfl rfl (SemiprimeD1StackOwnerLookupExecution.source_run q rows []) hin h1
/-- Own complete dictionary acquisition cap includes all copied/scanned/unread physical bytes. -/
def readBound (q:List Bool) (rows:List (List Bool×List Bool)):Nat:=
  (5*(Map.records rows []).length+4)+(SemiprimeD1StackOwnerLookupBounds.runBound q rows+1)+((Map.result q rows []).2.length+1)
/-- Actual preserving map copy and real complete lookup acquire OLD count/marker, then really drain every unread catalogue byte. -/
theorem read_run (what:Read) (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool)
    (q:List Bool) (rows:List (List Bool×List Bool))
    (hready:∀k,view f r o (lookupStack k)=(Map.initial q []).data k)
    (hmap:view f r o (readWord what)=Map.records rows []) :
    ∃t ≤ readBound q rows,Runs SemiprimeD1StackPacketInventory.program t (ctl (.copyMap what)) (view f r o)
      (ctl (next what))
      (view {f with lookupReader:=[],oldCount:=(Map.result q rows []).1} r o) :=by
  have h0:=copy_call (.dictionary what) (.copyMap what) (.lookup what) rfl
    (view f r o) (Map.records rows []) [] hmap (hready (.inr .reader)) (hready (.inr .copyScratch))
  change Runs SemiprimeD1StackPacketInventory.program _ _ _ _ (Function.update (view f r o)
    (frequencyStack (F.lookupStack (.inr .reader))) (Map.records rows []++[])) at h0
  rw [List.append_nil,update_lookupReader] at h0
  have hi:∀k,view {f with lookupReader:=Map.records rows []} r o (lookupStack k)=
      (Map.initial q (Map.records rows [])).data k:=by
    intro k
    have hk:=hready k
    rcases k with k|k <;> cases k
    all_goals first | rfl | exact hk
  obtain ⟨t,ht,h1⟩:=lookup_call what {f with lookupReader:=Map.records rows []} r o q rows hi
  let unread:=(Map.result q rows []).2
  let payload:=(Map.result q rows []).1
  have h2:=drain_loop (.clearLookupReader what) (ctl (next what))
    (lookupStack (.inr .reader)) (by cases what <;> rfl) (view {f with lookupReader:=unread,oldCount:=payload} r o) unread rfl
  change Runs SemiprimeD1StackPacketInventory.program _ _ _ _ (Function.update
    (view {f with lookupReader:=unread,oldCount:=payload} r o) (frequencyStack (F.lookupStack (.inr .reader))) []) at h2
  rw [update_lookupReader] at h2
  have h:=join (join h0 h1) h2
  exact ⟨_,by unfold readBound;dsimp only [unread];omega,h⟩
end RiemannGaussian.SemiprimeD1StackPacketInventoryRead
