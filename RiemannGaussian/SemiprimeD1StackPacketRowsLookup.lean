/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsView
import RiemannGaussian.SemiprimeD1StackPacketRowsEncoding
/-! # Actual retained-catalogue copy, complete lookup, presence peek and suffix drain
A successful empty payload is accepted only after the real unread-reader peek.
The nonempty suffix follows from the actual lookup trace; no found bit or row
answer is supplied. Every unconsumed catalogue byte is physically erased.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsLookup
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsPrimitives SemiprimeD1StackPacketRowsView
open SemiprimeD1StackPacketRowsEncoding (present result_presence)
open SemiprimeD1StackProcedureTrace
namespace Map
export SemiprimeD1StackOwnerLookup (records result)
end Map
local notation "ctl" => Label.local
/-- Own cap for actual complete lookup acquisition, including retained input copy, presence and unread-tail drain. -/
def lookupBound (q:List Bool) (rows:List (List Bool×List Bool)) :Nat :=
  (5*(Map.records rows []).length+4)+(SemiprimeD1StackOwnerLookupBounds.runBound q rows+1)+1+
    ((Map.result q rows []).2.length+1)
/-- A real lookup acquires the exact raw row and consumes its actual unread catalogue suffix, retaining all private inputs. -/
theorem lookup_run (right:Bool) (key keyReader leftBytes q leftHistory rightHistory leftOutput rightOutput:List Bool)
    (rows:List (List Bool×List Bool)) (hp:present q rows=true) :
    ∃t ≤ lookupBound q rows,
      Runs program t (ctl (.copyMenu right))
        (view key (Map.records rows []) keyReader leftBytes [] q [] [] [] [] [] [] leftHistory rightHistory leftOutput rightOutput)
        (ctl (if right then .clearQuery true else .copyLeft))
        (view key (Map.records rows []) keyReader leftBytes (Map.result q rows []).1 q [] [] [] [] [] []
          leftHistory rightHistory leftOutput rightOutput) :=by
  let catalogue:=Map.records rows []
  let payload:=(Map.result q rows []).1
  let unread:=(Map.result q rows []).2
  have h0:=copy_call .catalogue (.copyMenu right) (.lookup right) rfl
    (view key catalogue keyReader leftBytes [] q [] [] [] [] [] [] leftHistory rightHistory leftOutput rightOutput)
    catalogue [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view key catalogue keyReader leftBytes [] q [] [] [] [] [] [] leftHistory rightHistory leftOutput rightOutput)
    lookupReader (catalogue++[])) at h0
  rw [List.append_nil,update_reader] at h0
  let before:=view key catalogue keyReader leftBytes [] q [] [] [] catalogue [] [] leftHistory rightHistory leftOutput rightOutput
  have hi:∀k,before (lookupStack k)=(SemiprimeD1StackOwnerLookup.initial q catalogue).data k:=by
    intro k
    rcases k with k|k <;> cases k <;> rfl
  obtain ⟨t,ht,h1⟩:=lookup_call right before q rows hi
  have he:Sum.elim (SemiprimeD1StackOwnerLookup.done q rows []).data (fun k=>before (aux k))=
      view key catalogue keyReader leftBytes payload q [] [] [] unread [] [] leftHistory rightHistory leftOutput rightOutput:=by
    funext k
    rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h1
  have h2:=presence_run right
    (view key catalogue keyReader leftBytes payload q [] [] [] unread [] [] leftHistory rightHistory leftOutput rightOutput)
    unread rfl ((result_presence q rows).mpr hp)
  have h3:=drain_loop (.clearLookupReader right) (ctl (if right then .clearQuery true else .copyLeft)) lookupReader rfl
    (view key catalogue keyReader leftBytes payload q [] [] [] unread [] [] leftHistory rightHistory leftOutput rightOutput)
    unread rfl
  rw [update_reader] at h3
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,h⟩
  unfold lookupBound
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left ht _) _) _
end RiemannGaussian.SemiprimeD1StackPacketRowsLookup
