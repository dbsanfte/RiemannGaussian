/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsPrepare
import RiemannGaussian.SemiprimeD1StackPacketRowsLookup
/-! # Complete actual two-ID raw colour-stream acquisition
Both row streams come only from the two actual preserving lookup calls. The
owner query, raw factor tail, both copied catalogue suffixes and first temporary
payload are really drained before the paired row-parser entry is reached.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsAcquire
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsPrimitives SemiprimeD1StackPacketRowsView
open SemiprimeD1StackPacketRowsPrepare SemiprimeD1StackPacketRowsLookup
open SemiprimeD1StackPacketRowsEncoding (present)
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Map
export SemiprimeD1StackOwnerLookup (records result)
end Map
local notation "ctl" => Label.local
/-- Actual first-match payload word, used only to name the two real source outputs. -/
def payload (id:List Bool) (rows:List (List Bool×List Bool)) :List Bool :=(Map.result id rows []).1
/-- Own complete source-fragment cap, retaining the real parser/copy/lookup/presence/drain provenance. -/
def acquireBound (owner factor:List Bool) (rows:List (List Bool×List Bool)) :Nat :=
  (5*(frame owner factor).length+8*owner.length+14)+lookupBound owner rows+
    (5*(payload owner rows).length+4)+((payload owner rows).length+1)+(owner.length+1)+
    (5*factor.length+4)+lookupBound factor rows+(factor.length+1)+(factor.length+1)
/-- Complete real front end supplies only actual looked-up raw colour streams to the paired physical EOF loop. -/
theorem acquire_run (owner factor:List Bool) (rows:List (List Bool×List Bool))
    (hl:present owner rows=true) (hr:present factor rows=true) :
    ∃t ≤ acquireBound owner factor rows,
      Runs program t (ctl .start) (initial (frame owner factor) (Map.records rows [])).data (ctl .leftEOF)
        (view (frame owner factor) (Map.records rows []) [] (payload owner rows) (payload factor rows) [] [] [] [] [] [] []
          [] [] [false] [false]) :=by
  let key:=frame owner factor
  let catalogue:=Map.records rows []
  let left:=payload owner rows
  let right:=payload factor rows
  have h0:=prepare_run owner factor catalogue
  obtain ⟨t1,ht1,h1⟩:=lookup_run false key factor [] owner [] [] [false] [false] rows hl
  have h2:=copy_call .leftPayload .copyLeft .clearLeftResult rfl
    (view key catalogue factor [] left owner [] [] [] [] [] [] [] [] [false] [false]) left [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view key catalogue factor [] left owner [] [] [] [] [] [] [] [] [false] [false]) (aux .leftBytes) (left++[])) at h2
  rw [List.append_nil,update_leftBytes] at h2
  have h3:=drain_loop .clearLeftResult (ctl (.clearQuery false)) rightBytes rfl
    (view key catalogue factor left left owner [] [] [] [] [] [] [] [] [false] [false]) left rfl
  rw [update_rightRow] at h3
  have h4:=drain_loop (.clearQuery false) (ctl .copyFactor) query rfl
    (view key catalogue factor left [] owner [] [] [] [] [] [] [] [] [false] [false]) owner rfl
  rw [update_queryWord] at h4
  have h5:=copy_call .factor .copyFactor (.copyMenu true) rfl
    (view key catalogue factor left [] [] [] [] [] [] [] [] [] [] [false] [false]) factor [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view key catalogue factor left [] [] [] [] [] [] [] [] [] [] [false] [false]) query (factor++[])) at h5
  rw [List.append_nil,update_queryWord] at h5
  obtain ⟨t6,ht6,h6⟩:=lookup_run true key factor left factor [] [] [false] [false] rows hr
  have h7:=drain_loop (.clearQuery true) (ctl .clearKeyReader) query rfl
    (view key catalogue factor left right factor [] [] [] [] [] [] [] [] [false] [false]) factor rfl
  rw [update_queryWord] at h7
  have h8:=drain_loop .clearKeyReader (ctl .leftEOF) (aux .keyReader) rfl
    (view key catalogue factor left right [] [] [] [] [] [] [] [] [] [false] [false]) factor rfl
  rw [update_keyReader] at h8
  have h:=join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8
  refine ⟨_,?_,h⟩
  unfold acquireBound
  dsimp only [left]
  omega
end RiemannGaussian.SemiprimeD1StackPacketRowsAcquire
