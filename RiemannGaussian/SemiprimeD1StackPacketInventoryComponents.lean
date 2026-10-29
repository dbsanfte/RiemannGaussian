/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryView
/-! # Real complete Reader19 and Orientation19 calls with direct physical aliases
The displaced input allocations retain their actual global dictionaries/history.
Each callee is the frozen whole literal source with its proved own clock; no
row answer, old index, packet or evaluator is supplied to the inventory program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryComponents
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
namespace Reader
export SemiprimeD1StackPacketRows (initial)
export SemiprimeD1StackPacketRowsExecution (done)
export SemiprimeD1StackPacketRowsMeaning (fields)
export SemiprimeD1StackPacketRowsOriginal (catalogue)
end Reader
namespace Orient
export SemiprimeD1StackPacketOrientation (initial)
export SemiprimeD1StackPacketOrientationExecution (done)
end Orient
local notation "ctl"=>Label.local
/-- The two displaced reader allocations are persistent globals, never callee inputs or work. -/
def withReader (r data:R.Stack→List Bool):R.Stack→List Bool
  | .inr .key=>r (.inr .key)
  | .inr .catalogue=>r (.inr .catalogue)
  | k=>data k
/-- The three displaced orientation allocations are persistent globals, never callee inputs or work. -/
def withOrientation (o data:O.Stack→List Bool):O.Stack→List Bool
  | .inr .leftInput=>o (.inr .leftInput)
  | .inr .rightInput=>o (.inr .rightInput)
  | .inr .indexInput=>o (.inr .indexInput)
  | k=>data k
/-- Complete actual Reader19 call, with OLD-j and all other counter/map words preserved physically. -/
theorem reader_call (a:Nat) (owner factor:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool)
    (hin:∀k,view f r o (readerStack k)=(Reader.initial (frame owner factor) (Reader.catalogue a)).data k):
    ∃t ≤ SemiprimeD1StackPacketRowsClock.polynomial (frame owner factor) (Reader.catalogue a)+1,
      Runs program t (ctl .readRows) (view f r o) (ctl .rowsValid)
        (view f (withReader r (Reader.done (frame owner factor) (Reader.catalogue a)
          (Reader.fields 64 a owner) (Reader.fields 64 a factor)).data) o) :=by
  let start:=Reader.initial (frame owner factor) (Reader.catalogue a)
  let stop:=Reader.done (frame owner factor) (Reader.catalogue a) (Reader.fields 64 a owner) (Reader.fields 64 a factor)
  obtain ⟨t,ht,hrun,_,_,_,_⟩:=SemiprimeD1StackPacketRowsOriginal.source_run_original a owner factor ho hf
  have hi:Link.DataRel readerStack (view f r o) start.data (view f r o):=⟨hin,fun _ _=>rfl⟩
  have hout:Link.DataRel readerStack (view f r o) stop.data (view f (withReader r stop.data) o):=by
    constructor
    · intro k
      have hk:=hin k
      rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> first | rfl | exact hk
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · by_cases hkey:k=(.inr .key:R.Stack)
          · subst k;rfl
          · by_cases hcat:k=(.inr .catalogue:R.Stack)
            · subst k;rfl
            · have he:readerStack k=readerAllocation k:=by
                rcases k with k|k
                · rfl
                · cases k <;> first | rfl | exact (hkey rfl).elim | exact (hcat rfl).elim
              exact (hk k he).elim
        · rfl
  refine ⟨t+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program readerStack Label.readerCode reader_injective
    R.program (.local .start) (fun _=>rfl) (ctl .readRows) (ctl .rowsValid) rfl t start stop (view f r o) _
    rfl rfl rfl rfl hrun hi hout
/-- Complete actual Orientation19 call starts from the REAL row vectors and retained physically acquired OLD-j cache. -/
theorem orientation_call (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length)
    (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool)
    (hin:∀k,view f r o (orientationStack k)=(Orient.initial (SemiprimeD1TensorTapeCodec.vectorBits left)
      (SemiprimeD1TensorTapeCodec.vectorBits right) index).data k):
    ∃t ≤ SemiprimeD1StackPacketOrientationClock.polynomial (SemiprimeD1TensorTapeCodec.vectorBits left)
        (SemiprimeD1TensorTapeCodec.vectorBits right) index+1,
      Runs program t (ctl .orient) (view f r o) (ctl .orientationValid)
        (view f r (withOrientation o (Orient.done left right index).data)) :=by
  let start:=Orient.initial (SemiprimeD1TensorTapeCodec.vectorBits left) (SemiprimeD1TensorTapeCodec.vectorBits right) index
  let stop:=Orient.done left right index
  obtain ⟨t,ht,hrun⟩:=SemiprimeD1StackPacketOrientationClock.source_run_bounded left right index hlen
  have hi:Link.DataRel orientationStack (view f r o) start.data (view f r o):=⟨hin,fun _ _=>rfl⟩
  have hout:Link.DataRel orientationStack (view f r o) stop.data (view f r (withOrientation o stop.data)):=by
    constructor
    · intro k
      have hk:=hin k
      rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> first | rfl | exact hk
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · by_cases hleft:k=(SemiprimeD1StackPacketOrientation.aux .leftInput)
          · subst k;rfl
          · by_cases hright:k=(SemiprimeD1StackPacketOrientation.aux .rightInput)
            · subst k;rfl
            · by_cases hindex:k=(SemiprimeD1StackPacketOrientation.aux .indexInput)
              · subst k;rfl
              · have he:orientationStack k=orientationAllocation k:=by
                  rcases k with k|k
                  · rfl
                  · cases k <;> first | rfl | exact (hleft rfl).elim | exact (hright rfl).elim | exact (hindex rfl).elim
                exact (hk k he).elim
  refine ⟨t+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program orientationStack Label.orientationCode orientation_injective
    O.program (.local .start) (fun _=>rfl) (ctl .orient) (ctl .orientationValid) rfl t start stop (view f r o) _
    rfl rfl rfl rfl hrun hi hout
end RiemannGaussian.SemiprimeD1StackPacketInventoryComponents
