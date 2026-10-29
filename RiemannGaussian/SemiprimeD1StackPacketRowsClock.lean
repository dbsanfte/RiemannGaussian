/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsExecution
/-! # Own polynomial clock from actual lookup, copy, parser and logger traces -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsClock
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsExecution
open SemiprimeD1StackPacketRowsAcquire SemiprimeD1StackPacketRowsLookup
open SemiprimeD1StackPacketRowsEncoding SemiprimeD1StackPacketRowsLoop
open SemiprimeSourceHistogramKeyBits (frame frame_length)
namespace Map
export SemiprimeD1StackOwnerLookup (result records)
end Map
/-- Physical source size counts both preserved words and the empty-input boundary. -/
def inputSize (key catalogue:List Bool) :Nat:=key.length+catalogue.length+1
/-- Fixed polynomial for the complete actual successful source. -/
def polynomial (key catalogue:List Bool) :Nat:=100000*(inputSize key catalogue)^2
/-- Every first-match payload and every retained unread suffix are literal bounded slices of the actual catalogue. -/
theorem lookup_lengths (q:List Bool) (rows:List (List Bool×List Bool)) :
    (Map.result q rows []).1.length ≤ (Map.records rows []).length ∧
      (Map.result q rows []).2.length ≤ (Map.records rows []).length :=by
  induction rows with
  | nil=>simp only [Map.result,Map.records,List.length_nil,List.length_cons];omega
  | cons p ps ih=>
    rcases p with ⟨k,v⟩
    simp only [Map.result,Map.records,List.length_cons,frame_length]
    split_ifs
    · change v.length ≤ _ ∧ (Map.records ps []).length ≤ _
      omega
    · exact ⟨by omega,by omega⟩
/-- Tagged history fragments are bounded by twice the parsed raw row stream, including every empty colour field. -/
theorem history_length (fields:List (List Bool)) :
    (rowsPrefix fields).length ≤ 2*(SemiprimeD1PacketRows.serialize fields).length :=by
  induction fields with
  | nil=>rfl
  | cons word words ih=>
    simp only [rowsPrefix,List.flatMap_cons,List.length_append,row_length,SemiprimeD1PacketRows.serialize,frame_length]
    unfold rowsPrefix at ih
    omega
/-- Actual retained-map lookup, including suffix draining, has the same fixed quadratic source-size cap. -/
theorem lookupBound_le (q:List Bool) (rows:List (List Bool×List Bool)) (S:Nat)
    (hq:q.length+1 ≤ S) (hr:(Map.records rows []).length+1 ≤ S) :lookupBound q rows ≤ 110*S^2 :=by
  have hs:1 ≤ S:=by omega
  have hh:=lookup_lengths q rows
  have hm:(q.length+1)*((Map.records rows []).length+1) ≤ S*S:=Nat.mul_le_mul hq hr
  have hss:S ≤ S*S:=by nlinarith
  unfold lookupBound SemiprimeD1StackOwnerLookupBounds.runBound
  nlinarith
/-- Every cost summand is an actual source-fragment cap; no old reader report is transported to this machine. -/
theorem timeBound_le (owner factor:List Bool) (rows:List (List Bool×List Bool)) (left right:List (List Bool))
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length) :
    timeBound owner factor rows left right ≤ polynomial (frame owner factor) (Map.records rows []) :=by
  let S:=inputSize (frame owner factor) (Map.records rows [])
  have hs:1 ≤ S:=by dsimp [S,inputSize];omega
  have hk:(frame owner factor).length ≤ S:=by dsimp [S,inputSize];omega
  have hc:(Map.records rows []).length+1 ≤ S:=by dsimp [S,inputSize];omega
  have ho:owner.length+1 ≤ S:=by rw [frame_length] at hk;omega
  have hf:factor.length+1 ≤ S:=by rw [frame_length] at hk;omega
  have hq0:=lookupBound_le owner rows S ho hc
  have hq1:=lookupBound_le factor rows S hf hc
  have hl:=lookup_lengths owner rows
  have hr:=lookup_lengths factor rows
  have hpl: (SemiprimeD1PacketRows.serialize left).length ≤ (Map.records rows []).length:=by
    rw [←hleft];exact hl.1
  have hpr: (SemiprimeD1PacketRows.serialize right).length ≤ (Map.records rows []).length:=by
    rw [←hright];exact hr.1
  have ht:=loopTime_le left right hlen
  have hhl:=history_length left
  have hhr:=history_length right
  have hss:S ≤ S*S:=by nlinarith
  change _ ≤ 100000*S^2
  unfold timeBound acquireBound
  change _ ≤ _ at hq0 hq1
  have hplo: (payload owner rows).length ≤ (Map.records rows []).length:=hl.1
  nlinarith
/-- Actual whole source with the fixed polynomial in its two physical input words. -/
theorem source_run_bounded (owner factor:List Bool) (rows:List (List Bool×List Bool)) (left right:List (List Bool))
    (hl:present owner rows=true) (hr:present factor rows=true)
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length) :
    ∃t ≤ polynomial (frame owner factor) (Map.records rows []),SemiprimeD1StackCalls.run program t
      (initial (frame owner factor) (Map.records rows []))=some (done (frame owner factor) (Map.records rows []) left right) :=by
  obtain ⟨t,ht,h⟩:=source_run owner factor rows left right hl hr hleft hright hlen
  exact ⟨t,ht.trans (timeBound_le owner factor rows left right hleft hright hlen),h⟩
end RiemannGaussian.SemiprimeD1StackPacketRowsClock
