/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationResults
/-! # Physical input-byte capacities for the whole activation source
No estimate uses a recursive child's runtime. The fields are bounded by their
actual retained source-tape lengths and the paid vertex-marker count.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationCapacities
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryActivationLoop
open SemiprimeD1StackChildGroupFactoryActivationBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual vector logging overhead is linear in the actual raw row payload. -/
theorem vector_length_serialize (words:List (List Bool)):
    (vectorBits words).length≤2*(SemiprimeD1PacketRows.serialize words).length+1:=by
  induction words with
  | nil=>rfl
  | cons w ws ih=>
    simp only [vectorBits,SemiprimeD1PacketRows.serialize,List.length_cons,
      SemiprimeSourceHistogramKeyBits.frame_length] at ih ⊢
    omega
/-- Every selected ID, unread suffix and acquired colour field is paid by the two actual source tapes. -/
theorem row_lengths (i:Inputs) (key:List Bool) (environment catalogue:List (List Bool×List Bool)) (row:Row)
    (he:i.environment=SemiprimeD1StackOwnerLookup.records environment [])
    (hc:i.catalogue=SemiprimeD1StackOwnerLookup.records catalogue [])
    (hget:SemiprimeD1StackOwnerLookup.result key environment []=(true::row.selected,row.unread))
    (hr:SemiprimeD1StackPacketRowsAcquire.payload row.selected catalogue=SemiprimeD1PacketRows.serialize row.colours):
    row.selected.length+1≤ i.environment.length ∧ row.unread.length≤ i.environment.length ∧
      (vectorBits row.colours).length+1≤2*i.catalogue.length+2:=by
  have hl:=SemiprimeD1StackPacketRowsClock.lookup_lengths key environment
  rw [hget] at hl
  have hp:=SemiprimeD1StackPacketRowsClock.lookup_lengths row.selected catalogue
  have hraw:(SemiprimeD1PacketRows.serialize row.colours).length≤ i.catalogue.length:=by
    have h:=hp.1
    change (SemiprimeD1StackPacketRowsAcquire.payload row.selected catalogue).length≤_ at h
    rw [hr] at h
    simpa only [hc] using h
  have hv:=vector_length_serialize row.colours
  simpa only [he,List.length_cons] using (show row.selected.length+1≤
      (SemiprimeD1StackOwnerLookup.records environment []).length ∧
      row.unread.length≤(SemiprimeD1StackOwnerLookup.records environment []).length ∧
      (vectorBits row.colours).length+1≤2*i.catalogue.length+2 from ⟨hl.1,hl.2,by omega⟩)
/-- Whole actual loop has polynomial work per physically visited vertex. -/
theorem loop_timeBound_le (i:Inputs) (coordinate:Nat) (environment catalogue:List (List Bool×List Bool))
    (rows:List Row) (key:List Bool) (S:Nat)
    (he:i.environment=SemiprimeD1StackOwnerLookup.records environment [])
    (hc:i.catalogue=SemiprimeD1StackOwnerLookup.records catalogue [])
    (hi:i.colourIndex=List.replicate coordinate true) (hs:1≤S)
    (henv:i.environment.length+1≤S) (hcat:2*i.catalogue.length+2≤S)
    (hcoord:coordinate+1≤S) (hg:i.group.length+1≤S)
    (hk:key.length+2*rows.length+1≤S) (hv:Valid environment catalogue key rows):
    timeBound i coordinate environment catalogue key rows≤(100000000*S^2+1)*rows.length+1:=by
  induction rows generalizing key with
  | nil=>simp only [timeBound,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons row rows ih=>
    rcases hv with ⟨hget,hpresent,hrow,hvalid⟩
    have hlengths:=row_lengths i key environment catalogue row he hc hget hrow
    have hlen:=advance_length key
    have hkey:(advance key).length+2*rows.length+1≤S:=by
      simp only [List.length_cons] at hk
      omega
    have htail:=ih (advance key) hkey hvalid
    have hrowtime:=SemiprimeD1StackChildGroupFactoryActivationBounds.timeBound_le i key row.selected row.unread
      coordinate environment catalogue row.colours S he hc hi hrow hs
      (by omega) (by omega) (by omega) henv (by omega) hcoord (by omega) hg
    dsimp only [timeBound]
    simp only [List.length_cons]
    calc
      _≤1+100000000*S^2+((100000000*S^2+1)*rows.length+1):=by omega
      _=(100000000*S^2+1)*(rows.length+1)+1:=by ring
/-- Only actual activation source words contribute to its physical input-byte size. -/
def inputSize (i:Inputs):Nat:=i.environment.length+i.catalogue.length+i.owners.length+
  i.factors.length+i.colourIndex.length+i.group.length+1
/-- Linear physical-byte proof capacity, never a program operand. -/
def capacity (i:Inputs):Nat:=8*(inputSize i+1)
/-- Whole literal entry, every actual old vertex, final reversal and key cleanup have one fixed cubic bound. -/
theorem source_timeBound_le (i:Inputs) (coordinate:Nat) (environment catalogue:List (List Bool×List Bool))
    (rows:List Row)
    (he:i.environment=SemiprimeD1StackOwnerLookup.records environment [])
    (hc:i.catalogue=SemiprimeD1StackOwnerLookup.records catalogue [])
    (hi:i.colourIndex=List.replicate coordinate true)
    (hlen:rows.length=i.owners.length+i.factors.length) (hv:Valid environment catalogue [] rows):
    SemiprimeD1StackChildGroupFactoryActivationSource.timeBound i coordinate environment catalogue rows≤
      200000000*(capacity i)^3:=by
  let S:=capacity i
  have hs:1≤S:=by dsimp [S,capacity,inputSize];omega
  have hm:i.owners.length+i.factors.length≤S:=by dsimp [S,capacity,inputSize];omega
  have henv:i.environment.length+1≤S:=by dsimp [S,capacity,inputSize];omega
  have hcat:2*i.catalogue.length+2≤S:=by dsimp [S,capacity,inputSize];omega
  have hcoord:coordinate+1≤S:=by
    have hlen:=congrArg List.length hi
    simp only [List.length_replicate] at hlen
    dsimp [S,capacity,inputSize]
    omega
  have hg:i.group.length+1≤S:=by dsimp [S,capacity,inputSize];omega
  have hkey:([]:List Bool).length+2*rows.length+1≤S:=by
    dsimp [S,capacity,inputSize]
    rw [hlen]
    omega
  have ht:=loop_timeBound_le i coordinate environment catalogue rows [] S he hc hi hs henv hcat hcoord hg hkey hv
  have hh:=SemiprimeD1StackChildGroupFactoryActivationResults.finish_history i coordinate rows [] [] [false]
  have hk:=SemiprimeD1StackChildGroupFactoryActivationResults.finish_key_length i coordinate rows [] [] [false]
  have hhist:(finish i coordinate [] [] [false] rows).history.length=rows.length:=by
    rw [hh]
    simp only [List.append_nil,List.length_reverse,List.length_map]
  simp only [List.length_nil,Nat.zero_add] at hk
  have hn:rows.length≤S:=by omega
  have hS2:1≤S^2:=Nat.one_le_pow 2 S hs
  have hS3:1≤S^3:=Nat.one_le_pow 3 S hs
  have hmultiply:=Nat.mul_le_mul_left (100000000*S^2+1) hn
  have hlinear:S≤S^3:=Nat.le_pow (by decide:0<(3:Nat))
  dsimp only [SemiprimeD1StackChildGroupFactoryActivationSource.timeBound]
  rw [hhist]
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationCapacities
