/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationStorage
import RiemannGaussian.SemiprimeD1StackPacketRowsOriginal
/-! # Exact old orientation and actual acquired packet-row lineage
The generic source preserves arbitrary physical colour/index padding. The
original-family pipeline below retains two actual executions and both own
clocks: real PacketRows19 acquisition, then this real Orientation19 source.
An outer inventory controller still has to compose their literal calls.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationOriginal
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationExecution
open SemiprimeD1StackPacketOrientationClock
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Native
export SemiprimeD1OrientationBits (acquire)
end Native
namespace Reader
export SemiprimeD1StackPacketRows (program initial output)
export SemiprimeD1StackPacketRowsOriginal (catalogue)
export SemiprimeD1StackPacketRowsMeaning (fields)
end Reader
namespace Read
export SemiprimeD1PacketRows (read)
end Read
/-- Exact original packet class key, including its remaining index as a RAW tail. -/
theorem result_key (left right:List (List Bool)) (index:List Bool):
    (done left right index).data (aux .keyOutput)=(Native.acquire left right index).key:=rfl
/-- Exactly one original slot bit per coordinate, with no added vector terminator. -/
theorem result_slots (left right:List (List Bool)) (index:List Bool):
    (done left right index).data (aux .slotOutput)=(Native.acquire left right index).slots:=rfl
/-- Exact remaining raw high-index bytes, preserving arbitrary zero padding. -/
theorem result_high (left right:List (List Bool)) (index:List Bool):
    (done left right index).data (aux .highOutput)=(Native.acquire left right index).high:=rfl
/-- Successful physical flags agree with the original paired-row validity. -/
theorem result_valid (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    (done left right index).data answer=[(Native.acquire left right index).valid] :=by
  rw [(SemiprimeD1OrientationBits.acquire_valid left right index).mpr hlen]
  rfl
/-- All three acquired physical input words are preserved literally. -/
theorem inputs_retained (left right:List (List Bool)) (index:List Bool):
    (done left right index).data (aux .leftInput)=vectorBits left ∧
      (done left right index).data (aux .rightInput)=vectorBits right ∧
      (done left right index).data (aux .indexInput)=index:=⟨rfl,rfl,rfl⟩
/-- Complete SAME program, exact original key/slots/high, all numerical padding and own linear source clock. -/
theorem source_run_original (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    ∃t ≤ polynomial (vectorBits left) (vectorBits right) index,
      SemiprimeD1StackCalls.run program t (initial (vectorBits left) (vectorBits right) index)=some (done left right index) ∧
      (done left right index).data (aux .keyOutput)=(Native.acquire left right index).key ∧
      (done left right index).data (aux .slotOutput)=(Native.acquire left right index).slots ∧
      (done left right index).data (aux .highOutput)=(Native.acquire left right index).high :=by
  obtain ⟨t,ht,h⟩:=source_run_bounded left right index hlen
  exact ⟨t,ht,h,rfl,rfl,rfl⟩
/-- Two actually executed prepared sources, with the orientation input taken DIRECTLY from the stopped real reader.
This proof statement is not a runtime row getter or a claim of an assembled inventory controller. -/
def Pipeline (a:Nat) (key index:List Bool):Prop:=
  ∃r ≤ SemiprimeD1StackPacketRowsClock.polynomial key (Reader.catalogue a),
    ∃rd:SemiprimeD1StackPacketRows.C.State SemiprimeD1StackPacketRows.Stack SemiprimeD1StackPacketRows.Label,
      SemiprimeD1StackCalls.run Reader.program r (Reader.initial key (Reader.catalogue a))=some rd ∧
      ∃t ≤ polynomial (rd.data (Reader.output false)) (rd.data (Reader.output true)) index,
        SemiprimeD1StackCalls.run program t (initial (rd.data (Reader.output false)) (rd.data (Reader.output true)) index)=
          some (done (Read.read (SemiprimeSourceHistogramRows.acquire 64 a) a key).left
            (Read.read (SemiprimeSourceHistogramRows.acquire 64 a) a key).right index)
/-- The original acquired catalogue and both actual selected IDs discharge every row/order/presence premise internally. -/
theorem source_pipeline_original (a:Nat) (owner factor index:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids):
    Pipeline a (SemiprimeSourceHistogramKeyBits.frame owner factor) index :=by
  obtain ⟨r,hr,hread,_,_,_,_⟩:=SemiprimeD1StackPacketRowsOriginal.source_run_original a owner factor ho hf
  have hl:=SemiprimeD1StackPacketRowsMeaning.original_lookup 64 a owner ho
  have hg:=SemiprimeD1StackPacketRowsMeaning.original_lookup 64 a factor hf
  obtain ⟨t,ht,h⟩:=source_run_bounded (Reader.fields 64 a owner) (Reader.fields 64 a factor) index
    (hl.2.2.trans hg.2.2.symm)
  have hol:Reader.fields 64 a owner=(Read.read (SemiprimeSourceHistogramRows.acquire 64 a) a
      (SemiprimeSourceHistogramKeyBits.frame owner factor)).left:=by
    rw [(SemiprimeD1PacketRows.read_frame _ a owner factor).1]
    exact SemiprimeD1StackPacketRowsMeaning.fields_original 64 a owner ho
  have hor:Reader.fields 64 a factor=(Read.read (SemiprimeSourceHistogramRows.acquire 64 a) a
      (SemiprimeSourceHistogramKeyBits.frame owner factor)).right:=by
    rw [(SemiprimeD1PacketRows.read_frame _ a owner factor).2]
    exact SemiprimeD1StackPacketRowsMeaning.fields_original 64 a factor hf
  refine ⟨r,hr,_,hread,t,ht,?_⟩
  change SemiprimeD1StackCalls.run program t (initial (vectorBits (Reader.fields 64 a owner))
    (vectorBits (Reader.fields 64 a factor)) index)=_
  rw [←hol,←hor]
  exact h
/-- ALL original selected occurrence keys have two actual source executions with exact old packet acquisition.
No desired colour fields, comparison, remaining index or packet result is an operand of either program. -/
theorem source_pipeline_selected (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (p:(e:Fin F)×Fin (arity e)) (index:List Bool):
    Pipeline a (SemiprimeD1IncidenceAcquisition.originalKey n F 64 a arity owner p) index :=by
  obtain ⟨l,r,hl,hr,hkey⟩:=SemiprimeD1StackPacketRowsOriginal.selected_key_lineage n F a arity owner p
  rw [hkey]
  exact source_pipeline_original a l r index hl hr
end RiemannGaussian.SemiprimeD1StackPacketOrientationOriginal
