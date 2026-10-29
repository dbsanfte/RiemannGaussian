/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryRows
import RiemannGaussian.SemiprimeD1StackPacketInventorySeen
/-! # Exact original row/packet values for one real sparse replay step
These values describe actual source-produced bytes. Original dictionary getters
and functions occur solely in the semantic statements, never in runtime code.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryStepEncoding
open SemiprimeD1StackPacketInventoryEncoding
open SemiprimeSourceHistogramKeyBits (frame split_frame)
namespace Reader
export SemiprimeD1StackPacketRowsMeaning (fields)
end Reader
namespace Native
export SemiprimeD1OrientationBits (acquire)
end Native
/-- Original selected key bytes are the first ID frame and second ID RAW tail. -/
def key (owner factor:List Bool):List Bool:=frame owner factor
/-- Actual cached OLD class payload from the real sentinel dictionary scan. -/
def index (s:Summary) (owner factor:List Bool):List Bool:=Dict.read s.classes (key owner factor)
/-- Packet values acquired by the actual Orientation19 source from actual Reader19 outputs and OLD-j cache. -/
def oriented (a:Nat) (s:Summary) (owner factor:List Bool):SemiprimeD1OrientationBits.Packet:=
  Native.acquire (Reader.fields 64 a owner) (Reader.fields 64 a factor) (index s owner factor)
/-- Actual positive successor word, produced by the second real counter call. -/
def nextEdge (s:Summary):List Bool:=Counter.successor s.edge
/-- Exact actual six-field placement after the two real success flags have been consumed. -/
def placement (a:Nat) (s:Summary) (owner factor:List Bool):SemiprimeD1PacketInventory.Placement:=
  ⟨key owner factor,index s owner factor,(oriented a s owner factor).key,(oriented a s owner factor).slots,nextEdge s,true⟩
/-- Both old row-vector directions and validity are derived from actual acquired original IDs, including a0. -/
theorem read_info (a:Nat) (owner factor:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids):
    (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a (key owner factor)).left=Reader.fields 64 a owner ∧
      (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a (key owner factor)).right=Reader.fields 64 a factor ∧
      (SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a (key owner factor)).valid=true ∧
      (Reader.fields 64 a owner).length=(Reader.fields 64 a factor).length :=by
  refine ⟨?_,?_,?_,?_⟩
  · unfold key
    rw [(SemiprimeD1PacketRows.read_frame _ a owner factor).1]
    exact (SemiprimeD1StackPacketRowsMeaning.fields_original 64 a owner ho).symm
  · unfold key
    rw [(SemiprimeD1PacketRows.read_frame _ a owner factor).2]
    exact (SemiprimeD1StackPacketRowsMeaning.fields_original 64 a factor hf).symm
  · have hov:=(SemiprimeD1PacketRows.original_fields 64 a owner ho).2
    have hfv:=(SemiprimeD1PacketRows.original_fields 64 a factor hf).2
    simp only [key,SemiprimeD1PacketRows.read,split_frame,hov,hfv,Bool.true_and]
  · exact (SemiprimeD1StackPacketRowsMeaning.original_lookup 64 a owner ho).2.2.trans
      (SemiprimeD1StackPacketRowsMeaning.original_lookup 64 a factor hf).2.2.symm
/-- The exact operational step interpretation has the original row values and physically confirmed true placement validity. -/
theorem step_eq (a:Nat) (s:Summary) (owner factor:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids):
    step a s (key owner factor)=
      ⟨(key owner factor,Counter.successor (index s owner factor))::s.classes,
        ((oriented a s owner factor).key,[true])::s.seen,
        (frame (oriented a s owner factor).key (oriented a s owner factor).slots,nextEdge s)::s.slots,
        if (Dict.read s.seen (oriented a s owner factor).key).isEmpty then (oriented a s owner factor).key::s.packets else s.packets,
        nextEdge s,s.placements++[placement a s owner factor]⟩ :=by
  have hr:=read_info a owner factor ho hf
  have hv: (oriented a s owner factor).valid=true:=
    (SemiprimeD1OrientationBits.acquire_valid _ _ _).mpr hr.2.2.2
  have hv':(Native.acquire (Reader.fields 64 a owner) (Reader.fields 64 a factor)
      (Dict.read s.classes (key owner factor))).valid=true:=hv
  unfold step
  dsimp only
  rw [hr.1,hr.2.1,hr.2.2.1]
  simp only [oriented,index,nextEdge,placement,Bool.true_and,hv']
  rfl
/-- Actual marker insertion preserves the precise source-generated marker invariant. -/
theorem step_markers (a:Nat) (s:Summary) (k:List Bool) (h:SemiprimeD1StackPacketInventorySeen.Markers s.seen):
    SemiprimeD1StackPacketInventorySeen.Markers (step a s k).seen :=by
  intro row hr
  change row∈(_, [true])::s.seen at hr
  rcases List.mem_cons.mp hr with he|he
  · cases he;rfl
  · exact h row he
end RiemannGaussian.SemiprimeD1StackPacketInventoryStepEncoding
