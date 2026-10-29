/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1AllPacketRowProducts
import RiemannGaussian.SemiprimeD1OriginalDeformation

/-! # Physical original packet row values in occurrence-indexed kernel form
The common resolved endpoint assignment is the original X/Y assignment at the
actual typed occurrence position. Slot and packet coordinates come from replay.
-/
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace RiemannGaussian.SemiprimeD1OriginalPacketKernelRows
open scoped BigOperators
open SemiprimeD1ChildGraph SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketAssignmentRows SemiprimeD1ChildAssignmentEndpoint
open SemiprimeD1OriginalIncidenceIndex SemiprimeD1OriginalPacketPositions
open SemiprimeD1AllPacketRowProducts SemiprimeD1PacketRowProducts
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact X/Y bits in both physically acquired side wires at every occurrence. -/
theorem sideWire_bits (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (x y : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length→Bool)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length) :
    (sideWire n F r a arity owner true (originalEndpointBit n F r a arity owner (tagBits n F r a arity owner x y)) j).bit=y j ∧
    (sideWire n F r a arity owner false (originalEndpointBit n F r a arity owner (tagBits n F r a arity owner x y)) j).bit=x j := by
  let pair := ((position n F r a arity owner).symm j,
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements[j.val])
  have hp : pair∈SemiprimeD1ChildPortPullbackCorrectness.originalPairs n F r a arity owner := by
    change pair∈SemiprimeD1PacketColumnPartition.originalPairs n F r a arity owner
    rw [pairs_ofFn]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  have h := original_pair_xy n F r a arity owner q g x y pair hp
  change originalEndpointBit n F r a arity owner (tagBits n F r a arity owner x y)
    (endpoints owner pair.1 pair.2).1=y j ∧
    originalEndpointBit n F r a arity owner (tagBits n F r a arity owner x y)
    (endpoints owner pair.1 pair.2).2=x j
  simpa only [pair,Equiv.apply_symm_apply] using h

/-- Both copied orientation slots are exactly the original finite replay slot. -/
theorem sideWire_slot (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (side : Bool) (assignment : Endpoint (n+F)→Bool)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length) :
    (sideWire n F r a arity owner side assignment j).slot=
      SemiprimeD1OriginalDeformation.slot n F r a arity owner j := by
  have hl := (SemiprimeD1PacketReplayOriginal.placement_valid n F r a arity owner _ (List.getElem_mem j.isLt)).2
  apply Fin.ext
  cases side
  · exact wire_slot a _ _ hl
  · exact wire_slot a _ _ hl

/-- Sum over a literal optional filtered payload, preserving every occurrence. -/
theorem filterMap_sum {A B C : Type*} [AddCommMonoid C] (xs : List A)
    (pred : A→Prop) [DecidablePred pred] (wire : A→B) (value : B→C) :
    ((xs.filterMap (fun x => if pred x then some (wire x) else none)).map value).sum=
      (xs.map (fun x => if pred x then value (wire x) else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : pred x <;>
      simp only [List.filterMap_cons,h,ite_true,ite_false,List.map_cons,List.sum_cons,ih,zero_add]

/-- Same observed packet is exactly equality of the actual original byte keys. -/
theorem same_packet_iff (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (j k : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length) :
    observed n F r a arity owner k=observed n F r a arity owner j ↔
      SemiprimeD1OriginalDeformation.packet n F r a arity owner j=
        SemiprimeD1OriginalDeformation.packet n F r a arity owner k := by
  rw [observed_eq_iff]
  rw [observed_key]
  exact eq_comm

/-- Literal original packet column sum is the actual full occurrence-indexed
kernel row, with off-packet entries zero and the actual X assignment bits. -/
theorem column_kernel_sum (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (x y : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length→Bool)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hpos : ctx.Positive) (hp : 0<ctx.precision) :
    let assignment := originalEndpointBit n F r a arity owner (tagBits n F r a arity owner x y)
    let row := sideWire n F r a arity owner true assignment j
    ((SemiprimeD1PacketColumnPartition.originalSideWires n F r a arity owner false
      (observed n F r a arity owner j) assignment).map
      (fun c => interpret ctx (baseTerm ctx z a t row c).words)).sum=
      ∑k,(if SemiprimeD1OriginalDeformation.packet n F r a arity owner j=
          SemiprimeD1OriginalDeformation.packet n F r a arity owner k then
        SemiprimeD1UniversalModeData.entryValue ctx.precision
          (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
          (SemiprimeD1WireKernelOriginal.acquireOriginal a t
            (SemiprimeD1OriginalDeformation.slot n F r a arity owner j)
            (SemiprimeD1OriginalDeformation.slot n F r a arity owner k)) else 0)*
        SemiprimeStreamingTensor.bit (x k) := by
  dsimp only
  rw [originalSideWires_fin,filterMap_sum,←List.ofFn_eq_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  rw [SemiprimeD1PacketEntryComponents.baseTerm_value ctx z a t _ _ hpos hp]
  rw [(sideWire_bits n F r a arity owner q g x y k).2,sideWire_slot,sideWire_slot]
  by_cases he : observed n F r a arity owner k=observed n F r a arity owner j
  · have hk := (same_packet_iff n F r a arity owner j k).mp he
    cases hx : x k <;> simp only [he,hk,ite_true,Bool.false_eq_true,ite_false,
      SemiprimeStreamingTensor.bit,mul_zero,mul_one]
  · have hk := (same_packet_iff n F r a arity owner j k).not.mp he
    simp only [he,hk,ite_false,zero_mul]

/-- The actual original occurrence-indexed modular kernel row. -/
def kernelRow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (x : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length→Bool)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length) : Carrier ctx :=
  ∑k,(if SemiprimeD1OriginalDeformation.packet n F r a arity owner j=
      SemiprimeD1OriginalDeformation.packet n F r a arity owner k then
    SemiprimeD1UniversalModeData.entryValue ctx.precision
      (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
      (SemiprimeD1WireKernelOriginal.acquireOriginal a t
        (SemiprimeD1OriginalDeformation.slot n F r a arity owner j)
        (SemiprimeD1OriginalDeformation.slot n F r a arity owner k)) else 0)*SemiprimeStreamingTensor.bit (x k)

/-- The acquired original row is exactly its original D.8 Boolean row factor,
including the literal false-Y complement. -/
theorem wireRow_kernel (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (x y : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length→Bool)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hpos : ctx.Positive) (hp : 0<ctx.precision) :
    let assignment := originalEndpointBit n F r a arity owner (tagBits n F r a arity owner x y)
    wireRowValue ctx z n F r a arity owner (observed n F r a arity owner j) assignment t
      (sideWire n F r a arity owner true assignment j)=
      if y j then kernelRow ctx z n F r a arity owner t x j else 1-kernelRow ctx z n F r a arity owner t x j := by
  dsimp only
  unfold wireRowValue
  rw [(sideWire_bits n F r a arity owner q g x y j).1,column_kernel_sum ctx z n F r a arity owner q g x y j t hpos hp]
  rfl

end
end RiemannGaussian.SemiprimeD1OriginalPacketKernelRows
