/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
/-! # Actual acquired rows and orientation from the retained OLD-index cache
The two whole frozen sources execute on direct physical aliases. Their success
bytes are really popped. OLD j is read only from the real class-bump cache.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryRows
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryComponents SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Reader
export SemiprimeD1StackPacketRowsMeaning (fields)
export SemiprimeD1StackPacketRowsOriginal (catalogue)
end Reader
namespace Native
export SemiprimeD1OrientationBits (acquire)
end Native
local notation "ctl"=>Label.local
/-- The actual reader validity output is a separate physical word, not either retained input/global. -/
theorem reader_flag_update (packets hist left right flag word:List Bool):
    Function.update (reader packets hist left right flag) SemiprimeD1StackPacketRows.success word=
      reader packets hist left right word :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- The actual orientation validity output is a separate physical word, not any retained catalogue/map global. -/
theorem orientation_flag_update (cat seen slots key slot high flag word:List Bool):
    Function.update (orientation cat seen slots key slot high flag) SemiprimeD1StackPacketOrientation.answer word=
      orientation cat seen slots key slot high word :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Own sum of two actual whole-source clocks, two real caller returns and two physical success pops. -/
def rowsBound (a:Nat) (owner factor index:List Bool):Nat:=
  (SemiprimeD1StackPacketRowsClock.polynomial (frame owner factor) (Reader.catalogue a)+1)+1+
    (SemiprimeD1StackPacketOrientationClock.polynomial (vectorBits (Reader.fields 64 a owner))
      (vectorBits (Reader.fields 64 a factor)) index+1)+1
/-- Both actual whole sources run from acquired key/catalogue/OLD-j words, preserving all class/edge/maps and discovery/history globals. -/
theorem rows_run (a:Nat) (owner factor:List Bool)
    (ho:owner∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (hf:factor∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (f:W.Words) (packets hist seen slots:List Bool) (hkey:f.raw=frame owner factor):
    ∃t ≤ rowsBound a owner factor f.frameScratch,Runs program t (ctl .readRows)
      (view f (reader packets hist [] [] []) (orientation (Reader.catalogue a) seen slots [] [] [] []))
      (ctl .copyEdgeOperand)
      (view f (reader packets hist (vectorBits (Reader.fields 64 a owner)) (vectorBits (Reader.fields 64 a factor)) [])
        (orientation (Reader.catalogue a) seen slots
          (Native.acquire (Reader.fields 64 a owner) (Reader.fields 64 a factor) f.frameScratch).key
          (Native.acquire (Reader.fields 64 a owner) (Reader.fields 64 a factor) f.frameScratch).slots
          (Native.acquire (Reader.fields 64 a owner) (Reader.fields 64 a factor) f.frameScratch).high [])) :=by
  let left:=Reader.fields 64 a owner
  let right:=Reader.fields 64 a factor
  let cat:=Reader.catalogue a
  let rr:=reader packets hist [] [] []
  let oo:=orientation cat seen slots [] [] [] []
  have hin:∀k,view f rr oo (readerStack k)=
      (SemiprimeD1StackPacketRows.initial (frame owner factor) cat).data k:=by
    intro k;rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> first | rfl | exact hkey
  obtain ⟨t0,ht0,h0⟩:=reader_call a owner factor ho hf f rr oo hin
  rw [reader_patch] at h0
  let rr1:=reader packets hist (vectorBits left) (vectorBits right) [true]
  have h1:=pop_run .rowsValid (ctl .abort) (ctl .abort) (ctl .orient) (readerStack R.success)
    (view f rr1 oo) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update (view f rr1 oo) (readerAllocation SemiprimeD1StackPacketRows.success) []) at h1
  rw [update_readerAllocation] at h1
  dsimp only [rr1] at h1
  rw [reader_flag_update] at h1
  let rr2:=reader packets hist (vectorBits left) (vectorBits right) []
  have hop:∀k,view f rr2 oo (orientationStack k)=(SemiprimeD1StackPacketOrientation.initial
      (vectorBits left) (vectorBits right) f.frameScratch).data k:=by
    intro k;rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  have hl: left.length=a:=(SemiprimeD1StackPacketRowsMeaning.original_lookup 64 a owner ho).2.2
  have hr: right.length=a:=(SemiprimeD1StackPacketRowsMeaning.original_lookup 64 a factor hf).2.2
  obtain ⟨t2,ht2,h2⟩:=orientation_call left right f.frameScratch (hl.trans hr.symm) f rr2 oo hop
  rw [orientation_patch] at h2
  let oriented:=Native.acquire left right f.frameScratch
  let oo1:=orientation cat seen slots oriented.key oriented.slots oriented.high [true]
  have h3:=pop_run .orientationValid (ctl .abort) (ctl .abort) (ctl .copyEdgeOperand) (orientationStack O.answer)
    (view f rr2 oo1) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update (view f rr2 oo1)
    (orientationAllocation SemiprimeD1StackPacketOrientation.answer) []) at h3
  rw [update_orientationAllocation] at h3
  dsimp only [oo1] at h3
  rw [orientation_flag_update] at h3
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,h⟩
  unfold rowsBound
  dsimp only [left,right,cat] at ht0 ht2 ⊢
  omega
end RiemannGaussian.SemiprimeD1StackPacketInventoryRows
