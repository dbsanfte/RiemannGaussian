/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationLoop
/-! # Exact old packet layout and paid physical history sizes
The key consists of nested outer coordinate fields followed by the actual high
index raw tail. Slot and index words stay binary, including all original padding.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationLayout
open SemiprimeD1StackPacketOrientationLoop
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame_length)
namespace Spec
export SemiprimeD1StackPacketOrientationEncoding (chunk field_original frame_append chunk_length)
end Spec
namespace Native
export SemiprimeD1OrientationBits (acquire)
end Native
/-- The chronological emitted outer fields plus raw remaining high word are EXACTLY the original packet key. -/
theorem chunks_key (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    chunks left right++(Native.acquire left right index).high=(Native.acquire left right index).key :=by
  induction left generalizing right index with
  | nil=>cases right with
    | nil=>rfl
    | cons r rs=>simp only [List.length_nil,List.length_cons] at hlen;omega
  | cons l ls ih=>cases right with
    | nil=>simp only [List.length_cons,List.length_nil] at hlen;omega
    | cons r rs=>
      have h:=ih rs (SemiprimeD1OrientationBits.coordinate l r index).next
        (by simp only [List.length_cons] at hlen;omega)
      simp only [chunks,Native.acquire,SemiprimeSourceHistogramKeyBits.pair_bits,List.append_assoc]
      rw [h]
      simp only [Spec.chunk,Spec.frame_append,List.nil_append,Spec.field_original l r index]
/-- Every logged physical frame byte is charged to the two actual source vectors. -/
theorem chunks_length (left right:List (List Bool)):
    (chunks left right).length ≤ 2*((vectorBits left).length+(vectorBits right).length) :=by
  induction left generalizing right with
  | nil=>cases right <;> simp only [chunks,List.length_nil,Nat.zero_le]
  | cons l ls ih=>cases right with
    | nil=>simp only [chunks,List.length_nil,Nat.zero_le]
    | cons r rs=>
      have h:=ih rs
      have hc:=Spec.chunk_length l r
      simp only [chunks,List.length_append,vectorBits,List.length_cons,frame_length]
      omega
/-- Every actual slot bit is charged to a real acquired vector entry. -/
theorem slots_length (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    (Native.acquire left right index).slots.length ≤ (vectorBits left).length :=by
  rw [SemiprimeD1OrientationBits.acquire_slots_length left right index hlen]
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length]
  omega
/-- The high word is an actual original index suffix; no numeric normalization or new tail is supplied. -/
theorem high_length (left right:List (List Bool)) (index:List Bool):
    (Native.acquire left right index).high.length ≤ index.length:=
  SemiprimeD1OrientationBits.acquire_high_length left right index
end RiemannGaussian.SemiprimeD1StackPacketOrientationLayout
