/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationClassify
/-! # Whole actual paired-vector coordinate loop
The loop consumes real vector tags, calls both real Field parsers, performs
actual numeric classification, and preserves exact raw remaining index bits.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationLoop
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationPrimitives
open SemiprimeD1StackPacketOrientationRowView SemiprimeD1StackPacketOrientationClassify
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame frame_length)
namespace Spec
export SemiprimeD1StackPacketOrientationEncoding (chunk slot next slot_original next_original field_original frame_append)
end Spec
namespace Native
export SemiprimeD1OrientationBits (acquire)
end Native
local notation "ctl"=>Label.local
/-- Actual two physical vector-reader words, including literal false end markers. -/
def streams (left right:List (List Bool)) (side:Bool):List Bool:=if side then vectorBits right else vectorBits left
/-- Chronological outer packet fields, without a vector tag or terminator. -/
def chunks:List (List Bool)→List (List Bool)→List Bool
  | l::ls,r::rs=>Spec.chunk l r++chunks ls rs
  | _,_=>[]
/-- Sum of the actual parser/comparison/logger caps, plus real end-tag/EOF checks. -/
def loopBound:List (List Bool)→List (List Bool)→Nat
  | l::ls,r::rs=>1100*(l.length+r.length+1)+loopBound ls rs
  | _,_=>4
/-- Entire real paired loop, including zero coordinates and every empty colour field. -/
theorem loop_run (originals:Fin 3→List Bool) (left right:List (List Bool)) (index kh sh ko so hi:List Bool)
    (hlen:left.length=right.length):
    ∃t ≤ loopBound left right,Runs program t (ctl .leftTag)
      (rowView originals (streams left right) index (fun _=>[]) kh sh ko so hi) (ctl .copyHighOutput)
      (rowView originals (fun _=>[]) (Native.acquire left right index).high (fun _=>[])
        ((chunks left right).reverse++kh) ((Native.acquire left right index).slots.reverse++sh) ko so hi) :=by
  induction left generalizing right index kh sh with
  | nil=>cases right with
    | cons r rs=>simp only [List.length_nil,List.length_cons] at hlen;omega
    | nil=>
      let beforeRight:Bool→List Bool:=fun side=>if side then [false] else []
      have h0:=pop_run .leftTag (ctl .reject) (ctl .rightEnd) (ctl .rightTag) (reader false)
        (rowView originals (streams [] []) index (fun _=>[]) kh sh ko so hi) [false] rfl rfl
      rw [update_reader] at h0
      simp only [List.tail_cons,List.head?_cons,SemiprimeD1StackBytecode.choose] at h0
      have hu:Function.update (streams [] []) false []=beforeRight:=by funext side;cases side <;> rfl
      rw [hu] at h0
      have h1:=pop_run .rightEnd (ctl .reject) (ctl .leftEOF) (ctl .reject) (reader true)
        (rowView originals beforeRight index (fun _=>[]) kh sh ko so hi) [false] rfl rfl
      rw [update_reader] at h1
      simp only [List.tail_cons,List.head?_cons,SemiprimeD1StackBytecode.choose] at h1
      have hv:Function.update beforeRight true []=(fun _=>[] :Bool→List Bool):=by funext side;cases side <;> rfl
      rw [hv] at h1
      have h2:=peek_run .leftEOF (ctl .rightEOF) (ctl .reject) (ctl .reject) (reader false)
        (rowView originals (fun _=>[]) index (fun _=>[]) kh sh ko so hi) [] rfl rfl
      have h3:=peek_run .rightEOF (ctl .copyHighOutput) (ctl .reject) (ctl .reject) (reader true)
        (rowView originals (fun _=>[]) index (fun _=>[]) kh sh ko so hi) [] rfl rfl
      have h:=join (join (join h0 h1) h2) h3
      refine ⟨4,le_rfl,?_⟩
      simpa only [Native.acquire,SemiprimeSourceCompactBits.copy_bits,chunks,List.reverse_nil,List.nil_append,List.head?_nil,SemiprimeD1StackBytecode.choose] using h
  | cons l ls ih=>cases right with
    | nil=>simp only [List.length_cons,List.length_nil] at hlen;omega
    | cons r rs=>
      let beforeRight:Bool→List Bool:=fun side=>if side then vectorBits (r::rs) else frame l (vectorBits ls)
      let beforeLeft:Bool→List Bool:=fun side=>if side then frame r (vectorBits rs) else frame l (vectorBits ls)
      let beforeLast:Bool→List Bool:=fun side=>if side then frame r (vectorBits rs) else vectorBits ls
      have h0:=pop_run .leftTag (ctl .reject) (ctl .rightEnd) (ctl .rightTag) (reader false)
        (rowView originals (streams (l::ls) (r::rs)) index (fun _=>[]) kh sh ko so hi)
        (true::frame l (vectorBits ls)) rfl rfl
      rw [update_reader] at h0
      simp only [List.tail_cons,List.head?_cons,SemiprimeD1StackBytecode.choose] at h0
      have hu:Function.update (streams (l::ls) (r::rs)) false (frame l (vectorBits ls))=beforeRight:=by funext side;cases side <;> rfl
      rw [hu] at h0
      have h1:=pop_run .rightTag (ctl .reject) (ctl .reject) (ctl (.parse false)) (reader true)
        (rowView originals beforeRight index (fun _=>[]) kh sh ko so hi) (true::frame r (vectorBits rs)) rfl rfl
      rw [update_reader] at h1
      simp only [List.tail_cons,List.head?_cons,SemiprimeD1StackBytecode.choose] at h1
      have hv:Function.update beforeRight true (frame r (vectorBits rs))=beforeLeft:=by funext side;cases side <;> rfl
      rw [hv] at h1
      have h2:=field_valid false (.parse false) (.valid false) (ctl (.parse true)) rfl rfl
        (rowView originals beforeLeft index (fun _=>[]) kh sh ko so hi) l (vectorBits ls) rfl rfl rfl rfl
      change Runs program _ _ _ _ (Function.update (Function.update
        (rowView originals beforeLeft index (fun _=>[]) kh sh ko so hi) (reader false) (vectorBits ls)) (colour false) l) at h2
      rw [update_reader,update_colour] at h2
      have hw:Function.update beforeLeft false (vectorBits ls)=beforeLast:=by funext side;cases side <;> rfl
      have hc:Function.update (fun _=>[] :Bool→List Bool) false l=colours l []:=by funext side;cases side <;> rfl
      rw [hw,hc] at h2
      have h3:=field_valid true (.parse true) (.valid true) (ctl (.copyOperand false false)) rfl rfl
        (rowView originals beforeLast index (colours l []) kh sh ko so hi) r (vectorBits rs) rfl rfl rfl rfl
      change Runs program _ _ _ _ (Function.update (Function.update
        (rowView originals beforeLast index (colours l []) kh sh ko so hi) (reader true) (vectorBits rs)) (colour true) r) at h3
      rw [update_reader,update_colour] at h3
      have hz:Function.update beforeLast true (vectorBits rs)=streams ls rs:=by funext side;cases side <;> rfl
      have hd:Function.update (colours l []) true r=colours l r:=by funext side;cases side <;> rfl
      rw [hz,hd] at h3
      obtain ⟨t,ht,h4⟩:=coordinate_run originals (streams ls rs) index l r kh sh ko so hi
      obtain ⟨u,hu,h5⟩:=ih rs (Spec.next l r index) ((Spec.chunk l r).reverse++kh)
        (Spec.slot l r index::sh) (by simp only [List.length_cons] at hlen;omega)
      have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
      refine ⟨1+1+(8*l.length+8)+(8*r.length+8)+t+u,?_,?_⟩
      · change _ ≤ 1100*(l.length+r.length+1)+loopBound ls rs
        unfold stepBound at ht
        omega
      · simpa only [Spec.next_original,Spec.slot_original,chunks,List.reverse_append,List.append_assoc,
          Native.acquire,SemiprimeSourceHistogramKeyBits.pair_bits,List.reverse_cons,List.singleton_append] using h
/-- Paired parser/classifier/logger work is bounded by the two actual serialized source vectors. -/
theorem loopBound_le (left right:List (List Bool)) (hlen:left.length=right.length):
    loopBound left right ≤ 1100*((vectorBits left).length+(vectorBits right).length+1) :=by
  induction left generalizing right with
  | nil=>cases right with
    | nil=>simp only [loopBound,vectorBits,List.length_cons,List.length_nil];omega
    | cons r rs=>simp only [List.length_nil,List.length_cons] at hlen;omega
  | cons l ls ih=>cases right with
    | nil=>simp only [List.length_cons,List.length_nil] at hlen;omega
    | cons r rs=>
      have h:=ih rs (by simp only [List.length_cons] at hlen;omega)
      simp only [loopBound,vectorBits,List.length_cons,frame_length]
      omega
end RiemannGaussian.SemiprimeD1StackPacketOrientationLoop
