/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCounterBounds
/-! # Exact internally acquired child-global numbering and packet-major order
Actual full binary successors number literal observed packet buckets in order,
including empty and repeated packets. No supplied numbering, permutation or
original-occurrence/child-occurrence domain identification is required.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryCatalogueNumbers
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace Scan
export SemiprimeD1StackChildGroupFactoryBucketLoopView (selected finalPosition)
end Scan
namespace Step
export SemiprimeD1StackChildGroupFactoryBucketVisitView (nextPosition)
end Step
namespace Inc
export SemiprimeD1StackChildGroupFactoryBucketIncrement (successor)
end Inc
namespace C
export SemiprimeD1StackChildGroupFactoryCounterBounds (successor_value)
end C
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (buckets)
end Code
open SemiprimeBitArithmetic (bitValue)
/-- Literal whole-packet filtering is exactly the actual sentinel-equality branch. -/
def filtered (es:List E.Endpoint) (packet:List Bool):List E.Endpoint:=es.filter fun e=>decide (e.packet=packet)
/-- Actual counter finishes at the initial value plus the number actually emitted. -/
theorem final_value (es:List E.Endpoint) (packet position:List Bool):
    bitValue (Scan.finalPosition es packet position)=bitValue position+(filtered es packet).length:=by
  induction es generalizing position with
  | nil=>simp only [Scan.finalPosition,filtered,List.filter_nil,List.length_nil,Nat.add_zero]
  | cons e es ih=>
    by_cases h:e.packet=packet
    · simp only [Scan.finalPosition,Step.nextPosition,h,ite_true]
      rw [ih,C.successor_value]
      simp only [filtered,List.filter_cons,h,decide_true,ite_true,List.length_cons]
      omega
    · simp only [Scan.finalPosition,Step.nextPosition,h,ite_false]
      simpa only [filtered,List.filter_cons,h,decide_false,Bool.false_eq_true,ite_false] using ih position
/-- Actual emitted binary IDs decode to the exact native ordered zipIdx, not an advised permutation. -/
theorem selected_numbered (es:List E.Endpoint) (packet position:List Bool):
    (Scan.selected es packet position).map (fun p=>(p.1,bitValue p.2))=
      (filtered es packet).zipIdx (bitValue position):=by
  induction es generalizing position with
  | nil=>rfl
  | cons e es ih=>
    by_cases h:e.packet=packet
    · simp only [Scan.selected,ite_true,List.map_cons,filtered,List.filter_cons,h,decide_true,
        List.zipIdx_cons]
      rw [ih,C.successor_value]
      rfl
    · simp only [Scan.selected,ite_false,filtered,List.filter_cons,h,decide_false]
      exact ih position
/-- Native packet-major endpoint order, preserving empty observed factors and duplicate prepared keys. -/
def ordered (packets:List (List Bool)) (es:List E.Endpoint):List E.Endpoint:=
  packets.flatMap (filtered es)
/-- Every acquired child-global word is the exact ordinal of that endpoint in actual packet-major order. -/
theorem catalogue_numbered (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool):
    ((Code.buckets packets es position).flatMap (fun b=>b.children)).map (fun p=>(p.1,bitValue p.2))=
      (ordered packets es).zipIdx (bitValue position):=by
  induction packets generalizing position with
  | nil=>rfl
  | cons packet packets ih=>
    simp only [Code.buckets,List.flatMap_cons,List.map_append,ordered,List.flatMap_cons]
    rw [selected_numbered,ih,final_value,List.zipIdx_append]
    rfl
/-- Exact zero-based generated numbering at the real whole source's entry. -/
theorem catalogue_zero (packets:List (List Bool)) (es:List E.Endpoint):
    ((Code.buckets packets es []).flatMap (fun b=>b.children)).map (fun p=>(p.1,bitValue p.2))=
      (ordered packets es).zipIdx:=by
  simpa only [SemiprimeBitArithmetic.bitValue] using catalogue_numbered packets es []
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryCatalogueNumbers
