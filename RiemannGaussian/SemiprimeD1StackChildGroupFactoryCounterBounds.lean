/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCatalogueCodecs
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLoop
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamBounds
/-! # Internally generated counter bounds, allowing repeated prepared packets
The actual global counter starts at zero at the whole source's front door.
Both its raw binary width and numeric value are bounded by the actual emitted
endpoint count. No original occurrence address or supplied unary ordinal is
identified with this distinct child-global domain.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryCounterBounds
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace Scan
export SemiprimeD1StackChildGroupFactoryBucketLoopView (selected finalPosition portWords)
end Scan
namespace Inc
export SemiprimeD1StackChildGroupFactoryBucketIncrement (successor)
end Inc
namespace Step
export SemiprimeD1StackChildGroupFactoryBucketVisitView (nextPosition)
end Step
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (buckets)
end Code
open SemiprimeBitArithmetic (bitValue)
/-- Actual full binary successor has its true numeric value, including padded source words. -/
theorem successor_value (position:List Bool):bitValue (Inc.successor position)=bitValue position+1:=
  SemiprimeD1StackChildGroupFactoryActivationLoop.advance_value position
/-- Raw successor padding is paid additively, independently of numeric value. -/
theorem successor_length (position:List Bool):(Inc.successor position).length≤position.length+2:=
  SemiprimeD1StackChildGroupFactoryActivationLoop.advance_length position
/-- One actual packet scan emits at most one occurrence per forward endpoint. -/
theorem selected_length (es:List E.Endpoint) (packet position:List Bool):
    (Scan.selected es packet position).length≤es.length:=by
  induction es generalizing position with
  | nil=>exact le_rfl
  | cons e es ih=>
    by_cases h:e.packet=packet
    · simpa only [Scan.selected,h,ite_true,List.length_cons] using Nat.add_le_add_right (ih (Inc.successor position)) 1
    · have ht:=ih position
      simp only [Scan.selected,h,ite_false,List.length_cons]
      omega
/-- Both final raw width and final value are bounded by the actual EOF-limited visit count. -/
theorem scan_bounds (es:List E.Endpoint) (packet position:List Bool):
    (Scan.finalPosition es packet position).length≤position.length+2*es.length ∧
      bitValue (Scan.finalPosition es packet position)≤bitValue position+es.length:=by
  induction es generalizing position with
  | nil=>simp only [Scan.finalPosition,List.length_nil,Nat.mul_zero,Nat.add_zero,le_refl,and_self]
  | cons e es ih=>
    by_cases h:e.packet=packet
    · have htail:=ih (Inc.successor position)
      have hl:=successor_length position
      have hv:=successor_value position
      simp only [Scan.finalPosition,Step.nextPosition,h,ite_true,List.length_cons]
      constructor <;> omega
    · have htail:=ih position
      simp only [Scan.finalPosition,Step.nextPosition,h,ite_false,List.length_cons]
      constructor <;> omega
/-- Every actually emitted ID inherits the bound of the same physical generated counter. -/
theorem selected_word_bounds (es:List E.Endpoint) (packet position:List Bool)
    (p:E.Endpoint×List Bool) (hp:p∈Scan.selected es packet position):
    p.2.length≤position.length+2*es.length ∧ bitValue p.2≤bitValue position+es.length:=by
  induction es generalizing position with
  | nil=>simp only [Scan.selected,List.not_mem_nil] at hp
  | cons e es ih=>
    by_cases h:e.packet=packet
    · simp only [Scan.selected,h,ite_true,List.mem_cons] at hp
      rcases hp with rfl|hp
      · simp only [List.length_cons];constructor <;> omega
      · have htail:=ih (Inc.successor position) hp
        have hl:=successor_length position
        have hv:=successor_value position
        simp only [List.length_cons];constructor <;> omega
    · have htail:=ih position (by simpa only [Scan.selected,h,ite_false] using hp)
      simp only [List.length_cons];constructor <;> omega
/-- Prepared duplicate packets may replicate endpoint occurrences K times; no uniqueness is assumed. -/
theorem catalogue_count (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool):
    ((Code.buckets packets es position).flatMap (fun b=>b.children)).length≤packets.length*es.length:=by
  induction packets generalizing position with
  | nil=>simp only [Code.buckets,List.flatMap_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons packet packets ih=>
    have ht:=ih (Scan.finalPosition es packet position)
    have hh:=selected_length es packet position
    simp only [Code.buckets,List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith
/-- Every ID in the complete actual catalogue has a raw/value bound in K times forward-endpoint count. -/
theorem catalogue_word_bounds (packets:List (List Bool)) (es:List E.Endpoint) (position:List Bool)
    (p:E.Endpoint×List Bool) (hp:p∈(Code.buckets packets es position).flatMap (fun b=>b.children)):
    p.2.length≤position.length+2*(packets.length*es.length) ∧
      bitValue p.2≤bitValue position+packets.length*es.length:=by
  induction packets generalizing position with
  | nil=>simp only [Code.buckets,List.flatMap_nil,List.not_mem_nil] at hp
  | cons packet packets ih=>
    simp only [Code.buckets,List.flatMap_cons,List.mem_append] at hp
    rcases hp with hp|hp
    · have hh:=selected_word_bounds es packet position p hp
      simp only [List.length_cons];constructor <;> nlinarith
    · have ht:=ih (Scan.finalPosition es packet position) hp
      have hs:=scan_bounds es packet position
      simp only [List.length_cons];constructor <;> nlinarith
/-- At the real zero-counter front door, generated ordinal VALUE is bounded by the actual emitted-node cap. -/
theorem generated_value (packets:List (List Bool)) (es:List E.Endpoint)
    (p:E.Endpoint×List Bool) (hp:p∈(Code.buckets packets es []).flatMap (fun b=>b.children)):
    bitValue p.2≤packets.length*es.length:=by
  have h:=catalogue_word_bounds packets es [] p hp
  simpa only [SemiprimeBitArithmetic.bitValue,Nat.zero_add] using h.2
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryCounterBounds
