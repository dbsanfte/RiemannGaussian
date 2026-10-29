/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagIndexMeaning
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoop
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryUnaryScopeBounds
/-! # Computed original-order words and their actual unary-converter costs
Binary query counters are bounded by actual reached child occurrences. A
missing tag returns the real filtered length; repeated old ports are retained.
Numeric original N and coefficient values never become unary addresses.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOrderBounds
namespace Meaning
export SemiprimeD1StackChildGroupFactoryTagIndexMeaning (tags allTags inner_value outer_value)
end Meaning
namespace V
export SemiprimeD1StackChildGroupFactoryTagVisitView (advance hit)
end V
namespace Inner
export SemiprimeD1StackChildGroupFactoryTagInnerView (finalPosition)
end Inner
namespace Outer
export SemiprimeD1StackChildGroupFactoryTagLoopView (finalPosition)
end Outer
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket)
end B
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point)
end P
namespace Old
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (orderWords)
export SemiprimeD1StackChildGroupFactoryOldPortOneView (answerWord)
end Old
open SemiprimeBitArithmetic (bitValue)
/-- One real query-counter advance changes raw width by at most two. -/
theorem advance_length (e:E.Endpoint) (target position:List Bool):
    (V.advance e target position).length≤position.length+2:=by
  by_cases h:bitValue e.vertex=bitValue target
  · simp only [V.advance,h,ite_true]
    exact SemiprimeD1StackChildGroupFactoryCounterBounds.successor_length position
  · simp only [V.advance,h,ite_false];omega
/-- First-hit short circuit and physical EOF both preserve an actual visit-count width bound. -/
theorem inner_length (children:List (E.Endpoint×List Bool)) (target tag position:List Bool):
    (Inner.finalPosition children target tag position).length≤position.length+2*children.length:=by
  induction children generalizing position with
  | nil=>simp only [Inner.finalPosition,List.length_nil,Nat.mul_zero,Nat.add_zero,le_refl]
  | cons p ps ih=>
    by_cases hh:V.hit p.1 target tag
    · simp only [Inner.finalPosition,hh,ite_true,List.length_cons];omega
    · have ht:=ih (V.advance p.1 target position)
      have ha:=advance_length p.1 target position
      simp only [Inner.finalPosition,hh,ite_false,List.length_cons];omega
/-- Every outer bucket is an actual byte traversal; no search index exceeds all child occurrences. -/
theorem outer_length (buckets:List B.Bucket) (target tag position:List Bool):
    (Outer.finalPosition buckets target tag position).length≤
      position.length+2*(buckets.flatMap (fun b=>b.children)).length:=by
  induction buckets generalizing position with
  | nil=>simp only [Outer.finalPosition,List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.add_zero,le_refl]
  | cons b bs ih=>
    have hi:=inner_length b.children target tag position
    by_cases hh:SemiprimeD1StackChildGroupFactoryTagInner.found b.children target tag=true
    · simp only [Outer.finalPosition,hh,ite_true,List.flatMap_cons,List.length_append];omega
    · have ht:=ih (Inner.finalPosition b.children target tag position)
      simp only [Outer.finalPosition,hh,Bool.false_eq_true,ite_false,List.flatMap_cons,List.length_append];omega
/-- Same-vertex tag filtering retains at most the real child count. -/
theorem tags_length (children:List (E.Endpoint×List Bool)) (target:List Bool):
    (Meaning.tags children target).length≤children.length:=by
  induction children with
  | nil=>exact le_rfl
  | cons p ps ih=>
    by_cases h:bitValue p.1.vertex=bitValue target <;>
      simp only [Meaning.tags,h,ite_true,ite_false,List.length_cons] <;> omega
/-- Complete ordered query tag list is bounded by the whole physical child catalogue. -/
theorem allTags_length (buckets:List B.Bucket) (target:List Bool):
    (Meaning.allTags buckets target).length≤(buckets.flatMap (fun b=>b.children)).length:=by
  induction buckets with
  | nil=>exact le_rfl
  | cons b bs ih=>
    have h:=tags_length b.children target
    simp only [Meaning.allTags,List.flatMap_cons,List.length_append] at ih ⊢
    omega
/-- Every actual answer starts at zero and is bounded in raw width AND numeric value by actual children. -/
theorem answer_bounds (buckets:List B.Bucket) (p:P.Point) (target:List Bool):
    (Old.answerWord buckets p target).length≤2*(buckets.flatMap (fun b=>b.children)).length ∧
      bitValue (Old.answerWord buckets p target)≤(buckets.flatMap (fun b=>b.children)).length:=by
  constructor
  · simpa only [Old.answerWord,List.length_nil,Nat.zero_add] using outer_length buckets target _ []
  · have h:=Meaning.outer_value buckets target
      (SemiprimeD1StackChildGroupFactoryTagBuild.rawTag p.edge p.side) []
    change bitValue (Old.answerWord buckets p target)=_ at h
    rw [h]
    simp only [SemiprimeBitArithmetic.bitValue,Nat.zero_add]
    exact (List.idxOf_le_length).trans (allTags_length buckets target)
/-- Every matching old port emits once, and every actual duplicate old port remains present. -/
theorem order_count (buckets:List B.Bucket) (points:List P.Point) (target:List Bool):
    (Old.orderWords buckets points target).length≤points.length:=by
  induction points with
  | nil=>exact le_rfl
  | cons p ps ih=>
    by_cases h:bitValue p.vertex=bitValue target <;>
      simp only [Old.orderWords,h,ite_true,ite_false,List.length_cons] <;> omega
/-- Every word passed to real Ordinal12 has this derived bound; no source VALUE bound is assumed. -/
theorem order_word_bounds (buckets:List B.Bucket) (points:List P.Point) (target word:List Bool)
    (hw:word∈Old.orderWords buckets points target):
    word.length≤2*(buckets.flatMap (fun b=>b.children)).length ∧
      bitValue word≤(buckets.flatMap (fun b=>b.children)).length:=by
  induction points with
  | nil=>simp only [Old.orderWords,List.not_mem_nil] at hw
  | cons p ps ih=>
    by_cases h:bitValue p.vertex=bitValue target
    · simp only [Old.orderWords,h,ite_true,List.mem_cons] at hw
      rcases hw with rfl|hw
      · exact answer_bounds buckets p target
      · exact ih hw
    · exact ih (by simpa only [Old.orderWords,h,ite_false] using hw)
/-- The SAME actual unary-converter clock on all computed order IDs is polynomial in physical visit counts. -/
theorem ordinal_time (buckets:List B.Bucket) (points:List P.Point) (target:List Bool):
    SemiprimeD1StackPortOrdinalStreamExecution.timeBound (Old.orderWords buckets points target)≤
      100*(points.length+1)*(2*(buckets.flatMap (fun b=>b.children)).length+1):=by
  have h:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le (Old.orderWords buckets points target)
    (2*(buckets.flatMap (fun b=>b.children)).length)
    (fun w hw=>(order_word_bounds buckets points target w hw).1)
    (fun w hw=>(order_word_bounds buckets points target w hw).2.trans (by omega))
  have hc:=order_count buckets points target
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOrderBounds
