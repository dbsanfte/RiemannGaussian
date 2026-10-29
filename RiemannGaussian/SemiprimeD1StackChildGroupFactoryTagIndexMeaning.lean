/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagLoopView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCounterBounds
/-! # Exact first idxOf meaning of the actual binary original-port query
The real local counter advances only on same-vertex earlier children. Whole
raw tags compare literally after physical trailing-TRUE sentinels. Thus the
computed word is the first idxOf, including list length when absent; no
permutation/order answer is supplied to the runtime program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagIndexMeaning
namespace V
export SemiprimeD1StackChildGroupFactoryTagVisitView (hit advance)
export SemiprimeD1StackChildGroupFactoryTagVisit (candidate)
end V
namespace Inner
export SemiprimeD1StackChildGroupFactoryTagInner (found)
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
open SemiprimeBitArithmetic (bitValue)
/-- Literal old tags in physically observed child order for one numeric old vertex. -/
def tags :List (E.Endpoint×List Bool)→List Bool→List (List Bool)
  | [],_=>[]
  | p::ps,target=>if bitValue p.1.vertex=bitValue target then V.candidate p.1::tags ps target else tags ps target
/-- Actual finite source tests find exactly membership in those same raw tags. -/
theorem found_iff (children:List (E.Endpoint×List Bool)) (target tag:List Bool):
    Inner.found children target tag=true ↔ tag∈tags children target:=by
  induction children with
  | nil=>simp only [Inner.found,tags,Bool.false_eq_true,List.not_mem_nil]
  | cons p ps ih=>
    by_cases hv:bitValue p.1.vertex=bitValue target
    · by_cases he:tag=V.candidate p.1
      · simp only [Inner.found,V.hit,hv,he,and_self,ite_true,tags,List.mem_cons,eq_self,true_or]
      · simp only [Inner.found,V.hit,hv,and_false,ite_false,tags,ite_true,List.mem_cons,he,false_or,ih]
    · have hn:¬V.hit p.1 target tag:=fun h=>hv h.1
      simp only [Inner.found,hn,ite_false,tags,hv,ih]
/-- The actual inner first-hit counter is exactly initial value plus first raw-tag index. -/
theorem inner_value (children:List (E.Endpoint×List Bool)) (target tag position:List Bool):
    bitValue (Inner.finalPosition children target tag position)=bitValue position+(tags children target).idxOf tag:=by
  induction children generalizing position with
  | nil=>simp only [Inner.finalPosition,tags,List.idxOf_nil,Nat.add_zero]
  | cons p ps ih=>
    by_cases hv:bitValue p.1.vertex=bitValue target
    · by_cases he:tag=V.candidate p.1
      · have hh:V.hit p.1 target tag:=⟨hv,he⟩
        simp only [Inner.finalPosition,hh,ite_true,tags,hv,List.idxOf_cons_eq _ he.symm,Nat.add_zero]
      · have hn:¬V.hit p.1 target tag:=fun h=>he h.2
        simp only [Inner.finalPosition,hn,ite_false,V.advance,hv,ite_true,tags]
        rw [List.idxOf_cons_ne _ (Ne.symm he),ih]
        have hs:=SemiprimeD1StackChildGroupFactoryCounterBounds.successor_value position
        change bitValue (SemiprimeD1StackChildGroupFactoryBucketIncrement.successor position)+_= _
        omega
    · have hn:¬V.hit p.1 target tag:=fun h=>hv h.1
      simpa only [Inner.finalPosition,hn,ite_false,V.advance,hv,tags] using ih position
/-- Ordered raw tags in actual packet-major child order, preserving duplicate buckets. -/
def allTags (buckets:List B.Bucket) (target:List Bool):List (List Bool):=
  buckets.flatMap fun b=>tags b.children target
/-- Whole real nested first-hit counter computes the exact native first idxOf. -/
theorem outer_value (buckets:List B.Bucket) (target tag position:List Bool):
    bitValue (Outer.finalPosition buckets target tag position)=bitValue position+(allTags buckets target).idxOf tag:=by
  induction buckets generalizing position with
  | nil=>simp only [Outer.finalPosition,allTags,List.flatMap_nil,List.idxOf_nil,Nat.add_zero]
  | cons b bs ih=>
    by_cases hh:Inner.found b.children target tag=true
    · have hm:= (found_iff b.children target tag).mp hh
      simp only [Outer.finalPosition,hh,ite_true,allTags,List.flatMap_cons,List.idxOf_append_of_mem hm]
      exact inner_value _ _ _ _
    · have hn:tag∉tags b.children target:=fun hm=>hh ((found_iff _ _ _).mpr hm)
      simp only [Outer.finalPosition,hh,Bool.false_eq_true,ite_false]
      rw [ih,inner_value]
      simp only [allTags,List.flatMap_cons,List.idxOf_append_of_notMem hn,List.idxOf_of_notMem hn]
      omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagIndexMeaning
