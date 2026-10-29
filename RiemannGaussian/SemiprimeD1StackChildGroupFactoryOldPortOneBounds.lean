/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsByteBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagQueryBounds
/-! # Actual original-port filtering and completed query clock
The real numeric comparison chooses the branch. Actual restored physical work
roles establish the query ABI; no hit/index/readiness flag is an input word.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOneBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace One
export SemiprimeD1StackChildGroupFactoryOldPortOne (picked timeBound)
end One
namespace Pick
export SemiprimeD1StackChildGroupFactoryOldPortPick (result parsed built cleanupTime timeBound)
end Pick
namespace PV
export SemiprimeD1StackChildGroupFactoryOldPortPickView (result_other result_headerClean result_childClean result_tag)
end PV
namespace Loop
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (Fresh freshRole headerFresh childFresh)
end Loop
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point payload result)
end P
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end B
namespace Build
export SemiprimeD1StackChildGroupFactoryTagBuild (rawTag timeBound)
end Build
namespace Q
export SemiprimeD1StackChildGroupFactoryTagQueryBounds (Ready timeBound_le)
end Q
/-- Literal old-record fields, plus a positive delimiter allowance. -/
def pointBytes (p:P.Point):Nat:=p.vertex.length+p.edge.length+p.side.length+1
/-- The actual raw edge/side target tag is paid by its source fields. -/
theorem tag_length (p:P.Point):(Build.rawTag p.edge p.side).length≤3*pointBytes p:=by
  simp only [Build.rawTag,SemiprimeSourceHistogramKeyBits.frame_length,pointBytes]
  omega
/-- Full actual parse/filter/tag-build/field-cleanup cost is linear in physical bytes. -/
theorem pick_time (p:P.Point) (target:List Bool):
    Pick.timeBound p target≤1000*(pointBytes p+target.length+1):=by
  have hv:=SemiprimeD1StackChildGroupFactoryOperationBounds.vertex_time p.vertex target
  unfold Pick.timeBound SemiprimeD1StackChildGroupFactoryOldPortParse.timeBound
    P.payload Pick.cleanupTime Build.timeBound
  simp only [SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  split_ifs <;> dsimp only [pointBytes] at * <;> omega
/-- The real field/tag boundary has only local raw-byte growth, independent of previous runtime. -/
theorem picked_word_le (before:Stack→List Bool) (p:P.Point) (tail target:List Bool) (cap:Nat)
    (hc:∀k,(before k).length≤cap) (ht:tail.length≤cap):
    ∀k,(One.picked before p tail target k).length≤cap+3*pointBytes p:=by
  have htag:=tag_length p
  intro k
  have hk:=hc k
  simp only [One.picked,Pick.result,SemiprimeD1StackChildGroupFactoryOldPortCleanup.result,
    Pick.built,Pick.parsed,P.result,Function.update_apply]
  split_ifs <;> (try simp only [Function.update_apply]) <;> (try split_ifs) <;>
    (try simp only [List.length_nil]) <;> dsimp only [pointBytes] at * <;> omega
/-- Every one of the actual query preconditions follows from the restored caller bank. -/
theorem picked_ready (before:Stack→List Bool) (buckets:List B.Bucket) (p:P.Point) (tail target:List Bool)
    (hf:Loop.Fresh before) (hs:before (aux .buckets)=B.records buckets)
    (ht:before (aux .vertexKey)=target) (ha:∀k,before (arithmetic k)=[])
    (h:SemiprimeBitArithmetic.bitValue p.vertex=SemiprimeBitArithmetic.bitValue target):
    Q.Ready (One.picked before p tail target) buckets target (Build.rawTag p.edge p.side) []:=by
  have hh:=Loop.headerFresh before hf
  have hch:=Loop.childFresh before hf
  constructor
  · exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hs
  · exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans (hf 0)
  · exact PV.result_headerClean _ _ _ _ hh
  · exact PV.result_childClean _ _ _ _ hch
  · exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans ht
  · exact PV.result_tag _ _ _ _ h
  · exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans (hf 12)
  · exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans (hf 10)
  · exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans (hf 11)
  · exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans (hf 18)
  · exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans (hf 19)
  · intro k
    exact (PV.result_other _ _ _ _ _
      (by intro j;fin_cases j <;> simp [SemiprimeD1StackChildGroupFactoryOldPortCleanup.role,arithmetic,aux])
      (by simp [arithmetic,aux]) (by simp [arithmetic,aux])).trans (ha k)
/-- Whole actual iteration includes the acquired nested search and its paid unread-suffix cleanup. -/
theorem timeBound_le (before:Stack→List Bool) (buckets:List B.Bucket) (p:P.Point) (tail target:List Bool)
    (cap D:Nat) (hc:∀k,(before k).length≤cap) (htail:tail.length≤cap)
    (hf:Loop.Fresh before) (hs:before (aux .buckets)=B.records buckets)
    (ht:before (aux .vertexKey)=target) (ha:∀k,before (arithmetic k)=[])
    (hd:(buckets.flatMap (fun b=>b.children)).length≤D):
    One.timeBound before buckets p tail target≤1000000*(cap+pointBytes p+target.length+
      (B.records buckets).length+SemiprimeD1StackChildGroupFactoryTagLoop.timeBound buckets target
        (Build.rawTag p.edge p.side) []+D+1):=by
  have hpick:=pick_time p target
  by_cases h:SemiprimeBitArithmetic.bitValue p.vertex=SemiprimeBitArithmetic.bitValue target
  · have hr:=picked_ready before buckets p tail target hf hs ht ha h
    have hbytes:=picked_word_le before p tail target cap hc htail
    have hquery:=Q.timeBound_le (One.picked before p tail target) buckets target
      (Build.rawTag p.edge p.side) [] hr (cap+3*pointBytes p) (2*D) hbytes
      (by simp only [List.length_nil,Nat.zero_add];omega)
    have htag:=tag_length p
    simp only [One.timeBound,h,ite_true]
    omega
  · simp only [One.timeBound,h,ite_false,Nat.add_zero]
    omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOneBounds
