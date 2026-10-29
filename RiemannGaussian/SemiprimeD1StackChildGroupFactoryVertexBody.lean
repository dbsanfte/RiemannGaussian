/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsSourceView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsSourceView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexIncrement
/-! # Complete actual per-old-vertex left-scope and original-order acquisition
Both whole physical sources execute before one real binary old-vertex increment.
Every original vertex, including isolated vertices, uses the same literal path.
No tensor/coefficient/table/decoded colour or supplied scope/order is an input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBody
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Left
export SemiprimeD1StackChildGroupFactoryLeftPortsSource (result timeBound source_trace drained)
end Left
namespace LV
export SemiprimeD1StackChildGroupFactoryLeftPortsSourceView (FreshExceptGlobal drained_fresh result_other result_fresh result_ordinal)
end LV
namespace Old
export SemiprimeD1StackChildGroupFactoryOldPortsSource (result timeBound source_trace)
end Old
namespace OV
export SemiprimeD1StackChildGroupFactoryOldPortsSourceView (result_other result_fresh result_ordinal)
end OV
namespace Inc
export SemiprimeD1StackChildGroupFactoryVertexIncrement (successor timeBound source_trace)
end Inc
namespace Work
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (Fresh freshRole headerFresh childFresh)
end Work
namespace Header
export SemiprimeD1StackChildGroupFactoryBucketHeader (cleanRoles)
end Header
namespace Child
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Child
namespace Raw
export SemiprimeD1StackChildGroupFactoryChildCleanup (role)
end Raw
namespace Early
export SemiprimeD1StackChildGroupFactoryTagEarlyClear (role)
end Early
namespace Reuse
export SemiprimeD1StackChildGroupFactoryPortReuse (role bankRole)
end Reuse
namespace Points
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end Points
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end Buckets
/-- Actual data-only readiness; the saved global word may be nonempty before its real drain. -/
structure Ready (before:Stack→List Bool):Prop where
  work:LV.FreshExceptGlobal before
  arithmetic_clean:∀k,before (arithmetic k)=[]
  ordinal_clean:∀k,before (ordinal k)=[]
  oldReader_empty:before (aux .oldReader)=[]
  portBank_empty:before (aux .portBank)=[]
  portHistory_empty:before (aux .portHistory)=[]
  orderBank_empty:before (aux .orderBank)=[]
  orderHistory_empty:before (aux .orderHistory)=[]
/-- The actual left-scope source retains the separate four arithmetic tapes. -/
theorem left_arithmetic (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target:List Bool)
    (ha:∀k,before (arithmetic k)=[]):∀k,Left.result before buckets target (arithmetic k)=[]:=by
  intro k
  exact (LV.result_other _ _ _ _ (by intro j;fin_cases j <;> simp [Raw.role,arithmetic,aux])
    (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])
    (by intro j;fin_cases j <;> simp [Reuse.role,Reuse.bankRole,ordinal,arithmetic,aux])
    (by simp [arithmetic,aux])).trans (ha k)
/-- The whole old-port source retains those same four actual arithmetic tapes. -/
theorem old_arithmetic (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool)
    (ha:∀k,before (arithmetic k)=[]):∀k,Old.result before points buckets target (arithmetic k)=[]:=by
  intro k
  exact (OV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> simp [Early.role,arithmetic,aux])
    (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])
    (by simp [arithmetic,aux]) (by simp [arithmetic,aux])
    (by intro j;fin_cases j <;> simp [Reuse.role,Reuse.bankRole,ordinal,arithmetic,aux])
    (by simp [arithmetic,aux])).trans (ha k)
/-- Complete actual bank after both whole sources and the physically executed binary increment. -/
def result (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool):Stack→List Bool:=
  Function.update (Old.result (Left.result before buckets target) points buckets target)
    (aux .vertexKey) (Inc.successor target)
/-- Sum of SAME actual whole left/old sources and the real final increment. -/
def timeBound (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool):Nat:=
  Left.timeBound before buckets target+Old.timeBound (Left.result before buckets target) points buckets target+Inc.timeBound target
/-- One COMPLETE real old-vertex iteration, including isolated vertices and every actual source/return. -/
theorem source_trace (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (target:List Bool)
    (hp:before (aux .oldEndpoints)=Points.records points) (hb:before (aux .buckets)=Buckets.records buckets)
    (ht:before (aux .vertexKey)=target) (hr:Ready before):
    ∃t≤timeBound before points buckets target,
      Runs program t (.local 9 5) before (.local 9 4) (result before points buckets target):=by
  have hd:=LV.drained_fresh before hr.work
  have hh:∀k∈Header.cleanRoles,before k=[]:=by
    simpa [Left.drained,Header.cleanRoles,aux,field] using Work.headerFresh (Left.drained before) hd
  have hz:∀k∈Child.cleanRoles,k≠aux .globalPosition→before k=[]:=by
    intro k hk hn
    have h:=Work.childFresh (Left.drained before) hd k hk
    simpa only [Left.drained,Function.update_of_ne hn] using h
  obtain ⟨x,hx,h0⟩:=Left.source_trace before buckets target hb (hr.work 0 (by decide)) hh hz ht
    (hr.work 18 (by decide)) (hr.work 19 (by decide)) hr.arithmetic_clean hr.ordinal_clean hr.portHistory_empty hr.portBank_empty
  let leftState:=Left.result before buckets target
  have hp':leftState (aux .oldEndpoints)=Points.records points:=
    (LV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans hp
  have hb':leftState (aux .buckets)=Buckets.records buckets:=
    (LV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans hb
  have ht':leftState (aux .vertexKey)=target:=
    (LV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans ht
  have hold:leftState (aux .oldReader)=[]:=
    (LV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans hr.oldReader_empty
  have horderBank:leftState (aux .orderBank)=[]:=
    (LV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans hr.orderBank_empty
  have horderHistory:leftState (aux .orderHistory)=[]:=
    (LV.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans hr.orderHistory_empty
  have hwork:Work.Fresh leftState:=LV.result_fresh _ _ _ hr.work
  have ha:∀k,leftState (arithmetic k)=[]:=left_arithmetic _ _ _ hr.arithmetic_clean
  obtain ⟨y,hy,h1⟩:=Old.source_trace leftState points buckets target hp' hold hb' ht' hwork ha
    (LV.result_ordinal _ _ _) horderHistory horderBank
  let oldState:=Old.result leftState points buckets target
  have hkey:oldState (aux .vertexKey)=target:=
    (OV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans ht'
  have hclean:Work.Fresh oldState:=OV.result_fresh _ _ _ _ hwork
  have h2:=Inc.source_trace oldState target hkey (hclean 19) (old_arithmetic _ _ _ _ ha)
  refine ⟨x+y+Inc.timeBound target,?_,?_⟩
  · dsimp only [timeBound,leftState] at hy ⊢
    omega
  · have hwhole:=join h0 (join h1 h2)
    simpa only [result,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBody
