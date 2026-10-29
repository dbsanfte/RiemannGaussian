/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBody
/-! # One complete physical vertex body has a fixed byte/count bound
The intermediate bank cap follows this SAME actual left-source execution once.
Across later vertices the separate additive row potential is used instead of
feeding this local runtime estimate into the next iteration's operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBodyBounds
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackProcedureTrace
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready timeBound left_arithmetic)
end Body
namespace Left
export SemiprimeD1StackChildGroupFactoryLeftPortsSource (result timeBound source_trace drained)
end Left
namespace LV
export SemiprimeD1StackChildGroupFactoryLeftPortsSourceView (result_other result_fresh drained_fresh)
end LV
namespace Work
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (headerFresh childFresh Fresh)
end Work
namespace B
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end B
namespace P
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end P
namespace Old
export SemiprimeD1StackChildGroupFactoryOldPortsBounds (source_time)
end Old
namespace OB
export SemiprimeD1StackChildGroupFactoryOldPortOneBounds (pointBytes)
export SemiprimeD1StackChildGroupFactoryOldPortsLoopBounds (queryBudget)
end OB
/-- Actual complete left-scope allowance, including converted ordinal VALUE. -/
def leftBudget (cap H D K G:Nat):Nat:=1000000*(cap+G+H+1)*(D+1)*(K+1)
/-- One fixed formula bounds both actual full source calls and the binary successor. -/
def bodyBudget (cap H D K J G:Nat):Nat:=
  leftBudget cap H D K G+1000000000*
    (cap+leftBudget cap H D K G+J*(4*D+2)+3*H+OB.queryBudget H D K+D+1)*(J+1)+100*(H+1)
/-- Ready caller data, not an advised flag, discharges the actual left-source ABI. -/
theorem left_trace (before:Stack→List Bool) (buckets:List B.Bucket) (target:List Bool)
    (hr:Body.Ready before) (hb:before (aux .buckets)=B.records buckets)
    (ht:before (aux .vertexKey)=target):
    ∃t≤Left.timeBound before buckets target,
      Runs program t (.local 9 5) before (.local 11 6) (Left.result before buckets target):=by
  have hd:=LV.drained_fresh before hr.work
  have hh:∀k∈SemiprimeD1StackChildGroupFactoryBucketHeader.cleanRoles,before k=[]:=by
    simpa [Left.drained,SemiprimeD1StackChildGroupFactoryBucketHeader.cleanRoles,aux,field] using Work.headerFresh (Left.drained before) hd
  have hz:∀k∈SemiprimeD1StackChildGroupFactoryChildParse.cleanRoles,k≠aux .globalPosition→before k=[]:=by
    intro k hk hn
    have h:=Work.childFresh (Left.drained before) hd k hk
    simpa only [Left.drained,Function.update_of_ne hn] using h
  exact Left.source_trace before buckets target hb (hr.work 0 (by decide)) hh hz ht
    (hr.work 18 (by decide)) (hr.work 19 (by decide)) hr.arithmetic_clean hr.ordinal_clean
    hr.portHistory_empty hr.portBank_empty
/-- SAME actual left-source trace bounds every intermediate stopped physical word. -/
theorem left_word_le (before:Stack→List Bool) (buckets:List B.Bucket) (target:List Bool)
    (cap:Nat) (hc:∀k,(before k).length≤cap) (hr:Body.Ready before)
    (hb:before (aux .buckets)=B.records buckets) (ht:before (aux .vertexKey)=target):
    ∀k,(Left.result before buckets target k).length≤cap+Left.timeBound before buckets target:=by
  obtain ⟨t,htime,hrun⟩:=left_trace before buckets target hr hb ht
  let start:C.State Stack Label:=⟨some (.local 9 5),none,none,before,[]⟩
  obtain ⟨finish,hf,hat⟩:=hrun [] start ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program t cap start finish hc hf
  rw [hat.2.1] at hd
  intro k
  exact (hd k).trans (Nat.add_le_add_left htime _)
/-- Whole actual body budget, with no supplied route, order, scope or output sizes. -/
theorem timeBound_le (before:Stack→List Bool) (points:List P.Point) (buckets:List B.Bucket)
    (target:List Bool) (cap H D G:Nat) (hc:∀k,(before k).length≤cap) (hr:Body.Ready before)
    (hp:before (aux .oldEndpoints)=P.records points) (hb:before (aux .buckets)=B.records buckets)
    (ht:before (aux .vertexKey)=target) (hbs:(B.records buckets).length≤H)
    (hps:(P.records points).length≤H) (htar:target.length≤H)
    (hd:(buckets.flatMap (fun b=>b.children)).length≤D)
    (hv:∀p∈buckets.flatMap (fun b=>b.children),SemiprimeBitArithmetic.bitValue p.2≤G):
    Body.timeBound before points buckets target≤bodyBudget cap H D buckets.length points.length G:=by
  have hbsCap:(B.records buckets).length≤cap:=by rw [←hb];exact hc _
  have hleft:=SemiprimeD1StackChildGroupFactoryLeftPortsBounds.source_time before buckets target cap D G hc hbsCap hd hv
  have hleft':Left.timeBound before buckets target≤leftBudget cap H D buckets.length G:=by
    apply hleft.trans
    dsimp only [leftBudget]
    gcongr
  have hafter:=left_word_le before buckets target cap hc hr hb ht
  have hafter':∀k,(Left.result before buckets target k).length≤cap+leftBudget cap H D buckets.length G:=by
    intro k;exact (hafter k).trans (Nat.add_le_add_left hleft' _)
  have same (k:Stack) (hn:∀j,SemiprimeD1StackChildGroupFactoryChildCleanup.role j≠k)
      (he:k≠aux .endpointReader) (ho:k≠aux .outerReader) (hh:k≠aux .portHistory)
      (hx:∀j,SemiprimeD1StackChildGroupFactoryPortReuse.role false j≠k) (hv:k≠aux .vertexHistory):
      Left.result before buckets target k=before k:=LV.result_other _ _ _ _ hn he ho hh hx hv
  have hp':Left.result before buckets target (aux .oldEndpoints)=P.records points:=
    (same _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans hp
  have hb':Left.result before buckets target (aux .buckets)=B.records buckets:=
    (same _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans hb
  have ht':Left.result before buckets target (aux .vertexKey)=target:=
    (same _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)
      (by intro j;fin_cases j <;> decide) (by decide)).trans ht
  have hpsCap:(P.records points).length≤cap+leftBudget cap H D buckets.length G:=by
    rw [←hp'];exact hafter' _
  have hold:=Old.source_time (Left.result before buckets target) points buckets target
    (cap+leftBudget cap H D buckets.length G) H D hafter' (LV.result_fresh _ _ _ hr.work) hpsCap hb' ht'
    (Body.left_arithmetic _ _ _ hr.arithmetic_clean) hbs
    (fun p hp=>(SemiprimeD1StackChildGroupFactoryStructuralByteBounds.point_fields points p hp).trans hps) htar hd
  have hinc:=SemiprimeD1StackChildGroupFactoryOperationBounds.increment_time target
  change SemiprimeD1StackChildGroupFactoryVertexIncrement.timeBound target≤100*(target.length+1) at hinc
  dsimp only [Body.timeBound,bodyBudget]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBodyBounds
