/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortPickView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSource
/-! # Complete actual one-original-port ordering iteration
The actual original record is parsed and numerically filtered. A matching
vertex physically builds its old tag and executes the ENTIRE real nested
first-index query, answer-copy, paid early disposal, ordered log and cleanup.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOne
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Pick
export SemiprimeD1StackChildGroupFactoryOldPortPick (next result timeBound source_trace)
end Pick
namespace PV
export SemiprimeD1StackChildGroupFactoryOldPortPickView (result_other result_tag result_headerClean result_childClean)
end PV
namespace Parse
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point payload cleanRoles)
end Parse
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryOldPortCleanup (role)
end Cleanup
namespace Header
export SemiprimeD1StackChildGroupFactoryBucketHeader (cleanRoles)
end Header
namespace Child
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Child
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end Buckets
namespace Build
export SemiprimeD1StackChildGroupFactoryTagBuild (rawTag)
end Build
namespace Query
export SemiprimeD1StackChildGroupFactoryTagSource (result timeBound source_trace)
end Query
open SemiprimeBitArithmetic (bitValue)
/-- Actual parsed/filtered/target-tag boundary of the literal original-port source. -/
def picked (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool):Stack→List Bool:=Pick.result before p tail target
/-- Full actual result of the physically chosen skip or whole-query branch. -/
def result (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool):Stack→List Bool:=
  if bitValue p.vertex=bitValue target then Query.result (picked before p tail target) buckets target (Build.rawTag p.edge p.side) []
  else picked before p tail target
/-- Only complete actual source clocks, and only the actually chosen query branch, are counted. -/
def timeBound (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool):Nat:=
  Pick.timeBound p target+if bitValue p.vertex=bitValue target then
    Query.timeBound (picked before p tail target) buckets target (Build.rawTag p.edge p.side) [] else 0
/-- Complete actual original-port iteration with no supplied decoded tag, index, route, scope or permutation. -/
theorem source_trace (before:Stack→List Bool) (buckets:List Buckets.Bucket) (p:Parse.Point) (tail target:List Bool)
    (hi:before (aux .oldReader)=true::SemiprimeSourceHistogramKeyBits.frame (Parse.payload p) tail)
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (hs:before (aux .buckets)=Buckets.records buckets) (ho:before (aux .outerReader)=[])
    (hh:∀k∈Header.cleanRoles,before k=[]) (hch:∀k∈Child.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (htag:before (aux .tagWord)=[])
    (hp:before (aux .localPosition)=[]) (hcan:before (aux .candidateTag)=[])
    (hans:before (aux .answerPosition)=[]) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound before buckets p tail target) (.local 11 7) before (.local 11 7)
      (result before buckets p tail target):=by
  have h0:=Pick.source_trace before p tail target hi hz ht htag hc ha
  change Runs program _ _ _ _ (picked before p tail target) at h0
  by_cases hv:bitValue p.vertex=bitValue target
  · simp only [Pick.next,hv,ite_true] at h0
    have hs':picked before p tail target (aux .buckets)=Buckets.records buckets:=
      (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hs
    have ho':picked before p tail target (aux .outerReader)=[]:=
      (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans ho
    have hh':∀k∈Header.cleanRoles,picked before p tail target k=[]:=PV.result_headerClean _ _ _ _ hh
    have hch':∀k∈Child.cleanRoles,picked before p tail target k=[]:=PV.result_childClean _ _ _ _ hch
    have ht':picked before p tail target (aux .vertexKey)=target:=
      (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans ht
    have htag':picked before p tail target (aux .tagWord)=Build.rawTag p.edge p.side:=PV.result_tag _ _ _ _ hv
    have hp':picked before p tail target (aux .localPosition)=[]:=
      (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hp
    have hcan':picked before p tail target (aux .candidateTag)=[]:=
      (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hcan
    have hans':picked before p tail target (aux .answerPosition)=[]:=
      (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hans
    have hb':picked before p tail target (aux .frameBuffer)=[]:=
      (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hb
    have hc':picked before p tail target (aux .copyScratch)=[]:=
      (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans hc
    have ha':∀k,picked before p tail target (arithmetic k)=[]:=by
      intro k
      exact (PV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> simp [Cleanup.role,arithmetic,aux])
        (by simp [arithmetic,aux]) (by simp [arithmetic,aux])).trans (ha k)
    have h1:=Query.source_trace (picked before p tail target) buckets target (Build.rawTag p.edge p.side) []
      hs' ho' hh' hch' ht' htag' hp' hcan' hans' hb' hc' ha'
    have hwhole:=join h0 h1
    simpa only [timeBound,result,hv,ite_true] using hwhole
  · simpa only [timeBound,result,Pick.next,hv,ite_false,Nat.add_zero] using h0
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortOne
