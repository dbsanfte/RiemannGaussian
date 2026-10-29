/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagLoopView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagComplete
/-! # Whole actual first-index query from retained bucket bytes and actual raw tag
One paid bucket copy drives the real nested first-hit search. Its actual
computed local counter is copied, unread bytes are really drained on a hit,
and the real answer is logged before all local search operands are erased.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Loop
export SemiprimeD1StackChildGroupFactoryTagLoop (found next result timeBound source_trace)
end Loop
namespace View
export SemiprimeD1StackChildGroupFactoryTagLoopView (finalPosition result_other result_position)
end View
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end Buckets
namespace Parse
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Parse
namespace Header
export SemiprimeD1StackChildGroupFactoryBucketHeader (cleanRoles)
end Header
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (role)
end Cleanup
namespace Complete
export SemiprimeD1StackChildGroupFactoryTagComplete (start result timeBound source_trace)
end Complete
/-- Actual preserving copy of the physically acquired whole bucket vector. -/
def copied (before:Stack→List Bool) (buckets:List Buckets.Bucket):Stack→List Bool:=
  Function.update before (aux .outerReader) (Buckets.records buckets)
/-- Actual first-hit/physical-EOF bank of the real nested search. -/
def searched (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool):Stack→List Bool:=
  Loop.result buckets (copied before buckets) target tag position
/-- Complete actual query result, including real counter-copy, early unread-byte drains, log and erases. -/
def result (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool):Stack→List Bool:=
  Complete.result (Loop.found buckets target tag) (searched before buckets target tag position)
    (View.finalPosition buckets target tag position)
/-- All SAME actual source components, including the actual unread bytes left by the real short circuit. -/
def timeBound (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool):Nat:=
  (5*(Buckets.records buckets).length+4)+Loop.timeBound buckets target tag position+
    Complete.timeBound (Loop.found buckets target tag) (searched before buckets target tag position)
      (View.finalPosition buckets target tag position) tag
/-- Whole actual first-index query, without a supplied index/tag getter/permutation or found bit. -/
theorem source_trace (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target tag position:List Bool)
    (hs:before (aux .buckets)=Buckets.records buckets) (ho:before (aux .outerReader)=[])
    (hh:∀k∈Header.cleanRoles,before k=[]) (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (htag:before (aux .tagWord)=tag)
    (hp:before (aux .localPosition)=position) (hcan:before (aux .candidateTag)=[])
    (hans:before (aux .answerPosition)=[]) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound before buckets target tag position) (.local 11 27) before (.local 11 7)
      (result before buckets target tag position):=by
  have h0:=copy_call 26 (.local 11 27) (.local 11 28) rfl before (Buckets.records buckets) [] hs ho hc
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ (copied before buckets) at h0
  have h1:=Loop.source_trace buckets (copied before buckets) target tag position rfl
    (by simpa [copied,Header.cleanRoles,aux,field] using hh)
    (by simpa [copied,Parse.cleanRoles,aux,field] using hz)
    (by simpa [copied,aux] using ht) (by simpa [copied,aux] using htag)
    (by simpa [copied,aux] using hp) (by simpa [copied,aux] using hcan)
    (by simpa [copied,aux] using hc) (by intro k;simpa [copied,aux,arithmetic] using ha k)
  change Runs program _ _ _ _ (searched before buckets target tag position) at h1
  have hp':searched before buckets target tag position (aux .localPosition)=View.finalPosition buckets target tag position:=
    View.result_position _ _ _ _ _ (by simpa [copied,aux] using hp)
  have ha':searched before buckets target tag position (aux .answerPosition)=[]:=by
    rw [searched,View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using hans
  have ht':searched before buckets target tag position (aux .tagWord)=tag:=by
    rw [searched,View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using htag
  have hb':searched before buckets target tag position (aux .frameBuffer)=[]:=by
    rw [searched,View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using hb
  have hc':searched before buckets target tag position (aux .copyScratch)=[]:=by
    rw [searched,View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using hc
  have h2:=Complete.source_trace (Loop.found buckets target tag) (searched before buckets target tag position)
    (View.finalPosition buckets target tag position) tag hp' ha' ht' hb' hc'
  change Runs program _ (Loop.next buckets target tag) _ _ _ at h2
  have hwhole:=join h0 (join h1 h2)
  simpa only [timeBound,result,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagSource
