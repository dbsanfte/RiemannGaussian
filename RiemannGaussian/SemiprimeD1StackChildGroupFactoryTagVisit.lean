/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildParse
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexCompare
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagBuild
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagCompare
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagIncrement
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildCleanup
/-! # Actual first-index search visit: parse, numeric vertex, whole raw tag
The real local binary counter advances only for a same-vertex different-tag
child. The first literal tag match branches to the actual found-answer copy;
there is no supplied position, match flag, decoded tag or permutation input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagVisit
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
export SemiprimeD1StackChildGroupFactoryChildParse (result cleanRoles timeBound source_trace)
end Parse
namespace Vertex
export SemiprimeD1StackChildGroupFactoryVertexCompare (next matched different timeBound source_trace)
end Vertex
namespace Build
export SemiprimeD1StackChildGroupFactoryTagBuild (rawTag timeBound source_trace)
end Build
namespace Compare
export SemiprimeD1StackChildGroupFactoryTagCompare (next timeBound source_trace)
end Compare
namespace Inc
export SemiprimeD1StackChildGroupFactoryTagIncrement (successor timeBound source_trace)
end Inc
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (result timeBound source_trace)
end Cleanup
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact candidate raw tag, built from actual edge and side fields. -/
def candidate (e:Parse.Endpoint):List Bool:=Build.rawTag e.edge e.side
/-- Exact complete physical parse boundary. -/
def parsed (before:Stack→List Bool) (e:Parse.Endpoint) (global tail:List Bool):Stack→List Bool:=Parse.result before e global tail
/-- Exact complete physical candidate-build boundary. -/
def built (before:Stack→List Bool) (e:Parse.Endpoint) (global tail:List Bool):Stack→List Bool:=
  Function.update (parsed before e global tail) (aux .candidateTag) (candidate e)
/-- Only the actual first matching numeric vertex and literal raw tag reaches the real found site. -/
def next (e:Parse.Endpoint) (target tag:List Bool):Label:=
  if bitValue e.vertex=bitValue target ∧ tag=candidate e then .local 13 19 else .local 12 9
/-- Actual whole-bank result of the three physically computed branch outcomes. -/
def result (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool):Stack→List Bool:=
  if bitValue e.vertex=bitValue target then
    if tag=candidate e then built before e global tail
    else Cleanup.result (Function.update (parsed before e global tail) (aux .localPosition) (Inc.successor position))
  else Cleanup.result (parsed before e global tail)
/-- All six actual child fields and every one of their final EOF pops. -/
def cleanupTime (e:Parse.Endpoint) (global:List Bool):Nat:=
  e.vertex.length+e.packet.length+e.slot.length+e.edge.length+e.side.length+global.length+6
/-- Only actual source trace clocks are summed; branch predicates here interpret computed results. -/
def timeBound (e:Parse.Endpoint) (global target tag position:List Bool):Nat:=
  Parse.timeBound e global+Vertex.timeBound e.vertex target+
    (if bitValue e.vertex=bitValue target then Build.timeBound e.edge e.side+Compare.timeBound tag (candidate e)+
      (if tag=candidate e then 0 else (candidate e).length+1+Inc.timeBound position+cleanupTime e global)
    else cleanupTime e global)
/-- Complete real first-index child visit, including physical field erasure and actual counter increments. -/
theorem source_trace (before:Stack→List Bool) (e:Parse.Endpoint) (global tail target tag position:List Bool)
    (hi:before (aux .endpointReader)=true::frame (SemiprimeD1StackChildGroupFactoryBucketEmit.payload e global) tail)
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (htag:before (aux .tagWord)=tag)
    (hp:before (aux .localPosition)=position) (hcan:before (aux .candidateTag)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound e global target tag position) (.local 12 9) before (next e target tag)
      (result before e global tail target tag position):=by
  have h0:=Parse.source_trace true before e global tail hi hz
  change Runs program _ (.local 12 9) before (.local 12 26) (parsed before e global tail) at h0
  have ht':parsed before e global tail (aux .vertexKey)=target:=by simpa [parsed,Parse.result,aux] using ht
  have htag':parsed before e global tail (aux .tagWord)=tag:=by simpa [parsed,Parse.result,aux] using htag
  have hp':parsed before e global tail (aux .localPosition)=position:=by simpa [parsed,Parse.result,aux] using hp
  have hcan':parsed before e global tail (aux .candidateTag)=[]:=by simpa [parsed,Parse.result,aux] using hcan
  have hc':parsed before e global tail (aux .copyScratch)=[]:=by simpa [parsed,Parse.result,aux] using hc
  have ha':∀k,parsed before e global tail (arithmetic k)=[]:=by
    intro k;simpa [parsed,Parse.result,aux,arithmetic] using ha k
  have h1:=Vertex.source_trace 2 (parsed before e global tail) e.vertex target rfl ht' hc' ha'
  by_cases hv:bitValue e.vertex=bitValue target
  · simp only [Vertex.next,hv,ite_true] at h1
    change Runs program _ (.local 12 26) (parsed before e global tail) (.local 13 4) _ at h1
    have h2:=Build.source_trace true (parsed before e global tail) e.edge e.side rfl rfl hcan' hc'
    change Runs program _ (.local 13 4) _ (.local 13 6) (built before e global tail) at h2
    have ht2:built before e global tail (aux .tagWord)=tag:=by simpa [built,aux] using htag'
    have hc2:built before e global tail (aux .copyScratch)=[]:=by simpa [built,aux] using hc'
    have ha2:∀k,built before e global tail (arithmetic k)=[]:=by intro k;simpa [built,aux,arithmetic] using ha' k
    have h3:=Compare.source_trace (built before e global tail) tag (candidate e) ht2 rfl hc2 ha2
    by_cases he:tag=candidate e
    · simp only [Compare.next,he,ite_true] at h3
      have hwhole:=join h0 (join h1 (join h2 h3))
      simpa only [timeBound,result,next,hv,he,true_and,ite_true,Nat.add_zero,Nat.add_assoc] using hwhole
    · simp only [Compare.next,he,ite_false] at h3
      have h4:=drain_loop (.local 13 12) (.local 13 13) (aux .candidateTag) rfl (built before e global tail) (candidate e) rfl
      have hclear:Function.update (built before e global tail) (aux .candidateTag) []=parsed before e global tail:=by
        dsimp only [built]
        rw [Function.update_idem,←hcan']
        exact Function.update_eq_self _ _
      rw [hclear] at h4
      have h5:=Inc.source_trace (parsed before e global tail) position hp' hc' ha'
      have h6:=Cleanup.source_trace true (Function.update (parsed before e global tail) (aux .localPosition) (Inc.successor position))
      change Runs program (cleanupTime e global) (.local 12 30) _ (.local 12 9)
        (Cleanup.result (Function.update (parsed before e global tail) (aux .localPosition) (Inc.successor position))) at h6
      have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 h6)))))
      simpa only [timeBound,result,next,hv,he,true_and,ite_true,ite_false,Nat.add_assoc] using hwhole
  · simp only [Vertex.next,hv,ite_false] at h1
    change Runs program _ (.local 12 26) (parsed before e global tail) (.local 12 30) _ at h1
    have h2:=Cleanup.source_trace true (parsed before e global tail)
    change Runs program (cleanupTime e global) (.local 12 30) _ (.local 12 9) (Cleanup.result (parsed before e global tail)) at h2
    have hwhole:=join h0 (join h1 h2)
    simpa only [timeBound,result,next,hv,false_and,ite_false,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagVisit
