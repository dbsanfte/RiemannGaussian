/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortParse
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexCompare
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagBuild
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortCleanup
/-! # Whole actual old-port parse/filter/raw-target-tag acquisition
Every actual old record is parsed and numerically compared with the actual old
vertex counter. A matching record builds its actual edge/side tag before all
three raw fields are physically erased; other records are really skipped.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortPick
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Parse
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point payload cleanRoles result timeBound source_trace)
end Parse
namespace Vertex
export SemiprimeD1StackChildGroupFactoryVertexCompare (next matched different timeBound source_trace)
end Vertex
namespace Build
export SemiprimeD1StackChildGroupFactoryTagBuild (rawTag timeBound source_trace)
end Build
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryOldPortCleanup (result timeBound source_trace)
end Cleanup
open SemiprimeBitArithmetic (bitValue)
/-- Complete actual parsed original-port bank. -/
def parsed (before:Stack→List Bool) (p:Parse.Point) (tail:List Bool):Stack→List Bool:=Parse.result before p tail
/-- Actual raw target tag acquired by a real preserving copy and Frame. -/
def built (before:Stack→List Bool) (p:Parse.Point) (tail:List Bool):Stack→List Bool:=
  Function.update (parsed before p tail) (aux .tagWord) (Build.rawTag p.edge p.side)
/-- Actual numeric comparison, never an input classification, decides whether to search. -/
def next (p:Parse.Point) (target:List Bool):Label:=
  if bitValue p.vertex=bitValue target then .local 11 27 else .local 11 7
/-- Complete physical field cleanup before the actual chosen continuation. -/
def result (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool):Stack→List Bool:=
  Cleanup.result (if bitValue p.vertex=bitValue target then built before p tail else parsed before p tail)
/-- Every actual original-port field byte and three real EOF pops. -/
def cleanupTime (p:Parse.Point):Nat:=p.vertex.length+p.edge.length+p.side.length+3
/-- Same literal parse/numeric-test/conditional-tag-build/all-raw-field-erase clock. -/
def timeBound (p:Parse.Point) (target:List Bool):Nat:=
  Parse.timeBound p+Vertex.timeBound p.vertex target+
    (if bitValue p.vertex=bitValue target then Build.timeBound p.edge p.side else 0)+cleanupTime p
/-- Whole actual old-port visit before starting its real first-index query or reading the next old record. -/
theorem source_trace (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool)
    (hi:before (aux .oldReader)=true::SemiprimeSourceHistogramKeyBits.frame (Parse.payload p) tail)
    (hz:∀k∈Parse.cleanRoles,before k=[]) (ht:before (aux .vertexKey)=target)
    (htag:before (aux .tagWord)=[]) (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound p target) (.local 11 7) before (next p target) (result before p tail target):=by
  have h0:=Parse.source_trace before p tail hi hz
  change Runs program _ _ _ _ (parsed before p tail) at h0
  have ht':parsed before p tail (aux .vertexKey)=target:=by simpa [parsed,Parse.result,aux] using ht
  have htag':parsed before p tail (aux .tagWord)=[]:=by simpa [parsed,Parse.result,aux] using htag
  have hc':parsed before p tail (aux .copyScratch)=[]:=by simpa [parsed,Parse.result,aux] using hc
  have ha':∀k,parsed before p tail (arithmetic k)=[]:=by intro k;simpa [parsed,Parse.result,aux,arithmetic] using ha k
  have h1:=Vertex.source_trace 1 (parsed before p tail) p.vertex target rfl ht' hc' ha'
  by_cases h:bitValue p.vertex=bitValue target
  · simp only [Vertex.next,h,ite_true] at h1
    change Runs program _ (.local 11 18) _ (.local 11 22) _ at h1
    have h2:=Build.source_trace false (parsed before p tail) p.edge p.side rfl rfl htag' hc'
    change Runs program _ (.local 11 22) _ (.local 11 24) (built before p tail) at h2
    have h3:=Cleanup.source_trace true (built before p tail)
    change Runs program (cleanupTime p) (.local 11 24) _ (.local 11 27) (Cleanup.result (built before p tail)) at h3
    have hwhole:=join h0 (join h1 (join h2 h3))
    simpa only [timeBound,result,next,h,ite_true,Nat.add_assoc] using hwhole
  · simp only [Vertex.next,h,ite_false] at h1
    change Runs program _ (.local 11 18) _ (.local 14 6) _ at h1
    have h2:=Cleanup.source_trace false (parsed before p tail)
    change Runs program (cleanupTime p) (.local 14 6) _ (.local 11 7) (Cleanup.result (parsed before p tail)) at h2
    have hwhole:=join h0 (join h1 h2)
    simpa only [timeBound,result,next,h,ite_false,Nat.add_zero,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortPick
