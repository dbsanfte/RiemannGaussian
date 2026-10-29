/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildParse
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexCompare
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryWordLog
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildCleanup
/-! # Whole actual child-endpoint visit for one old vertex's left ports
A real six-field parse supplies the vertex/global-ID words. Real numeric vertex
equality selects whether to log that actual ID. All six fields are then erased.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortVisit
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
export SemiprimeD1StackChildGroupFactoryChildParse (pc cleanRoles result timeBound source_trace)
end Parse
namespace Compare
export SemiprimeD1StackChildGroupFactoryVertexCompare (pc next matched different timeBound source_trace)
end Compare
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (pc row timeBound source_trace)
end Log
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (pc role result timeBound source_trace)
end Cleanup
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Complete actual parsed child bank. -/
def parsed (before:Stack→List Bool) (e:Parse.Endpoint) (position tail:List Bool):Stack→List Bool:=Parse.result before e position tail
/-- Actual matched word logger effect. -/
def logged (before:Stack→List Bool) (position:List Bool):Stack→List Bool:=
  Function.update before (aux .portHistory) ((Log.row position).reverse++before (aux .portHistory))
/-- Only an actual numeric equality result changes the port history. -/
def result (before:Stack→List Bool) (e:Parse.Endpoint) (position tail target:List Bool):Stack→List Bool:=
  Cleanup.result (if bitValue e.vertex=bitValue target then logged (parsed before e position tail) position else parsed before e position tail)
/-- Actual cleanup bytes of the six physically parsed fields. -/
def cleanupTime (e:Parse.Endpoint) (position:List Bool):Nat:=
  e.vertex.length+e.packet.length+e.slot.length+e.edge.length+e.side.length+position.length+6
/-- Complete literal parse/test/conditional-log/cleanup clock. -/
def timeBound (e:Parse.Endpoint) (position target:List Bool):Nat:=
  Parse.timeBound e position+Compare.timeBound e.vertex target+
    (if bitValue e.vertex=bitValue target then Log.timeBound position else 0)+cleanupTime e position
/-- Complete actual child visit, without any supplied membership, port or order answer. -/
theorem source_trace (before:Stack→List Bool) (e:Parse.Endpoint) (position tail target:List Bool)
    (hi:before (aux .endpointReader)=true::frame (SemiprimeD1StackChildGroupFactoryBucketEmit.payload e position) tail)
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (ht:before (aux .vertexKey)=target) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound e position target) (.local 9 20) before (.local 9 20)
      (result before e position tail target):=by
  have h0:=Parse.source_trace false before e position tail hi hz
  change Runs program _ (.local 9 20) before (.local 10 5) (parsed before e position tail) at h0
  have ht':parsed before e position tail (aux .vertexKey)=target:=by simpa [parsed,Parse.result,aux] using ht
  have hb':parsed before e position tail (aux .frameBuffer)=[]:=by simpa [parsed,Parse.result,aux] using hb
  have hc':parsed before e position tail (aux .copyScratch)=[]:=by simpa [parsed,Parse.result,aux] using hc
  have ha':∀k,parsed before e position tail (arithmetic k)=[]:=by
    intro k;simpa [parsed,Parse.result,aux,arithmetic] using ha k
  have h1:=Compare.source_trace 0 (parsed before e position tail) e.vertex target rfl ht' hc' ha'
  by_cases h:bitValue e.vertex=bitValue target
  · simp only [Compare.next,h,ite_true] at h1
    change Runs program _ (.local 10 5) (parsed before e position tail) (.local 10 15) _ at h1
    have h2:=Log.source_trace 0 (parsed before e position tail) position rfl hb' hc'
    change Runs program _ (.local 10 15) _ (.local 10 9) (logged (parsed before e position tail) position) at h2
    have h3:=Cleanup.source_trace false (logged (parsed before e position tail) position)
    change Runs program (cleanupTime e position) (.local 10 9) _ (.local 9 20)
      (Cleanup.result (logged (parsed before e position tail) position)) at h3
    have hwhole:=join h0 (join h1 (join h2 h3))
    simpa only [timeBound,result,h,ite_true,Nat.add_assoc] using hwhole
  · simp only [Compare.next,h,ite_false] at h1
    change Runs program _ (.local 10 5) (parsed before e position tail) (.local 10 9) _ at h1
    have h2:=Cleanup.source_trace false (parsed before e position tail)
    change Runs program (cleanupTime e position) (.local 10 9) _ (.local 9 20)
      (Cleanup.result (parsed before e position tail)) at h2
    have hwhole:=join h0 (join h1 h2)
    simpa only [timeBound,result,h,ite_false,Nat.add_zero,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortVisit
