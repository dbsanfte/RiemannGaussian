/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketParse
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketCompare
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketEmit
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketIncrement
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketCleanup
/-! # Complete actual endpoint visit within one whole raw-packet scan
The real parser and actual sentinel equality determine emission. A matched
endpoint gets the actual fresh binary counter, then the counter really advances.
Every parsed field is physically drained before the next visit.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketVisit
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint payload cleanRoles result timeBound source_trace)
end Parse
namespace Compare
export SemiprimeD1StackChildGroupFactoryBucketCompare (next timeBound source_trace)
end Compare
namespace Emit
export SemiprimeD1StackChildGroupFactoryBucketEmit (result timeBound source_trace)
end Emit
namespace Inc
export SemiprimeD1StackChildGroupFactoryBucketIncrement (successor timeBound source_trace)
end Inc
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryBucketCleanup (role word pc result timeBound source_trace)
end Cleanup
open SemiprimeSourceHistogramKeyBits (frame)
/-- Full actual parsed bank, with all original endpoint bytes retained literally. -/
def parsed (before:Stack→List Bool) (e:Parse.Endpoint) (tail:List Bool):Stack→List Bool:=Parse.result before e tail
/-- Actual matched branch effect, after both real loggers and the actual binary add-one. -/
def emitted (before:Stack→List Bool) (e:Parse.Endpoint) (position:List Bool):Stack→List Bool:=
  Function.update (Emit.result before e position) (aux .globalPosition) (Inc.successor position)
/-- Full physical result of the real computed branch and all five final field drains. -/
def result (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool):Stack→List Bool:=
  Cleanup.result (if e.packet=packet then emitted (parsed before e tail) e position else parsed before e tail)
/-- Same source trace sum; the predicate describes the real sentinel comparison, not an input bit. -/
def timeBound (e:Parse.Endpoint) (packet position:List Bool):Nat:=
  Parse.timeBound e+Compare.timeBound e.packet packet+
    (if e.packet=packet then Emit.timeBound e position+Inc.timeBound position else 0)+Cleanup.timeBound e
/-- Whole actual parse/compare/conditional-emit/increment/cleanup, with no supplied verdict. -/
theorem source_trace (before:Stack→List Bool) (e:Parse.Endpoint) (tail packet position:List Bool)
    (hi:before (aux .endpointReader)=true::frame (Parse.payload e) tail)
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (hp:before (aux .packetKey)=packet) (hpos:before (aux .globalPosition)=position)
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound e packet position) (.local 6 23) before (.local 6 23)
      (result before e tail packet position):=by
  have h0:=Parse.source_trace before e tail hi hz
  change Runs program _ _ _ _ (parsed before e tail) at h0
  have hp':parsed before e tail (aux .packetKey)=packet:=by simpa [parsed,Parse.result,aux] using hp
  have hpos':parsed before e tail (aux .globalPosition)=position:=by simpa [parsed,Parse.result,aux] using hpos
  have hb':parsed before e tail (aux .frameBuffer)=[]:=by simpa [parsed,Parse.result,aux] using hb
  have hc':parsed before e tail (aux .copyScratch)=[]:=by simpa [parsed,Parse.result,aux] using hc
  have ha':∀k,parsed before e tail (arithmetic k)=[]:=by
    intro k;simpa [parsed,Parse.result,aux,arithmetic] using ha k
  have hr:=hz (aux .rowBuffer) (by simp [Parse.cleanRoles])
  have hr':parsed before e tail (aux .rowBuffer)=[]:=by simpa [parsed,Parse.result,aux] using hr
  have h1:=Compare.source_trace (parsed before e tail) e.packet packet rfl hp' hc' ha'
  by_cases h:e.packet=packet
  · have h1':Runs program (Compare.timeBound e.packet packet) (.local 7 6)
        (parsed before e tail) (.local 7 12) (parsed before e tail):=by
      simpa only [Compare.next,h,ite_true] using h1
    have h2:=Emit.source_trace (parsed before e tail) e position rfl rfl rfl rfl rfl hpos' hr' hb' hc'
    have hep:Emit.result (parsed before e tail) e position (aux .globalPosition)=position:=by
      simpa [Emit.result,aux] using hpos'
    have hec:Emit.result (parsed before e tail) e position (aux .copyScratch)=[]:=by
      simpa [Emit.result,aux] using hc'
    have hea:∀k,Emit.result (parsed before e tail) e position (arithmetic k)=[]:=by
      intro k;simpa [Emit.result,aux,arithmetic] using ha' k
    have h3:=Inc.source_trace (Emit.result (parsed before e tail) e position) position hep hec hea
    change Runs program _ _ _ _ (emitted (parsed before e tail) e position) at h3
    have hfields:∀j,emitted (parsed before e tail) e position (Cleanup.role j)=Cleanup.word e j:=by
      intro j;fin_cases j <;> rfl
    have h4:=Cleanup.source_trace (emitted (parsed before e tail) e position) e hfields
    have hwhole:=join h0 (join h1' (join h2 (join h3 h4)))
    simpa only [timeBound,result,Cleanup.pc,h,ite_true,Nat.add_assoc] using hwhole
  · have h1':Runs program (Compare.timeBound e.packet packet) (.local 7 6)
        (parsed before e tail) (.local 7 31) (parsed before e tail):=by
      simpa only [Compare.next,h,ite_false] using h1
    have hfields:∀j,parsed before e tail (Cleanup.role j)=Cleanup.word e j:=by
      intro j;fin_cases j <;> rfl
    have h2:=Cleanup.source_trace (parsed before e tail) e hfields
    have hwhole:=join h0 (join h1' h2)
    simpa only [timeBound,result,Cleanup.pc,h,ite_false,Nat.add_zero,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketVisit
