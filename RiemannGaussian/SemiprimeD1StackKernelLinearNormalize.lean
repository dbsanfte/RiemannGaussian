/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearSigned
import RiemannGaussian.SemiprimeD1StackKernelLinearScan
import RiemannGaussian.SemiprimeD1StackKernelLinearTail
import RiemannGaussian.SemiprimeD1StackKernelLinearFinish
/-! # Entire actual normalization continuation on the acquired original cache -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearNormalize
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearView
open SemiprimeD1StackKernelLinearPrimitives SemiprimeD1StackKernelLinearDivisionView
open SemiprimeD1StackProcedureTrace
namespace Spec
export SemiprimeD1StackKernelLinearSpec (magnitude negative odd)
end Spec
namespace Signed
export SemiprimeD1StackKernelLinearSigned (source_trace timeBound)
end Signed
namespace Scan
export SemiprimeD1StackKernelLinearScan (source_trace timeBound result next)
end Scan
namespace Tail
export SemiprimeD1StackKernelLinearTail (zero_trace prepareTime prepare_trace divideTime divide_trace quotient remainder)
end Tail
namespace Finish
export SemiprimeD1StackKernelLinearFinish (source_trace timeBound result input)
end Finish
/-- Exactly those private destinations required empty by actual normalization calls. -/
def Clean (w:Words):Prop:=∀r∈([.scratch,.sign,.scan,.content,.constant,.slope,.valid]:List Aux),words w r=[]
/-- The actual signed magnitude being physically scanned. -/
def mag (w:Words):List Bool:=Spec.magnitude w.j w.displacement
/-- Exact cache following actual signed subtraction. -/
def signed (w:Words):Words:={w with sign:=[Spec.negative w.j w.displacement]}
/-- Exact cache following the real copied low-bit scan. -/
def scanned (w:Words):Words:=Scan.result (signed w) (mag w)
/-- Actual all-zero branch after provisional content cleanup. -/
def zeroed (w:Words):Words:={scanned w with content:=w.alpha,slope:=[true]}
/-- Actual nonzero divisor-entry cache, after physical source/scan cleanup. -/
def prepared (w:Words):Words:={scanned w with constant:=(scanned w).scan,scan:=[]}
/-- Actual nonzero branch following the real restoring division. -/
def divided (w:Words):Words:={prepared w with slope:=Tail.quotient (prepared w)}
/-- Complete stopped words, with all transient fields physically cleaned. -/
def result (w:Words):Words:=
  if Spec.odd (mag w)=[] then Finish.result (zeroed w) else Finish.result (divided w)
/-- Own exact branch time, composed only from actual included program clocks. -/
def timeBound (w:Words):Nat:=Signed.timeBound w+Scan.timeBound (mag w)+
  if Spec.odd (mag w)=[] then
    (((scanned w).content.length+3)+(5*(scanned w).alpha.length+4)+1)+
      Finish.timeBound (zeroed w) (mag w) [] []
  else Tail.prepareTime (scanned w) (mag w)+Tail.divideTime (prepared w)+
    Finish.timeBound (divided w) [] (Tail.remainder (prepared w)) (Tail.quotient (prepared w))
/-- The zero branch retains its real padded magnitude until common cleanup. -/
theorem zero_input (w:Words) (value:List Bool):
    Finish.input w value [] []=arithmeticData w [] [] value:=by
  funext r;rcases r with r|r
  · rcases r with r|r <;> cases r <;> rfl
  · rfl
/-- The nonzero branch reaches common cleanup with the actual divider outputs. -/
theorem division_input (w:Words) (remainder quotient:List Bool):
    Finish.input w [] remainder quotient=divisionData w [] [] remainder quotient:=rfl
/-- Whole actual acquired-cache continuation, preserving every foreign word and real return. -/
theorem source_trace (w:Words) (hc:Clean w):
    Runs program (timeBound w) (.local .normalize) (data w) (.local .done) (data (result w)):=by
  have hs:w.scratch=[]:=hc .scratch (by simp)
  have hsign:w.sign=[]:=hc .sign (by simp)
  have hscan:w.scan=[]:=hc .scan (by simp)
  have hcontent:w.content=[]:=hc .content (by simp)
  have hconstant:w.constant=[]:=hc .constant (by simp)
  have hslope:w.slope=[]:=hc .slope (by simp)
  have hvalid:w.valid=[]:=hc .valid (by simp)
  have h0:=Signed.source_trace w hs hsign
  have h1:=Scan.source_trace (signed w) (mag w) hs hscan hcontent
  by_cases hz:Spec.odd (mag w)=[]
  · have h2:=Tail.zero_trace (scanned w) (mag w) hs hslope
    have h3:=Finish.source_trace (zeroed w) (mag w) [] [] hvalid
    rw [zero_input] at h3
    have h1':Runs program (Scan.timeBound (mag w)) (.local .deltaCopy)
        (arithmeticData (signed w) [] [] (mag w)) (.local .zeroContent)
        (arithmeticData (scanned w) [] [] (mag w)):=by
      simpa only [scanned,Scan.next,hz,ite_true] using h1
    have hh:=join h0 (join h1' (join h2 h3))
    simpa only [timeBound,result,hz,ite_true,Nat.add_assoc] using hh
  · have h2:=Tail.prepare_trace (scanned w) (mag w) hs hconstant
    have h3:=Tail.divide_trace (prepared w) hs hslope
    have h4:=Finish.source_trace (divided w) [] (Tail.remainder (prepared w)) (Tail.quotient (prepared w)) hvalid
    rw [division_input] at h4
    have h1':Runs program (Scan.timeBound (mag w)) (.local .deltaCopy)
        (arithmeticData (signed w) [] [] (mag w)) (.local .constantCopy)
        (arithmeticData (scanned w) [] [] (mag w)):=by
      simpa only [scanned,Scan.next,hz,ite_false] using h1
    have hh:=join h0 (join h1' (join h2 (join h3 h4)))
    simpa only [timeBound,result,hz,ite_false,Nat.add_assoc] using hh
end RiemannGaussian.SemiprimeD1StackKernelLinearNormalize
