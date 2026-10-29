/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearStrip
import RiemannGaussian.SemiprimeD1StackKernelLinearView
import RiemannGaussian.SemiprimeD1StackKernelLinearSpec
/-! # Whole real signed-magnitude copy and exact low-bit scan -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearScan
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearView
open SemiprimeD1StackKernelLinearPrimitives SemiprimeD1StackProcedureTrace
namespace Spec
export SemiprimeD1StackKernelLinearSpec (leading odd power decompose odd_cases)
end Spec
namespace Strip
export SemiprimeD1StackKernelLinearStrip (data prefix_run one_run empty_run)
end Strip
/-- Exact interpretation of the two actual scanner-field updates in the whole29 bank. -/
theorem strip_data (w:Words) (mag scan content:List Bool):
    Strip.data (arithmeticData w [] [] mag) scan content=
      arithmeticData {w with scan:=scan,content:=content} [] [] mag:=by
  unfold Strip.data
  rw [arithmeticData_aux_update,arithmeticData_aux_update]
  rfl
/-- The next finite source label is selected by the physically encountered one or EOF. -/
def next (mag:List Bool):Control:=if Spec.odd mag=[] then .zeroContent else .constantCopy
/-- Exact copy/seed/low-bit-scan clock; no native cost report is used. -/
def timeBound (mag:List Bool):Nat:=(5*mag.length+4)+1+2*Spec.leading mag+
  if Spec.odd mag=[] then 1 else 2
/-- Exact physically constructed prefix content and retained padded suffix. -/
def result (w:Words) (mag:List Bool):Words:=
  {w with scan:=Spec.odd mag,content:=Spec.power (Spec.leading mag)}
/-- Every leading false, first one and actual EOF is executed on the copied magnitude. -/
theorem source_trace (w:Words) (mag:List Bool) (hs:w.scratch=[]) (hz:w.scan=[]) (hc:w.content=[]):
    Runs program (timeBound mag) (.local .deltaCopy) (arithmeticData w [] [] mag)
      (.local (next mag)) (arithmeticData (result w mag) [] [] mag):=by
  have h0:=copy_call .deltaScan (.local .deltaCopy) (.local .seedContent) rfl
    (arithmeticData w [] [] mag) mag [] rfl hz hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (arithmeticData w [] [] mag) (aux .scan) mag) at h0
  rw [arithmeticData_aux_update] at h0
  have h1:=push_run (.local .seedContent) (.local .strip) (aux .content) true
    (arithmeticData {w with scan:=mag} [] [] mag) rfl
  change Runs program 1 _ _ _ (Function.update (arithmeticData {w with scan:=mag} [] [] mag) (aux .content) (true::w.content)) at h1
  rw [arithmeticData_aux_update] at h1
  have h2:=Strip.prefix_run (Spec.leading mag) (arithmeticData w [] [] mag) (Spec.odd mag) (true::w.content)
  rw [←Spec.decompose] at h2
  rcases Spec.odd_cases mag with ho|⟨tail,ho⟩
  · have h3:=Strip.empty_run (arithmeticData w [] [] mag)
      (List.replicate (Spec.leading mag) false++true::w.content)
    rw [ho] at h2
    simp only [strip_data] at h2 h3
    have hh:=join h0 (join h1 (join h2 h3))
    simpa only [timeBound,next,result,Spec.power,ho,hc,ite_true,SemiprimeD1StackKernelLinearView.set,Nat.add_assoc] using hh
  · have h3:=Strip.one_run (arithmeticData w [] [] mag) tail
      (List.replicate (Spec.leading mag) false++true::w.content)
    rw [ho] at h2
    simp only [strip_data] at h2 h3
    have hh:=join h0 (join h1 (join h2 h3))
    simpa only [timeBound,next,result,Spec.power,ho,hc,List.cons_ne_self,List.cons_ne_nil,ite_false,
      SemiprimeD1StackKernelLinearView.set,Nat.add_assoc] using hh
/-- The real low-zero scan visits no more bits than the actual copied word. -/
theorem leading_le (mag:List Bool):Spec.leading mag ≤ mag.length:=by
  induction mag with
  | nil=>rfl
  | cons b mag ih=>cases b <;> simp only [Spec.leading,List.length_cons] <;> omega
/-- Complete actual scan has a linear physical-byte budget. -/
theorem timeBound_le (mag:List Bool):timeBound mag≤10*(mag.length+1):=by
  have h:=leading_le mag
  unfold timeBound
  split <;> omega
end RiemannGaussian.SemiprimeD1StackKernelLinearScan
