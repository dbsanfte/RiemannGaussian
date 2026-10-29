/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearExecution
import RiemannGaussian.SemiprimeD1StackKernelLinearArithmeticBounds
/-! # All acquired operand widths and the paid original-input prefix clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearAcquisitionBounds
open SemiprimeD1StackKernelLinearView SemiprimeD1StackKernelLinearArithmeticBounds
open SemiprimeD1StackKernelLinearPrimitives SemiprimeBitArithmetic SemiprimeBitDivision
namespace Acq
export SemiprimeD1StackKernelLinearAcquisition (readyWords timeBound sumWords displacementWords gridWords)
end Acq
namespace P
export SemiprimeD1StackKernelLinearPower (result)
end P
namespace Sum
export SemiprimeD1StackKernelLinearSum (value timeBound)
end Sum
namespace Fit
export SemiprimeD1StackKernelLinearFit (displacementTime)
end Fit
/-- All original padding and unary a markers are physically paid. -/
def inputSize (a t x y:List Bool):Nat:=a.length+t.length+x.length+y.length+1
/-- Positive common physical source scale. -/
theorem input_pos (a t x y:List Bool):1 ≤ inputSize a t x y:=by unfold inputSize;omega
/-- Actual fixed-width destination words both have exactly a+1 cells. -/
theorem ready_widths (a t x y:List Bool):
    (Acq.readyWords a t x y).j.length=a.length+1 ∧
    (Acq.readyWords a t x y).displacement.length=a.length+1 ∧
    (Acq.readyWords a t x y).alpha.length=a.length+2:=by
  constructor
  · exact SemiprimeD1StackWordFitExecution.result_length t (true::a)
  · constructor
    · exact SemiprimeD1StackWordFitExecution.result_length
        (subBits (Acq.sumWords a t x y).buffer x false).result.bits (true::a)
    · change (false::SemiprimeD1StackKernelLinearSpec.power a.length).length=a.length+2
      rw [List.length_cons,SemiprimeD1StackKernelLinearSpec.power_length]
/-- The retained intermediate sum has source-byte width, not magnitude-sized unary storage. -/
theorem buffer_length (a t x y:List Bool):
    (Acq.readyWords a t x y).buffer.length ≤ inputSize a t x y+1:=by
  have h:=add_length (SemiprimeD1StackKernelLinearSpec.power a.length) y
  rw [SemiprimeD1StackKernelLinearSpec.power_length] at h
  change (addBits (SemiprimeD1StackKernelLinearSpec.power a.length) y false).bits.length ≤ _
  unfold inputSize
  have hm:max (a.length+1) y.length ≤ a.length+t.length+x.length+y.length+1:=max_le (by omega) (by omega)
  omega
/-- A uniform physical radius bounds every operand entering the real normalization continuation. -/
theorem ready_caps (a t x y:List Bool):
    (Acq.readyWords a t x y).j.length ≤ 2*inputSize a t x y ∧
    (Acq.readyWords a t x y).displacement.length ≤ 2*inputSize a t x y ∧
    (Acq.readyWords a t x y).alpha.length ≤ 2*inputSize a t x y ∧
    (Acq.readyWords a t x y).buffer.length ≤ 2*inputSize a t x y:=by
  have h:=ready_widths a t x y
  have hb:=buffer_length a t x y
  have hp:=input_pos a t x y
  unfold inputSize at *
  omega
/-- Generic actual center-plus-y source bound from the two physical operand widths. -/
theorem sumTime_le (w:Words) (r:Nat) (hc:w.center.length ≤ r) (hy:w.y.length ≤ r):
    Sum.timeBound w ≤ 100*(r+1):=by
  have ha:=addTime_le w.center w.y
  have hw:=add_length w.center w.y
  have hm:max w.center.length w.y.length ≤ r:=max_le hc hy
  unfold Sum.timeBound Sum.value
  omega
/-- Generic actual displacement copy/subtract/borrow/fit bound. -/
theorem displacementTime_le (w:Words) (r:Nat) (hb:w.buffer.length ≤ r) (hx:w.x.length ≤ r) (hk:w.k.length ≤ r):
    Fit.displacementTime w ≤ 100*(r+1):=by
  have hs:=subTime_le w.buffer w.x
  have hw:=sub_length w.buffer w.x
  have hm:max w.buffer.length w.x.length ≤ r:=max_le hb hx
  have hf:=fitTime_le (subBits w.buffer w.x false).result.bits w.k
  unfold Fit.displacementTime
  omega
/-- Actual full four-original-word acquisition prefix has a linear physical-byte bound. -/
theorem timeBound_le (a t x y:List Bool):Acq.timeBound a t x y ≤ 1000*inputSize a t x y:=by
  let s:=inputSize a t x y
  have hp:1 ≤ s:=input_pos a t x y
  have ha:a.length ≤ s:=by unfold s inputSize;omega
  have ht:t.length ≤ s:=by unfold s inputSize;omega
  have hx:x.length ≤ s:=by unfold s inputSize;omega
  have hy:y.length ≤ s:=by unfold s inputSize;omega
  have hcenter:(P.result a t x y).center.length=a.length+1:=SemiprimeD1StackKernelLinearSpec.power_length a.length
  have hk:(Acq.sumWords a t x y).k.length=a.length+1:=rfl
  have hb:(Acq.sumWords a t x y).buffer.length ≤ s+1:=buffer_length a t x y
  have h0:=sumTime_le (P.result a t x y) (2*s) (by omega) (by exact hy.trans (by omega))
  have h1:=displacementTime_le (Acq.sumWords a t x y) (2*s) (by omega) (by exact hx.trans (by omega)) (by omega)
  have hf:=fitTime_le t (true::a)
  simp only [List.length_cons] at hf
  change Acq.timeBound a t x y ≤ 1000*s
  unfold Acq.timeBound
  omega
end RiemannGaussian.SemiprimeD1StackKernelLinearAcquisitionBounds
