/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearDivisionView
/-! # Actual final divider/cache cleanup and literal accepted halt boundary -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearFinish
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearView
open SemiprimeD1StackKernelLinearPrimitives SemiprimeD1StackKernelLinearDivisionView
open SemiprimeD1StackProcedureTrace
/-- Actual final bank may still contain the zero branch's padded magnitude. -/
def input (w:Words) (mag remainder quotient:List Bool):Stack→List Bool:=
  bank (SemiprimeD1StackDivider.payload [] [] [] [] [] [] mag remainder quotient [] []) w
/-- The real magnitude cleanup produces the identical clean divider boundary. -/
theorem input_output_update (w:Words) (mag remainder quotient:List Bool):
    Function.update (input w mag remainder quotient) (arithmetic .output) []=
      divisionData w [] [] remainder quotient:=by
  funext r;rcases r with r|r
  · rcases r with r|r <;> cases r <;> rfl
  · rfl
/-- Every retained binary result and source word survives actual private cleanup. -/
def result (w:Words):Words:={w with buffer:=[],valid:=[true]}
/-- Own actual cleanup clock includes four EOF pops, real returns and accepted bit push. -/
def timeBound (w:Words) (mag remainder quotient:List Bool):Nat:=mag.length+w.buffer.length+quotient.length+remainder.length+13
/-- Both branch paths execute the same actual final cleanup and accepted push. -/
theorem source_trace (w:Words) (mag remainder quotient:List Bool) (hv:w.valid=[]):
    Runs program (timeBound w mag remainder quotient) (.local .clearDelta) (input w mag remainder quotient)
      (.local .done) (data (result w)):=by
  have h0:=drain_call (.local .clearDelta) (.local .clearBuffer) (arithmetic .output)
    (input w mag remainder quotient) mag rfl rfl
  rw [input_output_update] at h0
  have h1:=drain_call (.local .clearBuffer) (.local .clearQuotient) (aux .buffer)
    (divisionData w [] [] remainder quotient) w.buffer rfl rfl
  rw [divisionData_aux_update] at h1
  have h2:=drain_call (.local .clearQuotient) (.local .clearRemainder) (divider (.inr .quotient))
    (divisionData {w with buffer:=[]} [] [] remainder quotient) quotient rfl rfl
  rw [divisionData_quotient_update] at h2
  have h3:=drain_call (.local .clearRemainder) (.local .accept) (divider (.inr .remainder))
    (divisionData {w with buffer:=[]} [] [] remainder []) remainder rfl rfl
  rw [divisionData_remainder_update,divisionData_empty] at h3
  have h4:=push_run (.local .accept) (.local .done) (aux .valid) true (data {w with buffer:=[]}) rfl
  change Runs program 1 _ _ _ (Function.update (data {w with buffer:=[]}) (aux .valid) (true::w.valid)) at h4
  simp only [data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h4
  have hh:=join h0 (join h1 (join h2 (join h3 h4)))
  simpa only [timeBound,result,data,hv,SemiprimeD1StackKernelLinearView.set,List.length_nil,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
end RiemannGaussian.SemiprimeD1StackKernelLinearFinish
