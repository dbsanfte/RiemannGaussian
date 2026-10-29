/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearAcquisitionBounds
import RiemannGaussian.SemiprimeD1StackKernelLinearNormalizeBounds
/-! # Whole same-program factor source with one fixed physical-bit polynomial -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearBounds
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearExecution
open SemiprimeD1StackKernelLinearAcquisitionBounds
/-- Fixed coefficient and degree precede every original exponent and binary grid word. -/
def polynomial (a t x y:List Bool):Nat:=100000000*(inputSize a t x y)^3
/-- Every executed acquisition/normalization/copy/drain/return/halt is paid by physical input size. -/
theorem runBound_le (a t x y:List Bool):runBound a t x y ≤ polynomial a t x y:=by
  let s:=inputSize a t x y
  have hp:1 ≤ s:=input_pos a t x y
  have ha:=SemiprimeD1StackKernelLinearAcquisitionBounds.timeBound_le a t x y
  have hc:=ready_caps a t x y
  have hn:=SemiprimeD1StackKernelLinearNormalizeBounds.timeBound_le
    (SemiprimeD1StackKernelLinearAcquisition.readyWords a t x y) (2*s) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hq:(2*s+2)^2 ≤ 16*s^2:=by nlinarith
  have h13:s ≤ s^3:=Nat.le_pow (by decide:0<3)
  have h23:s^2 ≤ s^3:=Nat.pow_le_pow_right hp (by decide:2≤3)
  have h03:1 ≤ s^3:=Nat.one_le_pow _ _ hp
  change SemiprimeD1StackKernelLinearAcquisition.timeBound a t x y+
    SemiprimeD1StackKernelLinearNormalize.timeBound (SemiprimeD1StackKernelLinearAcquisition.readyWords a t x y)+1 ≤ 100000000*s^3
  nlinarith only [ha,hn,hq,h13,h23,h03]
/-- Actual acquired-cache entry omits all already paid original-input acquisition. -/
theorem readyBound_le (a t x y:List Bool):readyBound a t x y ≤ polynomial a t x y:=by
  have h:readyBound a t x y ≤ runBound a t x y:=by unfold readyBound runBound;omega
  exact h.trans (runBound_le a t x y)
/-- Complete same-source physical run and its fixed polynomial hold together. -/
theorem source_run_bounded (a t x y:List Bool) (hx:SemiprimeBitArithmetic.bitValue x<2^a.length):
    ∃q ≤ polynomial a t x y,SemiprimeD1StackCalls.run program q (initial a t x y)=some (done a t x y):=
  ⟨runBound a t x y,runBound_le a t x y,source_run a t x y hx⟩
/-- Ready same-source physical continuation never replays source inputs. -/
theorem ready_run_bounded (a t x y:List Bool):
    ∃q ≤ polynomial a t x y,SemiprimeD1StackCalls.run program q (ready a t x y)=some (done a t x y):=
  ⟨readyBound a t x y,readyBound_le a t x y,ready_run a t x y⟩
/-- Actual compiled-machine time certificate, not a native arithmetic clock transport. -/
def machineSource (a t x y:List Bool) (hx:SemiprimeBitArithmetic.bitValue x<2^a.length):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a t x y))
      (some (SemiprimeD1StackCalls.configuration (done a t x y))) (polynomial a t x y):=
  SemiprimeD1StackCalls.evalsCorrect (aux .a) (aux .slope) (Label.local Control.start) program
    (initial a t x y) (done a t x y) (polynomial a t x y)
    ⟨⟨runBound a t x y,source_run a t x y hx⟩,runBound_le a t x y⟩
end RiemannGaussian.SemiprimeD1StackKernelLinearBounds
