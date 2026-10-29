/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearAcquisition
import RiemannGaussian.SemiprimeD1StackKernelLinearNormalize
/-! # Actual complete original-input and acquired-cache kernel-factor execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearExecution
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearView
open SemiprimeD1StackKernelLinearPrimitives SemiprimeD1StackProcedureTrace
namespace Acq
export SemiprimeD1StackKernelLinearAcquisition (readyWords timeBound source_trace)
end Acq
namespace Norm
export SemiprimeD1StackKernelLinearNormalize (Clean result timeBound source_trace)
end Norm
/-- Exact complete physical stopped bank; all originals and acquired factor fields remain. -/
def result (a t x y:List Bool):Stack→List Bool:=data (Norm.result (Acq.readyWords a t x y))
/-- Full actual halt has no flags, return pc or internal return frame. -/
def done (a t x y:List Bool):C.State Stack Label:=⟨none,none,none,result a t x y,[]⟩
/-- SAME finite program continuation on its actually acquired normalization cache. -/
def ready (a t x y:List Bool):C.State Stack Label:=
  ⟨some (.local .normalize),none,none,data (Acq.readyWords a t x y),[]⟩
/-- Exact own whole clock, including every real source call and final halt. -/
def runBound (a t x y:List Bool):Nat:=Acq.timeBound a t x y+Norm.timeBound (Acq.readyWords a t x y)+1
/-- Ready clock omits the already executed acquisition prefix. -/
def readyBound (a t x y:List Bool):Nat:=Norm.timeBound (Acq.readyWords a t x y)+1
/-- Every destination required by normalization is cleared by the actual source prefix. -/
theorem ready_clean (a t x y:List Bool):Norm.Clean (Acq.readyWords a t x y):=by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
/-- SAME complete source physically acquires all factor bytes before reaching its actual halt label. -/
theorem source_trace (a t x y:List Bool) (hx:SemiprimeBitArithmetic.bitValue x<2^a.length):
    Runs program (Acq.timeBound a t x y+Norm.timeBound (Acq.readyWords a t x y)) (.local .start)
      (data (sourceWords a t x y)) (.local .done) (result a t x y):=
  join (Acq.source_trace a t x y hx) (Norm.source_trace _ (ready_clean a t x y))
/-- Entire original-only physical source reaches true halt within its own actual clock. -/
theorem source_run (a t x y:List Bool) (hx:SemiprimeBitArithmetic.bitValue x<2^a.length):
    SemiprimeD1StackCalls.run program (runBound a t x y) (initial a t x y)=some (done a t x y):=by
  obtain ⟨finish,hf,ha⟩:=source_trace a t x y hx [] (initial a t x y) ⟨rfl,initial_eq a t x y,rfl⟩
  have hh:=halt_run program (.local .done) rfl (result a t x y) [] finish ha
  rw [runBound,SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- The acquired-cache entry executes only normalization, with no source/geometry replay. -/
theorem ready_run (a t x y:List Bool):
    SemiprimeD1StackCalls.run program (readyBound a t x y) (ready a t x y)=some (done a t x y):=by
  obtain ⟨finish,hf,ha⟩:=Norm.source_trace _ (ready_clean a t x y) [] (ready a t x y) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (result a t x y) [] finish ha
  rw [readyBound,SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Genuine compiled fixed finite-machine certificate for the same four physical inputs. -/
def kernelInTime (a t x y:List Bool) (hx:SemiprimeBitArithmetic.bitValue x<2^a.length):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a t x y))
      (some (SemiprimeD1StackCalls.configuration (done a t x y))) (runBound a t x y):=
  SemiprimeD1StackCalls.evalsCorrect (aux .a) (aux .slope) (Label.local Control.start) program
    (initial a t x y) (done a t x y) (runBound a t x y)
    ⟨⟨runBound a t x y,source_run a t x y hx⟩,le_rfl⟩
end RiemannGaussian.SemiprimeD1StackKernelLinearExecution
