/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridLoop
import RiemannGaussian.SemiprimeD1StackRecoveryGridFinal
/-! # Whole actual original-grid source from five physical input words
The SAME fixed program acquires all geometry/height/index data, executes every
original row and rational operation, frames every repeated slope, drains all
private work and truly halts. No coefficient or operation-stream answer is
supplied. All dimensions in the theorem are interpretations of original words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridExecution
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackProcedureTrace
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload view one)
end Model
namespace Front
export SemiprimeD1StackRecoveryGridFront (sizeWord front_run runBound q_width q_value)
export SemiprimeD1StackRecoveryGridModel (front_eq)
end Front
namespace Loop
export SemiprimeD1StackRecoveryGridLoop (iterate rows_run timeBound)
export SemiprimeD1StackRecoveryGridLoopPrimitives (zeroWord)
end Loop
namespace Finish
export SemiprimeD1StackRecoveryGridFinal (result final_run runBound)
end Finish
/-- Initial true binary N−1 is physically acquired from actual true geometry. -/
def firstWord (a:Nat) :List Bool:=SemiprimeD1StackRecoveryGridDecrement.difference (Front.sizeWord a)
/-- Exact chronological acquired grid payload, determined by the same actual whole loop. -/
def payload (a M u:Nat) (t width:List Bool) :Model.Payload:=
  Loop.iterate a M u t width (2^(a+1)) (firstWord a) Model.one
/-- Complete actual boundary before the six final scalar/argument operations. -/
def beforeFinish (a M u:Nat) (t width:List Bool) :Words:=
  Model.view a M u 0 t (Loop.zeroWord a) width (payload a M u t width)
/-- Exact actual104-word stopped bank; all foreign source words are retained and all private work is physically clear. -/
def result (a M u:Nat) (t width:List Bool) :Stack→List Bool:=bank (Finish.result (beforeFinish a M u t width) width)
/-- True halted state with both finite flags and every actual internal return cell empty. -/
def done (a M u:Nat) (t width:List Bool) :C.State Stack Label:=⟨none,none,none,result a M u t width,[]⟩
/-- Own whole clock includes the same acquisition/loop/finish traces and the true halt instruction. -/
def runBound (a M u:Nat) (t width:List Bool) :Nat:=Front.runBound a M u t width+
  Loop.timeBound a M u t width (2^(a+1)) (firstWord a) Model.one+
  Finish.runBound (beforeFinish a M u t width) width+1
attribute [local irreducible] result runBound Front.runBound Loop.timeBound Finish.runBound
/-- The entire five-input source executes its own physically acquired grid and complete rational fold; no native report clock is used. -/
theorem source_trace (a M u:Nat) (t width:List Bool) :
    ∃q≤ runBound a M u t width-1,Runs program q (.local .start)
      (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
      (.local .done) (result a M u t width):=by
  obtain ⟨p,hp,h0⟩:=Front.front_run a M u t width
  rw [Front.front_eq] at h0
  have hl:(firstWord a).length=a+2:=Front.q_width a M u t width
  have hv:SemiprimeBitArithmetic.bitValue (firstWord a)=2^(a+1)-1:=Front.q_value a M u t width
  obtain ⟨q,hq,h1⟩:=Loop.rows_run a M u (2^(a+1)) t (firstWord a) width Model.one hl hv
  change Runs program q _ _ _ (bank (beforeFinish a M u t width)) at h1
  have hgn:(beforeFinish a M u t width).registers (.gridNum,false)≠[]:=List.cons_ne_nil _ _
  have hgd:(beforeFinish a M u t width).registers (.gridDen,false)≠[]:=List.cons_ne_nil _ _
  have hn:(beforeFinish a M u t width).registers (.node,false)≠[]:=List.cons_ne_nil _ _
  have hc:(beforeFinish a M u t width).registers (.center,false)≠[]:=List.cons_ne_nil _ _
  have ha:(beforeFinish a M u t width).registers (.alpha,false)≠[]:=List.cons_ne_nil _ _
  obtain ⟨r,hr,h2⟩:=Finish.final_run (beforeFinish a M u t width) width rfl rfl hgn hgd hn hc ha
  have he:bank (Finish.result (beforeFinish a M u t width) width)=result a M u t width:=by unfold result;rfl
  rw [he] at h2
  refine ⟨p+q+r,?_,SemiprimeD1StackRecoveryGridPrimitives.join (SemiprimeD1StackRecoveryGridPrimitives.join h0 h1) h2⟩
  unfold runBound
  omega
/-- Actual whole halt, with SAME whole source and exact input/output/work/return cells. -/
theorem source_run (a M u:Nat) (t width:List Bool) :
    ∃q≤ runBound a M u t width,SemiprimeD1StackCalls.run program q
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (done a M u t width):=by
  obtain ⟨q,hq,h⟩:=source_trace a M u t width
  obtain ⟨finish,hfinish,hAt⟩:=h [] (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) ⟨rfl,rfl,rfl⟩
  have hp:0<runBound a M u t width:=by unfold runBound;omega
  refine ⟨q+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  exact halt_run program (.local .done) rfl (result a M u t width) [] finish hAt
/-- Genuine fixed finite104-role machine follows the same own-clock whole source from the honest acquired five-tape bank. -/
noncomputable def gridInTime (a M u:Nat) (t width:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width))
      (some (SemiprimeD1StackCalls.configuration (done a M u t width))) (runBound a M u t width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .originalA) (aux .slopes) (.local .start) program
  let h:=source_run a M u t width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryGridExecution
