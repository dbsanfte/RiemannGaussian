/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureFragments

/-! # Actual local call/return fragment composition
This proof composes literal instructions of one fixed program. Its premises
are real traces; it introduces no runtime evaluator or cost-as-time principle.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackLocalCall
open SemiprimeD1StackProcedureFragments (At Runs)
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- A literal same-program call executes its actual proved body and real return pop. -/
theorem call_run {K L:Type} [DecidableEq K] (program:L→C.Instruction K L)
    (pc entry ret next:L) (input output:K→List Bool) (time:ℕ)
    (hcall:program pc=.call entry next) (hret:program ret=.ret)
    (hbody:Runs program time entry input ret output) :
    Runs program (time+2) pc input next output := by
  intro frames state hs
  rcases hs with ⟨hpc,hdata,hframes⟩
  let mid:=C.execute (.call entry next) state
  have hm:C.run program 1 state=some mid:=by
    change C.step program state=some mid
    simp [C.step,SemiprimeD1StackCalls.step,hpc,hcall,mid]
  have hmid:At entry input (next::frames) mid:=by
    exact ⟨rfl,hdata,by simp only [mid,C.execute,hframes]⟩
  obtain ⟨last,hl,hh⟩:=hbody (next::frames) mid hmid
  rcases hh with ⟨hlpc,hld,hfr⟩
  let finish:=C.execute .ret last
  have hf:C.run program 1 last=some finish:=by
    change C.step program last=some finish
    simp [C.step,SemiprimeD1StackCalls.step,hlpc,hret,finish]
  refine ⟨finish,?_,?_,?_,?_⟩
  · rw [show time+2=1+(time+1) by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hl,Option.bind_some,hf]
  · simp only [finish,C.execute,hfr]
  · simp only [finish,C.execute,hfr,hld]
  · simp only [finish,C.execute,hfr]
end RiemannGaussian.SemiprimeD1StackLocalCall
