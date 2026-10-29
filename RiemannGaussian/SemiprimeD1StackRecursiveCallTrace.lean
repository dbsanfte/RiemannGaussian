/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
/-! # Actual recursive calls from a trace ending at a literal return
This helper preserves the dynamic physical return stack. It does not introduce
an evaluator or procedure opcode: both the call and the return are real steps.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackRecursiveCallTrace
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
open SemiprimeD1StackProcedureTrace (At Runs)
/-- A real call, proved recursive body and real return, preserving all outer frames. -/
theorem invoke {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (pc entry returnPC next : L) (hcall : program pc=.call entry next)
    (hret : program returnPC=.ret) (time : ℕ) (input output : K→List Bool)
    (body : Runs program time entry input returnPC output) :
    Runs program (time+2) pc input next output := by
  intro frames target h
  rcases h with ⟨hpc,hdata,hframes⟩
  let called := C.execute (.call entry next) target
  have hfirst : C.run program 1 target=some called := by
    change C.step program target=some called
    simp only [C.step,SemiprimeD1StackCalls.step,hpc,Option.map_some,hcall,called]
  have hcalled : At entry input (next::frames) called := by
    exact ⟨rfl,hdata,by simp only [called,C.execute,hframes]⟩
  obtain ⟨between,hbody,hbetween⟩ := body (next::frames) called hcalled
  let finish := C.execute .ret between
  have hlast : C.run program 1 between=some finish := by
    change C.step program between=some finish
    simp only [C.step,SemiprimeD1StackCalls.step,hbetween.1,Option.map_some,hret,finish]
  have hout : At next output frames finish := by
    exact ⟨by simp only [finish,C.execute,hbetween.2.2],
      by simpa only [finish,C.execute,hbetween.2.2] using hbetween.2.1,
      by simp only [finish,C.execute,hbetween.2.2]⟩
  refine ⟨finish,?_,hout⟩
  rw [show time+2=1+(time+1) by omega,SemiprimeD1StackReturnLink.run_add,hfirst,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add,hbody,Option.bind_some,hlast]
end RiemannGaussian.SemiprimeD1StackRecursiveCallTrace
