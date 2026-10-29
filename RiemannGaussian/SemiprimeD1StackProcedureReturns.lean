/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
/-! # Exact real-return traces for recursive finite procedures
These predicates describe executions of literal fixed programs. Their time and
store parameters occur only in proofs, never as runtime instruction payloads.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
namespace RiemannGaussian.SemiprimeD1StackProcedureReturns
open SemiprimeD1StackProcedureTrace
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
/-- A procedure consumes exactly its actual caller frame and returns its data
for every fixed finite continuation, outer frames and transient flags. -/
def Returns {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (time : ℕ) (entry : L) (data result : K→List Bool) : Prop :=
  ∀next frames before,At entry data (next::frames) before→
    ∃after,C.run program time before=some after ∧ At next result frames after
/-- A proved body followed by a literal real return consumes one caller frame. -/
theorem of_runs {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (time : ℕ) (entry finish : L) (data result : K→List Bool)
    (hbody : Runs program time entry data finish result) (hret : program finish=.ret) :
    Returns program (time+1) entry data result := by
  intro next frames before hb
  obtain ⟨between,hr,hp,hd,hf⟩:=hbody (next::frames) before hb
  let out:=C.execute (.ret : C.Instruction K L) between
  have hone : C.run program 1 between=some out := by
    change C.step program between=some out
    simp only [C.step,SemiprimeD1StackCalls.step,hp,Option.map_some,hret]
    rfl
  refine ⟨out,?_,?_,?_,?_⟩
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hone]
  · simp only [out,C.execute,SemiprimeD1StackCalls.execute,hf]
  · simpa only [out,C.execute,SemiprimeD1StackCalls.execute,hf] using hd
  · simp only [out,C.execute,SemiprimeD1StackCalls.execute,hf]
/-- An actual call pushes its continuation, then executes the proved recursive
procedure and physically pops that frame. No evaluator instruction is added. -/
theorem call {K L : Type} [DecidableEq K] (program : L→C.Instruction K L)
    (time : ℕ) (pc entry next : L) (data result : K→List Bool)
    (hc : program pc=.call entry next) (hr : Returns program time entry data result) :
    Runs program (1+time) pc data next result := by
  intro frames before hb
  rcases hb with ⟨hp,hd,hf⟩
  let entered:=C.execute (.call entry next : C.Instruction K L) before
  have hone : C.run program 1 before=some entered := by
    change C.step program before=some entered
    simp only [C.step,SemiprimeD1StackCalls.step,hp,Option.map_some,hc]
    rfl
  have he : At entry data (next::frames) entered := by
    exact ⟨rfl,hd,congrArg (List.cons next) hf⟩
  obtain ⟨out,hout,ho⟩:=hr next frames entered he
  refine ⟨out,?_,ho⟩
  rw [SemiprimeD1StackReturnLink.run_add,hone,Option.bind_some,hout]
end RiemannGaussian.SemiprimeD1StackProcedureReturns
