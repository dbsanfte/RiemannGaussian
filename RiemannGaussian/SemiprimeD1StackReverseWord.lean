/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCopy

/-! # Fixed physical reversal used by the original edge-descriptor producer
The input is physically consumed; every bit is pushed onto the actual output.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackReverseWord
open SemiprimeD1StackBytecode
open SemiprimeD1StackCopy (run_add)

/-- Four literal labels and two Boolean stacks, fixed before every input. -/
def code (label:Fin 4) : Instruction (Fin 2) (Fin 4) :=
  if label=0 then .pop 0 3 1 2
  else if label=1 then .push 1 false 0
  else if label=2 then .push 1 true 0
  else .halt
/-- Actual input and output stack payloads. -/
def payload (input output:List Bool) : Fin 2→List Bool := fun k=>if k=0 then input else output
/-- Actual running source configuration. -/
def state (flag:Option Bool) (input output:List Bool) : State (Fin 2) (Fin 4) :=
  ⟨some 0,flag,payload input output⟩
/-- Actual stopped state, with consumed input. -/
def done (output:List Bool) : State (Fin 2) (Fin 4) := ⟨none,none,payload [] output⟩
/-- One actual pop and one actual push move a bit. -/
theorem move_bit (b:Bool) (xs ys:List Bool) (flag:Option Bool) :
    run code 2 (state flag (b::xs) ys)=some (state (some b) xs (b::ys)) := by
  cases b <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,
    choose,Function.update] <;> funext k <;> fin_cases k <;> rfl
/-- The complete loop, including the actual empty pop and halt. -/
theorem reverse_run (xs ys:List Bool) (flag:Option Bool) :
    run code (2*xs.length+2) (state flag xs ys)=some (done (xs.reverse++ys)) := by
  induction xs generalizing ys flag with
  | nil => simp [run,Function.iterate_succ_apply,step,execute,code,state,done,payload,choose]
  | cons b xs ih =>
    rw [show 2*(b::xs).length+2=2+(2*xs.length+2) by simp;omega,run_add,move_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- One fixed genuine finite machine, with only Boolean alphabets. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine 0 1 0 code
/-- Actual TM2 transition certificate; no retained report or reversed-word advice. -/
def reverseInTime (xs ys:List Bool) (flag:Option Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (state flag xs ys))
      (some (configuration (done (xs.reverse++ys)))) (2*xs.length+2) := by
  apply evalsCorrect 0 1 0 code
  exact ⟨⟨_,reverse_run xs ys flag⟩,le_refl _⟩
end RiemannGaussian.SemiprimeD1StackReverseWord
