/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCopy

/-! # Literal finite-code inclusion with preserved auxiliary payload
This is a proof-producing inclusion of one fixed bytecode component into a
larger fixed program. Sum tags are static finite names. No input-sized program
or dynamically supplied operation is executed by this construction.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRename
open SemiprimeD1StackBytecode

/-- Embed every literal stack/label operand into the left fixed-name component. -/
def instruction {K L A B:Type} : Instruction K L→Instruction (K⊕A) (L⊕B)
  | .push k bit next => .push (.inl k) bit (.inl next)
  | .pop k empty low high => .pop (.inl k) (.inl empty) (.inl low) (.inl high)
  | .peek k empty low high => .peek (.inl k) (.inl empty) (.inl low) (.inl high)
  | .jump next => .jump (.inl next)
  | .halt => .halt

/-- Embed a component state while retaining every other actual stack payload. -/
def state {K L A B:Type} (aux:A→List Bool) (s:State K L) : State (K⊕A) (L⊕B) :=
  ⟨s.pc.map Sum.inl,s.flag,Sum.elim s.store aux⟩

/-- A component push/pop updates only its named physical stack. -/
theorem payload_update {K A:Type} [DecidableEq K] [DecidableEq A]
    (store:K→List Bool) (aux:A→List Bool) (k:K) (bits:List Bool) :
    Sum.elim (Function.update store k bits) aux=
      Function.update (Sum.elim store aux) (.inl k) bits := by
  funext target
  cases target with
  | inl target => simp [Function.update]
  | inr target => simp [Function.update]

/-- Literal three-way dispatch commutes with fixed finite label inclusion. -/
theorem choose_inl {L B:Type} (empty low high:L) (flag:Option Bool) :
    choose (Sum.inl empty: L⊕B) (.inl low) (.inl high) flag=
      Sum.inl (choose empty low high flag) := by
  cases flag with
  | none => rfl
  | some bit => cases bit <;> rfl

/-- Every included component instruction has exactly the same payload effect. -/
theorem execute_inl {K L A B:Type} [DecidableEq K] [DecidableEq A]
    (op:Instruction K L) (aux:A→List Bool) (s:State K L) :
    execute (instruction (A:=A) (B:=B) op) (state aux s)=state aux (execute op s) := by
  cases op with
  | push k bit next =>
    simp only [instruction,execute,state,Sum.elim_inl,Option.map_some]
    exact congrArg (fun store=>(State.mk (some (Sum.inl next)) s.flag store:State (K⊕A) (L⊕B))) (payload_update s.store aux k _).symm
  | pop k empty low high =>
    simp only [instruction,execute,state,Sum.elim_inl,choose_inl,Option.map_some]
    exact congrArg (fun store=>(State.mk (some (Sum.inl (choose empty low high (s.store k).head?)))
      (s.store k).head? store:State (K⊕A) (L⊕B))) (payload_update s.store aux k _).symm
  | peek k empty low high => simp only [instruction,execute,state,Sum.elim_inl,choose_inl,Option.map_some]
  | jump next => rfl
  | halt => rfl

/-- Static code inclusion gives actual one-step refinement; auxiliary stacks persist. -/
theorem step_inl {K L A B:Type} [DecidableEq K] [DecidableEq A]
    (code:L→Instruction K L) (whole:L⊕B→Instruction (K⊕A) (L⊕B))
    (hcode:∀label,whole (.inl label)=instruction (code label))
    (aux:A→List Bool) (s:State K L) :
    step whole (state aux s)=(step code s).map (state aux) := by
  cases hp:s.pc with
  | none => simp [step,state,hp]
  | some label =>
    simp only [step,state,hp,Option.map_some]
    rw [hcode]
    exact congrArg some (execute_inl (code label) aux s)

/-- Every executed finite component trace embeds, with the same transition count. -/
theorem run_inl {K L A B:Type} [DecidableEq K] [DecidableEq A]
    (code:L→Instruction K L) (whole:L⊕B→Instruction (K⊕A) (L⊕B))
    (hcode:∀label,whole (.inl label)=instruction (code label))
    (aux:A→List Bool) (fuel:ℕ) (s:State K L) :
    run whole fuel (state aux s)=(run code fuel s).map (state aux) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [show fuel+1=1+fuel by omega,SemiprimeD1StackCopy.run_add,SemiprimeD1StackCopy.run_add]
    change (step whole (state aux s)).bind (run whole fuel)=
      ((step code s).bind (run code fuel)).map (state aux)
    rw [step_inl code whole hcode]
    cases step code s with
    | none => rfl
    | some next => exact ih next

/-- An actual component certificate becomes a genuine finite-machine certificate
for the larger FIXED program, not a semantic procedure-call instruction. -/
def evalsIncluded {K L A B:Type} [DecidableEq K] [DecidableEq A]
    [Fintype K] [Fintype L] [Fintype A] [Fintype B]
    (code:L→Instruction K L) (whole:L⊕B→Instruction (K⊕A) (L⊕B))
    (hcode:∀label,whole (.inl label)=instruction (code label))
    (input output:K⊕A) (main:L⊕B) (aux:A→List Bool) (s out:State K L) (time:ℕ)
    (h:StateTransition.EvalsToInTime (step code) s (some out) time) :
    StateTransition.EvalsToInTime (machine input output main whole).step
      (configuration (state aux s)) (some (configuration (state aux out))) time := by
  apply evalsCorrect input output main whole
  refine ⟨⟨h.steps,?_⟩,h.steps_le_m⟩
  change run whole h.steps (state aux s)=some (state aux out)
  rw [run_inl code whole hcode]
  have he:=h.evals_in_steps
  change run code h.steps s=some out at he
  rw [he]
  rfl
/-- A concrete larger fixed program containing copy and one extra literal label. -/
def copyProgram : Fin 9⊕Unit→Instruction (Fin 3⊕Unit) (Fin 9⊕Unit)
  | .inl label => instruction (SemiprimeD1StackCopy.code label)
  | .inr _ => .halt

/-- One fixed larger machine; its fourth stack is arbitrary preserved payload. -/
def copyMachine : Turing.FinTM2 := machine (.inl 0) (.inl 1) (.inl 0) copyProgram

/-- Concrete inclusion actually copies through the larger machine while preserving
an unrelated fourth Boolean stack, without an opaque submachine opcode. -/
def copyWithAuxInTime (xs ys aux:List Bool) (flag:Option Bool) :
    StateTransition.EvalsToInTime copyMachine.step
      (configuration (state (fun _:Unit=>aux) (SemiprimeD1StackCopy.state 0 flag xs ys [])))
      (some (configuration (state (fun _:Unit=>aux) (SemiprimeD1StackCopy.done xs (xs++ys)))))
      (5*xs.length+3) := by
  apply evalsIncluded SemiprimeD1StackCopy.code copyProgram (fun _=>rfl)
    (.inl 0) (.inl 1) (.inl 0) (fun _:Unit=>aux)
  exact ⟨⟨5*xs.length+3,SemiprimeD1StackCopy.copy_words xs ys flag⟩,le_refl _⟩
end RiemannGaussian.SemiprimeD1StackRename
