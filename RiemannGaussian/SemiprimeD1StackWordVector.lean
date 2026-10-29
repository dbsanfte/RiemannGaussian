/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordBlockBounds
import RiemannGaussian.SemiprimeD1StackAssignmentBody
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # Physical word-vector acquisition from the actual assignment tape
The actual count cache drives closed word-block calls. Each actual fixed-width
word is logged in reverse framed form; one physical reversal then gives the
original word order. Original input, unread suffix and both caches are retained.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordVector
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Block
export SemiprimeD1StackWordBlock (Stack Label program initial store)
end Block
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry contents body_run)
end Body

/-- Ten fixed Boolean roles: five block roles and five acquisition/cache roles. -/
abbrev Stack := Block.Stack⊕Fin 5
/-- Actual retained original binary assignment tape. -/
def original : Stack := .inr 4
/-- Retained physical count-marker cache; only its byte LENGTH is used. -/
def countCache : Stack := .inr 0
/-- Actual disposable count, acquired by a preserving copy. -/
def remaining : Stack := .inr 1
/-- Real reverse-framed chronological word history. -/
def history : Stack := .inr 2
/-- Final physically produced encoded vector. -/
def output : Stack := .inr 3
/-- Real copy of either original input or retained physical count. -/
def copyStack (count : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if count then countCache else original) else
  if k=1 then (if count then remaining else .inl 0) else .inl 3
/-- Real reverse-entry logging shares only the restored block scratch. -/
def bodyStack : Body.Stack→Stack
  | .word => .inl 4 | .scratch => .inl 3 | .history => history
/-- Fixed literal source acquisition and reversal phases. -/
inductive Control where
  | start | copyCount | loop | blockCall | logCall | clearBlock | finish | reverse | emit (bit : Bool) | done
  deriving DecidableEq,Fintype,Repr
/-- All included component locations are finite before every assignment. -/
inductive Label where
  | control (pc : Control) | copy (count : Bool) (pc : Fin 9)
  | block (pc : Block.Label) | body (pc : Body.Label)
  deriving Fintype
local notation "ctl" => SemiprimeD1StackWordVector.Label.control
/-- ONE closed literal finite program, with no grouping or selected-word opcode. -/
def program : Label→C.Instruction Stack Label
  | .control .start => .call (.copy false 0) (ctl .copyCount)
  | .control .copyCount => .call (.copy true 0) (ctl .loop)
  | .control .loop => .base (.pop remaining (ctl .finish) (ctl .blockCall) (ctl .blockCall))
  | .control .blockCall => .call (.block .start) (ctl .logCall)
  | .control .logCall => .call (.body Body.entry) (ctl .clearBlock)
  | .control .clearBlock => .base (.pop (.inl 4) (ctl .loop) (ctl .clearBlock) (ctl .clearBlock))
  | .control .finish => .base (.push output false (ctl .reverse))
  | .control .reverse => .base (.pop history (ctl .done) (ctl (.emit false)) (ctl (.emit true)))
  | .control (.emit b) => .base (.push output b (ctl .reverse))
  | .control .done => .base .halt
  | .copy count pc => SemiprimeD1StackMultiplierLink.instruction (copyStack count) (Label.copy count)
      (SemiprimeD1StackCopy.code pc)
  | .block pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.block (Block.program pc)
  | .body pc => SemiprimeD1StackMultiplierLink.instruction bodyStack Label.body (Body.code pc)
/-- Clean reached payload view; all block/restore scratch is empty here. -/
def store (word reader width count todo block hist out : List Bool) : Stack→List Bool :=
  Sum.elim (Block.store reader width [] [] block)
    (fun k=>if k=0 then count else if k=1 then todo else if k=2 then hist else if k=3 then out else word)
/-- Only original raw assignment, physical width template and count cache enter. -/
def initial (word width count : List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,store word [] width count [] [] [] [],[]⟩
/-- All actual copy roles are distinct. -/
theorem copyStack_injective (count : Bool) : Function.Injective (copyStack count) := by cases count <;> decide
/-- Actual logger word/restoration/history are disjoint. -/
theorem bodyStack_injective : Function.Injective bodyStack := by
  intro i j h;cases i <;> cases j <;> simp_all [bodyStack,history]
/-- Genuine fixed finite bit machine, independent of every original assignment. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine original output (ctl .start) program
/-- Actual Boolean and return-tag alphabets are fixed and finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite original output (ctl .start) program
/-- No word, count, width, original value, list or grouping closure is in control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite original output (ctl .start) program
/-- Every physical data role is counted at all actual prefixes. -/
theorem stack_card : Fintype.card Stack=10 := by decide

end RiemannGaussian.SemiprimeD1StackWordVector
