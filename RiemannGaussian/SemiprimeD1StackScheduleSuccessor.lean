/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1Schedule

/-! # Physical successor of the original dyadic recursion schedule
The prepared level and exponent markers are Boolean stack payloads. A literal
pairwise scan halves the levels; real preserving copies add twice that new
block to the exponent. Root metadata acquisition is a separate obligation.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackScheduleSuccessor
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
/-- Six fixed Boolean roles, including the retained parent metadata. -/
inductive Stack where
  | exponent | levels | reader | scratch | nextLevels | nextExponent
  deriving DecidableEq,Repr
instance : Fintype Stack where
  elems := {.exponent,.levels,.reader,.scratch,.nextLevels,.nextExponent}
  complete := by intro k;cases k <;> simp
/-- Three fixed uses of the same literal preserving-copy program. -/
inductive CopyKind where
  | levels | exponent | nextLevels
  deriving DecidableEq,Repr
instance : Fintype CopyKind where
  elems := {.levels,.exponent,.nextLevels}
  complete := by intro k;cases k <;> simp
/-- Finite schedule phases; no numerical recursion depth is internal control. -/
inductive Control where
  | start | half | second | emit | exponent | first | last | done
  deriving DecidableEq,Repr
instance : Fintype Control where
  elems := {.start,.half,.second,.emit,.exponent,.first,.last,.done}
  complete := by intro k;cases k <;> simp
/-- Fixed local labels and included copy labels. -/
abbrev Label := Control ⊕ (CopyKind × Fin 9)
/-- Actual copied parent or child stack. -/
def copySource : CopyKind→Stack
  | .levels => .levels | .exponent => .exponent | .nextLevels => .nextLevels
/-- Actual copy destination. -/
def copyTarget : CopyKind→Stack
  | .levels => .reader | .exponent => .nextExponent | .nextLevels => .nextExponent
/-- Three distinct operands of each included preserving copy. -/
def copyStack (kind:CopyKind) (k:Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else .scratch
local notation "ctl" => Sum.inl
local notation "cpy" => (fun kind pc=>Sum.inr (kind,pc))
/-- Literal fixed program, with neither a halving oracle nor an exponent opcode. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .call (cpy .levels 0) (ctl .half)
  | .inl .half => .base (.pop .reader (ctl .exponent) (ctl .second) (ctl .second))
  | .inl .second => .base (.pop .reader (ctl .exponent) (ctl .emit) (ctl .emit))
  | .inl .emit => .base (.push .nextLevels true (ctl .half))
  | .inl .exponent => .call (cpy .exponent 0) (ctl .first)
  | .inl .first => .call (cpy .nextLevels 0) (ctl .last)
  | .inl .last => .call (cpy .nextLevels 0) (ctl .done)
  | .inl .done => .base .halt
  | .inr (kind,pc) => SemiprimeD1StackMultiplierLink.instruction
      (copyStack kind) (cpy kind) (SemiprimeD1StackCopy.code pc)
/-- Exact six-stack payload, with all scratch explicitly represented. -/
def data (a u reader scratch nextLevels nextExponent:List Bool) : Stack→List Bool
  | .exponent => a | .levels => u | .reader => reader | .scratch => scratch
  | .nextLevels => nextLevels | .nextExponent => nextExponent
/-- Prepared metadata input; numerical input words are not made unary here. -/
def initial (a u:List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,data a u [] [] [] [],[]⟩
/-- Actual child block produced by the scan. -/
def halfWord (u:List Bool) : List Bool := List.replicate (u.length/2) true
/-- Final physical payload, including both retained parent words. -/
def result (a u:List Bool) : Stack→List Bool :=
  data a u [] [] (halfWord u) (halfWord u++halfWord u++a)
/-- One fixed genuine finite machine before all prepared inputs. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  Stack.levels Stack.nextExponent (ctl .start) program
/-- Every included copy has three distinct physical operands. -/
theorem copyStack_injective (kind:CopyKind) : Function.Injective (copyStack kind) := by
  cases kind <;> decide
/-- Every physical data role is counted. -/
theorem stack_card : Fintype.card Stack=6 := by decide
/-- All actual alphabets, including real return labels, are finite. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- The internal state carries only finite Boolean and return-label flags. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackScheduleSuccessor
