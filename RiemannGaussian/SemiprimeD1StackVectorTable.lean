/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticWordTable
/-! # Actual whole-table compiler for a fixed physical coefficient-vector source
The literal source code and complete role inventory are compile-time constants.
Each real DFS leaf copies its input template, reverses the actual assignment,
calls that source and copies its ACTUAL vector bytes. Only the tree-leaf FALSE
tag is added. All source roles are physically drained before the next leaf.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackVectorTable
export SemiprimeD1StackStaticWordTable
  (Static Aux Stack Label checker template counter aux role copyStack reverseStack
    loadNext recordReverseStack store data initial stack_card)
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace D
export SemiprimeD1StackDigitCount (Stack Label program data)
end D
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- Three real preserving-copy roles for the source's actual complete vector payload. -/
def vectorCopyStack (k : Fin 3) : Stack K :=
  if k=0 then checker s.output else if k=1 then aux .work else aux .scratch
/-- The old finite eleven-label frame range contains this actual nine-label copy inclusion. -/
def vectorCopyLabel (pc : Fin 9) : Label L s.roles.length :=
  .frame ⟨pc.val,Nat.lt_trans pc.isLt (by decide : 9<11)⟩
/-- One fixed literal table program: actual source vector bytes are copied, tagged and reversed. -/
def program : Label L s.roles.length→C.Instruction (Stack K) (Label L s.roles.length)
  | .emitSentinel => .call (vectorCopyLabel s 0) .emitLeaf
  | .emitLeaf => .base (.push (aux .reversed) false .emitReverse)
  | .frame pc => if h : pc.val<9 then
      SemiprimeD1StackMultiplierLink.instruction (vectorCopyStack s) (vectorCopyLabel s)
        (SemiprimeD1StackCopy.code ⟨pc.val,h⟩)
      else .base .halt
  | pc => SemiprimeD1StackStaticWordTable.program s pc
omit [DecidableEq K] in
/-- The actual vector payload source, buffer and restoration scratch are distinct. -/
theorem vectorCopy_injective : Function.Injective (vectorCopyStack s) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [vectorCopyStack,checker,aux]
omit [DecidableEq K] in
/-- Every included real copy label has exactly its own literal source instruction. -/
theorem vectorCopy_program (pc : Fin 9) :
    program s (vectorCopyLabel s pc)=
      SemiprimeD1StackMultiplierLink.instruction (vectorCopyStack s) (vectorCopyLabel s)
        (SemiprimeD1StackCopy.code pc) := by
  simp only [vectorCopyLabel,program,pc.isLt,dite_eq_left]
/-- Actual fixed finite whole-table machine; its only designated input is the physical scope tape. -/
def machine [Fintype K] [Fintype L] : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine (counter .bank) (aux .output) .start (program s)
/-- No vector, coefficient, scope, count, getter or native evaluator inhabits runtime control. -/
theorem control_finite [Fintype K] [Fintype L] : Finite (machine s).σ :=
  SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackVectorTable
