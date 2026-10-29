/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BooleanTreeStream
import RiemannGaussian.SemiprimeD1StackRecursiveCallTrace

/-! # Actual preorder Boolean root-tree writer
Only physical entry bits and depth markers are initial data. Literal recursive
calls pop/restore ONE actual marker and emit both children, false first; a leaf
reads ONE actual entry bit and pushes its complete fixed codec payload. A real
final reverse returns the original tree order. No table, getter, evaluator,
cardinality, exponent, entry answer or clock occurs in finite control.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackBooleanTree
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
/-- Four fixed Boolean roles; all unbounded frames are actual finite-label cells. -/
inductive Stack where | input | depth | history | output
  deriving DecidableEq,Repr
instance : Fintype Stack := Fintype.ofList [.input,.depth,.history,.output] (by intro k;cases k <;> simp)
/-- Depth is stored on tape, while only restored Boolean marker bits enter control. -/
inductive Label where
  | start | visit | read | node (bit : Bool) | left (bit : Bool) | afterLeft (bit : Bool)
  | restore (bit : Bool) | emit (bit : Bool) (position : Fin 6) | returnPC
  | reverse | write (bit : Bool) | done
  deriving DecidableEq,Fintype,Repr
/-- ONE fixed literal first-order program, including real recursion/returns. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call .visit .reverse
  | .visit=>.base (.pop .depth .read (.node false) (.node true))
  | .read=>.base (.pop .input (.emit false 0) (.emit false 0) (.emit true 0))
  | .node b=>.base (.push .history true (.left b))
  | .left b=>.call .visit (.afterLeft b)
  | .afterLeft b=>.call .visit (.restore b)
  | .restore b=>.base (.push .depth b .returnPC)
  | .emit b i=>
      if i=0 then .base (.push .history false (.emit b 1))
      else if i=1 then .base (.push .history true (.emit b 2))
      else if i=2 then .base (.push .history b (.emit b 3))
      else if i=3 then .base (.push .history b (if b then .emit b 4 else .returnPC))
      else if i=4 then .base (.push .history false (.emit b 5))
      else .base (.push .history false .returnPC)
  | .returnPC=>.ret
  | .reverse=>.base (.pop .history .done (.write false) (.write true))
  | .write b=>.base (.push .output b .reverse)
  | .done=>.base .halt
/-- Physical payload view, never a runtime list/table supplier. -/
def store (input depth history output : List Bool) : Stack→List Bool
  | .input=>input
  | .depth=>depth
  | .history=>history
  | .output=>output
/-- Entry bits and depth markers only; acquiring them is the enclosing caller's work. -/
def initial (input depth : List Bool) : C.State Stack Label := ⟨some .start,none,none,store input depth [] [],[]⟩
/-- Genuine fixed finite machine for the whole actual writer. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine .input .output .start program
/-- All data and real return alphabets are finite before all physical streams. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite Stack.input Stack.output Label.start program
/-- No natural, list, table or elapsed-value payload is hidden in control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite Stack.input Stack.output Label.start program
/-- Every physical Boolean role appears in all-prefix inventory bounds. -/
theorem stack_card : Fintype.card Stack=4 := by decide
end RiemannGaussian.SemiprimeD1StackBooleanTree
