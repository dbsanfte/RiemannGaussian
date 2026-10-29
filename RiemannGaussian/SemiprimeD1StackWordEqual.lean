/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAdder
import RiemannGaussian.SemiprimeD1StackBytecodeBounds

/-! # Literal streaming equality of binary numeric words
Both bit values are compared directly. Missing high bits mean zero, so unequal
zero padding is accepted. Mismatches physically drain both remaining words.
This compares binary VALUES, distinct from the unary index-length comparator.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordEqual
open SemiprimeD1StackBytecode
open SemiprimeD1StackAdder (Stack store store_left store_right store_output)

/-- Nine fixed labels, storing at most one just-read operand bit in the label. -/
inductive Label where
  | loop | rightEmpty | rightFalse | rightTrue | accept | reject | clearLeft | clearRight | done
  deriving DecidableEq,Repr
/-- Static finite label catalogue, independent of both words and their values. -/
instance : Fintype Label := Fintype.ofList
  [.loop,.rightEmpty,.rightFalse,.rightTrue,.accept,.reject,.clearLeft,.clearRight,.done]
  (by intro k;cases k <;> simp)

/-- ONE fixed literal numeric equality and cleanup table. -/
def code : Label→Instruction Stack Label
  | .loop => .pop .left .rightEmpty .rightFalse .rightTrue
  | .rightEmpty => .pop .right .accept .rightEmpty .reject
  | .rightFalse => .pop .right .loop .loop .reject
  | .rightTrue => .pop .right .reject .reject .loop
  | .accept => .push .output true .done
  | .reject => .push .output false .clearLeft
  | .clearLeft => .pop .left .clearRight .clearLeft .clearLeft
  | .clearRight => .pop .right .done .clearRight .clearRight
  | .done => .halt

/-- Physical operands and output; the fourth fixed stack is empty throughout. -/
def state (pc : Option Label) (flag : Option Bool) (left right output : List Bool) : State Stack Label :=
  ⟨pc,flag,store left right [] output⟩
/-- Actual finite four-stack Boolean machine; no numeric comparison opcode exists. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine Stack.left Stack.output Label.loop code
/-- All data alphabets are fixed Boolean alphabets before either operand. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := by intro k;exact inferInstanceAs (Finite Bool)
/-- The sole transient flag is finite; it contains no numeric word or decoded value. -/
theorem control_finite : Finite machine.σ := by exact inferInstanceAs (Finite (Option Bool))

end RiemannGaussian.SemiprimeD1StackWordEqual
