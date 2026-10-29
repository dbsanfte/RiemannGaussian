/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAdder
import RiemannGaussian.SemiprimeBitDivision

/-! # Fixed finite-stack ripple subtraction
Both operands live on Boolean stacks. Borrow and read digits occupy only finite
labels. The final borrow is an actual output-prefix bit, never a native record
or an assumed non-underflow predicate.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace RiemannGaussian.SemiprimeD1StackSubtractor
open SemiprimeD1StackBytecode SemiprimeBitDivision
open SemiprimeD1StackAdder (Stack store store_left store_right store_scratch store_output)

/-- Borrow and digit flags form a fixed finite control table. -/
inductive Label where
  | start (borrow : Bool)
  | readRight (borrow : Bool) (left : Option Bool)
  | emit (borrow : Bool) (left right : Option Bool)
  | reverse (borrow : Bool)
  | output (borrow bit : Bool)
  | borrow (bit : Bool)
  | done
  deriving DecidableEq,Fintype,Repr

/-- Literal finite subtraction code, fixed before either operand is chosen. -/
def code : Label → Instruction Stack Label
  | .start b => .pop .left (.readRight b none) (.readRight b (some false)) (.readRight b (some true))
  | .readRight b x => .pop .right (.emit b x none) (.emit b x (some false)) (.emit b x (some true))
  | .emit b none none => .jump (.reverse b)
  | .emit b x y =>
    let digit:=fullSubtractor (x.getD false) (y.getD false) b
    .push .scratch digit.1 (.start digit.2)
  | .reverse b => .pop .scratch (.borrow b) (.output b false) (.output b true)
  | .output b bit => .push .output bit (.reverse b)
  | .borrow b => .push .output b .done
  | .done => .halt

/-- Literal state over four Boolean stacks, with only finite labels/flags. -/
def state (pc : Option Label) (flag : Option Bool) (left right scratch output : List Bool) : State Stack Label :=
  ⟨pc,flag,store left right scratch output⟩

/-- Actual compiled finite machine. A caller prepares both operand stacks. -/
def machine (borrow : Bool) : Turing.FinTM2 :=
  SemiprimeD1StackBytecode.machine Stack.left Stack.output (.start borrow) code

/-- Every actual stack alphabet is Boolean, independent of input width. -/
theorem all_alphabets (borrow : Bool) : ∀k,(machine borrow).Γ k=Bool := by intro k;rfl

/-- All machine stack alphabets are genuinely finite. -/
theorem all_alphabets_finite (borrow : Bool) : ∀k,Finite ((machine borrow).Γ k) := by
  intro k
  exact inferInstanceAs (Finite Bool)

/-- No unbounded operand is hidden in the machine's finite internal state. -/
theorem control_finite (borrow : Bool) : Finite (machine borrow).σ :=
  inferInstanceAs (Finite (Option Bool))

/-- The literal program has35 control labels before any words are supplied. -/
theorem label_count : Fintype.card Label=35 := by decide

/-- Three-way first-read dispatch includes real EOF. -/
theorem choose_left (b : Bool) (bit : Option Bool) :
    choose (Label.readRight b none) (.readRight b (some false)) (.readRight b (some true)) bit=
      Label.readRight b bit := by cases bit with | none=>rfl | some x=>cases x <;> rfl

/-- Three-way second-read dispatch retains the actual right bit or EOF. -/
theorem choose_right (b : Bool) (x bit : Option Bool) :
    choose (Label.emit b x none) (.emit b x (some false)) (.emit b x (some true)) bit=
      Label.emit b x bit := by cases bit with | none=>rfl | some y=>cases y <;> rfl

/-- First actual transition pops the first operand, without a value oracle. -/
theorem step_left (b : Bool) (flag : Option Bool) (xs ys acc out : List Bool) :
    step code (state (some (.start b)) flag xs ys acc out)=
      some (state (some (.readRight b xs.head?)) xs.head? xs.tail ys acc out) := by
  simp only [step,state,Option.map_some,code,execute,choose_left,store,store_left]

/-- Second actual transition pops the second prepared operand. -/
theorem step_right (b : Bool) (x flag : Option Bool) (xs ys acc out : List Bool) :
    step code (state (some (.readRight b x)) flag xs ys acc out)=
      some (state (some (.emit b x ys.head?)) ys.head? xs ys.tail acc out) := by
  simp only [step,state,Option.map_some,code,execute,choose_right,store,store_right]

end RiemannGaussian.SemiprimeD1StackSubtractor
