/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBytecode
import RiemannGaussian.SemiprimeBitArithmetic

/-! # Actual finite-stack ripple adder
Four Boolean stacks hold the two operands, reverse output and final output.
All carry and digit flags are finite label fields. The code uses only actual
pop/push/jump/halt bytecode, compiled by the checked finite-machine compiler.
There is no native natural/list value in the machine control.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackAdder
open SemiprimeD1StackBytecode SemiprimeBitArithmetic

/-- Fixed finite data-stack bank. -/
inductive Stack where
  | left | right | scratch | output
  deriving DecidableEq,Repr

/-- An explicit constant stack enumeration, independent of all operand data. -/
instance : Fintype Stack := Fintype.ofList [.left,.right,.scratch,.output] (by
  intro k
  cases k <;> simp)

/-- Carry and the two just-read bits form only a fixed finite control table. -/
inductive Label where
  | start (carry : Bool)
  | readRight (carry : Bool) (left : Option Bool)
  | emit (carry : Bool) (left right : Option Bool)
  | reverse
  | output (bit : Bool)
  | done
  deriving DecidableEq,Fintype,Repr

/-- Literal finite word-adder program, independent of either input length. -/
def code : Label→Instruction Stack Label
  | .start c => .pop .left (.readRight c none) (.readRight c (some false)) (.readRight c (some true))
  | .readRight c x => .pop .right (.emit c x none) (.emit c x (some false)) (.emit c x (some true))
  | .emit c none none => if c then .push .scratch true .reverse else .jump .reverse
  | .emit c x y =>
    let digit:=fullAdder (x.getD false) (y.getD false) c
    .push .scratch digit.1 (.start digit.2)
  | .reverse => .pop .scratch .done (.output false) (.output true)
  | .output b => .push .output b .reverse
  | .done => .halt

/-- Literal four-stack payload encoding, including work and pre-existing output. -/
def store (left right scratch output : List Bool) : Stack→List Bool
  | .left => left
  | .right => right
  | .scratch => scratch
  | .output => output

/-- Source configuration for the fixed finite program, with no result advice. -/
def state (pc : Option Label) (flag : Option Bool) (left right scratch output : List Bool) : State Stack Label :=
  ⟨pc,flag,store left right scratch output⟩

/-- Actual finite target machine. Subroutine arguments occupy the two data
stacks; a separate caller/frame parser supplies the second prepared operand. -/
def machine (carry : Bool) : Turing.FinTM2 :=
  SemiprimeD1StackBytecode.machine Stack.left Stack.output (.start carry) code

/-- Every stack, not merely the designated input, has Boolean alphabet. -/
theorem all_alphabets (carry : Bool) : ∀k,(machine carry).Γ k=Bool := by intro k;rfl

/-- Every actual machine alphabet is finite. -/
theorem all_alphabets_finite (carry : Bool) : ∀k,Finite ((machine carry).Γ k) := by
  intro k
  exact inferInstanceAs (Finite Bool)

/-- Internal machine flags are finite and contain no unbounded operand. -/
theorem control_finite (carry : Bool) : Finite (machine carry).σ :=
  inferInstanceAs (Finite (Option Bool))

/-- Actual operand replacement is exactly the corresponding stack update. -/
theorem store_left (xs ys acc out xs' : List Bool) :
    Function.update (store xs ys acc out) .left xs'=store xs' ys acc out := by
  funext k
  cases k <;> rfl

/-- Actual second-operand replacement has no implicit array lookup. -/
theorem store_right (xs ys acc out ys' : List Bool) :
    Function.update (store xs ys acc out) .right ys'=store xs ys' acc out := by
  funext k
  cases k <;> rfl

/-- Every reverse-output push changes only its actual Boolean stack. -/
theorem store_scratch (xs ys acc out acc' : List Bool) :
    Function.update (store xs ys acc out) .scratch acc'=store xs ys acc' out := by
  funext k
  cases k <;> rfl

/-- Every final-output push changes only its actual Boolean stack. -/
theorem store_output (xs ys acc out out' : List Bool) :
    Function.update (store xs ys acc out) .output out'=store xs ys acc out' := by
  funext k
  cases k <;> rfl

/-- Three-way finite dispatch retains the actual first read, including EOF. -/
theorem choose_left (c : Bool) (bit : Option Bool) :
    choose (Label.readRight c none) (.readRight c (some false)) (.readRight c (some true)) bit=
      Label.readRight c bit := by cases bit with | none=>rfl | some b=>cases b <;> rfl

/-- Three-way finite dispatch retains the actual second read, including EOF. -/
theorem choose_right (c : Bool) (x bit : Option Bool) :
    choose (Label.emit c x none) (.emit c x (some false)) (.emit c x (some true)) bit=
      Label.emit c x bit := by cases bit with | none=>rfl | some b=>cases b <;> rfl

/-- First real transition consumes one actual left operand bit. -/
theorem step_left (c : Bool) (flag : Option Bool) (xs ys acc out : List Bool) :
    step code (state (some (.start c)) flag xs ys acc out)=
      some (state (some (.readRight c xs.head?)) xs.head? xs.tail ys acc out) := by
  simp only [step,state,Option.map_some,code,execute,choose_left,store,store_left]

/-- Second real transition consumes one actual right operand bit. -/
theorem step_right (c : Bool) (x flag : Option Bool) (xs ys acc out : List Bool) :
    step code (state (some (.readRight c x)) flag xs ys acc out)=
      some (state (some (.emit c x ys.head?)) ys.head? xs ys.tail acc out) := by
  simp only [step,state,Option.map_some,code,execute,choose_right,store,store_right]

end RiemannGaussian.SemiprimeD1StackAdder
