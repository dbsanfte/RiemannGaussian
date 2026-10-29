/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnaryProduct
/-! # Physical strict sum comparison for mixed-radix digits
The machine consumes three unary counters, emits one Boolean, and clears every
operand. Its control and Boolean stack alphabets are fixed before all inputs.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackUnarySumLess
open Turing Turing.TM2 Turing.TM2.Stmt
open SemiprimeD1StackUnaryDivmod (unary unary_succ unary_bump)
open SemiprimeD1StackFiniteControlPaths (SourcePath)
/-- Four fixed physical operand/result stacks. -/
inductive Stack | left | right | limit | valid deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.left,.right,.limit,.valid}
  complete := by intro k; cases k <;> simp
/-- Eight fixed join, comparison and cleanup phases. -/
inductive PC | join | compare | consume | test | clear | reject | fail | accept
  deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.join,.compare,.consume,.test,.clear,.reject,.fail,.accept}
  complete := by intro k; cases k <;> simp
/-- Every unbounded tape symbol is Boolean. -/
abbrev Alphabet (_ : Stack) := Bool
/-- Every comparison step pops literal data cells; no numerical predicate is executed. -/
def program : PC → Stmt Alphabet PC (Option Bool)
  | .join => .pop .right (fun _ b=>b) (.branch Option.isSome
      (.push .left (fun _=>true) (.goto (fun _=>.join))) (.goto (fun _=>.compare)))
  | .compare => .pop .left (fun _ b=>b) (.branch Option.isSome
      (.goto (fun _=>.consume)) (.goto (fun _=>.test)))
  | .consume => .pop .limit (fun _ b=>b) (.branch Option.isSome
      (.goto (fun _=>.compare)) (.goto (fun _=>.reject)))
  | .test => .peek .limit (fun _ b=>b) (.branch Option.isSome
      (.goto (fun _=>.clear)) (.goto (fun _=>.fail)))
  | .clear => .pop .limit (fun _ b=>b) (.branch Option.isSome
      (.goto (fun _=>.clear)) (.goto (fun _=>.accept)))
  | .reject => .pop .left (fun _ b=>b) (.branch Option.isSome
      (.goto (fun _=>.reject)) (.goto (fun _=>.fail)))
  | .fail => .push .valid (fun _=>false) .halt
  | .accept => .push .valid (fun _=>true) .halt

/-- Literal physical stack bank. -/
def contents (left right limit valid : List Bool) : Stack→List Bool
  | .left=>left | .right=>right | .limit=>limit | .valid=>valid

/-- Explicit finite-control configuration. -/
def cfg (pc : Option PC) (flag : Option Bool) (left right limit valid : List Bool) :
    Cfg Alphabet PC (Option Bool) := ⟨pc,flag,contents left right limit valid⟩
/-- Actual source transition paths for the fixed comparison code. -/
abbrev Executes := SourcePath program
@[simp] theorem update_contents (left right limit valid xs : List Bool) (k : Stack) :
    Function.update (contents left right limit valid) k xs=
      contents (if k=.left then xs else left) (if k=.right then xs else right)
        (if k=.limit then xs else limit) (if k=.valid then xs else valid) := by
  funext j; cases k <;> cases j <;> simp [contents]

/-- Actual input concatenation pays one pop/push transition for every right operand token. -/
theorem join_exec (m n d : ℕ) (flag : Option Bool) :
    Executes (n+1) (cfg (some .join) flag (unary m) (unary n) (unary d) [])
      (cfg (some .compare) none (unary (n+m)) [] (unary d) []) := by
  induction n generalizing m flag with
  | zero =>
    apply SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,unary,TM2.step,TM2.stepAux]
  | succ n ih =>
    have hs : TM2.step program (cfg (some .join) flag (unary m) (unary (n+1)) (unary d) [])=
        some (cfg (some .join) (some true) (unary (m+1)) (unary n) (unary d) []) := by
      simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
    have ht := SourcePath.next hs (ih (m+1) (some true))
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ht

end RiemannGaussian.SemiprimeD1StackUnarySumLess
