/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAdder
import RiemannGaussian.SemiprimeD1StackCopy

/-! # Physical acquisition of unary precision counters from binary words
One fixed finite program reverses its binary input, then physically doubles a
marker stack and appends the next digit. No native natural-number value is in
machine control. Large factor/coefficient payloads remain binary; this routine
is for control values, such as precision, whose VALUES are already bounded.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackUnaryCounter
open SemiprimeD1StackBytecode
open SemiprimeD1StackAdder (Stack store store_left store_right store_scratch store_output)

/-- Fixed labels; the only remembered digit is one Boolean. -/
inductive Label where
  | reverse | save (bit : Bool) | read | double (bit : Bool)
  | first (bit : Bool) | second (bit : Bool)
  | move (bit : Bool) | movePush (bit : Bool) | finish (bit : Bool) | done
  deriving DecidableEq,Fintype,Repr

/-- Real reversal, doubling, movement and digit insertion instructions. -/
def code : Label→Instruction Stack Label
  | .reverse => .pop .left .read (.save false) (.save true)
  | .save b => .push .right b .reverse
  | .read => .pop .right .done (.double false) (.double true)
  | .double b => .pop .output (.move b) (.first b) (.first b)
  | .first b => .push .scratch true (.second b)
  | .second b => .push .scratch true (.double b)
  | .move b => .pop .scratch (.finish b) (.movePush b) (.movePush b)
  | .movePush b => .push .output true (.move b)
  | .finish false => .jump .read
  | .finish true => .push .output true .read
  | .done => .halt

/-- Data-only source state for the fixed four-stack program. -/
def state (pc : Option Label) (flag : Option Bool) (input digits scratch counter : List Bool) :
    State Stack Label := ⟨pc,flag,store input digits scratch counter⟩

/-- One actual fixed finite machine, before all binary inputs. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine Stack.left Stack.output .reverse code

/-- All physical stack alphabets are Boolean. -/
theorem all_alphabets : ∀k,machine.Γ k=Bool := by intro k;rfl

/-- Native numbers and lists are absent from the finite internal state. -/
theorem control_finite : Finite machine.σ := inferInstanceAs (Finite (Option Bool))

/-- Two genuine transitions for one input digit of the reversal. -/
theorem reverse_bit (b : Bool) (xs digits : List Bool) (flag : Option Bool) :
    run code 2 (state (some .reverse) flag (b::xs) digits [] [])=
      some (state (some .reverse) (some b) xs (b::digits) [] []) := by
  cases b <;> simp only [run,Function.iterate_succ_apply,Function.iterate_zero,
    id_eq,Option.bind_some,step,state,Option.map_some,code,execute,store,
    store_left,store_right,List.head?_cons,List.tail_cons,choose]

/-- The actual first loop pays for the full physical input reversal. -/
theorem reverse_run (xs digits : List Bool) (flag : Option Bool) :
    run code (2*xs.length+1) (state (some .reverse) flag xs digits [] [])=
      some (state (some .read) none [] (xs.reverse++digits) [] []) := by
  induction xs generalizing digits flag with
  | nil =>
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,run,Function.iterate_one,
      Option.bind_some,step,state,Option.map_some,code,execute,store,store_left,
      List.head?_nil,List.tail_nil,choose,List.reverse_nil,List.nil_append]
  | cons b xs ih =>
    rw [show 2*(b::xs).length+1=2+(2*xs.length+1) by simp;omega,
      SemiprimeD1StackCopy.run_add,reverse_bit,Option.bind_some,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

end RiemannGaussian.SemiprimeD1StackUnaryCounter
