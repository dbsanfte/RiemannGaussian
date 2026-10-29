/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAdder
import RiemannGaussian.SemiprimeD1JetScalarBits

/-! # Fixed finite-stack low-prefix reduction and canonical trimming
The width is a physical counter word whose LENGTH is the precision. Unbounded
input/counter/output words live on four Boolean stacks, never in control. All
input leftovers and counter leftovers are physically consumed. The following
execution module proves the actual transition bound and old-reducer bytes.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackReduce
open SemiprimeD1StackBytecode
open SemiprimeD1StackAdder (Stack store store_left store_right store_scratch store_output)

/-- Fixed control labels, independent of the input word and requested width. -/
inductive Label where
  | take | read | save (bit : Bool) | clearInput | clearWidth
  | trim | found | move | copy (bit : Bool) | done
  deriving DecidableEq,Fintype,Repr

/-- Actual bytecode: consume low prefix, clear leftovers, strip high zeros,
then reverse the remaining prefix onto the physical output stack. -/
def code : Label→Instruction Stack Label
  | .take => .pop .right .clearInput .read .read
  | .read => .pop .left .clearWidth (.save false) (.save true)
  | .save b => .push .scratch b .take
  | .clearInput => .pop .left .trim .clearInput .clearInput
  | .clearWidth => .pop .right .trim .clearWidth .clearWidth
  | .trim => .pop .scratch .done .trim .found
  | .found => .push .output true .move
  | .move => .pop .scratch .done (.copy false) (.copy true)
  | .copy b => .push .output b .move
  | .done => .halt

/-- Literal data-only state; width markers are supplied on the second stack. -/
def state (pc : Option Label) (flag : Option Bool) (word width scratch output : List Bool) : State Stack Label :=
  ⟨pc,flag,store word width scratch output⟩

/-- Actual fixed finite machine, with Boolean alphabet on ALL four stacks. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine Stack.left Stack.output Label.take code

/-- All alphabets are Boolean, beyond FinTM2's input-alphabet requirement. -/
theorem all_alphabets : ∀k,machine.Γ k=Bool := by intro k;rfl

/-- No unbounded numeric/word operand is hidden in the internal control. -/
theorem control_finite : Finite machine.σ := inferInstanceAs (Finite (Option Bool))

/-- Source iterations concatenate without an assumed cost contract. -/
theorem run_append (m n : ℕ) (a b c : State Stack Label)
    (hm:run code m a=some b) (hn:run code n b=some c) : run code (n+m) a=some c := by
  unfold run at hm hn ⊢
  rw [Function.iterate_add_apply,hm,hn]

/-- Two literal executed instructions compose. -/
theorem two_steps {a b c : State Stack Label} (h0:step code a=some b) (h1:step code b=some c) :
    run code 2 a=some c := by
  change (step code a).bind (step code)=some c
  rw [h0]
  exact h1

/-- Three literal executed instructions compose. -/
theorem three_steps {a b c d : State Stack Label}
    (h0:step code a=some b) (h1:step code b=some c) (h2:step code c=some d) : run code 3 a=some d := by
  change ((step code a).bind (step code)).bind (step code)=some d
  rw [h0]
  simp only [Option.bind_some]
  rw [h1]
  exact h2

/-- Each remaining input bit is actually consumed after the width is exhausted. -/
theorem clear_input_run (word acc out : List Bool) (flag : Option Bool) :
    run code (word.length+1) (state (some .clearInput) flag word [] acc out)=
      some (state (some .trim) none [] [] acc out) := by
  induction word generalizing flag with
  | nil =>
    simp only [List.length_nil,Nat.zero_add,run,Function.iterate_one,Option.bind_some,
      step,state,Option.map_some,code,execute,store,store_left,List.head?_nil,List.tail_nil,choose]
  | cons b word ih =>
    have hh:run code 1 (state (some .clearInput) flag (b::word) [] acc out)=
        some (state (some .clearInput) (some b) word [] acc out):=by
      cases b <;> simp only [run,Function.iterate_one,Option.bind_some,step,state,Option.map_some,
        code,execute,store,store_left,List.head?_cons,List.tail_cons,choose]
    have h:=run_append 1 (word.length+1) _ _ _ hh (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc] using h

/-- Every unused physical precision marker is also consumed after input EOF. -/
theorem clear_width_run (width acc out : List Bool) (flag : Option Bool) :
    run code (width.length+1) (state (some .clearWidth) flag [] width acc out)=
      some (state (some .trim) none [] [] acc out) := by
  induction width generalizing flag with
  | nil =>
    simp only [List.length_nil,Nat.zero_add,run,Function.iterate_one,Option.bind_some,
      step,state,Option.map_some,code,execute,store,store_right,List.head?_nil,List.tail_nil,choose]
  | cons b width ih =>
    have hh:run code 1 (state (some .clearWidth) flag [] (b::width) acc out)=
        some (state (some .clearWidth) (some b) [] width acc out):=by
      cases b <;> simp only [run,Function.iterate_one,Option.bind_some,step,state,Option.map_some,
        code,execute,store,store_right,List.head?_cons,List.tail_cons,choose]
    have h:=run_append 1 (width.length+1) _ _ _ hh (ih (some b))
    simpa only [List.length_cons,Nat.add_assoc] using h

end RiemannGaussian.SemiprimeD1StackReduce
