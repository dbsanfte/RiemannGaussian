/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAdder

/-! # Executed finite-stack adder refinement
The fixed program consumes both prepared Boolean operand stacks, constructs the
actual ripple sum, reverses its scratch cells and halts. No report or encoded
answer is used to infer machine time.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1StackAdderExecution
open SemiprimeD1StackBytecode SemiprimeD1StackAdder SemiprimeBitArithmetic

/-- Two actual transitions compose chronologically. -/
theorem two_steps {a b c : State Stack Label}
    (h0 : step code a=some b) (h1 : step code b=some c) : run code 2 a=some c := by
  change (step code a).bind (step code)=some c
  rw [h0]
  exact h1

/-- Three real bytecode transitions, without an operation-count assumption. -/
theorem three_steps {a b c d : State Stack Label}
    (h0 : step code a=some b) (h1 : step code b=some c) (h2 : step code c=some d) :
    run code 3 a=some d := by
  change ((step code a).bind (step code)).bind (step code)=some d
  rw [h0]
  simp only [Option.bind_some]
  rw [h1]
  exact h2

/-- Literal source iterations compose, preserving the exact intermediate store. -/
theorem run_append (m n : ℕ) (a b c : State Stack Label)
    (hm : run code m a=some b) (hn : run code n b=some c) :
    run code (n+m) a=some c := by
  unfold run at hm hn ⊢
  rw [Function.iterate_add_apply,hm,hn]

/-- An actual nonterminal emit writes one sum bit and finite carry flag. -/
theorem step_emit (c : Bool) (x y : Option Bool) (flag : Option Bool)
    (xs ys acc out : List Bool) (hne : x≠none ∨ y≠none) :
    step code (state (some (.emit c x y)) flag xs ys acc out)=
      some (state (some (.start (fullAdder (x.getD false) (y.getD false) c).2)) flag xs ys
        ((fullAdder (x.getD false) (y.getD false) c).1::acc) out) := by
  cases x with
  | none =>
    cases y with
    | none => simp only [ne_eq,not_true_eq_false,or_self] at hne
    | some y => simp only [step,state,Option.map_some,code,execute,store,store_scratch]
  | some x =>
    cases y <;> simp only [step,state,Option.map_some,code,execute,store,store_scratch]

/-- End-of-input handles the actual final carry before entering reversal. -/
theorem step_eof (c : Bool) (flag : Option Bool) (acc out : List Bool) :
    step code (state (some (.emit c none none)) flag [] [] acc out)=
      some (state (some .reverse) flag [] [] ((if c then [true] else [])++acc) out) := by
  cases c <;> simp only [step,state,Option.map_some,code,execute,store,store_scratch,
    Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.cons_append]

/-- One literal reversal pop consumes the selected scratch bit. -/
theorem step_reverse (b : Bool) (acc out : List Bool) (flag : Option Bool) :
    step code (state (some .reverse) flag [] [] (b::acc) out)=
      some (state (some (.output b)) (some b) [] [] acc out) := by
  cases b <;> simp only [step,state,Option.map_some,code,execute,store,store_scratch,
    List.head?_cons,List.tail_cons,choose]

/-- One actual output push restores the little-endian digit order. -/
theorem step_output (b : Bool) (acc out : List Bool) :
    step code (state (some (.output b)) (some b) [] [] acc out)=
      some (state (some .reverse) (some b) [] [] acc (b::out)) := by
  simp only [step,state,Option.map_some,code,execute,store,store_output]

/-- Empty scratch reaches the genuine halt label and resets the machine flag. -/
theorem reverse_empty (out : List Bool) (flag : Option Bool) :
    run code 2 (state (some .reverse) flag [] [] [] out)=
      some (state none none [] [] [] out) := by
  apply two_steps (b := state (some .done) none [] [] [] out)
  · simp only [step,state,Option.map_some,code,execute,store,store_scratch,
      List.head?_nil,List.tail_nil,choose]
  · rfl

/-- Actual reversal visits each constructed scratch cell and halts. -/
theorem reverse_run (acc out : List Bool) (flag : Option Bool) :
    run code (2*acc.length+2) (state (some .reverse) flag [] [] acc out)=
      some (state none none [] [] [] (acc.reverse++out)) := by
  induction acc generalizing out flag with
  | nil => simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.reverse_nil,List.nil_append] using reverse_empty out flag
  | cons b acc ih =>
    have hh:=two_steps (step_reverse b acc out flag) (step_output b acc out)
    have ht:=ih (b::out) (some b)
    have h:=run_append 2 (2*acc.length+2) _ _ _ hh ht
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,
      List.reverse_cons,List.append_assoc,List.singleton_append] using h

/-- The executed ripple loop consumes every original digit, including unequal
padding, and accumulates EXACT addBits output in reverse. -/
theorem ripple_run (xs ys : List Bool) (c : Bool) (flag : Option Bool) (acc out : List Bool) :
    run code (3*(max xs.length ys.length+1)) (state (some (.start c)) flag xs ys acc out)=
      some (state (some .reverse) none [] [] ((addBits xs ys c).bits.reverse++acc) out) := by
  induction xs generalizing ys c flag acc out with
  | nil =>
    induction ys generalizing c flag acc out with
    | nil =>
      have h:=three_steps (step_left c flag [] [] acc out)
        (step_right c none none [] [] acc out) (step_eof c none acc out)
      cases c <;> simpa only [addBits,List.length_nil,max_self,Nat.zero_add,Nat.mul_one,
        Bool.false_eq_true,ite_false,ite_true,List.reverse_nil,List.reverse_cons,List.nil_append,
        List.append_nil,List.cons_append] using h
    | cons y ys ih =>
      let d:=fullAdder false y c
      have h0:=three_steps (step_left c flag [] (y::ys) acc out)
        (step_right c none none [] (y::ys) acc out)
        (step_emit c none (some y) (some y) [] ys acc out (by simp))
      have ht:=ih d.2 (some y) (d.1::acc) out
      have h:=run_append 3 (3*(max (0:ℕ) ys.length+1)) _ _ _ h0 ht
      simpa only [d,addBits,List.length_nil,List.length_cons,Nat.zero_max,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,List.reverse_cons,List.append_assoc,List.singleton_append] using h
  | cons x xs ih =>
    cases ys with
    | nil =>
      let d:=fullAdder x false c
      have h0:=three_steps (step_left c flag (x::xs) [] acc out)
        (step_right c (some x) (some x) xs [] acc out)
        (step_emit c (some x) none none xs [] acc out (by simp))
      have ht:=ih [] d.2 none (d.1::acc) out
      have h:=run_append 3 (3*(max xs.length (0:ℕ)+1)) _ _ _ h0 ht
      simpa only [d,addBits,List.length_nil,List.length_cons,Nat.max_zero,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,List.reverse_cons,List.append_assoc,List.singleton_append] using h
    | cons y ys =>
      let d:=fullAdder x y c
      have h0:=three_steps (step_left c flag (x::xs) (y::ys) acc out)
        (step_right c (some x) (some x) xs (y::ys) acc out)
        (step_emit c (some x) (some y) (some y) xs ys acc out (by simp))
      have ht:=ih ys d.2 (some y) (d.1::acc) out
      have h:=run_append 3 (3*(max xs.length ys.length+1)) _ _ _ h0 ht
      simpa only [d,addBits,List.length_cons,max_add_add_right,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,List.reverse_cons,List.append_assoc,List.singleton_append] using h



/-- Exact complete executed trace from two prepared operands to only the sum. -/
theorem source_run (xs ys : List Bool) (c : Bool) :
    run code (3*(max xs.length ys.length+1)+2*(addBits xs ys c).bits.length+2)
      (state (some (.start c)) none xs ys [] [])=
      some (state none none [] [] [] (addBits xs ys c).bits) := by
  have hr:=ripple_run xs ys c none [] []
  simp only [List.append_nil] at hr
  have hv:=reverse_run (addBits xs ys c).bits.reverse [] none
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hv
  have h:=run_append (3*(max xs.length ys.length+1)) (2*(addBits xs ys c).bits.length+2) _ _ _ hr hv
  have ht : (2*(addBits xs ys c).bits.length+2)+3*(max xs.length ys.length+1)=
      3*(max xs.length ys.length+1)+2*(addBits xs ys c).bits.length+2 := by omega
  simpa only [ht] using h

/-- Prepared operands alone determine an actual source execution certificate.
The bound is derived from the executed trace and exact addBits output length. -/
def sourceAdd (xs ys : List Bool) (c : Bool) :
    StateTransition.EvalsToInTime (step code) (state (some (.start c)) none xs ys [] [])
      (some (state none none [] [] [] (addBits xs ys c).bits)) (5*(xs.length+ys.length)+7) := by
  refine ⟨⟨3*(max xs.length ys.length+1)+2*(addBits xs ys c).bits.length+2,source_run xs ys c⟩,?_⟩
  change 3*(max xs.length ys.length+1)+2*(addBits xs ys c).bits.length+2 ≤ 5*(xs.length+ys.length)+7
  have hlen:=(addBits_counts xs ys c).2.2.2.2
  have hm : max xs.length ys.length ≤ xs.length+ys.length := max_le (by omega) (by omega)
  omega

/-- All operands and scratch are genuinely empty in the final configuration. -/
theorem finish_eq_final (bits : List Bool) :
    state none none [] [] [] bits=(final Stack.output bits : State Stack Label) := by
  change (⟨none,none,store [] [] [] bits⟩ : State Stack Label)=
    ⟨none,none,fun k => if k=Stack.output then bits else []⟩
  congr 1
  funext k
  cases k <;> rfl

/-- The actual cleared source store is the target machine's halt configuration. -/
theorem finish_configuration (c : Bool) (bits : List Bool) :
    configuration (state none none [] [] [] bits)=Turing.haltList (machine c) bits := by
  rw [finish_eq_final]
  exact final_correct Stack.left Stack.output (.start c) code bits

/-- The actual compiled fixed finite machine computes exactly frozen addBits
from TWO prepared stacks, in a proved linear transition bound. There is no
second-operand or output advice; caller/parser preparation is a separate trace. -/
def machineAdd (xs ys : List Bool) (c : Bool) :
    StateTransition.EvalsToInTime (machine c).step
      (configuration (state (some (.start c)) none xs ys [] []))
      (some (Turing.haltList (machine c) (addBits xs ys c).bits))
      (5*(xs.length+ys.length)+7) := by
  have h:=evalsCorrect Stack.left Stack.output (.start c) code _ _ _ (sourceAdd xs ys c)
  change StateTransition.EvalsToInTime (machine c).step
    (configuration (state (some (.start c)) none xs ys [] []))
    (some (configuration (state none none [] [] [] (addBits xs ys c).bits)))
    (5*(xs.length+ys.length)+7) at h
  exact Eq.mp (congrArg (fun finish : (machine c).Cfg =>
    StateTransition.EvalsToInTime (machine c).step
      (configuration (state (some (.start c)) none xs ys [] [])) (some finish)
      (5*(xs.length+ys.length)+7)) (finish_configuration c (addBits xs ys c).bits)) h

/-- The finite control table has exactly30 labels before any input is chosen. -/
theorem label_count : Fintype.card Label=30 := by decide

end RiemannGaussian.SemiprimeD1StackAdderExecution
