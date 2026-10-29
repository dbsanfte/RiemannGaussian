/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSubtractor

/-! # Executed finite-stack subtraction with an actual borrow output bit
The fixed compiled machine consumes both prepared operand words and returns
exactly finalBorrow::differenceBits. No desired borrow, output or time is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1StackSubtractorExecution
open SemiprimeD1StackBytecode SemiprimeD1StackSubtractor SemiprimeBitDivision
open SemiprimeD1StackAdder (Stack store store_left store_right store_scratch store_output)

/-- Two actual source transitions compose chronologically. -/
theorem two_steps {a b c : State Stack Label}
    (h0 : step code a=some b) (h1 : step code b=some c) : run code 2 a=some c := by
  change (step code a).bind (step code)=some c
  rw [h0]
  exact h1

/-- Three actual bytecode transitions, with no assumed instruction cost. -/
theorem three_steps {a b c d : State Stack Label}
    (h0 : step code a=some b) (h1 : step code b=some c) (h2 : step code c=some d) :
    run code 3 a=some d := by
  change ((step code a).bind (step code)).bind (step code)=some d
  rw [h0]
  simp only [Option.bind_some]
  rw [h1]
  exact h2

/-- Literal source iterations preserve the exact intermediate physical store. -/
theorem run_append (m n : ℕ) (a b c : State Stack Label)
    (hm : run code m a=some b) (hn : run code n b=some c) :
    run code (n+m) a=some c := by
  unfold run at hm hn ⊢
  rw [Function.iterate_add_apply,hm,hn]

/-- Each nonterminal emit physically writes the low difference bit and next borrow. -/
theorem step_emit (b : Bool) (x y : Option Bool) (flag : Option Bool)
    (xs ys acc out : List Bool) (hne : x≠none ∨ y≠none) :
    step code (state (some (.emit b x y)) flag xs ys acc out)=
      some (state (some (.start (fullSubtractor (x.getD false) (y.getD false) b).2)) flag xs ys
        ((fullSubtractor (x.getD false) (y.getD false) b).1::acc) out) := by
  cases x with
  | none =>
    cases y with
    | none => simp only [ne_eq,not_true_eq_false,or_self] at hne
    | some y => simp only [step,state,Option.map_some,code,execute,store,store_scratch]
  | some x =>
    cases y <;> simp only [step,state,Option.map_some,code,execute,store,store_scratch]

/-- EOF retains the actual borrow in a finite label; it emits no difference digit. -/
theorem step_eof (b : Bool) (flag : Option Bool) (acc out : List Bool) :
    step code (state (some (.emit b none none)) flag [] [] acc out)=
      some (state (some (.reverse b)) flag [] [] acc out) := rfl

/-- A reversal pop consumes one actual scratch bit. -/
theorem step_reverse (borrow bit : Bool) (acc out : List Bool) (flag : Option Bool) :
    step code (state (some (.reverse borrow)) flag [] [] (bit::acc) out)=
      some (state (some (.output borrow bit)) (some bit) [] [] acc out) := by
  cases bit <;> simp only [step,state,Option.map_some,code,execute,store,store_scratch,
    List.head?_cons,List.tail_cons,choose]

/-- A reversal push restores one actual little-endian difference bit. -/
theorem step_output (borrow bit : Bool) (acc out : List Bool) :
    step code (state (some (.output borrow bit)) (some bit) [] [] acc out)=
      some (state (some (.reverse borrow)) (some bit) [] [] acc (bit::out)) := by
  simp only [step,state,Option.map_some,code,execute,store,store_output]

/-- Empty scratch physically pushes the final borrow prefix, then genuinely halts. -/
theorem reverse_empty (borrow : Bool) (out : List Bool) (flag : Option Bool) :
    run code 3 (state (some (.reverse borrow)) flag [] [] [] out)=
      some (state none none [] [] [] (borrow::out)) := by
  apply three_steps (b := state (some (.borrow borrow)) none [] [] [] out)
    (c := state (some .done) none [] [] [] (borrow::out))
  · simp only [step,state,Option.map_some,code,execute,store,store_scratch,
      List.head?_nil,List.tail_nil,choose]
  · simp only [step,state,Option.map_some,code,execute,store,store_output]
  · rfl

/-- Actual reverse/output/borrow-prefix execution visits every scratch cell once. -/
theorem reverse_run (borrow : Bool) (acc out : List Bool) (flag : Option Bool) :
    run code (2*acc.length+3) (state (some (.reverse borrow)) flag [] [] acc out)=
      some (state none none [] [] [] (borrow::(acc.reverse++out))) := by
  induction acc generalizing out flag with
  | nil => simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.reverse_nil,List.nil_append] using reverse_empty borrow out flag
  | cons bit acc ih =>
    have hh:=two_steps (step_reverse borrow bit acc out flag) (step_output borrow bit acc out)
    have ht:=ih (bit::out) (some bit)
    have h:=run_append 2 (2*acc.length+3) _ _ _ hh ht
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,
      List.reverse_cons,List.append_assoc,List.singleton_append] using h

/-- Every original subtraction digit executes three transitions, including
unequal padding and initial borrow. The terminal label carries EXACT final borrow. -/
theorem ripple_run (xs ys : List Bool) (b : Bool) (flag : Option Bool) (acc out : List Bool) :
    run code (3*(max xs.length ys.length+1)) (state (some (.start b)) flag xs ys acc out)=
      some (state (some (.reverse (subBits xs ys b).borrow)) none [] []
        ((subBits xs ys b).result.bits.reverse++acc) out) := by
  induction xs generalizing ys b flag acc out with
  | nil =>
    induction ys generalizing b flag acc out with
    | nil =>
      have h:=three_steps (step_left b flag [] [] acc out)
        (step_right b none none [] [] acc out) (step_eof b none acc out)
      simpa only [subBits,List.length_nil,max_self,Nat.zero_add,Nat.mul_one,
        List.reverse_nil,List.nil_append] using h
    | cons y ys ih =>
      let d:=fullSubtractor false y b
      have h0:=three_steps (step_left b flag [] (y::ys) acc out)
        (step_right b none none [] (y::ys) acc out)
        (step_emit b none (some y) (some y) [] ys acc out (by simp))
      have ht:=ih d.2 (some y) (d.1::acc) out
      have h:=run_append 3 (3*(max (0:ℕ) ys.length+1)) _ _ _ h0 ht
      simpa only [d,subBits,List.length_nil,List.length_cons,Nat.zero_max,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,List.reverse_cons,List.append_assoc,List.singleton_append] using h
  | cons x xs ih =>
    cases ys with
    | nil =>
      let d:=fullSubtractor x false b
      have h0:=three_steps (step_left b flag (x::xs) [] acc out)
        (step_right b (some x) (some x) xs [] acc out)
        (step_emit b (some x) none none xs [] acc out (by simp))
      have ht:=ih [] d.2 none (d.1::acc) out
      have h:=run_append 3 (3*(max xs.length (0:ℕ)+1)) _ _ _ h0 ht
      simpa only [d,subBits,List.length_nil,List.length_cons,Nat.max_zero,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,List.reverse_cons,List.append_assoc,List.singleton_append] using h
    | cons y ys =>
      let d:=fullSubtractor x y b
      have h0:=three_steps (step_left b flag (x::xs) (y::ys) acc out)
        (step_right b (some x) (some x) xs (y::ys) acc out)
        (step_emit b (some x) (some y) (some y) xs ys acc out (by simp))
      have ht:=ih ys d.2 (some y) (d.1::acc) out
      have h:=run_append 3 (3*(max xs.length ys.length+1)) _ _ _ h0 ht
      simpa only [d,subBits,List.length_cons,max_add_add_right,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,List.reverse_cons,List.append_assoc,List.singleton_append] using h

/-- Complete actual source trace returns borrow::difference bits and no other payload. -/
theorem source_run (xs ys : List Bool) (b : Bool) :
    run code (3*(max xs.length ys.length+1)+2*(subBits xs ys b).result.bits.length+3)
      (state (some (.start b)) none xs ys [] [])=
      some (state none none [] [] [] ((subBits xs ys b).borrow::(subBits xs ys b).result.bits)) := by
  have hr:=ripple_run xs ys b none [] []
  simp only [List.append_nil] at hr
  have hv:=reverse_run (subBits xs ys b).borrow (subBits xs ys b).result.bits.reverse [] none
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hv
  have h:=run_append (3*(max xs.length ys.length+1)) (2*(subBits xs ys b).result.bits.length+3) _ _ _ hr hv
  have ht : (2*(subBits xs ys b).result.bits.length+3)+3*(max xs.length ys.length+1)=
      3*(max xs.length ys.length+1)+2*(subBits xs ys b).result.bits.length+3 := by omega
  simpa only [ht] using h

/-- Input words alone determine the actual source transition certificate. -/
def sourceSubtract (xs ys : List Bool) (b : Bool) :
    StateTransition.EvalsToInTime (step code) (state (some (.start b)) none xs ys [] [])
      (some (state none none [] [] [] ((subBits xs ys b).borrow::(subBits xs ys b).result.bits)))
      (5*(xs.length+ys.length)+8) := by
  refine ⟨⟨3*(max xs.length ys.length+1)+2*(subBits xs ys b).result.bits.length+3,source_run xs ys b⟩,?_⟩
  change 3*(max xs.length ys.length+1)+2*(subBits xs ys b).result.bits.length+3 ≤ 5*(xs.length+ys.length)+8
  have hlen:=(subBits_counts xs ys b).2.2.2.2
  have hm : max xs.length ys.length ≤ xs.length+ys.length := max_le (by omega) (by omega)
  omega

/-- The actual final store has only the encoded borrow and difference output. -/
theorem finish_eq_final (bits : List Bool) :
    state none none [] [] [] bits=(final Stack.output bits : State Stack Label) := by
  change (⟨none,none,store [] [] [] bits⟩ : State Stack Label)=
    ⟨none,none,fun k => if k=Stack.output then bits else []⟩
  congr 1
  funext k
  cases k <;> rfl

/-- Concrete source halt and actual compiled-machine halt encodings agree. -/
theorem finish_configuration (b : Bool) (bits : List Bool) :
    configuration (state none none [] [] [] bits)=Turing.haltList (machine b) bits := by
  rw [finish_eq_final]
  exact final_correct Stack.left Stack.output (.start b) code bits

/-- The actual fixed finite machine computes exact frozen subtraction, including
underflow and arbitrary borrow. The final borrow is a physical output-prefix bit. -/
def machineSubtract (xs ys : List Bool) (b : Bool) :
    StateTransition.EvalsToInTime (machine b).step
      (configuration (state (some (.start b)) none xs ys [] []))
      (some (Turing.haltList (machine b) ((subBits xs ys b).borrow::(subBits xs ys b).result.bits)))
      (5*(xs.length+ys.length)+8) := by
  have h:=evalsCorrect Stack.left Stack.output (.start b) code _ _ _ (sourceSubtract xs ys b)
  change StateTransition.EvalsToInTime (machine b).step
    (configuration (state (some (.start b)) none xs ys [] []))
    (some (configuration (state none none [] [] [] ((subBits xs ys b).borrow::(subBits xs ys b).result.bits))))
    (5*(xs.length+ys.length)+8) at h
  exact Eq.mp (congrArg (fun finish : (machine b).Cfg =>
    StateTransition.EvalsToInTime (machine b).step
      (configuration (state (some (.start b)) none xs ys [] [])) (some finish)
      (5*(xs.length+ys.length)+8))
      (finish_configuration b ((subBits xs ys b).borrow::(subBits xs ys b).result.bits))) h

end RiemannGaussian.SemiprimeD1StackSubtractorExecution
