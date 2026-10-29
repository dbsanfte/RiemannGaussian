/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackReduce
import RiemannGaussian.SemiprimeSourceCompactWordIds
import RiemannGaussian.SemiprimeD1StackBytecodeBounds

/-! # Actual finite-machine canonical modular reduction
The precision is the length of the physically supplied counter stack. This
proves actual executions, including consuming unused bits/markers, rather than
identifying an existing arithmetic report with machine time.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackReduceExecution
open SemiprimeD1StackBytecode SemiprimeD1StackReduce
open SemiprimeD1StackAdder (Stack store store_left store_right store_scratch store_output)
open SemiprimeBitArithmetic SemiprimeSourceCompactBits

/-- Actual prefix acquisition/cleanup time, including both EOF cases. -/
def prefixTime (xs width : List Bool) : ℕ := xs.length+width.length+min xs.length width.length+2

/-- The width counter is read by a real pop, regardless of marker value. -/
theorem step_take (b : Bool) (xs ws acc out : List Bool) (flag : Option Bool) :
    step code (state (some .take) flag xs (b::ws) acc out)=
      some (state (some .read) (some b) xs ws acc out) := by
  cases b <;> simp only [step,state,Option.map_some,code,execute,store,store_right,
    List.head?_cons,List.tail_cons,choose]

/-- An actual low input bit is read, including its zero value. -/
theorem step_read (b : Bool) (xs ws acc out : List Bool) (flag : Option Bool) :
    step code (state (some .read) flag (b::xs) ws acc out)=
      some (state (some (.save b)) (some b) xs ws acc out) := by
  cases b <;> simp only [step,state,Option.map_some,code,execute,store,store_left,
    List.head?_cons,List.tail_cons,choose]

/-- A copied low digit is physically allocated in reverse scratch order. -/
theorem step_save (b : Bool) (xs ws acc out : List Bool) (flag : Option Bool) :
    step code (state (some (.save b)) flag xs ws acc out)=
      some (state (some .take) flag xs ws (b::acc) out) := by
  simp only [step,state,Option.map_some,code,execute,store,store_scratch]

/-- Width EOF really enters the input-clearing loop. -/
theorem step_width_eof (xs acc out : List Bool) (flag : Option Bool) :
    step code (state (some .take) flag xs [] acc out)=
      some (state (some .clearInput) none xs [] acc out) := by
  simp only [step,state,Option.map_some,code,execute,store,store_right,List.head?_nil,List.tail_nil,choose]

/-- Input EOF really enters the counter-clearing loop. -/
theorem step_input_eof (ws acc out : List Bool) (flag : Option Bool) :
    step code (state (some .read) flag [] ws acc out)=
      some (state (some .clearWidth) none [] ws acc out) := by
  simp only [step,state,Option.map_some,code,execute,store,store_left,List.head?_nil,List.tail_nil,choose]

/-- Exact physical low-prefix trace, with ALL unused input/counter cells consumed. -/
theorem prefix_run (xs width acc out : List Bool) (flag : Option Bool) :
    run code (prefixTime xs width) (state (some .take) flag xs width acc out)=
      some (state (some .trim) none [] [] ((xs.take width.length).reverse++acc) out) := by
  induction xs generalizing width acc flag with
  | nil =>
    cases width with
    | nil =>
      have hh:run code 1 (state (some .take) flag [] [] acc out)=
          some (state (some .clearInput) none [] [] acc out):=step_width_eof [] acc out flag
      have h:=run_append 1 1 _ _ _ hh (clear_input_run [] acc out none)
      simpa only [prefixTime,List.length_nil,Nat.min_self,Nat.zero_add,List.take_nil,List.reverse_nil,
        List.nil_append] using h
    | cons b ws =>
      have hh:=two_steps (step_take b [] ws acc out flag) (step_input_eof ws acc out (some b))
      have h:=run_append 2 (ws.length+1) _ _ _ hh (clear_width_run ws acc out none)
      simpa only [prefixTime,List.length_nil,List.length_cons,Nat.zero_add,Nat.zero_min,List.take_nil,
        List.reverse_nil,List.nil_append,Nat.add_assoc] using h
  | cons x xs ih =>
    cases width with
    | nil =>
      have hh:run code 1 (state (some .take) flag (x::xs) [] acc out)=
          some (state (some .clearInput) none (x::xs) [] acc out):=step_width_eof _ acc out flag
      have h:=run_append 1 ((x::xs).length+1) _ _ _ hh (clear_input_run (x::xs) acc out none)
      simpa only [prefixTime,List.length_nil,Nat.add_zero,Nat.min_zero,List.take_zero,List.reverse_nil,
        List.nil_append,Nat.add_assoc] using h
    | cons b ws =>
      have hh:=three_steps (step_take b (x::xs) ws acc out flag)
        (step_read x xs ws acc out (some b)) (step_save x xs ws acc out (some x))
      have ht:=ih ws (x::acc) (some x)
      have h:=run_append 3 (prefixTime xs ws) _ _ _ hh ht
      have he:prefixTime (x::xs) (b::ws)=prefixTime xs ws+3:=by
        unfold prefixTime
        simp only [List.length_cons]
        omega
      simpa only [he,List.length_cons,List.take_succ_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

/-- Proof-side description of stripping zeros from a reversed word. -/
def trimReverse : List Bool→List Bool
  | [] => []
  | false::xs => trimReverse xs
  | true::xs => (true::xs).reverse

/-- Exact trace length of the finite trim/reverse phase. -/
def trimTime : List Bool→ℕ
  | [] => 2
  | false::xs => trimTime xs+1
  | true::xs => 2*xs.length+4

/-- One actual reverse-loop pop. -/
theorem step_move (b : Bool) (xs out : List Bool) (flag : Option Bool) :
    step code (state (some .move) flag [] [] (b::xs) out)=
      some (state (some (.copy b)) (some b) [] [] xs out) := by
  cases b <;> simp only [step,state,Option.map_some,code,execute,store,store_scratch,
    List.head?_cons,List.tail_cons,choose]

/-- One actual reverse-loop output push. -/
theorem step_copy (b : Bool) (xs out : List Bool) :
    step code (state (some (.copy b)) (some b) [] [] xs out)=
      some (state (some .move) (some b) [] [] xs (b::out)) := by
  simp only [step,state,Option.map_some,code,execute,store,store_output]

/-- Literal moving/reversal loop with its genuine final halt. -/
theorem move_run (xs out : List Bool) (flag : Option Bool) :
    run code (2*xs.length+2) (state (some .move) flag [] [] xs out)=
      some (state none none [] [] [] (xs.reverse++out)) := by
  induction xs generalizing out flag with
  | nil =>
    apply two_steps (b:=state (some .done) none [] [] [] out)
    · simp only [step,state,Option.map_some,code,execute,store,store_scratch,
        List.head?_nil,List.tail_nil,choose]
    · rfl
  | cons b xs ih =>
    have hh:=two_steps (step_move b xs out flag) (step_copy b xs out)
    have h:=run_append 2 (2*xs.length+2) _ _ _ hh (ih (b::out) (some b))
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,
      List.reverse_cons,List.append_assoc,List.singleton_append] using h

/-- High-zero stripping and all retained-byte reversal execute literally. -/
theorem trim_run (xs out : List Bool) (flag : Option Bool) :
    run code (trimTime xs) (state (some .trim) flag [] [] xs out)=
      some (state none none [] [] [] (trimReverse xs++out)) := by
  induction xs generalizing out flag with
  | nil =>
    apply two_steps (b:=state (some .done) none [] [] [] out)
    · simp only [step,state,Option.map_some,code,execute,store,store_scratch,
        List.head?_nil,List.tail_nil,choose]
    · rfl
  | cons b xs ih =>
    cases b with
    | false =>
      have hh:run code 1 (state (some .trim) flag [] [] (false::xs) out)=
          some (state (some .trim) (some false) [] [] xs out):=by
        simp only [run,Function.iterate_one,Option.bind_some,step,state,Option.map_some,code,execute,
          store,store_scratch,List.head?_cons,List.tail_cons,choose]
      exact run_append 1 (trimTime xs) _ _ _ hh (ih out (some false))
    | true =>
      have hh:run code 2 (state (some .trim) flag [] [] (true::xs) out)=
          some (state (some .move) (some true) [] [] xs (true::out)):=by
        apply two_steps (b:=state (some .found) (some true) [] [] xs out)
        · simp only [step,state,Option.map_some,code,execute,store,store_scratch,
            List.head?_cons,List.tail_cons,choose]
        · simp only [step,state,Option.map_some,code,execute,store,store_output]
      have h:=run_append 2 (2*xs.length+2) _ _ _ hh (move_run xs (true::out) (some true))
      simpa only [trimTime,trimReverse,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc] using h

/-- All trim/copy instructions cost at most twice the supplied scratch width. -/
theorem trimTime_le (xs : List Bool) : trimTime xs ≤ 2*xs.length+2 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp only [trimTime,List.length_cons] <;> omega

/-- Appending a literal high zero changes no numerical payload. -/
theorem bitValue_append_false (xs : List Bool) : bitValue (xs++[false])=bitValue xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.cons_append,bitValue,ih]

/-- Reverse stripping preserves the represented original low word. -/
theorem trimReverse_value (xs : List Bool) : bitValue (trimReverse xs)=bitValue xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => simpa only [trimReverse,List.reverse_cons,bitValue_append_false] using ih
    | true => rfl

/-- Any word ending in a true high bit is canonical, regardless of its low bits. -/
theorem compact_append_true (xs : List Bool) : Compact (xs++[true]) := by
  induction xs with
  | nil => simp only [List.nil_append,Compact,implies_true,and_self]
  | cons b xs ih =>
    change Compact (xs++[true]) ∧ (xs++[true]=[]→b=true)
    exact ⟨ih,by simp⟩

/-- Every actual reverse-strip result is compact. -/
theorem trimReverse_compact (xs : List Bool) : Compact (trimReverse xs) := by
  induction xs with
  | nil => trivial
  | cons b xs ih =>
    cases b with
    | false => exact ih
    | true => simpa only [trimReverse,List.reverse_cons] using compact_append_true xs.reverse

/-- Physical result agrees literally with the old low-prefix modular reducer. -/
theorem trimReverse_reduce (word width : List Bool) :
    trimReverse (word.take width.length).reverse=(SemiprimeD1JetScalarBits.reduce width.length word).bits := by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _
    (trimReverse_compact _) (SemiprimeD1JetScalarBits.reduce_compact _ _)
  rw [trimReverse_value,List.reverse_reverse,SemiprimeD1JetScalarBits.bitValue_take,
    SemiprimeD1JetScalarBits.reduce_value]

/-- Full exact source trace, with BOTH inputs/scratch consumed. -/
theorem source_run (word width : List Bool) :
    run code (trimTime (word.take width.length).reverse+prefixTime word width)
      (state (some .take) none word width [] [])=
      some (state none none [] [] [] (SemiprimeD1JetScalarBits.reduce width.length word).bits) := by
  have hp:=prefix_run word width [] [] none
  simp only [List.append_nil] at hp
  have ht:=trim_run (word.take width.length).reverse [] none
  simp only [List.append_nil,trimReverse_reduce] at ht
  exact run_append _ _ _ _ _ hp ht

/-- Actual source-time certificate, not an assumed bound on a retained report. -/
def sourceReduce (word width : List Bool) :
    StateTransition.EvalsToInTime (step code) (state (some .take) none word width [] [])
      (some (state none none [] [] [] (SemiprimeD1JetScalarBits.reduce width.length word).bits))
      (5*(word.length+width.length)+10) := by
  refine ⟨⟨_,source_run word width⟩,?_⟩
  change trimTime (word.take width.length).reverse+prefixTime word width ≤ _
  have ht:=trimTime_le (word.take width.length).reverse
  have hl: (word.take width.length).length ≤ word.length:=List.length_take_le' _ _
  simp only [List.length_reverse] at ht
  unfold prefixTime
  omega

/-- All physical operands are empty at the actual target halt. -/
theorem finish_configuration (bits : List Bool) :
    configuration (state none none [] [] [] bits)=Turing.haltList machine bits := by
  have hs:state none none [] [] [] bits=(final Stack.output bits:State Stack Label):=by
    change (⟨none,none,store [] [] [] bits⟩:State Stack Label)=
      ⟨none,none,fun k=>if k=Stack.output then bits else []⟩
    congr 1
    funext k
    cases k <;> rfl
  rw [hs]
  exact final_correct Stack.left Stack.output Label.take code bits

/-- The actual fixed finite machine returns exactly the scalar reducer's bytes
in linear word/counter length. Width-counter preparation is a caller operation. -/
def machineReduce (word width : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (configuration (state (some .take) none word width [] []))
      (some (Turing.haltList machine (SemiprimeD1JetScalarBits.reduce width.length word).bits))
      (5*(word.length+width.length)+10) := by
  have h:=evalsCorrect Stack.left Stack.output Label.take code _ _ _ (sourceReduce word width)
  change StateTransition.EvalsToInTime machine.step
    (configuration (state (some .take) none word width [] []))
    (some (configuration (state none none [] [] [] (SemiprimeD1JetScalarBits.reduce width.length word).bits)))
    (5*(word.length+width.length)+10) at h
  exact Eq.mp (congrArg (fun finish:machine.Cfg=>StateTransition.EvalsToInTime machine.step
    (configuration (state (some .take) none word width [] [])) (some finish)
      (5*(word.length+width.length)+10)) (finish_configuration _)) h

/-- Every successful prefix is bounded by the actual proved halt, rather than
by a supplied execution-fuel promise. -/
theorem prefix_fuel_le (word width : List Bool) (fuel : ℕ) (out : State Stack Label)
    (h : run code fuel (state (some .take) none word width [] [])=some out) :
    fuel ≤ 5*(word.length+width.length)+10 := by
  have hf := SemiprimeD1StackBytecodeBounds.fuel_le_halt code _ _ out _ fuel
    (source_run word width) rfl h
  have ht : trimTime (word.take width.length).reverse+prefixTime word width ≤
      5*(word.length+width.length)+10 := (sourceReduce word width).steps_le_m
  exact hf.trans ht

/-- The initial physical store has exactly the supplied input/counter cells. -/
theorem initial_cells (word width : List Bool) :
    SemiprimeD1StackBytecodeBounds.cells (state (some .take) none word width [] [])=
      word.length+width.length := by
  change word.length+(width.length+(0+(0+0)))=word.length+width.length
  omega

/-- All actual source prefixes have linear physical storage. -/
theorem prefix_cells (word width : List Bool) (fuel : ℕ) (out : State Stack Label)
    (h : run code fuel (state (some .take) none word width [] [])=some out) :
    SemiprimeD1StackBytecodeBounds.cells out ≤ 21*(word.length+width.length)+40 := by
  have hs := SemiprimeD1StackBytecodeBounds.run_cells code fuel _ out h
  have hf := prefix_fuel_le word width fuel out h
  have hk : Fintype.card Stack=4 := by decide
  rw [initial_cells,hk] at hs
  omega

/-- The same bound counts cells on every stack of the actual compiled machine. -/
theorem machine_prefix_cells (word width : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (h : (fun c=>c.bind machine.step)^[fuel]
      (some (configuration (state (some .take) none word width [] [])))=some cfg) :
    (∑k : Stack,(cfg.stk k).length) ≤ 21*(word.length+width.length)+40 := by
  have hh := run_correct Stack.left Stack.output Label.take code fuel
    (state (some .take) none word width [] [])
  change (run code fuel (state (some .take) none word width [] [])).map configuration=
    (fun c=>c.bind machine.step)^[fuel]
      (some (configuration (state (some .take) none word width [] []))) at hh
  rw [h] at hh
  cases hr : run code fuel (state (some .take) none word width [] []) with
  | none => rw [hr] at hh;cases hh
  | some out =>
    rw [hr] at hh
    have he : configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells word width fuel out hr

end RiemannGaussian.SemiprimeD1StackReduceExecution
