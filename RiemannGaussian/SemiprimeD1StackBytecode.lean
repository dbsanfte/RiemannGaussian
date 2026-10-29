/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Computability.TuringMachine.Computable

/-! # Finite Boolean-stack bytecode and an actual TM2 compiler
Only literal push/pop/peek/jump/halt instructions exist. All unbounded data are
Boolean stack payloads; control is a finite label and one optional Boolean.
There is no native-number register or arbitrary source-function opcode.
This compiler core does not assert translation of the whole WordTape program.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackBytecode

/-- First-order instructions with only literal finite stack/label operands. -/
inductive Instruction (K L : Type) where
  /-- Push one literal bit and continue at a literal label. -/
  | push (stack : K) (bit : Bool) (next : L)
  /-- Pop one bit, branching on EOF/false/true. -/
  | pop (stack : K) (empty low high : L)
  /-- Inspect one bit without removing it, branching on EOF/false/true. -/
  | peek (stack : K) (empty low high : L)
  /-- Continue at a literal finite label. -/
  | jump (next : L)
  /-- Halt, resetting the finite flag. -/
  | halt
  deriving Repr

/-- Executable source configuration; all unbounded objects are on Boolean store. -/
structure State (K L : Type) where
  /-- Finite current label; none means halted. -/
  pc : Option L
  /-- Finite last inspected bit, including EOF. -/
  flag : Option Bool
  /-- Complete literal finite-stack payload. -/
  store : K→List Bool

/-- Literal three-way dispatch has no native numeric or function-valued operand. -/
def choose {L : Type} (empty low high : L) : Option Bool→L
  | none => empty
  | some false => low
  | some true => high

/-- Execute exactly one bytecode instruction. -/
def execute {K L : Type} [DecidableEq K] (instruction : Instruction K L) (state : State K L) : State K L :=
  match instruction with
  | .push k b next => ⟨some next,state.flag,Function.update state.store k (b::state.store k)⟩
  | .pop k empty low high =>
    let bit:=(state.store k).head?
    ⟨some (choose empty low high bit),bit,Function.update state.store k (state.store k).tail⟩
  | .peek k empty low high =>
    let bit:=(state.store k).head?
    ⟨some (choose empty low high bit),bit,state.store⟩
  | .jump next => ⟨some next,state.flag,state.store⟩
  | .halt => ⟨none,none,state.store⟩

/-- Actual small-step source execution; no semantic result is supplied. -/
def step {K L : Type} [DecidableEq K] (code : L→Instruction K L) (state : State K L) : Option (State K L) :=
  state.pc.map (fun label=>execute (code label) state)

/-- Execute a literal number of source transitions, preserving genuine early halt. -/
def run {K L : Type} [DecidableEq K] (code : L→Instruction K L) (fuel : ℕ)
    (state : State K L) : Option (State K L) :=
  (fun state=>state.bind (step code))^[fuel] (some state)

/-- Fixed finite Boolean dispatch statement for an already inspected bit. -/
def dispatch {K L : Type} (empty low high : L) : Turing.TM2.Stmt (fun _ : K=>Bool) L (Option Bool) :=
  .branch Option.isNone (.goto (fun _=>empty))
    (.branch (fun bit=>bit.getD false) (.goto (fun _=>high)) (.goto (fun _=>low)))

/-- Compile literal bytecode into an actual finite TM2 statement. -/
def compileInstruction {K L : Type} : Instruction K L→Turing.TM2.Stmt (fun _ : K=>Bool) L (Option Bool)
  | .push k b next => .push k (fun _=>b) (.goto (fun _=>next))
  | .pop k empty low high => .pop k (fun _ bit=>bit) (dispatch empty low high)
  | .peek k empty low high => .peek k (fun _ bit=>bit) (dispatch empty low high)
  | .jump next => .goto (fun _=>next)
  | .halt => .load (fun _=>none) .halt

/-- The actual machine has finite store/labels/flags and Boolean alphabet on EVERY stack.
Code is fixed before the machine's input, never acquired from a count/solver answer. -/
def machine {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) : Turing.FinTM2 where
  K:=K
  k₀:=input
  k₁:=output
  Γ _:=Bool
  Λ:=L
  main:=main
  σ:=Option Bool
  initialState:=none
  m label:=compileInstruction (code label)

/-- Literal source state interpreted as the actual target machine configuration. -/
def configuration {K L : Type} (state : State K L) :
    Turing.TM2.Cfg (fun _ : K=>Bool) L (Option Bool) :=
  ⟨state.pc,state.flag,state.store⟩

/-- Every stack alphabet, beyond FinTM2's required input alphabet, is finite. -/
theorem all_alphabets_bool {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) :
    ∀k,(machine input output main code).Γ k=Bool := by intro k;rfl

/-- ALL target stack alphabets are finite, rather than only the input alphabet. -/
theorem all_alphabets_finite {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) :
    ∀k,Finite ((machine input output main code).Γ k) := by
  intro k
  exact inferInstanceAs (Finite Bool)

/-- Internal target control is finite and contains no native Nat/List data. -/
theorem control_finite {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) :
    Finite (machine input output main code).σ :=
  inferInstanceAs (Finite (Option Bool))

/-- Dispatch is a fixed finite truth table, not an arbitrary native branch callback. -/
theorem dispatch_correct {K L : Type} [DecidableEq K] (empty low high : L)
    (flag : Option Bool) (store : K→List Bool) :
    Turing.TM2.stepAux (dispatch empty low high) flag store=
      ⟨some (choose empty low high flag),flag,store⟩ := by
  cases flag with
  | none => rfl
  | some bit => cases bit <;> rfl

/-- Each source instruction executes as exactly one genuine TM2 transition. -/
theorem instruction_correct {K L : Type} [DecidableEq K]
    (instruction : Instruction K L) (state : State K L) :
    Turing.TM2.stepAux (compileInstruction instruction) state.flag state.store=
      configuration (execute instruction state) := by
  cases instruction with
  | push k b next => rfl
  | pop k empty low high =>
    exact dispatch_correct empty low high _ _
  | peek k empty low high =>
    exact dispatch_correct empty low high _ _
  | jump next => rfl
  | halt => rfl

/-- Exact source-step/actual-machine-step commuting square. -/
theorem step_correct {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (state : State K L) :
    (machine input output main code).step (configuration state)=
      (step code state).map configuration := by
  cases state with
  | mk pc flag store =>
    cases pc with
    | none => rfl
    | some label =>
      exact congrArg some (instruction_correct (code label) (⟨some label,flag,store⟩:State K L))

/-- Finite source-run output equals the actual target-machine run at the SAME transition count. -/
theorem run_correct {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (fuel : ℕ) (state : State K L) :
    (run code fuel state).map configuration=
      (fun cfg=>cfg.bind (machine input output main code).step)^[fuel] (some (configuration state)) := by
  have h (n : ℕ) (state : Option (State K L)) :
      ((fun state=>state.bind (step code))^[n] state).map configuration=
        (fun cfg=>cfg.bind (machine input output main code).step)^[n] (state.map configuration) := by
    induction n generalizing state with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',←ih]
      cases hs:((fun state=>state.bind (step code))^[n] state) with
      | none => rfl
      | some state => exact (step_correct input output main code state).symm
  exact h fuel (some state)

/-- A proved executable SOURCE trace transfers to an actual transition bound.
This is not a report-to-time assumption: both sides execute the specified instructions. -/
def evalsCorrect {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (start finish : State K L)
    (time : ℕ) (h:StateTransition.EvalsToInTime (step code) start (some finish) time) :
    StateTransition.EvalsToInTime (machine input output main code).step
      (configuration start) (some (configuration finish)) time := by
  refine ⟨⟨h.steps,?_⟩,h.steps_le_m⟩
  have hr:=run_correct input output main code h.steps start
  have he:=h.evals_in_steps
  change (run code h.steps start)=some finish at he
  rw [he] at hr
  exact hr.symm
/-- Actual initial source configuration with the input on its designated stack. -/
def initial {K L : Type} [DecidableEq K] (input : K) (main : L) (bits : List Bool) : State K L :=
  ⟨some main,none,fun k=>if k=input then bits else []⟩

/-- Actual final source configuration with only the output stack populated. -/
def final {K L : Type} [DecidableEq K] (output : K) (bits : List Bool) : State K L :=
  ⟨none,none,fun k=>if k=output then bits else []⟩

/-- Source input encoding is exactly Mathlib's actual TM2 input configuration. -/
theorem initial_correct {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (bits : List Bool) :
    configuration (initial input main bits)=Turing.initList (machine input output main code) bits := by
  dsimp only [configuration,initial,Turing.initList,machine]
  congr 1

/-- Source output encoding is exactly Mathlib's actual reset/halting configuration. -/
theorem final_correct {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (bits : List Bool) :
    configuration (final output bits : State K L)=Turing.haltList (machine input output main code) bits := by
  dsimp only [configuration,final,Turing.haltList,machine]
  congr 1

/-- A proved actual bytecode input/output trace supplies a genuine finite-machine
output/time certificate. It assumes no retained clock or source-value oracle. -/
def outputsOfSource {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (bits result : List Bool)
    (time : ℕ) (h:StateTransition.EvalsToInTime (step code)
      (initial input main bits) (some (final output result)) time) :
    Turing.TM2OutputsInTime (machine input output main code) bits (some result) time := by
  have ht:=evalsCorrect input output main code _ _ time h
  exact ht

/-- Syntactic maximum number of fundamental stack/control commands on one branch. -/
def statementDepth {K L S : Type} {Γ : K→Type} : Turing.TM2.Stmt Γ L S→ℕ
  | .push _ _ next => 1+statementDepth next
  | .peek _ _ next => 1+statementDepth next
  | .pop _ _ next => 1+statementDepth next
  | .load _ next => 1+statementDepth next
  | .branch _ low high => 1+max (statementDepth low) (statementDepth high)
  | .goto _ => 1
  | .halt => 1

/-- Every compiled transition has at most four literal stack/control commands. -/
theorem compile_depth {K L : Type} (instruction : Instruction K L) :
    statementDepth (compileInstruction instruction) ≤ 4 := by
  cases instruction <;> simp only [compileInstruction,statementDepth,dispatch] <;> decide

/-- Concrete fixed two-label code, prepending one bit on its single stack. -/
def prependCode : Bool→Instruction Unit Bool
  | false => .push () true true
  | true => .halt

/-- Actual fixed finite machine, independent of its arbitrary input word. -/
def prependMachine : Turing.FinTM2 := machine () () false prependCode

/-- Concrete bytecode execution acquires the whole output; no result is supplied. -/
theorem prepend_run (bits : List Bool) :
    run prependCode 2 (initial () false bits)=some (final () (true::bits) : State Unit Bool) := by
  change some (⟨none,none,Function.update (fun k:Unit=>if k=() then bits else []) ()
    (true::(if ()=() then bits else []))⟩:State Unit Bool)=_
  congr 1

/-- A variable-input actual machine-time control, proved through source compilation. -/
def prependOutputs (bits : List Bool) :
    Turing.TM2OutputsInTime prependMachine bits (some (true::bits)) 2 := by
  apply outputsOfSource () () false prependCode bits (true::bits) 2
  exact ⟨⟨2,prepend_run bits⟩,le_refl _⟩
end RiemannGaussian.SemiprimeD1StackBytecode
