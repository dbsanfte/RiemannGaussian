/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype
import RiemannGaussian.SemiprimeD1TensorTapeCodec

/-! # Finite-alphabet TM2 program for the actual tape field parser
Every stack alphabet is Bool. Control consists only of eight labels and six
finite register settings. No Nat, List, address or closure is a control symbol.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1TensorTapeFieldMachine
open Turing Turing.TM2 Turing.TM2.Stmt

/-- Three physical Boolean-stack indices; lists occur only as stack contents. -/
inductive Stack
  /-- Unconsumed input tape. -/
  | input
  /-- Reverse copied field. -/
  | scratch
  /-- Forward copied output field. -/
  | output
  deriving DecidableEq,Inhabited,Repr

/-- Fixed finite instruction labels. -/
inductive PC
  /-- Consume one framing tag. -/
  | tagPop
  /-- Test the consumed tag. -/
  | tagBranch
  /-- Consume one framed data bit. -/
  | dataPop
  /-- Test data-bit availability. -/
  | dataBranch
  /-- Copy one data bit to the reverse stack. -/
  | dataPush
  /-- Consume one reverse-stack bit. -/
  | reversePop
  /-- Test reverse-stack exhaustion. -/
  | reverseBranch
  /-- Copy one reverse bit to the forward output. -/
  | reversePush
  deriving DecidableEq,Inhabited,Repr

/-- Explicit finite stack-index catalogue. -/
instance : Fintype Stack where
  elems:={.input,.scratch,.output}
  complete:=by intro k;cases k <;> simp

/-- Explicit fixed instruction-label catalogue. -/
instance : Fintype PC where
  elems:={.tagPop,.tagBranch,.dataPop,.dataBranch,.dataPush,.reversePop,.reverseBranch,.reversePush}
  complete:=by intro k;cases k <;> simp

/-- A popped optional bit and a valid-terminator flag: exactly six settings. -/
abbrev Registers := Option Bool×Bool

/-- EVERY stack has the same two-symbol alphabet, not only the input stack. -/
abbrev Alphabet (_ : Stack) := Bool

/-- Actual fixed instruction table: only top-pop, push, finite tests, goto and halt. -/
def program : PC → Stmt Alphabet PC Registers
  | .tagPop => .pop .input (fun _ top => (top,top==some false)) (.goto (fun _ => .tagBranch))
  | .tagBranch => .branch (fun v => v.1==some true)
      (.goto (fun _ => .dataPop)) (.goto (fun _ => .reversePop))
  | .dataPop => .pop .input (fun _ top => (top,false)) (.goto (fun _ => .dataBranch))
  | .dataBranch => .branch (fun v => v.1.isSome)
      (.goto (fun _ => .dataPush)) (.goto (fun _ => .reversePop))
  | .dataPush => .push .scratch (fun v => v.1.getD false) (.goto (fun _ => .tagPop))
  | .reversePop => .pop .scratch (fun v top => (top,v.2)) (.goto (fun _ => .reverseBranch))
  | .reverseBranch => .branch (fun v => v.1.isSome)
      (.goto (fun _ => .reversePush)) .halt
  | .reversePush => .push .output (fun v => v.1.getD false) (.goto (fun _ => .reversePop))

/-- Bundled actual Mathlib machine; all finiteness witnesses are constructive. -/
def machine : FinTM2 where
  K:=Stack
  k₀:=.input
  k₁:=.output
  Γ:=Alphabet
  Λ:=PC
  main:=.tagPop
  σ:=Registers
  initialState:=(none,false)
  m:=program

/-- Explicit finite alphabet cardinality at EVERY stack. -/
theorem alphabet_card (k : Stack) : Fintype.card (Alphabet k)=2 := by
  change Fintype.card Bool=2
  decide

/-- No unbounded internal register is hidden in the model. -/
theorem registers_card : Fintype.card Registers=6 := by decide

/-- Actual literal stack arrangement. -/
def contents (input scratch output : List Bool) : (k : Stack) → List (Alphabet k)
  | .input => input
  | .scratch => scratch
  | .output => output

/-- Concrete machine configurations; all unbounded data live in Boolean stacks. -/
def config (pc : Option PC) (v : Registers) (input scratch output : List Bool) :
    TM2.Cfg Alphabet PC Registers := ⟨pc,v,contents input scratch output⟩

/-- The actual TM2 transition, not a report annotation. -/
def step := TM2.step program

/-- Input-stack update touches exactly its physical contents. -/
@[simp] theorem update_input (input scratch output xs : List Bool) :
    Function.update (contents input scratch output) Stack.input xs=contents xs scratch output := by
  funext k
  cases k <;> simp [contents]

/-- Scratch-stack update touches exactly its physical contents. -/
@[simp] theorem update_scratch (input scratch output xs : List Bool) :
    Function.update (contents input scratch output) Stack.scratch xs=contents input xs output := by
  funext k
  cases k <;> simp [contents]

/-- Output-stack update touches exactly its physical contents. -/
@[simp] theorem update_output (input scratch output xs : List Bool) :
    Function.update (contents input scratch output) Stack.output xs=contents input scratch xs := by
  funext k
  cases k <;> simp [contents]

/-- Exactly n actual machine transitions, with no additional executable fuel input. -/
inductive Executes : ℕ → TM2.Cfg Alphabet PC Registers → TM2.Cfg Alphabet PC Registers → Prop
  /-- Empty path. -/
  | refl (c) : Executes 0 c c
  /-- One actual transition followed by the remaining transitions. -/
  | next {n c d e} : step c=some d → Executes n d e → Executes (n+1) c e

/-- Actual paths compose by adding their transition counts. -/
theorem Executes.trans {n m : ℕ} {a b c : TM2.Cfg Alphabet PC Registers}
    (h : Executes n a b) (g : Executes m b c) : Executes (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next hs (ih g)

/-- One actual TM2 transition gives the corresponding one-step execution path. -/
theorem Executes.single {a b : TM2.Cfg Alphabet PC Registers} (h : step a=some b) :
    Executes 1 a b := Executes.next h (Executes.refl b)

/-- Exact paths satisfy the actual iterated Mathlib transition equation. -/
theorem Executes.iterates {n : ℕ} {a b : TM2.Cfg Alphabet PC Registers} (h : Executes n a b) :
    ((fun x : Option (TM2.Cfg Alphabet PC Registers) => x.bind step)^[n]) (some a)=some b := by
  induction h with
  | refl c => rfl
  | @next n a d b hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,hs] using ih

/-- This path semantics constructs Mathlib's actual transition-time certificate. -/
def Executes.inTime {n : ℕ} {a b : TM2.Cfg Alphabet PC Registers} (h : Executes n a b) :
    StateTransition.EvalsToInTime step a (some b) n :=
  ⟨⟨n,h.iterates⟩,le_rfl⟩

end RiemannGaussian.SemiprimeD1TensorTapeFieldMachine
