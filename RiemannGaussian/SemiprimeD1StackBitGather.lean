/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBitIndex
import RiemannGaussian.SemiprimeD1TensorTapeVectorMachine
import RiemannGaussian.SemiprimeD1TensorTapeCodec
import RiemannGaussian.SemiprimeD1LeafCounter

/-! # Physical ordered gather from framed unary indices
Every index receives a fresh physical copy of the assignment. Both that copy and
its unused suffix are consumed. The assignment is restored literally. The final
result is reversed physically into original port order. No indexed-read callback
or native index register occurs in the program.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackBitGather
open Turing Turing.TM2 Turing.TM2.Stmt
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Fixed Boolean data stacks. -/
inductive Stack | input | assignment | reader | scratch | accumulator | output
  deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.input,.assignment,.reader,.scratch,.accumulator,.output}
  complete := by intro k; cases k <;> simp

/-- Fixed control labels, independent of every scope/index length. -/
inductive PC | marker | drain | restore | tag | drop | get | clear | reverse
  deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.marker,.drain,.restore,.tag,.drop,.get,.clear,.reverse}
  complete := by intro k; cases k <;> simp

/-- Every stack contains individual Boolean symbols. -/
abbrev Alphabet (_ : Stack) := Bool
/-- The sole finite register is an optional popped bit. -/
abbrev Registers := Option Bool

/-- Actual finite stack instructions, including all assignment copying/clearing. -/
def program : PC → Stmt Alphabet PC Registers
  | .marker => .pop .input (fun _ b => b)
      (.branch (fun b => b==some true) (.goto (fun _ => .drain)) (.goto (fun _ => .reverse)))
  | .drain => .pop .assignment (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .scratch (fun b => b.getD false) (.goto (fun _ => .drain)))
        (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .assignment (fun b => b.getD false)
          (.push .reader (fun b => b.getD false) (.goto (fun _ => .restore))))
        (.goto (fun _ => .tag)))
  | .tag => .pop .input (fun _ b => b)
      (.branch (fun b => b==some true) (.goto (fun _ => .drop)) (.goto (fun _ => .get)))
  | .drop => .pop .input (fun _ b => b)
      (.pop .reader (fun _ b => b) (.goto (fun _ => .tag)))
  | .get => .pop .reader (fun _ b => b)
      (.push .accumulator (fun b => b.getD false) (.goto (fun _ => .clear)))
  | .clear => .pop .reader (fun _ b => b)
      (.branch (fun b => b.isSome) (.goto (fun _ => .clear)) (.goto (fun _ => .marker)))
  | .reverse => .pop .accumulator (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .output (fun b => b.getD false) (.goto (fun _ => .reverse))) .halt)

/-- Genuine fixed finite-alphabet machine. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := PC
  main := .marker
  σ := Registers
  initialState := none
  m := program

/-- Explicit actual stack payloads. -/
def contents (input assignment reader scratch accumulator output : List Bool) :
    (k : Stack) → List (Alphabet k)
  | .input => input
  | .assignment => assignment
  | .reader => reader
  | .scratch => scratch
  | .accumulator => accumulator
  | .output => output

/-- Actual configurations; all unbounded data live only in stacks. -/
def cfg (pc : Option PC) (flag : Registers)
    (input assignment reader scratch accumulator output : List Bool) :
    Cfg Alphabet PC Registers := ⟨pc,flag,contents input assignment reader scratch accumulator output⟩

/-- Actual primitive transition function. -/
def step := TM2.step program

/-- Every physical update is a literal single-stack update. -/
@[simp] theorem update_contents (input assignment reader scratch accumulator output xs : List Bool)
    (k : Stack) : Function.update (contents input assignment reader scratch accumulator output) k xs=
      contents (if k=.input then xs else input) (if k=.assignment then xs else assignment)
        (if k=.reader then xs else reader) (if k=.scratch then xs else scratch)
        (if k=.accumulator then xs else accumulator) (if k=.output then xs else output) := by
  funext j
  cases k <;> cases j <;> simp [contents]

/-- Exact actual transition paths, with proof-only lengths. -/
inductive Executes : ℕ → Cfg Alphabet PC Registers → Cfg Alphabet PC Registers → Prop
  | refl (c) : Executes 0 c c
  | next {n c d e} : step c=some d → Executes n d e → Executes (n+1) c e

/-- Actual execution paths compose. -/
theorem Executes.trans {n m : ℕ} {a b c : Cfg Alphabet PC Registers}
    (h : Executes n a b) (g : Executes m b c) : Executes (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next hs (ih g)

/-- Actual iterate equation needed by Mathlib time certificates. -/
theorem Executes.iterates {n : ℕ} {a b : Cfg Alphabet PC Registers} (h : Executes n a b) :
    ((fun x : Option (Cfg Alphabet PC Registers) => x.bind step)^[n]) (some a)=some b := by
  induction h with
  | refl => rfl
  | @next n a d b hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,hs] using ih

/-- The first copy pass physically drains every assignment cell. -/
theorem drain_exec (flag : Registers) (input assignment reader scratch acc out : List Bool) :
    Executes (assignment.length+1) (cfg (some .drain) flag input assignment reader scratch acc out)
      (cfg (some .restore) none input [] reader (assignment.reverse++scratch) acc out) := by
  induction assignment generalizing flag scratch with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : step (cfg (some .drain) flag input (b::bs) reader scratch acc out)=
        some (cfg (some .drain) (some b) input bs reader (b::scratch) acc out) := by
      simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using Executes.next hs (ih (some b) (b::scratch))

/-- The second copy pass restores the assignment AND creates the disposable reader. -/
theorem restore_exec (flag : Registers) (input assignment reader scratch acc out : List Bool) :
    Executes (scratch.length+1) (cfg (some .restore) flag input assignment reader scratch acc out)
      (cfg (some .tag) none input (scratch.reverse++assignment) (scratch.reverse++reader) [] acc out) := by
  induction scratch generalizing flag assignment reader with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : step (cfg (some .restore) flag input assignment reader (b::bs) acc out)=
        some (cfg (some .restore) (some b) input (b::assignment) (b::reader) bs acc out) := by
      simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using
      Executes.next hs (ih (some b) (b::assignment) (b::reader))

/-- Actual two-pass assignment copy, including both EOF tests. -/
theorem copy_exec (flag : Registers) (input assignment acc out : List Bool) :
    Executes (2*assignment.length+2) (cfg (some .drain) flag input assignment [] [] acc out)
      (cfg (some .tag) none input assignment assignment [] acc out) := by
  have h := (drain_exec flag input assignment [] [] acc out).trans
    (restore_exec none input [] [] (assignment.reverse++[]) acc out)
  simp only [List.append_nil,List.length_reverse,List.reverse_reverse] at h
  convert h using 1
  omega

/-- Scan a framed unary index and physically discard that many reader cells. -/
theorem field_exec (flag : Registers) (index input assignment reader acc out : List Bool) :
    Executes (2*index.length+1)
      (cfg (some .tag) flag (frame index input) assignment reader [] acc out)
      (cfg (some .get) (some false) input assignment (reader.drop index.length) [] acc out) := by
  induction index generalizing flag reader with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackBitGather.step,program,cfg,contents,frame,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : step (cfg (some .tag) flag (frame (b::bs) input) assignment reader [] acc out)=
        some (cfg (some .drop) (some true) (b::frame bs input) assignment reader [] acc out) := by
      simp [SemiprimeD1StackBitGather.step,program,cfg,contents,frame,TM2.step,TM2.stepAux]
    have hd : step (cfg (some .drop) (some true) (b::frame bs input) assignment reader [] acc out)=
        some (cfg (some .tag) reader.head? (frame bs input) assignment reader.tail [] acc out) := by
      simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
    have h := Executes.next hs (Executes.next hd (ih reader.head? reader.tail))
    convert h using 1
    simp

/-- Clear every unused reader suffix physically before processing the next port. -/
theorem clear_exec (flag : Registers) (input assignment reader acc out : List Bool) :
    Executes (reader.length+1) (cfg (some .clear) flag input assignment reader [] acc out)
      (cfg (some .marker) none input assignment [] [] acc out) := by
  induction reader generalizing flag with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    apply Executes.next ?_ (ih (some b))
    simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- Reverse the gathered accumulator into original port order. -/
theorem reverse_exec (flag : Registers) (input assignment acc out : List Bool) :
    Executes (acc.length+1) (cfg (some .reverse) flag input assignment [] [] acc out)
      (cfg none none input assignment [] [] [] (acc.reverse++out)) := by
  induction acc generalizing flag out with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : step (cfg (some .reverse) flag input assignment [] [] (b::bs) out)=
        some (cfg (some .reverse) (some b) input assignment [] [] bs (b::out)) := by
      simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using Executes.next hs (ih (some b) (b::out))

/-- Finish the indexed read and physically clear its entire unused reader suffix. -/
theorem get_clear_exec (flag : Registers) (input assignment reader acc out : List Bool) :
    Executes (reader.tail.length+2) (cfg (some .get) flag input assignment reader [] acc out)
      (cfg (some .marker) none input assignment [] [] (reader.head?.getD false::acc) out) := by
  have hs : step (cfg (some .get) flag input assignment reader [] acc out)=
      some (cfg (some .clear) reader.head? input assignment reader.tail []
        (reader.head?.getD false::acc) out) := by
    simp [SemiprimeD1StackBitGather.step,program,cfg,contents,TM2.step,TM2.stepAux]
  simpa using Executes.next hs (clear_exec reader.head? input assignment reader.tail
    (reader.head?.getD false::acc) out)

/-- Actual per-port scan cost, including restored assignment and disposed suffix. -/
def portSteps (assignment index : List Bool) : ℕ :=
  2*assignment.length+2*index.length+(assignment.drop (index.length+1)).length+6

/-- Actual full scan cost before final output reversal. -/
def scanSteps (assignment : List Bool) : List (List Bool) → ℕ
  | [] => 1
  | i::is => portSteps assignment i+scanSteps assignment is

/-- Physical indexing values, specified without any runtime getter callback. -/
def values (assignment : List Bool) (indices : List (List Bool)) : List Bool :=
  indices.map (fun i => (assignment[i.length]?).getD false)

/-- Complete chronological gather scan, preserving the original assignment. -/
theorem gather_scan (flag : Registers) (assignment : List Bool) (indices : List (List Bool))
    (tail acc out : List Bool) :
    Executes (scanSteps assignment indices)
      (cfg (some .marker) flag (vectorBits indices++tail) assignment [] [] acc out)
      (cfg (some .reverse) (some false) tail assignment [] []
        ((values assignment indices).reverse++acc) out) := by
  induction indices generalizing flag acc with
  | nil =>
    apply Executes.next ?_ (Executes.refl _)
    simp [SemiprimeD1StackBitGather.step,program,cfg,contents,vectorBits,values,
      TM2.step,TM2.stepAux]
  | cons i is ih =>
    have hs : step (cfg (some .marker) flag (vectorBits (i::is)++tail) assignment [] [] acc out)=
        some (cfg (some .drain) (some true) (frame i (vectorBits is++tail)) assignment [] [] acc out) := by
      simp [SemiprimeD1StackBitGather.step,program,cfg,contents,vectorBits,
        SemiprimeD1TensorTapeVectorMachine.frame_append,TM2.step,TM2.stepAux]
    have hc := copy_exec (some true) (frame i (vectorBits is++tail)) assignment acc out
    have hf := field_exec none i (vectorBits is++tail) assignment assignment acc out
    have hg := get_clear_exec (some false) (vectorBits is++tail) assignment
      (assignment.drop i.length) acc out
    have hi := ih none ((assignment.drop i.length).head?.getD false::acc)
    have h := Executes.next hs (hc.trans (hf.trans (hg.trans hi)))
    convert h using 1 <;> simp [scanSteps,portSteps,values,List.reverse_cons,List.append_assoc,
      List.head?_eq_getElem?,List.getElem?_drop,Nat.add_assoc]
    all_goals omega

/-- Complete actual machine execution with one physical output bit per port. -/
theorem gather_exec (assignment : List Bool) (indices : List (List Bool)) (tail out : List Bool) :
    Executes (scanSteps assignment indices+indices.length+1)
      (cfg (some .marker) none (vectorBits indices++tail) assignment [] [] [] out)
      (cfg none none tail assignment [] [] [] (values assignment indices++out)) := by
  have hs := gather_scan none assignment indices tail [] out
  have hr := reverse_exec (some false) tail assignment ((values assignment indices).reverse++[]) out
  have h := hs.trans hr
  simpa [values,Nat.add_assoc] using h

/-- Literal frozen ordered gather from original unary port indices, no producer oracle. -/
theorem original_gather_exec (assignment : List Bool) (ports : List ℕ) (tail out : List Bool) :
    Executes (scanSteps assignment (ports.map (fun i => List.replicate i true))+ports.length+1)
      (cfg (some .marker) none (vectorBits (ports.map (fun i => List.replicate i true))++tail)
        assignment [] [] [] out)
      (cfg none none tail assignment [] [] []
        ((SemiprimeD1LeafCounter.gather assignment ports).bits++out)) := by
  simpa [values,List.map_map,Function.comp_def,SemiprimeD1LeafCounter.gather_value] using
    gather_exec assignment (ports.map (fun i => List.replicate i true)) tail out

end RiemannGaussian.SemiprimeD1StackBitGather
