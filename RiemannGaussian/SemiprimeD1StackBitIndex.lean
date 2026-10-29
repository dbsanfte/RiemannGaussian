/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeFieldMachine

/-! # Actual finite-stack bit indexing
The index is a unary word on a physical Boolean stack. The machine has three
fixed labels and no native Nat/List register. Each unary cell causes one actual
word pop. A final physical pop supplies the selected bit, defaulting EOF to false.
Input acquisition and reuse/copy of the consumed word are separate operations.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackBitIndex
open Turing Turing.TM2 Turing.TM2.Stmt

/-- Three physical Boolean stacks. -/
inductive Stack | word | index | output deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.word,.index,.output}
  complete := by intro k; cases k <;> simp

/-- Three fixed instruction labels. -/
inductive PC | scan | drop | finish deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.scan,.drop,.finish}
  complete := by intro k; cases k <;> simp

/-- Every unbounded datum is a Boolean stack symbol. -/
abbrev Alphabet (_ : Stack) := Bool
/-- Only the most recent popped optional bit is held in finite control. -/
abbrev Registers := Option Bool

/-- Actual fixed stack program. -/
def program : PC → Stmt Alphabet PC Registers
  | .scan => .pop .index (fun _ b => b)
      (.branch (fun b => b.isSome) (.goto (fun _ => .drop)) (.goto (fun _ => .finish)))
  | .drop => .pop .word (fun _ b => b) (.goto (fun _ => .scan))
  | .finish => .pop .word (fun _ b => b)
      (.push .output (fun b => b.getD false) .halt)

/-- Genuine finite-alphabet TM2; indices are never native register values. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .word
  k₁ := .output
  Γ := Alphabet
  Λ := PC
  main := .scan
  σ := Registers
  initialState := none
  m := program

/-- Literal physical stack contents. -/
def contents (word index output : List Bool) : (k : Stack) → List (Alphabet k)
  | .word => word
  | .index => index
  | .output => output

/-- Explicit configurations with no hidden native payload. -/
def cfg (pc : Option PC) (flag : Registers) (word index output : List Bool) :
    Cfg Alphabet PC Registers := ⟨pc,flag,contents word index output⟩

/-- Actual Mathlib transition. -/
def step := TM2.step program

/-- Physical stack update. -/
@[simp] theorem update_contents (word index output xs : List Bool) (k : Stack) :
    Function.update (contents word index output) k xs=
      contents (if k=.word then xs else word) (if k=.index then xs else index)
        (if k=.output then xs else output) := by
  funext j
  cases k <;> cases j <;> simp [contents]

/-- Exact actual execution paths; counts live only in proofs. -/
inductive Executes : ℕ → Cfg Alphabet PC Registers → Cfg Alphabet PC Registers → Prop
  | refl (c) : Executes 0 c c
  | next {n c d e} : step c=some d → Executes n d e → Executes (n+1) c e

/-- Paths yield the real Mathlib iterated transition equation. -/
theorem Executes.iterates {n : ℕ} {a b : Cfg Alphabet PC Registers} (h : Executes n a b) :
    ((fun x : Option (Cfg Alphabet PC Registers) => x.bind step)^[n]) (some a)=some b := by
  induction h with
  | refl => rfl
  | @next n a d b hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,hs] using ih

/-- Consume one actual unary index symbol. -/
theorem scan_cons (flag : Registers) (word index output : List Bool) (b : Bool) :
    step (cfg (some .scan) flag word (b::index) output)=
      some (cfg (some .drop) (some b) word index output) := by
  simp [SemiprimeD1StackBitIndex.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- Empty physical unary index triggers the final read. -/
theorem scan_nil (flag : Registers) (word output : List Bool) :
    step (cfg (some .scan) flag word [] output)=
      some (cfg (some .finish) none word [] output) := by
  simp [SemiprimeD1StackBitIndex.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- One physical word pop, including EOF. -/
theorem drop_step (flag : Registers) (word index output : List Bool) :
    step (cfg (some .drop) flag word index output)=
      some (cfg (some .scan) word.head? word.tail index output) := by
  simp [SemiprimeD1StackBitIndex.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- The actual output is a single physical Boolean cell. -/
theorem finish_step (flag : Registers) (word index output : List Bool) :
    step (cfg (some .finish) flag word index output)=
      some (cfg none word.head? word.tail index (word.head?.getD false::output)) := by
  simp [SemiprimeD1StackBitIndex.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- Exact consumed suffix, bit/default, output cell and transition count. -/
theorem index_exec (flag : Registers) (word index output : List Bool) :
    Executes (2*index.length+2) (cfg (some .scan) flag word index output)
      (cfg none (word[index.length]?) (word.drop (index.length+1)) []
        ((word[index.length]?).getD false::output)) := by
  induction index generalizing word flag with
  | nil =>
    simpa [List.head?_eq_getElem?] using Executes.next (scan_nil flag word output)
      (Executes.next (finish_step none word [] output) (Executes.refl _))
  | cons b bs ih =>
    have ht := Executes.next (scan_cons flag word bs output b)
      (Executes.next (drop_step (some b) word bs output) (ih word.head? word.tail))
    convert ht using 1
    simp [List.getElem?_tail]

/-- Genuine TM2 time certificate; index acquisition is not hidden in its input. -/
def indexInTime (word index output : List Bool) :
    StateTransition.EvalsToInTime machine.step (cfg (some .scan) none word index output)
      (some (cfg none (word[index.length]?) (word.drop (index.length+1)) []
        ((word[index.length]?).getD false::output))) (2*index.length+2) :=
  ⟨⟨_,(index_exec none word index output).iterates⟩,le_rfl⟩

/-- Ordinary unary acquisition can instantiate this without changing the program. -/
def unaryInTime (word output : List Bool) (index : ℕ) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .scan) none word (List.replicate index true) output)
      (some (cfg none (word[index]?) (word.drop (index+1)) []
        ((word[index]?).getD false::output))) (2*index+2) := by
  simpa using indexInTime word (List.replicate index true) output

/-- Three register values, independent of word/index sizes. -/
theorem registers_card : Fintype.card Registers=3 := by decide

/-- Every stack alphabet has exactly two symbols. -/
theorem alphabet_card (k : Stack) : Fintype.card (Alphabet k)=2 := by
  change Fintype.card Bool=2
  decide

/-- Every elementary stack/control syntax node is counted statically. -/
def instructionDepth : Stmt Alphabet PC Registers → ℕ
  | .push _ _ q => 1+instructionDepth q
  | .peek _ _ q => 1+instructionDepth q
  | .pop _ _ q => 1+instructionDepth q
  | .load _ q => 1+instructionDepth q
  | .branch _ q r => 1+max (instructionDepth q) (instructionDepth r)
  | .goto _ => 1
  | .halt => 1

/-- At most three elementary instructions occur in any actual transition. -/
theorem program_depth (pc : PC) : instructionDepth (program pc)≤3 := by
  cases pc <;> decide

/-- Every goto stays in the fixed three-label program. -/
theorem program_supports : TM2.Supports program Finset.univ := by
  constructor
  · simp
  · intro pc hpc
    cases pc <;> simp [program,TM2.SupportsStmt]

/-- Total unbounded physical state, including the result cell. -/
def cells (c : Cfg Alphabet PC Registers) : ℕ :=
  (c.stk Stack.word).length+(c.stk Stack.index).length+(c.stk Stack.output).length

/-- Each literal primitive step increases Boolean storage by at most one cell. -/
theorem step_cells (c d : Cfg Alphabet PC Registers) (h : step c=some d) :
    cells d≤cells c+1 := by
  rcases c with ⟨pc,flag,store⟩
  cases pc with
  | none => simp [SemiprimeD1StackBitIndex.step,TM2.step] at h
  | some pc =>
    cases pc <;>
      simp [SemiprimeD1StackBitIndex.step,TM2.step,program,TM2.stepAux,
        Bool.cond_eq_ite,Function.update] at h <;>
      (try split_ifs at h) <;> cases h <;> simp [cells,Function.update] <;> omega

/-- Every visited prefix has a derived total Boolean-stack bound. -/
theorem path_cells {n : ℕ} {c d : Cfg Alphabet PC Registers} (h : Executes n c d) :
    cells d≤cells c+n := by
  induction h with
  | refl => omega
  | @next n c e d hs ht ih =>
    have hh := step_cells c e hs
    omega

/-- Uniform all-prefix linear space bound on physically indexed reads. -/
theorem index_cells (word index output : List Bool) (n : ℕ) (c : Cfg Alphabet PC Registers)
    (h : Executes n (cfg (some .scan) none word index output) c)
    (hn : n≤2*index.length+2) :
    cells c≤word.length+3*index.length+output.length+2 := by
  have hh := path_cells h
  simp only [cells,cfg,contents] at hh
  unfold cells
  omega

end RiemannGaussian.SemiprimeD1StackBitIndex
