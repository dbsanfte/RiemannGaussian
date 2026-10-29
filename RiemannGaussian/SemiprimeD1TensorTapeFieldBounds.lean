/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeFieldExecution

/-! # Concrete finite-program and stack-cell bounds for tape field parsing
No unbounded object occurs in internal control or an alphabet symbol. Actual
TM2 transition paths control both time and all three physical stack inventories.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1TensorTapeFieldBounds
open Turing Turing.TM2 SemiprimeD1TensorTapeFieldMachine
open SemiprimeD1TensorTapeFieldExecution SemiprimeSourceHistogramKeyBits

/-- Static instruction depth counts real stack/control syntax nodes on a branch. -/
def instructionDepth : Stmt Alphabet PC Registers → ℕ
  | .push _ _ q => 1+instructionDepth q
  | .peek _ _ q => 1+instructionDepth q
  | .pop _ _ q => 1+instructionDepth q
  | .load _ q => 1+instructionDepth q
  | .branch _ q r => 1+max (instructionDepth q) (instructionDepth r)
  | .goto _ => 1
  | .halt => 1

/-- Each actual TM2 label executes at most two fixed stack/control instructions. -/
theorem program_depth (pc : PC) : instructionDepth (program pc)=2 := by
  cases pc <;> rfl

/-- Every actual jump stays inside the fixed finite label catalogue. -/
theorem program_supports : TM2.Supports program Finset.univ := by
  constructor
  · simp
  · intro pc hpc
    cases pc <;> simp [program,TM2.SupportsStmt]

/-- The official FinTM2 initial configuration is the literal input-stack layout. -/
theorem init_eq (xs : List Bool) : Turing.initList machine xs=
    config (some .tagPop) (none,false) xs [] [] := by
  unfold Turing.initList config
  dsimp only [machine]
  congr 1
  funext k
  cases k <;> rfl

/-- Actual bundled-machine time certificate with all stack alphabets equal to Bool. -/
def bundledInTime (xs : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine xs)
      (some (final xs)) (4*xs.length+6) := by
  rw [init_eq]
  exact splitInTime xs

/-- Actual valid-field transition count is independent of the unconsumed tail. -/
theorem fieldSteps_frame (word tail : List Bool) : fieldSteps (frame word tail)=8*word.length+4 := by
  induction word with
  | nil => rfl
  | cons b bs ih =>
    simp only [frame,fieldSteps,List.length_cons,ih]
    omega

/-- Exact machine certificate for a real serialized coefficient field: every
copied bit costs its actual scan/reversal transitions; the tail is preserved. -/
def framedInTime (word tail : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine (frame word tail))
      (some (config none (none,true) tail [] word)) (8*word.length+4) := by
  rw [init_eq]
  have h:=parse_exec (frame word tail) (none,false) [] []
  have hs:=split_frame word tail
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.reverse_nil,List.nil_append,List.append_nil,
    fieldSteps_frame,hs.1,hs.2.1,hs.2.2] at h
  exact h.inTime

/-- ALL unbounded machine data are these three stacks of individual Boolean symbols. -/
def cells (c : Cfg Alphabet PC Registers) : ℕ :=
  (c.stk Stack.input).length+(c.stk Stack.scratch).length+(c.stk Stack.output).length

/-- A single actual finite instruction label allocates at most one stack symbol. -/
theorem step_cells (c d : Cfg Alphabet PC Registers)
    (h : SemiprimeD1TensorTapeFieldMachine.step c=some d) : cells d ≤ cells c+1 := by
  rcases c with ⟨pc,⟨flag,valid⟩,store⟩
  cases pc with
  | none => simp [SemiprimeD1TensorTapeFieldMachine.step,TM2.step] at h
  | some pc =>
    cases flag with
    | none =>
      cases pc <;>
        simp only [SemiprimeD1TensorTapeFieldMachine.step,TM2.step,program,TM2.stepAux] at h <;>
        cases h <;> simp [cells,Function.update] <;> omega
    | some b =>
      cases b <;> cases pc <;>
        simp only [SemiprimeD1TensorTapeFieldMachine.step,TM2.step,program,TM2.stepAux] at h <;>
        cases h <;> simp [cells,Function.update] <;> omega

/-- All intermediate actual paths, not only the final output, have a linear cell cap. -/
theorem path_cells {n : ℕ} {c d : Cfg Alphabet PC Registers} (h : Executes n c d) :
    cells d ≤ cells c+n := by
  induction h with
  | refl c => omega
  | @next n c e d hs ht ih =>
    have hh:=step_cells c e hs
    omega

/-- Every visited parsing configuration has a derived linear total stack footprint. -/
theorem parser_cells (xs : List Bool) (n : ℕ) (c : Cfg Alphabet PC Registers)
    (h : Executes n (config (some .tagPop) (none,false) xs [] []) c)
    (hn : n ≤ 4*xs.length+6) : cells c ≤ 5*xs.length+6 := by
  have hh:=path_cells h
  simp only [cells,config,contents,List.length_nil,Nat.add_zero] at hh
  unfold cells
  omega

end RiemannGaussian.SemiprimeD1TensorTapeFieldBounds
