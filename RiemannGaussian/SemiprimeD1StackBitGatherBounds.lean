/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBitGather

/-! # Actual primitive time/storage of physical gather
Repeated whole-assignment copies and discarded suffix scans are included. Input
index framing/unary acquisition and preparation of the assignment stack remain
caller operations. No native producer clock is assumed.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackBitGatherBounds
open Turing Turing.TM2
open SemiprimeD1StackBitGather
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Actual encoded-vector length dominates the number of requested ports. -/
theorem count_le_tape (indices : List (List Bool)) : indices.length≤(vectorBits indices).length := by
  induction indices with
  | nil => simp [vectorBits]
  | cons i is ih =>
    simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    omega

/-- Complete scan cost, including every repeated assignment copy and suffix clear. -/
theorem scanSteps_le (assignment : List Bool) (indices : List (List Bool)) :
    scanSteps assignment indices≤(3*assignment.length+6)*(vectorBits indices).length := by
  induction indices with
  | nil => simp [scanSteps,vectorBits]
  | cons i is ih =>
    have hd : (assignment.drop (i.length+1)).length≤assignment.length := by
      simp only [List.length_drop]
      omega
    simp only [scanSteps,portSteps,vectorBits,List.length_cons,
      SemiprimeSourceHistogramKeyBits.frame_length]
    nlinarith

/-- Fixed polynomial bound in the actual assignment and index-tape lengths. -/
def budget (assignmentLength indexTapeLength : ℕ) : ℕ :=
  (3*assignmentLength+8)*(indexTapeLength+1)

/-- All literal actual transition counts fit the displayed polynomial. -/
theorem gather_steps_le (assignment : List Bool) (indices : List (List Bool)) :
    scanSteps assignment indices+indices.length+1≤budget assignment.length (vectorBits indices).length := by
  have hs := scanSteps_le assignment indices
  have hc := count_le_tape indices
  unfold budget
  nlinarith

/-- Genuine TM2 time certificate; no bit getter or lookup callback is supplied. -/
def gatherInTime (assignment : List Bool) (indices : List (List Bool)) (tail out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .marker) none (vectorBits indices++tail) assignment [] [] [] out)
      (some (cfg none none tail assignment [] [] [] (values assignment indices++out)))
      (budget assignment.length (vectorBits indices).length) := by
  refine ⟨⟨_,(gather_exec assignment indices tail out).iterates⟩,?_⟩
  change scanSteps assignment indices+indices.length+1≤_
  exact gather_steps_le assignment indices

/-- Closed original ordered-port endpoint, with only physical unary indices as input. -/
def originalGatherInTime (assignment : List Bool) (ports : List ℕ) (tail out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .marker) none (vectorBits (ports.map (fun i => List.replicate i true))++tail)
        assignment [] [] [] out)
      (some (cfg none none tail assignment [] [] []
        ((SemiprimeD1LeafCounter.gather assignment ports).bits++out)))
      (budget assignment.length (vectorBits (ports.map (fun i => List.replicate i true))).length) := by
  simpa [values,List.map_map,Function.comp_def,SemiprimeD1LeafCounter.gather_value] using
    gatherInTime assignment (ports.map (fun i => List.replicate i true)) tail out

/-- Every alphabet is the same finite two-symbol set. -/
theorem alphabet_card (k : Stack) : Fintype.card (Alphabet k)=2 := by
  change Fintype.card Bool=2
  decide

/-- No unbounded register data are hidden in this program. -/
theorem registers_card : Fintype.card Registers=3 := by decide

/-- Every elementary stack/control syntax node is included in the static depth. -/
def instructionDepth : Stmt Alphabet PC Registers → ℕ
  | .push _ _ q => 1+instructionDepth q
  | .peek _ _ q => 1+instructionDepth q
  | .pop _ _ q => 1+instructionDepth q
  | .load _ q => 1+instructionDepth q
  | .branch _ q r => 1+max (instructionDepth q) (instructionDepth r)
  | .goto _ => 1
  | .halt => 1

/-- At most five elementary instructions occur in one TM2 transition. -/
theorem program_depth (pc : PC) : instructionDepth (program pc)≤5 := by
  cases pc <;> decide

/-- All actual jumps stay within the same fixed eight-label program. -/
theorem program_supports : TM2.Supports program Finset.univ := by
  constructor
  · simp
  · intro pc hpc
    cases pc <;> simp [program,TM2.SupportsStmt]

/-- All six unbounded data stacks, including restoration and result scratch. -/
def cells (c : Cfg Alphabet PC Registers) : ℕ :=
  (c.stk Stack.input).length+(c.stk Stack.assignment).length+(c.stk Stack.reader).length+
    (c.stk Stack.scratch).length+(c.stk Stack.accumulator).length+(c.stk Stack.output).length

/-- One actual instruction label creates at most two Boolean symbols. -/
theorem step_cells (c d : Cfg Alphabet PC Registers) (h : step c=some d) :
    cells d≤cells c+2 := by
  rcases c with ⟨pc,flag,store⟩
  cases pc with
  | none => simp [SemiprimeD1StackBitGather.step,TM2.step] at h
  | some pc =>
    cases pc <;>
      simp [SemiprimeD1StackBitGather.step,TM2.step,program,TM2.stepAux,
        Bool.cond_eq_ite,Function.update] at h <;>
      (try split_ifs at h) <;> cases h <;> simp [cells,Function.update] <;> omega

/-- All reached states, including copy/restore/clear frames, have derived storage. -/
theorem path_cells {n : ℕ} {c d : Cfg Alphabet PC Registers} (h : Executes n c d) :
    cells d≤cells c+2*n := by
  induction h with
  | refl => omega
  | @next n c e d hs ht ih =>
    have hh := step_cells c e hs
    omega

/-- Uniform quadratic all-prefix Boolean storage in actual encoded input sizes. -/
theorem gather_cells (assignment : List Bool) (indices : List (List Bool)) (tail out : List Bool)
    (n : ℕ) (c : Cfg Alphabet PC Registers)
    (h : Executes n (cfg (some .marker) none (vectorBits indices++tail) assignment [] [] [] out) c)
    (hn : n≤budget assignment.length (vectorBits indices).length) :
    cells c≤(vectorBits indices).length+tail.length+assignment.length+out.length+
      2*budget assignment.length (vectorBits indices).length := by
  have hh := path_cells h
  simp only [cells,cfg,contents,List.length_append,List.length_nil,Nat.add_zero] at hh
  unfold cells
  omega

end RiemannGaussian.SemiprimeD1StackBitGatherBounds
