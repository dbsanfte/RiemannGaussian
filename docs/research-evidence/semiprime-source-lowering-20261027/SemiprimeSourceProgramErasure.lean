/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceMemoryTrace

/-! # Executed source interpreter with outer report bookkeeping erased
The executable functions below use the actual Boolean tests, decrements,
word operations and output copies. Unused visit copies may be optimized away.
Only memory/interpreter report aggregation is
removed. Arithmetic/test primitive reports are still a separate erasure seam.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceProgramErasure
open SemiprimeRationalBits SemiprimeSourceMemoryBits SemiprimeSourceProgramBits
open SemiprimeBitPrimeScan SemiprimeBitArithmetic SemiprimeBitDivision

/-- Actual copied word, without the enclosing memory-copy report. -/
def copyWordErased (x : RationalWord) : RationalWord := (copyWord x).word

/-- Actual Boolean-address scan with only its outer report erased. -/
def readWordErased : List RationalWord → List Bool → RationalWord
  | [],_ => zeroWord
  | x::xs,address =>
    let visit := copyWordErased x
    if (nonzeroBits address).nonzero then
      readWordErased xs (subBits address [true] false).result.bits
    else visit

/-- Exact all-input scan refinement; validity and fit advice are unnecessary. -/
theorem readWordErased_eq (memory : List RationalWord) (address : List Bool) :
    readWordErased memory address=(readWord memory address).word := by
  induction memory generalizing address with
  | nil => rfl
  | cons x xs ih =>
    simp only [readWordErased,readWord,copyWordErased]
    split_ifs <;> simp only [ih]

/-- Literal recursive copied store with no clock additions. -/
def copyMemoryErased : List RationalWord → List RationalWord
  | [] => []
  | x::xs => copyWordErased x::copyMemoryErased xs

/-- Copy outputs are exactly the original physically executed copy outputs. -/
theorem copyMemoryErased_eq (memory : List RationalWord) :
    copyMemoryErased memory=(copyMemory memory).words := by
  induction memory with
  | nil => rfl
  | cons x xs ih => simp only [copyMemoryErased,copyMemory,copyWordErased,ih]

/-- Actual operand scans, arithmetic output and copied store; no outer Nat report. -/
def stepErased (template : List Bool) (i : Instruction) (memory : List RationalWord) : List RationalWord :=
  let left := readWordErased memory i.left
  let right := readWordErased memory i.right
  let out := executeOperation i.operation left right template
  out.word::copyMemoryErased memory

/-- Every actual instruction output survives outer report erasure. -/
theorem stepErased_eq (template : List Bool) (i : Instruction) (memory : List RationalWord) :
    stepErased template i memory=(step template i memory).memory := by
  simp only [stepErased,step,readWordErased_eq,copyMemoryErased_eq]

/-- Literal code traversal with neither step nor recursive clock aggregation. -/
def runErased (template : List Bool) : List Instruction → List RationalWord → List RationalWord
  | [],memory => memory
  | i::code,memory => runErased template code (stepErased template i memory)

/-- Outer clock erasure preserves the complete physical final store on ALL inputs. -/
theorem runErased_eq (template : List Bool) (code : List Instruction) (memory : List RationalWord) :
    runErased template code memory=(run template code memory).memory := by
  induction code generalizing memory with
  | nil => rfl
  | cons i code ih => simp only [runErased,run,stepErased_eq,ih]

/-- The erased executable still has the exact original register growth. -/
theorem runErased_length (template : List Bool) (code : List Instruction) (memory : List RationalWord) :
    (runErased template code memory).length=memory.length+code.length := by
  rw [runErased_eq,run_length]

open SemiprimeSourceMemoryTrace SemiprimeSourceProgramStorage
open SemiprimeReportPolynomialGrowth

/-- Explicit original-input polynomial majorant for auxiliary scan/copy frames
and a single step report. Arithmetic primitive-internal scratch is separate. -/
def stepAuxBudget (M W B : ℕ) : ℕ :=
  2*M*(M*(2*W+2)+4*W+2*B+2*((M+1)*(8*W+15*B+30))+19)+
    (M+1)*(M*(2*W+1)+M+M*(8*W+9)+4)+stepBudget M W B+6

/-- All actual nested scan/copy return records attached to one executed instruction. -/
def stepAuxCells (template : List Bool) (i : Instruction) (memory : List RationalWord) : ℕ :=
  ((readFrames memory i.left).map frameCells).sum+
    ((readFrames memory i.right).map frameCells).sum+
    ((copyReturns memory).map copyReturnCells).sum+(step template i memory).clock+6

/-- The concrete instruction auxiliary counter is bounded without a supplied
intermediate-state or desired runtime cap. -/
theorem stepAuxCells_bound (template : List Bool) (i : Instruction)
    (memory : List RationalWord) (B : ℕ) (hW : 1 ≤ template.length) (hB : 1 ≤ B)
    (hi : i.left.length ≤ B ∧ i.right.length ≤ B)
    (hm : ∀ x∈memory,Width x template.length) :
    stepAuxCells template i memory ≤ stepAuxBudget memory.length template.length B := by
  have hl := readFrames_cells memory i.left template.length B hW hB hi.1 hm
  have hr := readFrames_cells memory i.right template.length B hW hB hi.2 hm
  have hc := copyReturns_cells memory template.length hm
  have hs := step_clock template i memory B hW hB hi.1 hi.2 hm
  unfold stepAuxCells stepAuxBudget
  nlinarith

/-- Increasing the original memory cap preserves this explicit auxiliary envelope. -/
theorem stepAuxBudget_mono {M N W B : ℕ} (h : M ≤ N) :
    stepAuxBudget M W B ≤ stepAuxBudget N W B := by
  unfold stepAuxBudget stepBudget
  gcongr

/-- Same code/store recursion, retaining every nested auxiliary field view and
actual recursive run report counter. The base call contributes a return frame. -/
def programAuxCells (template : List Bool) : List Instruction → List RationalWord → ℕ
  | [],_ => 1
  | i::code,memory =>
    stepAuxCells template i memory+
      programAuxCells template code (step template i memory).memory+
      (run template code (step template i memory).memory).clock+3

/-- Closed original-input bound for ALL instruction-level auxiliary return frames. -/
theorem programAuxCells_bound (template : List Bool) (code : List Instruction)
    (memory : List RationalWord) (B : ℕ) (hW : 1 ≤ template.length) (hB : 1 ≤ B)
    (hi : ∀ i∈code,i.left.length ≤ B ∧ i.right.length ≤ B)
    (hm : ∀ x∈memory,Width x template.length) :
    programAuxCells template code memory ≤
      code.length*(stepAuxBudget (memory.length+code.length) template.length B+
        code.length*(stepBudget (memory.length+code.length) template.length B+3)+4)+1 := by
  induction code generalizing memory with
  | nil => simp [programAuxCells]
  | cons i code ih =>
    have hs := stepAuxCells_bound template i memory B hW hB (hi i List.mem_cons_self) hm
    have hn := step_width template i memory hm
    have hic := fun j hj => hi j (List.mem_cons_of_mem i hj)
    have ht := ih (step template i memory).memory hic hn
    have hc := run_clock template code (step template i memory).memory B hW hB hic hn
    have hlen := step_length template i memory
    rw [hlen] at ht hc
    have hs' := hs.trans (stepAuxBudget_mono
      (show memory.length ≤ memory.length+(i::code).length by simp))
    simp only [programAuxCells,List.length_cons] at hs' ht hc ⊢
    have he : memory.length+1+code.length=memory.length+(code.length+1) := by omega
    rw [he] at ht hc
    nlinarith

/-- Fixed polynomial witnesses for execution-linked auxiliary fields and copied
persistent-store payloads together. This does not count primitive circuit scratch. -/
theorem auxiliary_polynomial : ∃ C k : ℕ,∀ M T W B S,
    M ≤ S → T ≤ S → W ≤ S → B ≤ S →
    T*(stepAuxBudget (M+T) W B+T*(stepBudget (M+T) W B+3)+4)+1+
      (T+1)*(M+T)*(2*W+1) ≤ C*(S+1)^k := by
  have hp : Bound (fun S =>
      S*(stepAuxBudget (S+S) S S+S*(stepBudget (S+S) S S+3)+4)+1+
        (S+1)*(S+S)*(2*S+1)) := by
    unfold stepAuxBudget stepBudget
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  refine ⟨C,k,?_⟩
  intro M T W B S hM hT hW hB
  apply le_trans _ (h S)
  unfold stepAuxBudget stepBudget
  dsimp only
  gcongr

end RiemannGaussian.SemiprimeSourceProgramErasure
