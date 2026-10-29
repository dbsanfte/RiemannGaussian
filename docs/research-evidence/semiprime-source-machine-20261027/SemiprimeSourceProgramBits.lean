/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceMemoryBits

/-! # Finite rational instructions with paid Boolean addresses
Every operand is acquired by an actual sequential Boolean-address scan. Each
instruction executes the existing Boolean arithmetic/GCD circuit and copies the
persistent store. The generic height condition is discharged separately by
original-source instances; it is not a whole-program cost oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceProgramBits
open SemiprimeBitArithmetic SemiprimeRationalBits SemiprimeSourceMemoryBits

/-- A finite arithmetic opcode and two physical little-endian addresses. -/
structure Instruction where
  /-- The literal arithmetic opcode. -/
  operation : Operation
  /-- First operand address, including its padding. -/
  left : List Bool
  /-- Second operand address (also scanned for unary opcodes). -/
  right : List Bool

/-- Mathematical instruction output; this is never called by the physical interpreter. -/
def Instruction.value (i : Instruction) (state : List ℚ) : ℚ :=
  i.operation.value ((state[bitValue i.left]?).getD 0) ((state[bitValue i.right]?).getD 0)

/-- Actual computed store and complete retained bit/scan/copy work. -/
structure Report where
  /-- Newest register first, all values still physical words. -/
  memory : List RationalWord
  /-- Charged arithmetic, address scans, copies and list control. -/
  clock : ℕ

/-- Execute one instruction and preserve memory by a full paid copy. -/
def step (template : List Bool) (i : Instruction) (memory : List RationalWord) : Report :=
  let left := readWord memory i.left
  let right := readWord memory i.right
  let out := executeOperation i.operation left.word right.word template
  let saved := copyMemory memory
  ⟨out.word::saved.words,left.clock+right.clock+out.clock+saved.clock+5⟩

/-- Literal finite instruction traversal; no semantic value controls execution. -/
def run (template : List Bool) : List Instruction → List RationalWord → Report
  | [],memory => ⟨memory,1⟩
  | i::code,memory =>
    let current := step template i memory
    let rest := run template code current.memory
    ⟨rest.memory,current.clock+rest.clock+3⟩

/-- Specification of the same finite instruction sequence over rational values. -/
def evaluate : List Instruction → List ℚ → List ℚ
  | [],state => state
  | i::code,state => evaluate code (i.value state::state)

/-- Every computed intermediate fits the public width. Concrete source proofs must
establish this from original inputs, never from a supplied execution answer. -/
def Safe (W : ℕ) : List Instruction → List ℚ → Prop
  | [],_ => True
  | i::code,state => Fits (i.value state) W ∧ Safe W code (i.value state::state)

/-- Register growth is exactly one physical word pair per executed instruction. -/
theorem step_length (template : List Bool) (i : Instruction) (memory : List RationalWord) :
    (step template i memory).memory.length=memory.length+1 := by
  simp only [step,copyMemory_words,List.length_cons]

/-- The whole interpreter's finite store shape is known without an arithmetic-height premise. -/
theorem run_length (template : List Bool) (code : List Instruction) (memory : List RationalWord) :
    (run template code memory).memory.length=memory.length+code.length := by
  induction code generalizing memory with
  | nil => simp [run]
  | cons i code ih => simp only [run,ih,step_length,List.length_cons]; omega

/-- Every output instruction word has the chosen physical width, even before a fit proof. -/
theorem step_width (template : List Bool) (i : Instruction) (memory : List RationalWord)
    (h : ∀ x∈memory,Width x template.length) :
    ∀ x∈(step template i memory).memory,Width x template.length := by
  intro x hx
  simp only [step,copyMemory_words,List.mem_cons] at hx
  rcases hx with rfl | hx
  · have hw := fitRationalBits_width
      (rawOperation i.operation (readWord memory i.left).word (readWord memory i.right).word).word template
    exact ⟨hw.1.le,hw.2.le⟩
  · exact h x hx

/-- All later memory cells have the same bounded physical width. -/
theorem run_width (template : List Bool) (code : List Instruction) (memory : List RationalWord)
    (h : ∀ x∈memory,Width x template.length) :
    ∀ x∈(run template code memory).memory,Width x template.length := by
  induction code generalizing memory with
  | nil => exact h
  | cons i code ih => exact ih _ (step_width template i memory h)

/-- Semantic memory lookup is exactly the interpretation of the physical address scan. -/
theorem readWord_value (memory : List RationalWord) (address : List Bool) :
    (readWord memory address).word.value=
      ((memory.map RationalWord.value)[bitValue address]?).getD 0 := by
  rw [readWord_word,List.getElem?_map]
  cases memory[bitValue address]? with
  | none => simp [SemiprimeRationalBits.zeroWord,RationalWord.value,
      SemiprimeBitIndexClipping.SignedWord.value,bitValue,bitNat]
  | some x => rfl

/-- Single-step value/validity preservation, including every original operand read. -/
theorem step_correct (template : List Bool) (i : Instruction) (memory : List RationalWord)
    (hv : ∀ x∈memory,x.Valid) (hf : Fits (i.value (memory.map RationalWord.value)) template.length) :
    (step template i memory).memory.map RationalWord.value=
      i.value (memory.map RationalWord.value)::memory.map RationalWord.value ∧
    ∀ x∈(step template i memory).memory,x.Valid := by
  have hx := readWord_valid memory i.left hv
  have hy := readWord_valid memory i.right hv
  have he : i.operation.value (readWord memory i.left).word.value (readWord memory i.right).word.value=
      i.value (memory.map RationalWord.value) := by rw [readWord_value,readWord_value];rfl
  have ho := executeOperation_correct i.operation (readWord memory i.left).word
    (readWord memory i.right).word template hx hy (he.symm ▸ hf)
  constructor
  · simp only [step,copyMemory_words,List.map_cons,ho.1,he]
  · intro x h
    simp only [step,copyMemory_words,List.mem_cons] at h
    rcases h with rfl | h
    · exact ho.2.1
    · exact hv x h

/-- The physical sequence computes the same finite rational program, provided its
ORIGINAL-derived fit invariant is established at every actual instruction. -/
theorem run_correct (template : List Bool) (code : List Instruction) (memory : List RationalWord)
    (hv : ∀ x∈memory,x.Valid) (hf : Safe template.length code (memory.map RationalWord.value)) :
    (run template code memory).memory.map RationalWord.value=evaluate code (memory.map RationalWord.value) ∧
      ∀ x∈(run template code memory).memory,x.Valid := by
  induction code generalizing memory with
  | nil => exact ⟨rfl,hv⟩
  | cons i code ih =>
    have hs := step_correct template i memory hv hf.1
    have hh := ih (step template i memory).memory hs.2 (hs.1.symm ▸ hf.2)
    simpa only [run,evaluate,hs.1] using hh

/-- Numeric one-step bound from actual memory cells, payload width and address width. -/
def stepBudget (M W B : ℕ) : ℕ :=
  2*(M+1)*(8*W+15*B+30)+20000*(W+1)^3+M*(8*W+9)+6

/-- Every address scan, rational circuit and complete persistent-store copy stays paid. -/
theorem step_clock (template : List Bool) (i : Instruction) (memory : List RationalWord)
    (B : ℕ) (hW : 1 ≤ template.length) (hB : 1 ≤ B)
    (hl : i.left.length ≤ B) (hr : i.right.length ≤ B)
    (hm : ∀ x∈memory,Width x template.length) :
    (step template i memory).clock ≤  stepBudget memory.length template.length B := by
  have hx := readWord_width memory i.left template.length hW hm
  have hy := readWord_width memory i.right template.length hW hm
  have hc := executeOperation_cost i.operation (readWord memory i.left).word
    (readWord memory i.right).word template hx hy (Nat.le_refl _)
  have hlc := readWord_clock memory i.left template.length B hB hl hm
  have hrc := readWord_clock memory i.right template.length B hB hr hm
  have hm' := copyMemory_clock memory template.length hm
  unfold step stepBudget
  dsimp only
  nlinarith

/-- Increasing the original memory-cell cap preserves the physical one-step bound. -/
theorem stepBudget_mono {M N W B : ℕ} (h : M ≤ N) : stepBudget M W B ≤  stepBudget N W B := by
  unfold stepBudget
  gcongr

/-- Uniform execution bound, with every retained store growing from actual input length.
No scalar answer or desired runtime bound is a premise. -/
theorem run_clock (template : List Bool) (code : List Instruction) (memory : List RationalWord)
    (B : ℕ) (hW : 1 ≤ template.length) (hB : 1 ≤ B)
    (hc : ∀ i∈code,i.left.length ≤ B ∧ i.right.length ≤ B)
    (hm : ∀ x∈memory,Width x template.length) :
    (run template code memory).clock ≤ 
      code.length*(stepBudget (memory.length+code.length) template.length B+3)+1 := by
  induction code generalizing memory with
  | nil => simp [run]
  | cons i code ih =>
    have hi := hc i List.mem_cons_self
    have hs := step_clock template i memory B hW hB hi.1 hi.2 hm
    have ht := ih (step template i memory).memory
      (fun j hj => hc j (List.mem_cons_of_mem i hj)) (step_width template i memory hm)
    rw [step_length] at ht
    have he : memory.length+1+code.length=memory.length+(i::code).length := by simp;omega
    rw [he] at ht
    have hs' := hs.trans (stepBudget_mono (show memory.length ≤ memory.length+(i::code).length by omega))
    simp only [run,List.length_cons] at ⊢
    simp only [List.length_cons] at ht hs'
    nlinarith

end RiemannGaussian.SemiprimeSourceProgramBits
