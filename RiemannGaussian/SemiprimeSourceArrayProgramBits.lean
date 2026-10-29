/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramCompiler
import RiemannGaussian.SemiprimeSourceArrayProgramAcquisition

/-! # Actual physical execution of generated original source coefficient programs
The entry point accepts the original finite expression and dimensions. It
extracts/encodes its actual literal bank, generates addresses, executes the
Boolean interpreter and performs an actual output scan. The remaining scalar
source/compiler metadata work is explicitly distinguished from the bit ledger.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceArrayProgramBits
open SemiprimeRationalBits SemiprimeSourceArrayProgramAcquisition
open SemiprimeSourceArrayProgramCompiler SemiprimeSourceArrayProgramLowering
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation

/-- Actual total register frontier of the original generated program. -/
def frontier (J : ℕ) (p : PolynomialCode ℚ) : ℕ := (bank p).length+(program J p).code.length

/-- Executed store with separate physical and literal/address-acquisition ledgers. -/
structure Execution where
  /-- Every register produced by the actual interpreter. -/
  memory : List RationalWord
  /-- Literal encoding, address digit generation and template cells.
  Original source syntax construction and compiler metadata are separate. -/
  acquisitionWork : ℕ
  /-- Every interpreted operation, operand scan and full store copy. -/
  bitWork : ℕ

/-- Compile and execute from the actual original expression; no code or word bank is supplied. -/
def execute (bits J : ℕ) (p : PolynomialCode ℚ) : Execution :=
  let inputs := acquireBank bits (bank p)
  let source := program J p
  let initial := (bank p).length
  let B := initial+source.code.length+1
  let instructions := lower initial B initial source.code
  let template := List.replicate (bits+1) false
  let result := SemiprimeSourceProgramBits.run template instructions.code inputs.words
  ⟨result.memory,inputs.scalarWork+instructions.work+2*(bits+1)+5,result.clock⟩

/-- The physical backend preserves its chosen word width on every executed input. -/
theorem execute_width (bits J : ℕ) (p : PolynomialCode ℚ) :
    ∀ w∈(execute bits J p).memory,Width w (bits+1) := by
  have h := SemiprimeSourceProgramBits.run_width (List.replicate (bits+1) false)
    (lower (bank p).length (frontier J p+1) (bank p).length (program J p).code).code
    (acquireBank bits (bank p)).words
    (by simpa only [List.length_replicate] using acquireBank_width bits (bank p))
  simpa only [execute,List.length_replicate,frontier] using h

/-- Original bank bounds and the derived source fit invariant give exact execution. -/
theorem execute_spec (bits J : ℕ) (p : PolynomialCode ℚ)
    (hb : ∀ q∈bank p,q.num.natAbs ≤ 2^bits ∧ q.den ≤ 2^bits)
    (hs : Safe (bits+1) (program J p).code (bank p).length (initialEnv p)) :
    Represents (bank p).length (frontier J p)
      ((execute bits J p).memory.map RationalWord.value)
      (SemiprimeSourceArrayProgramIR.evaluate (program J p).code (bank p).length (initialEnv p)) ∧
      (∀ w∈(execute bits J p).memory,w.Valid) ∧
      (∀ w∈(execute bits J p).memory,Width w (bits+1)) := by
  have hi := acquireBank_spec bits (bank p) hb
  have hm : Represents (bank p).length (bank p).length
      ((acquireBank bits (bank p)).words.map RationalWord.value) (initialEnv p) := by
    rw [hi.1]
    exact represents_initial (bank p)
  have hr := run_refines (bank p).length (frontier J p+1) (bank p).length
    (program J p).code (List.replicate (bits+1) false) (acquireBank bits (bank p)).words
    (initialEnv p) (Nat.le_refl _) (program_spec J p).1
    (frontier_fits (bank p).length (program J p).code) hm hi.2
    (by simpa only [List.length_replicate] using hs)
  exact ⟨hr.1,hr.2,execute_width bits J p⟩

/-- Structural register growth does not depend on an output fit assumption. -/
theorem execute_length (bits J : ℕ) (p : PolynomialCode ℚ) :
    (execute bits J p).memory.length=frontier J p := by
  simp only [execute,SemiprimeSourceProgramBits.run_length,acquireBank_length,lower_length,frontier]

/-- An exact acquisition ledger and a bound for the real physical interpreter. -/
theorem execute_work (bits J : ℕ) (p : PolynomialCode ℚ) :
    (execute bits J p).acquisitionWork=
      (bank p).length*(8*(bits+1)+16)+1+
        (program J p).code.length*(8*(frontier J p+1)+17)+1+2*(bits+1)+5 ∧
    (execute bits J p).bitWork ≤
      (program J p).code.length*
        (SemiprimeSourceProgramBits.stepBudget (frontier J p) (bits+1) (frontier J p+1)+3)+1 := by
  constructor
  · simp only [execute,acquireBank_work,lower_work,frontier];omega
  · have h := run_clock (bank p).length (frontier J p+1) (bank p).length (program J p).code
      (List.replicate (bits+1) false) (acquireBank bits (bank p)).words
      (by simp) (by omega) (by simpa only [List.length_replicate] using acquireBank_width bits (bank p))
    simpa only [acquireBank_length,List.length_replicate,frontier,execute] using h

/-- Computed source coefficient word and the complete joined backend readout ledgers. -/
structure CoefficientRun where
  /-- Actual selected word; there is no rational decoding on the execution path. -/
  word : RationalWord
  /-- Original-literal/address digit acquisition and finite template metadata. -/
  acquisitionWork : ℕ
  /-- Actual interpreter and final memory scan/copy work. -/
  bitWork : ℕ

/-- Execute the generated original program and acquire one coefficient physically. -/
def coefficient (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) : CoefficientRun :=
  let result := execute bits J p
  let out := readout (bank p).length (frontier J p) (frontier J p+1)
    ((program J p).output k) result.memory
  ⟨out.word,result.acquisitionWork+out.scalarWork+3,result.bitWork+out.bitWork+2⟩

/-- The physical output is the ACTUAL original cached-array coefficient.
Original-source specializations discharge both premises from their source constants. -/
theorem coefficient_correct (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) (hk : k < J)
    (hb : ∀ q∈bank p,q.num.natAbs ≤ 2^bits ∧ q.den ≤ 2^bits)
    (hs : Safe (bits+1) (program J p).code (bank p).length (initialEnv p)) :
    (coefficient bits J p k).word.value=
      SemiprimeJetArray.coefficient (SemiprimeSourceCodeArrays.compile J p).coefficients k ∧
      (coefficient bits J p k).word.Valid ∧ Width (coefficient bits J p k).word (bits+1) := by
  have he := execute_spec bits J p hb hs
  have hv := readout_value (bank p).length (frontier J p) (frontier J p+1)
    ((program J p).output k) (execute bits J p).memory _
    (by unfold frontier;omega) ((program_spec J p).2.1 k hk)
    (frontier_fits (bank p).length (program J p).code) he.1
  refine ⟨hv.trans (program_original_coefficient J p k hk),?_,?_⟩
  · exact readout_valid _ _ _ _ _ he.2.1
  · exact readout_width _ _ _ _ _ _ (by omega) he.2.2

/-- Final acquisition and all bit-level backend work have an original-code-size envelope. -/
theorem coefficient_work (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) :
    (coefficient bits J p k).acquisitionWork ≤
      (bank p).length*(8*(bits+1)+16)+1+
        (program J p).code.length*(8*(frontier J p+1)+17)+1+2*(bits+1)+5+
        4*(frontier J p+1)+10 ∧
    (coefficient bits J p k).bitWork ≤
      (program J p).code.length*
        (SemiprimeSourceProgramBits.stepBudget (frontier J p) (bits+1) (frontier J p+1)+3)+1+
        (frontier J p+1)*(8*(bits+1)+15*(frontier J p+1)+30)+2 := by
  have hw := execute_width bits J p
  have hr := readout_work (bank p).length (frontier J p) (frontier J p+1)
    ((program J p).output k) (bits+1) (execute bits J p).memory (by omega) hw
  have he := execute_work bits J p
  rw [execute_length] at hr
  constructor
  · simp only [coefficient,hr.1,he.1];omega
  · simp only [coefficient]
    omega

end RiemannGaussian.SemiprimeSourceArrayProgramBits
