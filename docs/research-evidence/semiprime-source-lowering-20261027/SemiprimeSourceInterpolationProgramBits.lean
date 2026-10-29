/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramBits
import RiemannGaussian.SemiprimeSourceArrayCompilerSafe

/-! # Original universal source interpolation through the physical compiler
The supplied data are original dimensions, two universal source types and a
coefficient index. Every literal and intermediate fit is proved from those data.
The original parity/prescription/syntax construction and compiler metadata still
have native scalar interfaces; no whole original-input bit clock is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceInterpolationProgramBits
open SemiprimeRationalBits SemiprimeSourceArrayProgramCompiler
open SemiprimeSourceArrayProgramLowering SemiprimeSourceArrayProgramBits
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Actual finite source expression acquired from original parity and universal types. -/
abbrev source {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) :=
  SemiprimeSourceInterpolationExecution.code (SemiprimeBinomialExecution.parity A R) a 0 y

/-- Every encoded original bank literal fits from the actual source constructor. -/
theorem source_bank_bounds {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) :
    ∀ q∈bank (source A R a y),
      q.num.natAbs ≤ 2^SemiprimeSourceInterpolationBits.stateBits A Q R ∧
      q.den ≤ 2^SemiprimeSourceInterpolationBits.stateBits A Q R := by
  intro q hq
  simp only [bank,List.mem_cons] at hq
  rcases hq with rfl | rfl | hq
  · norm_num;exact Nat.one_le_two_pow
  · norm_num;exact Nat.one_le_two_pow
  · have h := SemiprimeSourceArrayCompilerSafe.source_literal_bounds A R a y q hq
    exact ⟨h.2,h.1⟩

/-- The actual source-generated program is safe without any intermediate-fit premise. -/
theorem source_program_safe {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) :
    Safe (SemiprimeSourceInterpolationBits.stateBits A Q R+1)
      (program (R+1) (source A R a y)).code (bank (source A R a y)).length
      (initialEnv (source A R a y)) := by
  exact SemiprimeSourceArrayCompilerSafe.source_safe A R 0 1
    (bank (source A R a y)).length (literalId (source A R a y)) a y (initialEnv (source A R a y))
    (by rw [bank_length];omega) (by rw [bank_length];omega)
    (by simp [initialEnv,bank]) (by simp [initialEnv,bank]) (bank_literals (source A R a y))

/-- Acquire an actual original source coefficient using the compiled physical path. -/
def acquire {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) (k : ℕ) : CoefficientRun :=
  coefficient (SemiprimeSourceInterpolationBits.stateBits A Q R) (R+1) (source A R a y) k

/-- Unconditional original-data coefficient refinement, validity and physical width. -/
theorem acquire_correct {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1)
    (k : ℕ) (hk : k < R+1) :
    (acquire A R a y k).word.value =
      SemiprimeJetArray.coefficient
        (SemiprimeSourceInterpolationExecution.row (SemiprimeBinomialExecution.parity A R) a 0 y).coefficients k ∧
      (acquire A R a y k).word.Valid ∧
      Width (acquire A R a y k).word (SemiprimeSourceInterpolationBits.stateBits A Q R+1) :=
  coefficient_correct _ _ _ k hk (source_bank_bounds A R a y) (source_program_safe A R a y)

/-- Original syntax bounds give the actual generated initial-bank and code dimensions. -/
theorem source_dimensions {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) :
    (bank (source A R a y)).length ≤ 2+SemiprimeSourceInterpolationHeight.nodeCap Q ∧
      (program (R+1) (source A R a y)).code.length ≤
        SemiprimeSourceInterpolationHeight.nodeCap Q*((R+1)*((R+1)+1)+(R+1)) := by
  have hn := SemiprimeSourceInterpolationHeight.code_nodes A R a y
  constructor
  · rw [bank_length]
    exact Nat.add_le_add_left ((constants_length_le _).trans hn) 2
  · exact (program_code_length _ _).trans (Nat.mul_le_mul_right _ hn)

end RiemannGaussian.SemiprimeSourceInterpolationProgramBits
