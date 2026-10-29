/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayGeneratedBits
import RiemannGaussian.SemiprimeSourceInterpolationProgramBits

/-! # Original source entry point with acquired code generation retained
This entry point acquires the original expression's code/bank once, runs the
physical interpreter and returns its actual selected coefficient word. Both
generic fit and bank-input premises are discharged from original data. Original
parity, prescription and syntax construction still have native scalar interfaces;
this is not the full public factorizer's primitive-bit clock theorem.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceInterpolationGeneratedBits
open SemiprimeRationalBits SemiprimeSourceInterpolationProgramBits
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Actual original-data entry point, including tracked cached-code generation. -/
def acquire {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) (k : ℕ) :
    SemiprimeSourceArrayProgramBits.CoefficientRun :=
  SemiprimeSourceArrayGeneratedBits.coefficient (SemiprimeSourceInterpolationBits.stateBits A Q R)
    (R+1) (source A R a y) k

/-- No literal-bank, coefficient-answer or intermediate-fit premise remains. -/
theorem acquire_correct {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1)
    (k : ℕ) (hk : k < R+1) :
    (acquire A R a y k).word.value =
      SemiprimeJetArray.coefficient
        (SemiprimeSourceInterpolationExecution.row (SemiprimeBinomialExecution.parity A R) a 0 y).coefficients k ∧
      (acquire A R a y k).word.Valid ∧
      Width (acquire A R a y k).word (SemiprimeSourceInterpolationBits.stateBits A Q R+1) :=
  SemiprimeSourceArrayGeneratedBits.coefficient_correct _ _ _ k hk
    (source_bank_bounds A R a y) (source_program_safe A R a y)

/-- Actual generated-source work retains the generator and the verified complete backend. -/
theorem acquire_work_components {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1) (k : ℕ) :
    (acquire A R a y k).acquisitionWork+(acquire A R a y k).bitWork ≤
      (SemiprimeSourceArrayProgramGeneration.generate (R+1) (source A R a y)).work+
        ((SemiprimeSourceInterpolationProgramBits.acquire A R a y k).acquisitionWork+
          (SemiprimeSourceInterpolationProgramBits.acquire A R a y k).bitWork)+
        (SemiprimeSourceArrayProgramCompiler.bank (source A R a y)).length+20 :=
  SemiprimeSourceArrayGeneratedBits.coefficient_totalWork _ _ _ k

end RiemannGaussian.SemiprimeSourceInterpolationGeneratedBits
