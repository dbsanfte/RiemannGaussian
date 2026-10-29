/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramBits
import RiemannGaussian.SemiprimeSourceArrayProgramGeneration

/-! # One acquired source-code generator joined to physical execution and readout
The generator runs once, and its returned bank, cached code size and constant-size
output descriptor are used directly. The retained scalar ledger includes actual
syntax traversal, constant lookup, append copying, address generation and final
output-ID acquisition. Native scalar metadata remains distinct from primitive
Boolean interpreter work.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeSourceArrayGeneratedBits
open SemiprimeRationalBits SemiprimeSourceArrayProgramAcquisition
open SemiprimeSourceArrayProgramCompiler SemiprimeSourceArrayProgramLowering
open SemiprimeSourceArrayProgramGeneration
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation

/-- The actual returned code is exactly the verified original compiler program. -/
theorem generated_code (J : ℕ) (p : PolynomialCode ℚ) :
    (generate J p).result.compiled.code=(program J p).code :=
  congrArg Block.code (generate_block J p)

/-- Cached allocation size is the actual verified code length. -/
theorem generated_size (J : ℕ) (p : PolynomialCode ℚ) :
    (generate J p).result.compiled.size=(program J p).code.length := by
  rw [(generate J p).result.compiled.size_eq,generated_code]

/-- Actual constant-size output descriptors have the original stable-register meaning. -/
theorem generated_output (J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) :
    (generate J p).result.shape.value k=(program J p).output k :=
  congrArg (fun b : Block => b.output k) (generate_block J p)

/-- Generate ONCE, encode its acquired bank, execute its code and read the actual output ID. -/
def coefficient (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) :
    SemiprimeSourceArrayProgramBits.CoefficientRun :=
  let generated := generate J p
  let initial := generated.bank.length
  let final := initial+generated.result.compiled.size
  let B := final+1
  let inputs := acquireBank bits generated.bank
  let instructions := lower initial B initial generated.result.compiled.code
  let result := SemiprimeSourceProgramBits.run (List.replicate (bits+1) false)
    instructions.code inputs.words
  let id := generated.result.shape.read k
  let out := readout initial final B id.value result.memory
  ⟨out.word,generated.work+inputs.scalarWork+instructions.work+id.work+out.scalarWork+
    2*(bits+1)+initial+20,result.clock+out.bitWork+2⟩

/-- Code-generation caching changes no physical output bit. -/
theorem coefficient_word (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) :
    (coefficient bits J p k).word=(SemiprimeSourceArrayProgramBits.coefficient bits J p k).word := by
  simp only [coefficient,generate_bank,generated_size,generated_code,Shape.read_value,generated_output,
    SemiprimeSourceArrayProgramBits.coefficient,SemiprimeSourceArrayProgramBits.execute,
    SemiprimeSourceArrayProgramBits.frontier]

/-- The joined code generator retains precisely the same actual Boolean backend execution. -/
theorem coefficient_bitWork (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) :
    (coefficient bits J p k).bitWork=(SemiprimeSourceArrayProgramBits.coefficient bits J p k).bitWork := by
  simp only [coefficient,generate_bank,generated_size,generated_code,Shape.read_value,generated_output,
    SemiprimeSourceArrayProgramBits.coefficient,SemiprimeSourceArrayProgramBits.execute,
    SemiprimeSourceArrayProgramBits.frontier]

/-- The scalar ledger pays generated code, output descriptor lookup and bank traversal as well. -/
theorem coefficient_acquisitionWork (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) :
    (coefficient bits J p k).acquisitionWork ≤
      (generate J p).work+(SemiprimeSourceArrayProgramBits.coefficient bits J p k).acquisitionWork+
        (bank p).length+20 := by
  have hid := (generate J p).result.shape.read_work k
  simp only [coefficient,generate_bank,generated_size,generated_code,Shape.read_value,generated_output,
    SemiprimeSourceArrayProgramBits.coefficient,SemiprimeSourceArrayProgramBits.execute,
    SemiprimeSourceArrayProgramBits.frontier]
  omega

/-- Join generated-code acquisition with both retained coefficient backend ledgers. -/
theorem coefficient_totalWork (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) :
    (coefficient bits J p k).acquisitionWork+(coefficient bits J p k).bitWork ≤
      (generate J p).work+
        ((SemiprimeSourceArrayProgramBits.coefficient bits J p k).acquisitionWork+
          (SemiprimeSourceArrayProgramBits.coefficient bits J p k).bitWork)+(bank p).length+20 := by
  have ha := coefficient_acquisitionWork bits J p k
  rw [coefficient_bitWork]
  omega

/-- Original-data bank and instruction-fit proofs now apply to the generated runtime itself. -/
theorem coefficient_correct (bits J : ℕ) (p : PolynomialCode ℚ) (k : ℕ) (hk : k < J)
    (hb : ∀ q∈bank p,q.num.natAbs ≤ 2^bits ∧ q.den ≤ 2^bits)
    (hs : Safe (bits+1) (program J p).code (bank p).length (initialEnv p)) :
    (coefficient bits J p k).word.value=
      SemiprimeJetArray.coefficient (SemiprimeSourceCodeArrays.compile J p).coefficients k ∧
      (coefficient bits J p k).word.Valid ∧ Width (coefficient bits J p k).word (bits+1) := by
  rw [coefficient_word]
  exact SemiprimeSourceArrayProgramBits.coefficient_correct bits J p k hk hb hs

end RiemannGaussian.SemiprimeSourceArrayGeneratedBits
