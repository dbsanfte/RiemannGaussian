/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OrdinalBankSpec
/-! # Physical unary occurrence query into the actually generated padded bank
This reuses the actual preserving reader, rather than building a second bank or
using an ID getter. The query is a physical marker list, not a supplied ID word.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackOrdinalBankRead
open SemiprimeD1StackJetRead
open SemiprimeD1StackJetReadExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OrdinalBankSpec

/-- Actual linked-reader source trace, with bank retained and query/work cleared. -/
theorem read_run (M : ℕ) (query : List Bool) :
    SemiprimeD1StackCalls.run program (totalTime query (words M))
      (state (some .start) none none (vectorBits (words M)) [] query [] [] [] [] [])=
    some (state none none none (vectorBits (words M)) [] [] [] [] (idAt M query.length) [] []) :=
  source_run query (words M)

/-- Physical bank lookup returns the canonical ordinal, without a Compact premise. -/
theorem read_value (M : ℕ) (query : List Bool) (h : query.length<M) :
    SemiprimeBitArithmetic.bitValue (idAt M query.length)=query.length := id_value _ _ h

/-- Every valid lookup has the COMMON acquired M-bit width. -/
theorem read_length (M : ℕ) (query : List Bool) (h : query.length<M) :
    (idAt M query.length).length=M := id_length _ _ h

/-- The actual preserving read is polynomial in physical bank/query inventory. -/
theorem read_clock (M : ℕ) (query : List Bool) :
    totalTime query (words M)≤30*(2*M*M+2*M+query.length+3) := by
  have h:=totalTime_le query (words M)
  rw [bank_bytes] at h
  unfold timeBound at h
  omega

end RiemannGaussian.SemiprimeD1StackOrdinalBankRead
