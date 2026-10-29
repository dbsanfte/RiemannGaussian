/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanEntryMachine
import RiemannGaussian.SemiprimeD1RootTensorTables
import RiemannGaussian.SemiprimeD1TensorTapeCodec
import RiemannGaussian.SemiprimeD1JetLiteralLift
/-! # Original fixed Boolean root tables, individually lifted canonical entries -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BooleanRootTables
open SemiprimeD1StackBooleanEntry (Mode)
open SemiprimeD1StackBooleanEntryMachine (arity value)
open SemiprimeD1TensorTables
open SemiprimeD1RootOwnerTables (rootContext)
/-- Canonical false scalar at the original rank-one precision-two root. -/
def zero : Table 0 := .leaf [[]]
/-- Canonical true scalar at the original rank-one precision-two root. -/
def one : Table 0 := .leaf [[true]]
/-- All local tables are LITERAL data, fixed before N; first port is outermost
and false precedes true at every fork. No supplied producer/predicate is used. -/
def table : (mode : Mode)→Table (arity mode)
  | .orGate => .fork (.fork (.fork one zero) (.fork zero one))
      (.fork (.fork zero one) (.fork zero one))
  | .inputCheck => .fork zero one
  | .equality => .fork (.fork one zero) (.fork zero one)
/-- Actual tagged-tree bytes, not a requested encoded answer. -/
def bytes (mode : Mode) : List Bool := SemiprimeD1TensorTapeCodec.tape (table mode)
/-- Literal byte lengths include every branch, leaf, word frame and final tag. -/
theorem bytes_length (mode : Mode) : (bytes mode).length=
    match mode with | .orGate => 47 | .inputCheck => 11 | .equality => 23 := by cases mode <;> rfl
/-- Every literal stored entry has the actual original root context/precision. -/
theorem good (mode : Mode) : Good rootContext (table mode) := by
  cases mode <;> simp [table,one,zero,Good,GoodWords,rootContext,
    SemiprimeD1JetAxes.Context.rank,SemiprimeSourceCompactBits.Compact]
/-- Exact original ordered local semantics, including all false entries. -/
theorem entry (mode : Mode) (input : Fin (arity mode)→Bool) :
    valueAt (table mode) input=[if value mode input then [true] else []] := by
  cases mode with
  | orGate =>
    cases h0:input 0 <;> cases h1:input 1 <;> cases h2:input 2 <;>
      simp [table,one,zero,valueAt,value,h0,h1,h2]
  | inputCheck => cases h0:input 0 <;> simp [table,one,zero,valueAt,value,h0]
  | equality => cases h0:input 0 <;> cases h1:input 1 <;> simp [table,one,zero,valueAt,value,h0,h1]
/-- Each entry's literal integer coefficient is 0 or1 BEFORE any product.
This does not lift a product already reduced modulo the parent precision. -/
theorem entry_integer (mode : Mode) (input : Fin (arity mode)→Bool) :
    (SemiprimeBitArithmetic.bitValue ((valueAt (table mode) input)[0]?.getD []):ℤ)=
      if value mode input then 1 else 0 := by
  rw [entry]
  cases h:value mode input <;> simp [SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat]
/-- The ACTUAL integral old-jet coefficient of EACH literal entry is 0 or1,
not an integer lift of an already multiplied/reduced tensor contraction. -/
theorem literal_entry_coefficient (mode : Mode) (input : Fin (arity mode)→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (valueAt (table mode) input))=
      if value mode input then 1 else 0 := by
  rw [SemiprimeD1JetLiteralLift.literal_coefficient [] _ (by simp) 0 (by decide),entry]
  cases h:value mode input <;> simp [SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat]
/-- At every precision the SAME individually acquired integer entry reduces
correctly; this invokes only the legitimate integral coefficient reduction. -/
theorem entry_reduce (mode : Mode) (input : Fin (arity mode)→Bool) (p : ℕ) :
    SemiprimeD1JetScalarMap.scalarMap (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1DyadicInteger.reduction p)
      (SemiprimeD1JetLiteralLift.literal [] (valueAt (table mode) input))=
      SemiprimeD1JetInterpretation.interpret ⟨[],p⟩ (valueAt (table mode) input) :=
  SemiprimeD1JetLiteralLift.literal_reduce [] p _
end RiemannGaussian.SemiprimeD1BooleanRootTables
