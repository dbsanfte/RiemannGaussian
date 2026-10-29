/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsEncoding
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRelay
/-! # Every actual paired row has the entire ordered original marked table
Input constructors execute the real marked source; all other constructors
relay exact integer0/1 data. No equality of reduced products is lifted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTables
open SemiprimeD1StackMarkedRootRecordsEncoding
open SemiprimeD1TensorTapeCodec (tape)
open SemiprimeD1TensorTables SemiprimeMacroGraph SemiprimeMacroParameters SemiprimeBitArithmetic
namespace Old
export SemiprimeD1BooleanRootTablesOriginal (reference)
end Old
namespace New
export SemiprimeD1StackMarkedPublicInputTableOriginal (reference)
end New
/-- Generic paired descriptor with arbitrary physical scope payloads. -/
def paired {r t digits : Nat} (v : SubdividedVertex r t digits) (scope : List (List Bool))
    (old : List Bool) : Row :=
  ⟨scope,old,SemiprimeD1EdgeCatalogueEncoding.vertex v,inputSide v,original_shape v⟩
/-- ALL original constructor families, in their exact original ordered finite scope. -/
theorem table_for_vertex (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) (v : SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits))
    (scope : List (List Bool)) (ha : scope.length=subdividedArity v) :
    newTable bits (paired v scope (tape (Old.reference (bitValue bits) hN v)))=
      tape (New.reference (bitValue bits) hN v) := by
  rcases v with v|v
  · cases v with
    | input side i =>
      change SemiprimeD1StackMarkedPublicInputTableExecution.outputTape bits (List.replicate i.val true)
        (decide (side=1)) scope=_
      exact SemiprimeD1StackMarkedPublicInputTableOriginal.tape_original bits hc hN side i
        (List.replicate i.val true) (List.length_replicate ..) scope ha
    | first tr j | scale tr j k | second tr k | product k | carry k | orGate side i | inputCheck side =>
      apply congrArg (fun t => tape t)
      exact SemiprimeD1StackMarkedRootRecordsRelay.relay_table _ _ _ (fun _ => rfl)
    | carryInitial | carryTerminal =>
      apply congrArg (fun t => tape t)
      exact SemiprimeD1StackMarkedRootRecordsRelay.relay_table _ _ _ (fun _ => rfl)
  · apply congrArg (fun t => tape t)
    exact SemiprimeD1StackMarkedRootRecordsRelay.relay_table _ _ _ (fun _ => rfl)
/-- The old full-factor source's local table cast changes no literal byte. -/
theorem old_local_tape (N : Nat) (hN : 0 < N) (f : Fin (SemiprimePublicAcquiredExecution.factorCount N)) :
    tape (SemiprimeD1StackFullFactorCatalogueOriginal.localVertex N hN f).table=
      tape (Old.reference N hN (SemiprimeD1BooleanFactorCatalogueIndices.vertex N f)) :=
  SemiprimeD1StackBooleanRecordOriginal.tape_cast
    (SemiprimeD1StackFullFactorCatalogueOriginal.numeric_arity N f).symm _
/-- Exact WHOLE new table for every actual original factor, including both input sides. -/
theorem original_table (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) (f : Fin (SemiprimePublicAcquiredExecution.factorCount (bitValue bits))) :
    newTable bits (originalRow (bitValue bits) hN f)=
      tape (New.reference (bitValue bits) hN (SemiprimeD1BooleanFactorCatalogueIndices.vertex (bitValue bits) f)) := by
  change newTable bits (paired (SemiprimeD1BooleanFactorCatalogueIndices.vertex (bitValue bits) f)
    ((SemiprimeD1BooleanFactorCatalogueIndicesOriginal.numericPorts (bitValue bits) f).map (fun p => List.replicate p true))
    (tape (SemiprimeD1StackFullFactorCatalogueOriginal.localVertex (bitValue bits) hN f).table))=_
  rw [old_local_tape]
  apply table_for_vertex bits hc hN
  rw [List.length_map]
  exact SemiprimeD1StackFullFactorCatalogueOriginal.numeric_arity _ _
/-- Entire original marked tables have canonical compact coefficients at NEW2ell precision. -/
theorem marked_good (N : Nat) (hN : 0 < N) (v : SemiprimePublicAcquiredExecution.PublicVertex N) :
    Good ⟨[],SemiprimeD1PackedMomentPrecision.precision N⟩ (New.reference N hN v) := by
  unfold New.reference
  apply build_good
  intro raw _
  refine ⟨rfl,?_⟩
  intro word hw
  have he := List.mem_singleton.mp hw
  subst word
  refine ⟨SemiprimeSourceHistogramPortKeys.encodeKey_compact _,?_⟩
  apply SemiprimeSourceCompactBits.compact_length_of_lt _
    (SemiprimeSourceHistogramPortKeys.encodeKey_compact _)
  rw [SemiprimeSourceHistogramPortKeys.encodeKey_value]
  exact SemiprimeD1PackedMomentPrecision.coefficient_fits N hN v _
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTables
