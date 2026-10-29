/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsPrimitives
/-! # Real record logging and final reversal with arbitrary retained banks -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsLogger
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackProcedureTrace
namespace S
export SemiprimeD1StackVertexRecordStream (data row recordTime record_run initialize_run reverse_run)
end S
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Real logger input projection; every other actual word is retained. -/
theorem logger_in (bank : Stack → List Bool) :
    Link.DataRel loggerStack bank (S.data (bank ports) (bank table) (bank (aux .history)) (bank (aux .output))) bank := by
  constructor
  · intro k;cases k <;> rfl
  · intro k _;rfl
/-- Initialization physically pushes the sole final FALSE, paying the actual return. -/
theorem initialize_call (bank : Stack → List Bool) :
    Runs program 3 (ctl .initialize) bank (ctl .rowTag)
      (Function.update bank (aux .output) (false::bank (aux .output))) := by
  let input := S.data (bank ports) (bank table) (bank (aux .history)) (bank (aux .output))
  let output := S.data (bank ports) (bank table) (bank (aux .history)) (false::bank (aux .output))
  have hi := logger_in bank
  apply included_call program loggerStack loggerLabel logger_injective L.code .initialize (fun _ => rfl)
    (ctl .initialize) (ctl .rowTag) rfl 2 ⟨some .initialize,none,input⟩ ⟨none,none,output⟩
    bank _ rfl rfl (S.initialize_run _ _ _ _ none) hi
  have hh := Link.data_update loggerStack logger_injective bank input bank hi .output (false::bank (aux .output))
  have he : Function.update input .output (false::bank (aux .output))=output := by
    funext k;cases k <;> rfl
  simpa only [he,loggerStack] using hh
/-- The real logger consumes BOTH current fields and physically prepends the reversed row. -/
theorem record_call (bank : Stack → List Bool) :
    Runs program (S.recordTime (bank ports) (bank table)+1) (ctl .log) bank (ctl (.clearField 0))
      (Function.update (Function.update (Function.update bank ports []) table []) (aux .history)
        ((S.row (bank ports) (bank table)).reverse++bank (aux .history))) := by
  let input := S.data (bank ports) (bank table) (bank (aux .history)) (bank (aux .output))
  let output := S.data [] [] ((S.row (bank ports) (bank table)).reverse++bank (aux .history)) (bank (aux .output))
  have hi := logger_in bank
  apply included_call program loggerStack loggerLabel logger_injective L.code .record (fun _ => rfl)
    (ctl .log) (ctl (.clearField 0)) rfl (S.recordTime (bank ports) (bank table))
    ⟨some .record,none,input⟩ ⟨none,none,output⟩ bank _ rfl rfl (S.record_run _ _ _ _ none) hi
  have h0 := Link.data_update loggerStack logger_injective bank input bank hi .ports []
  have h1 := Link.data_update loggerStack logger_injective bank _ _ h0 .table []
  have h2 := Link.data_update loggerStack logger_injective bank _ _ h1 .history
    ((S.row (bank ports) (bank table)).reverse++bank (aux .history))
  have he : Function.update (Function.update (Function.update input .ports []) .table []) .history
      ((S.row (bank ports) (bank table)).reverse++bank (aux .history))=output := by
    funext k;cases k <;> rfl
  simpa only [he,loggerStack] using h2
/-- One final actual history reversal restores chronological factor order. -/
theorem reverse_call (bank : Stack → List Bool) :
    Runs program (2*(bank (aux .history)).length+3) (ctl .reverseFactors) bank (ctl .copyOwners)
      (Function.update (Function.update bank (aux .history) []) (aux .output)
        ((bank (aux .history)).reverse++bank (aux .output))) := by
  let input := S.data (bank ports) (bank table) (bank (aux .history)) (bank (aux .output))
  let output := S.data (bank ports) (bank table) [] ((bank (aux .history)).reverse++bank (aux .output))
  have hi := logger_in bank
  apply included_call program loggerStack loggerLabel logger_injective L.code .reverse (fun _ => rfl)
    (ctl .reverseFactors) (ctl .copyOwners) rfl (2*(bank (aux .history)).length+2)
    ⟨some .reverse,none,input⟩ ⟨none,none,output⟩ bank _ rfl rfl (S.reverse_run _ _ _ _ none) hi
  have h0 := Link.data_update loggerStack logger_injective bank input bank hi .history []
  have h1 := Link.data_update loggerStack logger_injective bank _ _ h0 .output
    ((bank (aux .history)).reverse++bank (aux .output))
  have he : Function.update (Function.update input .history []) .output
      ((bank (aux .history)).reverse++bank (aux .output))=output := by
    funext k;cases k <;> rfl
  simpa only [he,loggerStack] using h1
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsLogger
