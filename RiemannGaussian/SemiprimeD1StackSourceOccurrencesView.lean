/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesPrimitives
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesEncoding
/-! # Exact actual occurrence-source clean bank boundaries
All source/parser/counter/key/history/tally words remain real physical tapes.
The following pure views specify those words in proofs, never runtime control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesView
open SemiprimeD1StackSourceOccurrences
/-- Every clean-boundary live word, with all other actual helper/parser/carry/frame words empty. -/
def data (rows number reader row word todo counter ownerKey factorKey history factors occurrences:List Bool) :Stack→List Bool
  | .rows=>rows
  | .number=>number
  | .reader=>reader
  | .row=>row
  | .word=>word
  | .todo=>todo
  | .counter=>counter
  | .ownerKey=>ownerKey
  | .factorKey=>factorKey
  | .history=>history
  | .factors=>factors
  | .occurrences=>occurrences
  | _=>[]
/-- Exact physical update of only the actual rows boundary word. -/
theorem data_rows (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .rows xs=data xs number reader row word todo counter ownerKey factorKey history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual number boundary word. -/
theorem data_number (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .number xs=data rows xs reader row word todo counter ownerKey factorKey history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual reader boundary word. -/
theorem data_reader (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .reader xs=data rows number xs row word todo counter ownerKey factorKey history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual row boundary word. -/
theorem data_row (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .row xs=data rows number reader xs word todo counter ownerKey factorKey history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual word boundary word. -/
theorem data_word (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .word xs=data rows number reader row xs todo counter ownerKey factorKey history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual todo boundary word. -/
theorem data_todo (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .todo xs=data rows number reader row word xs counter ownerKey factorKey history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual counter boundary word. -/
theorem data_counter (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .counter xs=data rows number reader row word todo xs ownerKey factorKey history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual ownerKey boundary word. -/
theorem data_ownerKey (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .ownerKey xs=data rows number reader row word todo counter xs factorKey history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual factorKey boundary word. -/
theorem data_factorKey (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .factorKey xs=data rows number reader row word todo counter ownerKey xs history factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual history boundary word. -/
theorem data_history (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .history xs=data rows number reader row word todo counter ownerKey factorKey xs factors occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual factors boundary word. -/
theorem data_factors (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .factors xs=data rows number reader row word todo counter ownerKey factorKey history xs occurrences :=by
  funext k;cases k <;> simp [data,Function.update]
/-- Exact physical update of only the actual occurrences boundary word. -/
theorem data_occurrences (rows number reader row word todo counter ownerKey factorKey history factors occurrences xs:List Bool) :
    Function.update (data rows number reader row word todo counter ownerKey factorKey history factors occurrences) .occurrences xs=data rows number reader row word todo counter ownerKey factorKey history factors xs :=by
  funext k;cases k <;> simp [data,Function.update]
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesView
