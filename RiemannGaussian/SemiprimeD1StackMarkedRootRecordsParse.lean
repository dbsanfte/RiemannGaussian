/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsFields
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowView
/-! # Actual synchronous two-record-field and five-descriptor-field parsing -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsParse
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsRowView SemiprimeD1StackMarkedRootRecordsFields
open SemiprimeD1StackMarkedRootRecordsPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Total payload length of the five actual descriptor fields. -/
def mass (fields : Fin 5 → List Bool) : Nat := ∑ i, (fields i).length
/-- Exact post-parser state; every actual validity singleton was consumed. -/
def parsed (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits portsWord tableWord : List Bool)
    (fields : Fin 5 → List Bool) (recordTail descriptorTail hist out : List Bool) : Stack → List Bool :=
  view r v bits {indexWord := fields 2,portsWord := portsWord,tableWord := tableWord}
    {records := recordTail,descriptors := descriptorTail,tag := fields 0,coord0 := fields 1,
      coord2 := fields 3,coord3 := fields 4,history := hist,output := out}
/-- All seven REAL field calls and true-validity pops, with original tail bytes retained. -/
theorem parse_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits portsWord tableWord : List Bool)
    (fields : Fin 5 → List Bool) (recordTail descriptorTail hist out : List Bool) :
    Runs program (8*(portsWord.length+tableWord.length+mass fields)+57) (ctl .rowTag)
      (view r v bits {} {records := true::frame portsWord (frame tableWord recordTail),descriptors := SemiprimeD1EdgeCatalogueEncoding.record fields descriptorTail,history := hist,output := out})
      (ctl .caseTag) (parsed r v bits portsWord tableWord fields recordTail descriptorTail hist out) := by
  have h0 := row_tag (view r v bits {} {records := true::frame portsWord (frame tableWord recordTail),descriptors := (frame (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))))),history := hist,output := out}) (frame portsWord (frame tableWord recordTail)) rfl
  rw [set_records] at h0
  have h1 := field_run .ports (view r v bits {} {records := frame portsWord (frame tableWord recordTail),descriptors := (frame (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))))),history := hist,output := out}) portsWord (frame tableWord recordTail) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view r v bits {} {records := frame portsWord (frame tableWord recordTail),descriptors := (frame (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))))),history := hist,output := out}) (aux .recordReader) (frame tableWord recordTail)) ports portsWord) at h1
  rw [set_records,set_portsWord] at h1
  have h2 := field_run .table (view r v bits {portsWord := portsWord} {records := frame tableWord recordTail,descriptors := (frame (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))))),history := hist,output := out}) tableWord recordTail rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view r v bits {portsWord := portsWord} {records := frame tableWord recordTail,descriptors := (frame (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))))),history := hist,output := out}) (aux .recordReader) recordTail) table tableWord) at h2
  rw [set_records,set_tableWord] at h2
  have h3 := field_run .tag (view r v bits {portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))))),history := hist,output := out}) (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail)))) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view r v bits {portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))))),history := hist,output := out}) (aux .descriptorReader) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))))) (aux .tag) (fields 0)) at h3
  rw [set_descriptors,set_tag] at h3
  have h4 := field_run .coord0 (view r v bits {portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail)))),tag := fields 0,history := hist,output := out}) (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view r v bits {portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail)))),tag := fields 0,history := hist,output := out}) (aux .descriptorReader) (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail)))) (aux .coord0) (fields 1)) at h4
  rw [set_descriptors,set_coord0] at h4
  have h5 := field_run .coord1 (view r v bits {portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))),tag := fields 0,coord0 := fields 1,history := hist,output := out}) (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail)) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view r v bits {portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 2) (frame (fields 3) (frame (fields 4) descriptorTail))),tag := fields 0,coord0 := fields 1,history := hist,output := out}) (aux .descriptorReader) (frame (fields 3) (frame (fields 4) descriptorTail))) (index) (fields 2)) at h5
  rw [set_descriptors,set_indexWord] at h5
  have h6 := field_run .coord2 (view r v bits {indexWord := fields 2,portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 3) (frame (fields 4) descriptorTail)),tag := fields 0,coord0 := fields 1,history := hist,output := out}) (fields 3) (frame (fields 4) descriptorTail) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view r v bits {indexWord := fields 2,portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 3) (frame (fields 4) descriptorTail)),tag := fields 0,coord0 := fields 1,history := hist,output := out}) (aux .descriptorReader) (frame (fields 4) descriptorTail)) (aux .coord2) (fields 3)) at h6
  rw [set_descriptors,set_coord2] at h6
  have h7 := field_run .coord3 (view r v bits {indexWord := fields 2,portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 4) descriptorTail),tag := fields 0,coord0 := fields 1,coord2 := fields 3,history := hist,output := out}) (fields 4) descriptorTail rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view r v bits {indexWord := fields 2,portsWord := portsWord,tableWord := tableWord} {records := recordTail,descriptors := (frame (fields 4) descriptorTail),tag := fields 0,coord0 := fields 1,coord2 := fields 3,history := hist,output := out}) (aux .descriptorReader) descriptorTail) (aux .coord3) (fields 4)) at h7
  rw [set_descriptors,set_coord3] at h7
  have h := join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 h7))))))
  have he : mass fields=(fields 0).length+(fields 1).length+(fields 2).length+(fields 3).length+(fields 4).length := by
    simp only [mass,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (fields 0).length+((fields 1).length+((fields 2).length+((fields 3).length+((fields 4).length+0))))=_
    omega
  convert h using 1 <;> first | rfl | (simp only [he];omega)
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsParse
