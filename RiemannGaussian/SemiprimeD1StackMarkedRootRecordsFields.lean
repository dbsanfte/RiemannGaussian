/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsPrimitives
/-! # Paid framed-field parsing with physical true-validity consumption -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsFields
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Parser validity never shares an input-reader word. -/
theorem status_ne_reader (what : Field) : aux .status≠fieldReader what := by cases what <;> decide
/-- Parser validity never shares a parsed destination. -/
theorem status_ne_target (what : Field) : aux .status≠fieldTarget what := by cases what <;> decide
/-- Each paid parser is followed by an actual TRUE pop, including empty tag/port fields. -/
theorem field_run (what : Field) (bank : Stack → List Bool) (word tail : List Bool)
    (hi : bank (fieldReader what)=frame word tail) (ho : bank (fieldTarget what)=[])
    (hs : bank (aux .fieldScratch)=[]) (hv : bank (aux .status)=[]) :
    Runs program (8*word.length+8) (ctl (.field what)) bank (fieldNext what)
      (Function.update (Function.update bank (fieldReader what) tail) (fieldTarget what) word) := by
  let after := Function.update (Function.update bank (fieldReader what) tail) (fieldTarget what) word
  have h0 := parse_call what bank word tail hi ho hs hv
  have h1 : Runs program 1 (ctl (.valid what)) (Function.update after (aux .status) [true])
      (fieldNext what) (Function.update after (aux .status) []) := by
    apply one_base program (ctl (.valid what)) (fieldNext what)
      (.pop (aux .status) (ctl .abort) (ctl .abort) (fieldNext what)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
    · simp [SemiprimeD1StackBytecode.execute,Function.update_idem]
  have he : after (aux .status)=[] := by
    dsimp only [after]
    rw [Function.update_of_ne (status_ne_target what),Function.update_of_ne (status_ne_reader what),hv]
  have hf : Function.update after (aux .status) []=after := by
    rw [←he,Function.update_eq_self]
  rw [hf] at h1
  simpa only [Nat.add_assoc] using join h0 h1
/-- The record TRUE is really read before either framed payload is inspected. -/
theorem row_tag (bank : Stack → List Bool) (tail : List Bool)
    (h : bank (aux .recordReader)=true::tail) :
    Runs program 1 (ctl .rowTag) bank (ctl (.field .ports))
      (Function.update bank (aux .recordReader) tail) := by
  apply one_base program (ctl .rowTag) (ctl (.field .ports))
    (.pop (aux .recordReader) (ctl .abort) (ctl .recordEOF) (ctl (.field .ports))) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,h]
  · simp [SemiprimeD1StackBytecode.execute,h]
/-- A final FALSE is physically consumed and is not confused with descriptor EOF. -/
theorem record_end (bank : Stack → List Bool) (h : bank (aux .recordReader)=[false]) :
    Runs program 1 (ctl .rowTag) bank (ctl .recordEOF)
      (Function.update bank (aux .recordReader) []) := by
  apply one_base program (ctl .rowTag) (ctl .recordEOF)
    (.pop (aux .recordReader) (ctl .abort) (ctl .recordEOF) (ctl (.field .ports))) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,h]
  · simp [SemiprimeD1StackBytecode.execute,h]
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsFields
