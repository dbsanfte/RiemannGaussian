/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheckFields

/-! # Complete actual three-word parsing before multiplication
The acquired vector is consumed by three real tagged Field calls, including
the computed validity pops. No parsed operand or framing answer is an input.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckParse
open SemiprimeD1StackProductCheck SemiprimeD1StackProductCheckAcquisition
open SemiprimeD1StackProductCheckFields SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)

/-- Physical vector/operand payload after the parser validity bit was popped. -/
def parsedData (i : Fin 3) (data : Stack→List Bool) (word tail : List Bool) : Stack→List Bool :=
  Function.update (Function.update data vectorRole tail) (operand i) word

/-- One real tagged Field call, including both physical tag and validity pops. -/
theorem read_one (i : Fin 3) (data : Stack→List Bool) (word tail : List Bool)
    (hvec : data vectorRole=true::frame word tail) (hop : data (operand i)=[])
    (hscratch : data (auxiliary 0)=[]) (hvalid : data (auxiliary 1)=[]) :
    Runs program (8*word.length+9) (.tag i) data (afterField i) (parsedData i data word tail) := by
  let stripped:=Function.update data vectorRole (frame word tail)
  have h0:=tag_run i data (frame word tail) hvec
  have h1:=field_call i stripped word tail rfl (by fin_cases i <;> exact hop)
    (by exact hscratch) (by exact hvalid)
  have h2:=parsed_run i (fieldData i stripped word tail) (by rfl)
  have hd : Function.update (fieldData i stripped word tail) (auxiliary 1) []=
      parsedData i data word tail := by
    funext k
    by_cases hk:k=auxiliary 1
    · subst k
      fin_cases i <;> exact hvalid.symm
    · simp only [fieldData,parsedData,stripped,Function.update_of_ne hk]
      by_cases hv:k=vectorRole
      · subst k;fin_cases i <;> rfl
      · by_cases ho:k=operand i
        · subst k;simp only [Function.update_self]
        · simp only [Function.update_of_ne ho,Function.update_of_ne hv]
  rw [hd] at h2
  have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  convert h using 1
  omega

/-- Actual first raw word, retaining literal padding. -/
def first (raw cached : List Bool) : List Bool := SemiprimeD1StackWordBlockExecution.result raw cached
/-- Actual second word acquired after exactly one width-sized raw block. -/
def second (raw cached : List Bool) : List Bool :=
  SemiprimeD1StackWordBlockExecution.result (raw.drop cached.length) cached
/-- Actual output word acquired after exactly two physical width-sized blocks. -/
def third (raw cached : List Bool) : List Bool :=
  SemiprimeD1StackWordBlockExecution.result ((raw.drop cached.length).drop cached.length) cached
/-- Literal remaining vector following the first field. -/
def tailFirst (raw cached : List Bool) : List Bool :=
  true::frame (second raw cached) (true::frame (third raw cached) [false])
/-- Literal remaining vector following the second field. -/
def tailSecond (raw cached : List Bool) : List Bool := true::frame (third raw cached) [false]
/-- Reached actual payload after first physical Field/validity execution. -/
def afterFirst (raw cached : List Bool) : Stack→List Bool :=
  parsedData 0 (afterAcquire raw cached) (first raw cached) (tailFirst raw cached)
/-- Reached actual payload after second physical Field/validity execution. -/
def afterSecond (raw cached : List Bool) : Stack→List Bool :=
  parsedData 1 (afterFirst raw cached) (second raw cached) (tailSecond raw cached)
/-- Reached actual payload after all three Field/validity executions. -/
def afterThird (raw cached : List Bool) : Stack→List Bool :=
  parsedData 2 (afterSecond raw cached) (third raw cached) [false]
/-- Every remaining vector byte is actually removed before multiplication. -/
def ready (raw cached : List Bool) : Stack→List Bool := Function.update (afterThird raw cached) vectorRole []
/-- Actual parser work plus the final vector nil-byte and EOF pop. -/
def parseTime (raw cached : List Bool) : ℕ :=
  (8*(first raw cached).length+9)+(8*(second raw cached).length+9)+(8*(third raw cached).length+9)+2

/-- Actual acquired vector layout, derived from the executed producer. -/
theorem acquired_layout (raw cached : List Bool) :
    afterAcquire raw cached vectorRole=true::frame (first raw cached) (tailFirst raw cached) := rfl

/-- Complete original raw-input three-field parse and vector cleanup. -/
theorem source_run (raw cached : List Bool) :
    Runs program (parseTime raw cached) (.tag 0) (afterAcquire raw cached) .multiply (ready raw cached) := by
  have h0:=read_one 0 (afterAcquire raw cached) (first raw cached) (tailFirst raw cached)
    (acquired_layout raw cached) rfl rfl rfl
  have h1:=read_one 1 (afterFirst raw cached) (second raw cached) (tailSecond raw cached) rfl rfl rfl rfl
  have h2:=read_one 2 (afterSecond raw cached) (third raw cached) [false] rfl rfl rfl rfl
  have h3:=SemiprimeD1StackProductCheckReject.clear_vector true (afterThird raw cached)
  change Runs program 2 (.clearVector true) (afterThird raw cached) .multiply (ready raw cached) at h3
  exact runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3

end RiemannGaussian.SemiprimeD1StackProductCheckParse
