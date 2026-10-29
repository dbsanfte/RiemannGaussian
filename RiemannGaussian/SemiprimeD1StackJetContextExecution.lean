/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetContext
/-! # Actual original-axis and binary-precision context acquisition -/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetContextExecution
open SemiprimeD1StackJetContext
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans At)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeBitArithmetic (bitValue)

/-- Exact acquired suffix-rank/records stage, with all unlisted registers empty. -/
def ready (rank records valid : List Bool) : S.Stack → List Bool := S.data [] [] [] rank [] records [] valid
/-- Exact empty precision-decoder work bank. -/
def emptyUnary : SemiprimeD1StackAdder.Stack → List Bool := SemiprimeD1StackAdder.store [] [] [] []

/-- Original axes are really copied before their suffix supplier consumes them. -/
theorem axes_copy (axes : List ℕ) (precision : List Bool) :
    Runs program (5*(vectorBits (axes.map unary)).length+4) .start
      (initial (vectorBits (axes.map unary)) precision).data .callSuffix
      (bank (vectorBits (axes.map unary)) precision (SemiprimeD1StackJetSuffixOriginal.initial axes).data emptyUnary) := by
  apply SemiprimeD1StackProcedureTrace.included_call program (copyStack false) (Label.copy false)
    (copyStack_injective false) SemiprimeD1StackCopy.code (0:Fin 9) (fun _=>rfl) .start .callSuffix rfl _
    (SemiprimeD1StackCopy.state 0 none (vectorBits (axes.map unary)) [] [])
    (SemiprimeD1StackCopy.done (vectorBits (axes.map unary)) (vectorBits (axes.map unary)))
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words (vectorBits (axes.map unary)) [] none
  · constructor
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      rfl
  · constructor
    · intro k
      fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact False.elim (hk 1 rfl)
      · rcases k with k|k
        · cases k <;> rfl
        · rfl

/-- The actual original-axis supplier acquires rank and every suffix record. -/
theorem suffix_call (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    ∃ m ≤ 100*(axes.length+1)*(axes.prod+1)+2,
      Runs program m .callSuffix
        (bank (vectorBits (axes.map unary)) precision (SemiprimeD1StackJetSuffixOriginal.initial axes).data emptyUnary)
        .suffixDone
        (bank (vectorBits (axes.map unary)) precision (SemiprimeD1StackJetSuffixOriginal.final axes).data emptyUnary) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackJetSuffixOriginal.acquire_run axes hp
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program Sum.inl Label.suffix Sum.inl_injective
    S.code (S.control .vector) (fun _=>rfl) .callSuffix .suffixDone rfl m
    (SemiprimeD1StackJetSuffixOriginal.initial axes) (SemiprimeD1StackJetSuffixOriginal.final axes)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k; rfl
    · intro k hk; rfl
  · constructor
    · intro k; rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- The successful original supplier flag is consumed physically. -/
theorem suffix_flag (axes precision rank records : List Bool) :
    Runs program 1 .suffixDone (bank axes precision (ready rank records [true]) emptyUnary) .clearRecords
      (bank axes precision (ready rank records []) emptyUnary) := by
  apply one_base program .suffixDone .clearRecords (.pop (.inl .valid) .reject .reject .clearRecords) _ _ rfl
  · rfl
  · funext k
    rcases k with k|k
    · cases k <;> rfl
    · rfl

/-- The generated record inventory is entirely drained by real pop transitions. -/
theorem clear_records (axes precision rank records : List Bool) :
    Runs program (records.length+1) .clearRecords (bank axes precision (ready rank records []) emptyUnary)
      .copyPrecision (bank axes precision (ready rank [] []) emptyUnary) := by
  induction records with
  | nil =>
    apply one_base program .clearRecords .copyPrecision (.pop (.inl .records) .copyPrecision .clearRecords .clearRecords) _ _ rfl
    · rfl
    · funext k
      rcases k with k|k
      · cases k <;> rfl
      · rfl
  | cons bit records ih =>
    have h1 : Runs program 1 .clearRecords (bank axes precision (ready rank (bit::records) []) emptyUnary)
        .clearRecords (bank axes precision (ready rank records []) emptyUnary) := by
      apply one_base program .clearRecords .clearRecords (.pop (.inl .records) .copyPrecision .clearRecords .clearRecords) _ _ rfl
      · cases bit <;> rfl
      · funext k
        rcases k with k|k
        · cases k <;> rfl
        · rfl
    have h:=runs_trans program _ _ _ _ _ _ _ _ h1 ih
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Original binary precision is really copied into the physical decoder. -/
theorem precision_copy (axes precision rank : List Bool) :
    Runs program (5*precision.length+4) .copyPrecision (bank axes precision (ready rank [] []) emptyUnary)
      .callUnary (bank axes precision (ready rank [] []) (SemiprimeD1StackAdder.store precision [] [] [])) := by
  apply SemiprimeD1StackProcedureTrace.included_call program (copyStack true) (Label.copy true)
    (copyStack_injective true) SemiprimeD1StackCopy.code (0:Fin 9) (fun _=>rfl) .copyPrecision .callUnary rfl _
    (SemiprimeD1StackCopy.state 0 none precision [] []) (SemiprimeD1StackCopy.done precision precision)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words precision [] none
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> first | rfl | exact False.elim (hk 1 rfl)
        · rfl

/-- Actual binary-to-unary execution creates precision markers; no marker
count or native decoded value is a runtime operand. Its VALUE cost is explicit. -/
theorem unary_call (axes precision rank : List Bool) :
    ∃ m ≤ 7*bitValue precision+6*precision.length+4,
      Runs program m .callUnary
        (bank axes precision (ready rank [] []) (SemiprimeD1StackAdder.store precision [] [] [])) .done
        (bank axes precision (ready rank [] [])
          (SemiprimeD1StackAdder.store [] [] [] (SemiprimeD1StackUnaryCounterExecution.markers (bitValue precision)))) := by
  refine ⟨(2*precision.length+1+SemiprimeD1StackUnaryCounterExecution.loopTime precision.reverse 0)+1,?_,?_⟩
  · have h:=SemiprimeD1StackUnaryCounterExecution.source_time precision
    omega
  · apply SemiprimeD1StackProcedureTrace.included_call program unaryStack Label.unary unaryStack_injective
      U.code .reverse (fun _=>rfl) .callUnary .done rfl _
      (U.state (some .reverse) none precision [] [] [])
      (U.state none none [] [] [] (SemiprimeD1StackUnaryCounterExecution.markers (bitValue precision)))
    · rfl
    · rfl
    · exact SemiprimeD1StackUnaryCounterExecution.source_run precision
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; cases k <;> rfl
      · intro k hk
        rcases k with k|k
        · rfl
        · rcases k with k|k
          · exact False.elim (hk k rfl)
          · rfl

end RiemannGaussian.SemiprimeD1StackJetContextExecution
