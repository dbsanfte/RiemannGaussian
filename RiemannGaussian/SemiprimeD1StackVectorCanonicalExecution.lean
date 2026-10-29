/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVectorCanonicalComponents

/-! # Whole executed canonicality guard, including rejection and draining
The guard executes comparisons on every visited field; a false comparison
chooses the actual rejecting branch and physically clears the remaining tape.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVectorCanonicalExecution
open SemiprimeD1StackVectorCanonical SemiprimeD1StackVectorCanonicalComponents
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Proof-side canonicality specification, never supplied to the finite program. -/
def answer (cached : List Bool) (words : List (List Bool)) : Bool :=
  words.all (fun word=>SemiprimeD1StackWordLessExecution.answer word cached)
/-- Exact own count for one actually parsed and compared word. -/
def stepBudget (word cached : List Bool) : ℕ :=
  1+(8*word.length+7)+1+(5*cached.length+4)+
    (SemiprimeD1StackWordLessExecution.totalTime word cached+1)+1
/-- An upper count for the real guard loop, paying an entire rejected suffix. -/
def loopBudget (cached : List Bool) : List (List Bool)→ℕ
  | [] => 2
  | word::words => stepBudget word cached+(vectorBits words).length+2+loopBudget cached words
/-- Complete own-program count bound, including real copy and final halt. -/
def timeBound (words : List (List Bool)) (cached : List Bool) : ℕ :=
  (5*(vectorBits words).length+4)+loopBudget cached words+1
/-- Exact clean actual halt: retained inputs and one computed Boolean. -/
def done (words : List (List Bool)) (cached : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store (vectorBits words) cached [] [] [] [] [] [] [answer cached words],[]⟩

/-- Whole field iteration uses its actual vector tag, parser and comparison bit. -/
theorem word_run (cache cached word : List Bool) (words : List (List Bool)) :
    Runs program (stepBudget word cached) .loop (store cache cached (vectorBits (word::words)) [] [] [] [] [] [])
      (if SemiprimeD1StackWordLessExecution.answer word cached then .loop else .reject)
      (store cache cached (vectorBits words) [] [] [] [] [] []) := by
  have h0 : Runs program 1 .loop (store cache cached (vectorBits (word::words)) [] [] [] [] [] [])
      .parse (store cache cached (frame word (vectorBits words)) [] [] [] [] [] []) := by
    apply one_base program .loop .parse (.pop .reader .bad .accept .parse) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h1:=field_call cache cached word (vectorBits words)
  have h2:=field_flag cache cached (vectorBits words) word
  have h3:=copy_modulus cache cached (vectorBits words) word
  have h4:=less_call cache cached (vectorBits words) word
  have h5:=less_flag cache cached (vectorBits words) (SemiprimeD1StackWordLessExecution.answer word cached)
  exact runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5

/-- A false numeric comparison is physically recorded before draining its suffix. -/
theorem reject_run (cache cached reader : List Bool) :
    Runs program (1+(reader.length+1)) .reject (store cache cached reader [] [] [] [] [] [])
      .done (store cache cached [] [] [] [] [] [] [false]) := by
  have h0 : Runs program 1 .reject (store cache cached reader [] [] [] [] [] [])
      .clearReader (store cache cached reader [] [] [] [] [] [false]) := by
    apply one_base program .reject .clearReader (.push .output false .clearReader) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  exact runs_trans program _ _ _ _ _ _ _ _ h0 (clear_reader cache cached reader false)

/-- Complete actual loop, terminating on both accepting and rejecting inputs.
No canonicality predicate is an execution premise. -/
theorem loop_run (cache cached : List Bool) (words : List (List Bool)) :
    ∃t ≤ loopBudget cached words,Runs program t .loop (store cache cached (vectorBits words) [] [] [] [] [] [])
      .done (store cache cached [] [] [] [] [] [] [answer cached words]) := by
  induction words with
  | nil =>
    have h0 : Runs program 1 .loop (store cache cached (vectorBits []) [] [] [] [] [] [])
        .accept (store cache cached [] [] [] [] [] [] []) := by
      apply one_base program .loop .accept (.pop .reader .bad .accept .parse) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    have h1 : Runs program 1 .accept (store cache cached [] [] [] [] [] [] [])
        .done (store cache cached [] [] [] [] [] [] [true]) := by
      apply one_base program .accept .done (.push .output true .done) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    exact ⟨2,le_refl _,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  | cons word words ih =>
    have h0:=word_run cache cached word words
    cases hbit:SemiprimeD1StackWordLessExecution.answer word cached with
    | false =>
      simp only [hbit,Bool.false_eq_true,ite_false] at h0
      have h1:=reject_run cache cached (vectorBits words)
      have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
      refine ⟨stepBudget word cached+(1+((vectorBits words).length+1)),?_,?_⟩
      · simp only [loopBudget]
        omega
      · simpa only [answer,List.all_cons,hbit,Bool.false_and] using h
    | true =>
      simp only [hbit,ite_true] at h0
      obtain ⟨m,hm,h1⟩:=ih
      refine ⟨stepBudget word cached+m,?_,?_⟩
      · simp only [loopBudget]
        omega
      · simpa only [answer,List.all_cons,hbit,Bool.true_and] using runs_trans program _ _ _ _ _ _ _ _ h0 h1

/-- COMPLETE real vector guard: physical inputs only and exact computed verdict. -/
theorem source_run (words : List (List Bool)) (cached : List Bool) :
    ∃t ≤ timeBound words cached,C.run program t (initial (vectorBits words) cached)=some (done words cached) := by
  have h0:=copy_cache (vectorBits words) cached
  obtain ⟨m,hm,h1⟩:=loop_run (vectorBits words) cached words
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  obtain ⟨finish,hr,ho⟩:=h [] (initial (vectorBits words) cached) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (store (vectorBits words) cached [] [] [] [] [] [] [answer cached words]) [] finish ho
  refine ⟨(5*(vectorBits words).length+4)+m+1,?_,?_⟩
  · unfold timeBound
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    rfl

/-- Exactly every physical original word is canonical; padding and empty words
are interpreted by their actual binary values, with no length-only shortcut. -/
theorem answer_true (cached : List Bool) (words : List (List Bool)) :
    answer cached words=true ↔ ∀word∈words,SemiprimeBitArithmetic.bitValue word<SemiprimeBitArithmetic.bitValue cached := by
  simp only [answer,List.all_eq_true,SemiprimeD1StackWordLessExecution.answer_true]

end RiemannGaussian.SemiprimeD1StackVectorCanonicalExecution
