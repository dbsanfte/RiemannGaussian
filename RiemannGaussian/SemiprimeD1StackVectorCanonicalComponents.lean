/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVectorCanonical

/-! # Literal component traces of the complete vector guard
These inclusions preserve both retained caches and the unconsumed source. Every
field validity bit, copied modulus, numeric answer and cleanup is actual data.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVectorCanonicalComponents
open SemiprimeD1StackVectorCanonical SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)

/-- The full encoded vector is actually copied once, with its cache retained. -/
theorem copy_cache (cache cached : List Bool) :
    Runs program (5*cache.length+4) .start (store cache cached [] [] [] [] [] [] [])
      .loop (store cache cached cache [] [] [] [] [] []) := by
  apply included_call program (copyStack false) (Label.copy false) (copyStack_injective false)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) .start .loop rfl (5*cache.length+3)
    (SemiprimeD1StackCopy.state 0 none cache [] []) (SemiprimeD1StackCopy.done cache cache)
    (store cache cached [] [] [] [] [] [] []) (store cache cached cache [] [] [] [] [] [])
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words cache [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk 1 rfl)

/-- Every destructive comparison receives a physically copied binary modulus. -/
theorem copy_modulus (cache cached reader word : List Bool) :
    Runs program (5*cached.length+4) .copyModulus (store cache cached reader word [] [] [] [] [])
      .compare (store cache cached reader word cached [] [] [] []) := by
  apply included_call program (copyStack true) (Label.copy true) (copyStack_injective true)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) .copyModulus .compare rfl (5*cached.length+3)
    (SemiprimeD1StackCopy.state 0 none cached [] []) (SemiprimeD1StackCopy.done cached cached)
    (store cache cached reader word [] [] [] [] []) (store cache cached reader word cached [] [] [] [])
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words cached [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk 1 rfl)

/-- A real field call acquires its exact word and actual validity Boolean. -/
theorem field_call (cache cached word tail : List Bool) :
    Runs program (8*word.length+7) .parse (store cache cached (frame word tail) [] [] [] [] [] [])
      .parsed (store cache cached tail word [] [true] [] [] []) := by
  apply included_call program fieldStack Label.field fieldStack_injective F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) .parse .parsed rfl (8*word.length+6)
    (F.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State F.Stack F.Label)
    (store cache cached (frame word tail) [] [] [] [] [] []) (store cache cached tail word [] [true] [] [] [])
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk (.inl .input) rfl) |
        exact False.elim (hk (.inl .output) rfl) | exact False.elim (hk (.inr ()) rfl)

/-- The physical parser verdict is consumed before any comparison begins. -/
theorem field_flag (cache cached reader word : List Bool) :
    Runs program 1 .parsed (store cache cached reader word [] [true] [] [] [])
      .copyModulus (store cache cached reader word [] [] [] [] []) := by
  apply one_base program .parsed .copyModulus (.pop .valid .bad .bad .copyModulus) _ _ rfl
  · rfl
  · funext k;cases k <;> rfl

/-- The COMPLETE actual numeric comparison consumes both operands and returns
only its computed Boolean, with no canonicality assumption. -/
theorem less_call (cache cached reader word : List Bool) :
    Runs program (SemiprimeD1StackWordLessExecution.totalTime word cached+1) .compare
      (store cache cached reader word cached [] [] [] []) .compared
      (store cache cached reader [] [] [] [] [SemiprimeD1StackWordLessExecution.answer word cached] []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program lessStack Label.less lessStack_injective
    W.program .start (fun _=>rfl) .compare .compared rfl
    (SemiprimeD1StackWordLessExecution.totalTime word cached) (W.initial word cached)
    (SemiprimeD1StackWordLessExecution.done word cached)
    (store cache cached reader word cached [] [] [] [])
    (store cache cached reader [] [] [] [] [SemiprimeD1StackWordLessExecution.answer word cached] [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackWordLessExecution.source_run word cached
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk (.inl .left) rfl) |
        exact False.elim (hk (.inl .right) rfl) | exact False.elim (hk (.inr ()) rfl)

/-- Control reads the actual comparison bit, never an external proof verdict. -/
theorem less_flag (cache cached reader : List Bool) (bit : Bool) :
    Runs program 1 .compared (store cache cached reader [] [] [] [] [bit] [])
      (if bit then .loop else .reject) (store cache cached reader [] [] [] [] [] []) := by
  apply one_base program .compared (if bit then .loop else .reject)
    (.pop .lessFlag .bad .reject .loop) _ _ rfl
  · cases bit <;> rfl
  · funext k;cases k <;> rfl

/-- Every rejected source-suffix bit is physically popped before returning. -/
theorem clear_reader (cache cached reader : List Bool) (bit : Bool) :
    Runs program (reader.length+1) .clearReader (store cache cached reader [] [] [] [] [] [bit])
      .done (store cache cached [] [] [] [] [] [] [bit]) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearReader .done Stack.reader rfl
    (store cache cached [] [] [] [] [] [] [bit]) reader
  have hi : Function.update (store cache cached [] [] [] [] [] [] [bit]) .reader reader=
      store cache cached reader [] [] [] [] [] [bit] := by
    funext k;cases k <;> simp [Function.update,store]
  have ho : Function.update (store cache cached [] [] [] [] [] [] [bit]) .reader []=
      store cache cached [] [] [] [] [] [] [bit] := Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

end RiemannGaussian.SemiprimeD1StackVectorCanonicalComponents
