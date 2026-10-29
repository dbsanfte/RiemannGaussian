/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentView
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentMeaning
/-! # Actual preserving marked-prefix lookup and complete unread-tail cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentLookup
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentPrimitives
open SemiprimeD1StackSourceEnvironmentEncoding SemiprimeD1StackSourceEnvironmentView
open SemiprimeD1StackSourceEnvironmentMeaning SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => Label.local
/-- An unread first-match suffix never exceeds its actual supplied catalogue tape. -/
theorem result_tail_le (q:List Bool) (rows:List (List Bool×List Bool)) :
    (SemiprimeD1StackOwnerLookup.result q rows []).2.length≤(L.records rows []).length :=by
  induction rows with
  | nil=>simp [SemiprimeD1StackOwnerLookup.result,L.records]
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    have h:(L.records rows []).length≤(L.records ((key,value)::rows) []).length:=by
      simp only [L.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
    simp only [SemiprimeD1StackOwnerLookup.result]
    split
    · exact h
    · exact ih.trans h
/-- The actual present flag is computed from the returned marker; the returned compact ID remains its physical suffix. -/
theorem result_pop (dict key chosen q pfx reader id:List Bool) (present:Bool) :
    Runs program 2 (ctl .readResult)
      (view dict key chosen q pfx [] [] [] reader (if present then true::id else []))
      (ctl .clearReader)
      (view dict key chosen q pfx [] [] [present] reader (if present then id else [])) :=by
  cases present
  · have h0:=pop_run .readResult (ctl .missing) (ctl .abort) (ctl .present) output
      (view dict key chosen q pfx [] [] [] reader []) [] rfl rfl
    change Runs program 1 _ _ (ctl .missing) (Function.update (view dict key chosen q pfx [] [] [] reader []) output []) at h0
    change Runs program 1 _ _ _ (Function.update (view dict key chosen q pfx [] [] [] reader []) (lookupStack (.inr .output)) []) at h0
    rw [view_lookup_output] at h0
    have h1:=push_run .missing (ctl .clearReader) (aux .found) false (view dict key chosen q pfx [] [] [] reader []) rfl
    change Runs program 1 _ _ _ (Function.update (view dict key chosen q pfx [] [] [] reader []) (aux .found) [false]) at h1
    rw [view_found] at h1
    exact join h0 h1
  · have h0:=pop_run .readResult (ctl .missing) (ctl .abort) (ctl .present) output
      (view dict key chosen q pfx [] [] [] reader (true::id)) (true::id) rfl rfl
    change Runs program 1 _ _ (ctl .present)
      (Function.update (view dict key chosen q pfx [] [] [] reader (true::id)) (lookupStack (.inr .output)) id) at h0
    rw [view_lookup_output] at h0
    have h1:=push_run .present (ctl .clearReader) (aux .found) true (view dict key chosen q pfx [] [] [] reader id) rfl
    change Runs program 1 _ _ _ (Function.update (view dict key chosen q pfx [] [] [] reader id) (aux .found) [true]) at h1
    rw [view_found] at h1
    exact join h0 h1
/-- Preserving physical dictionary copy, real numeric-key lookup, actual marker pop and complete actual unread-tail drain. -/
theorem lookup_trace (ids:List (List Bool)) (chosen q pfx:List Bool) :
    ∃t≤200*(q.length+1)*((dictionary ids).length+1),Runs program t (ctl .lookup)
      (view (dictionary ids) (variableKey ids.length) chosen q pfx [] [] [] [] [])
      (ctl .done)
      (view (dictionary ids) (variableKey ids.length) chosen q pfx [] []
        [decide (bitValue q < ids.length)] [] (if bitValue q < ids.length then SemiprimeSourceHistogramPrefix.expected ids (bitValue q) else [])) :=by
  let D:=dictionary ids
  let K:=variableKey ids.length
  let reader:=(SemiprimeD1StackOwnerLookup.result q (prefixRows ids) []).2
  let before:=view D K chosen q pfx [] [] [] [] []
  let copied:=view D K chosen q pfx [] [] [] D []
  have h0:=copy_call .dictionary .lookup .lookupCall rfl before D [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update before (lookupStack (.inr .reader)) D) at h0
  rw [view_lookup_reader] at h0
  change Runs program _ _ _ _ copied at h0
  obtain ⟨t,ht,h1⟩:=lookup_call copied q (prefixRows ids) (by
    intro k;rcases k with k|k <;> cases k <;> rfl)
  have he:Sum.elim (SemiprimeD1StackOwnerLookup.done q (prefixRows ids) []).data (fun k=>copied (aux k))=
      view D K chosen q pfx [] [] [] reader (markedRead ids (bitValue q)):=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | exact lookup_prefix q ids
    · cases k <;> rfl
  rw [he] at h1
  have h2:=result_pop D K chosen q pfx reader (SemiprimeSourceHistogramPrefix.expected ids (bitValue q))
    (decide (bitValue q < ids.length))
  simp only [decide_eq_true_eq] at h2
  change Runs program 2 _ (view D K chosen q pfx [] [] [] reader (markedRead ids (bitValue q))) _ _ at h2
  have h3:=drain_loop .clearReader (ctl .done) (lookupStack (.inr .reader)) rfl
    (view D K chosen q pfx [] [] [decide (bitValue q < ids.length)] reader
      (if bitValue q < ids.length then SemiprimeSourceHistogramPrefix.expected ids (bitValue q) else [])) reader rfl
  rw [view_lookup_reader] at h3
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,h⟩
  have hr:=result_tail_le q (prefixRows ids)
  change reader.length≤D.length at hr
  change t≤100*(q.length+1)*(D.length+1)+1 at ht
  change _≤200*(q.length+1)*(D.length+1)
  nlinarith
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentLookup
