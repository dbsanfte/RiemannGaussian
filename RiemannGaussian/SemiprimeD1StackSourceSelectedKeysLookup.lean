/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysView
/-! # Actual TRUEfound guarded ID lookup, paid ID saves and complete temporary cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLookup
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysPrimitives SemiprimeD1StackSourceSelectedKeysView
open SemiprimeD1StackProcedureTrace
/-- Proof-side current raw variable-key word, determined by the fixed owner/factor source address. -/
def queryWord :Part→List Bool→List Bool→List Bool | .owner,own,_=>own | .factor,_,fac=>fac
/-- The actual key address retains the physically parsed bytes for its fixed role. -/
theorem variable_projection (i:Inputs) (q present returned reader own fac ownID key valid buffer hist out:List Bool) (part:Part) :
    view i q present returned reader own fac ownID key valid buffer hist out (variableKey part)=queryWord part own fac :=by
  cases part <;> rfl
/-- Own actual complete-copy/lookup clock for the current physically acquired variable key. -/
def lookupClock (i:Inputs) (word:List Bool) :Nat :=
  201*(word.length+1)*((Env.dictionary i.ids).length+1)+10*(word.length+(readID i.ids word).length+1)+20
/-- Physical key copy and real dictionary call reach actualfoundTRUE; fixedIDzero remains a valid present payload. -/
theorem lookup_stage (i:Inputs) (part:Part) (reader own fac ownID key valid buffer hist out:List Bool)
    (hp:SemiprimeBitArithmetic.bitValue (queryWord part own fac) < i.ids.length) :
    ∃t≤201*((queryWord part own fac).length+1)*((Env.dictionary i.ids).length+1)+5*(queryWord part own fac).length+5,
      Runs program t (.copyQuery part) (view i [] [] [] reader own fac ownID key valid buffer hist out) (.readFound part)
        (view i (queryWord part own fac) [true] (readID i.ids (queryWord part own fac)) reader own fac ownID key valid buffer hist out) :=by
  have h0:=copy_call (.query part) (.copyQuery part) (.lookup part) rfl
    (view i [] [] [] reader own fac ownID key valid buffer hist out) rfl rfl
  change Runs program (5*(view i [] [] [] reader own fac ownID key valid buffer hist out (variableKey part)).length+4) _ _ _
    (Function.update (view i [] [] [] reader own fac ownID key valid buffer hist out) query
      (view i [] [] [] reader own fac ownID key valid buffer hist out (variableKey part))) at h0
  rw [variable_projection,update_q] at h0
  change Runs program (5*(queryWord part own fac).length+4) _ _ _
    (view i (queryWord part own fac) [] [] reader own fac ownID key valid buffer hist out) at h0
  obtain ⟨t,ht,h1⟩:=lookup_call part (view i (queryWord part own fac) [] [] reader own fac ownID key valid buffer hist out)
    i.ids i.chosen (queryWord part own fac) i.pfx
    (environment_projection i (queryWord part own fac) reader own fac ownID key valid buffer hist out)
  have he:Sum.elim (SemiprimeD1StackSourceEnvironmentExecution.lookupDone i.ids i.chosen (queryWord part own fac) i.pfx).data
      (fun k=>view i (queryWord part own fac) [] [] reader own fac ownID key valid buffer hist out (aux k))=
      view i (queryWord part own fac) [decide (SemiprimeBitArithmetic.bitValue (queryWord part own fac) < i.ids.length)]
        (if SemiprimeBitArithmetic.bitValue (queryWord part own fac) < i.ids.length then
          readID i.ids (queryWord part own fac) else []) reader own fac ownID key valid buffer hist out:=by
    funext k
    rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at h1
  simp only [hp,decide_true,ite_true] at h1
  exact ⟨_,by omega,join h0 h1⟩
/-- The actual true-found singleton is physically popped before any returned ID is used. -/
theorem found_true (i:Inputs) (part:Part) (q returned reader own fac ownID key valid buffer hist out:List Bool) :
    Runs program 1 (.readFound part) (view i q [true] returned reader own fac ownID key valid buffer hist out) (.copyID part)
      (view i q [] returned reader own fac ownID key valid buffer hist out) :=by
  have h:=pop_run (.readFound part) .abort .abort (.copyID part) found
    (view i q [true] returned reader own fac ownID key valid buffer hist out) [true] rfl rfl
  change Runs program 1 _ _ _
    (Function.update (view i q [true] returned reader own fac ownID key valid buffer hist out) found []) at h
  rw [update_present] at h
  exact h
/-- The actual owner ID is saved before the second physical lookup changes the shared returned-ID slot. -/
theorem save_owner (i:Inputs) (q returned reader own fac valid buffer hist out:List Bool) :
    Runs program (5*returned.length+4) (.copyID .owner) (view i q [] returned reader own fac [] [] valid buffer hist out)
      (.clearID .owner) (view i q [] returned reader own fac returned [] valid buffer hist out) :=by
  have h:=copy_call (.id .owner) (.copyID .owner) (.clearID .owner) rfl
    (view i q [] returned reader own fac [] [] valid buffer hist out) rfl rfl
  change Runs program (5*returned.length+4) _ _ _
    (Function.update (view i q [] returned reader own fac [] [] valid buffer hist out) (aux .ownerID) returned) at h
  rw [update_ownID] at h
  exact h
/-- The actual factor ID is copied directly into the eventual joint-key raw tail, paying every bit. -/
theorem save_factor (i:Inputs) (q returned reader own fac ownID valid buffer hist out:List Bool) :
    Runs program (5*returned.length+4) (.copyID .factor) (view i q [] returned reader own fac ownID [] valid buffer hist out)
      (.clearID .factor) (view i q [] returned reader own fac ownID returned valid buffer hist out) :=by
  have h:=copy_call (.id .factor) (.copyID .factor) (.clearID .factor) rfl
    (view i q [] returned reader own fac ownID [] valid buffer hist out) rfl rfl
  change Runs program (5*returned.length+4) _ _ _
    (Function.update (view i q [] returned reader own fac ownID [] valid buffer hist out) (aux .key) returned) at h
  rw [update_key] at h
  exact h
/-- Each actual returned ID and query is physically drained, restoring the shared Env25 operation slots. -/
theorem cleanup (i:Inputs) (part:Part) (q returned reader own fac ownID key valid buffer hist out:List Bool) :
    Runs program ((returned.length+1)+(q.length+1)) (.clearID part)
      (view i q [] returned reader own fac ownID key valid buffer hist out) (afterLookup part)
      (view i [] [] [] reader own fac ownID key valid buffer hist out) :=by
  have h0:=drain_loop (.clearID part) (.clearQuery part) idOutput rfl
    (view i q [] returned reader own fac ownID key valid buffer hist out) returned rfl
  rw [update_returned] at h0
  have h1:=drain_loop (.clearQuery part) (afterLookup part) query rfl
    (view i q [] [] reader own fac ownID key valid buffer hist out) q rfl
  rw [update_q] at h1
  exact join h0 h1
/-- Complete actual owner-ID read with a true-found guard and all shared lookup temporaries cleared. -/
theorem owner_run (i:Inputs) (reader own fac hist:List Bool) (hp:SemiprimeBitArithmetic.bitValue own < i.ids.length) :
    ∃q≤lookupClock i own,Runs program q (.copyQuery .owner) (view i [] [] [] reader own fac [] [] [] [] hist [])
      (.copyQuery .factor) (view i [] [] [] reader own fac (readID i.ids own) [] [] [] hist []) :=by
  obtain ⟨q,hq,h0⟩:=lookup_stage i .owner reader own fac [] [] [] [] hist [] hp
  have h1:=found_true i .owner own (readID i.ids own) reader own fac [] [] [] [] hist []
  have h2:=save_owner i own (readID i.ids own) reader own fac [] [] hist []
  have h3:=cleanup i .owner own (readID i.ids own) reader own fac (readID i.ids own) [] [] [] hist []
  refine ⟨_,?_,join (join (join h0 h1) h2) h3⟩
  unfold lookupClock
  change q≤201*(own.length+1)*((Env.dictionary i.ids).length+1)+5*own.length+5 at hq
  omega
/-- Complete actual factor-ID read leaves the saved owner ID and RAWfactor-ID joint tail ready for real Frame. -/
theorem factor_run (i:Inputs) (reader own fac hist:List Bool) (hp:SemiprimeBitArithmetic.bitValue fac < i.ids.length) :
    ∃q≤lookupClock i fac,Runs program q (.copyQuery .factor)
      (view i [] [] [] reader own fac (readID i.ids own) [] [] [] hist []) .frameJoint
      (view i [] [] [] reader own fac (readID i.ids own) (readID i.ids fac) [] [] hist []) :=by
  obtain ⟨q,hq,h0⟩:=lookup_stage i .factor reader own fac (readID i.ids own) [] [] [] hist [] hp
  have h1:=found_true i .factor fac (readID i.ids fac) reader own fac (readID i.ids own) [] [] [] hist []
  have h2:=save_factor i fac (readID i.ids fac) reader own fac (readID i.ids own) [] [] hist []
  have h3:=cleanup i .factor fac (readID i.ids fac) reader own fac (readID i.ids own) (readID i.ids fac) [] [] hist []
  refine ⟨_,?_,join (join (join h0 h1) h2) h3⟩
  unfold lookupClock
  change q≤201*(fac.length+1)*((Env.dictionary i.ids).length+1)+5*fac.length+5 at hq
  omega
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLookup
