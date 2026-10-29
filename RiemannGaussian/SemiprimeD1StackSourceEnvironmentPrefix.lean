/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentReverse
/-! # Whole oldest-first physical prefix extension loop
Each parsed ID calls the SAMEliteral extension entry and pays its real return.
The original selected prefix remains newest first; no count/key/dictionary or
function is a runtime operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentPrefix
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentPrimitives
open SemiprimeD1StackSourceEnvironmentEncoding SemiprimeD1StackSourceEnvironmentView
open SemiprimeD1StackSourceEnvironmentExtend SemiprimeD1StackSourceEnvironmentReverse
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Real parsed oldest-first ID, SAMEreal extension call/return, and complete chosen-word drain. -/
theorem old_step (prev:List (List Bool)) (id q pfx tail found lookupReader out:List Bool) :
    ∃t≤200*(id.length+prev.length+1),Runs program t (ctl .readOld)
      (view (dictionary prev) (variableKey prev.length) [] q pfx (true::frame id tail) [] found lookupReader out)
      (ctl .readOld)
      (view (dictionary (id::prev)) (variableKey (id::prev).length) [] q pfx tail [] found lookupReader out) :=by
  have h0:=parse_step true (dictionary prev) (variableKey prev.length) q pfx tail [] id found lookupReader out
  obtain ⟨t,ht,h1⟩:=extend_trace
    (view (dictionary prev) (variableKey prev.length) id q pfx tail [] found lookupReader out)
    (dictionary prev) (variableKey prev.length) id rfl rfl rfl (view_clear _ _ _ _ _ _ _ _ _ _)
  rw [view_dictionary,view_nextKey] at h1
  rw [←dictionary_cons,←variableKey_succ] at h1
  have h2:=local_call .extendPrefix .extend .clearOld rfl t _ _ h1
  have h3:=drain_loop .clearOld (ctl .readOld) (aux .chosenID) rfl
    (view (dictionary (id::prev)) (variableKey (prev.length+1)) id q pfx tail [] found lookupReader out) id rfl
  rw [view_chosenID] at h3
  have h:=join (join h0 h2) h3
  refine ⟨_,?_,h⟩
  have hk:=variableKey_length prev.length
  omega
/-- Own primitive sum cap for physical oldest-first fields and real per-ID returns. -/
def oldClock (k:Nat) (ids:List (List Bool)) :Nat :=
  200*((ids.map List.length).sum+ids.length*(k+ids.length+1))+2
/-- Every actual remaining ID contributes one real extension and one physically advanced compact key. -/
theorem old_loop (prev ids:List (List Bool)) (q pfx found lookupReader out:List Bool) :
    ∃t≤oldClock prev.length ids,Runs program t (ctl .readOld)
      (view (dictionary prev) (variableKey prev.length) [] q pfx (vectorBits ids) [] found lookupReader out)
      (ctl .done)
      (view (dictionary (ids.reverse++prev)) (variableKey (ids.reverse++prev).length) [] q pfx [] [] found lookupReader out) :=by
  induction ids generalizing prev with
  | nil=>
    have h0:=pop_run .readOld (ctl .abort) (ctl .oldEOF) (ctl .parseOld) (aux .reader)
      (view (dictionary prev) (variableKey prev.length) [] q pfx [false] [] found lookupReader out) [false] rfl rfl
    change Runs program 1 _ _ (ctl .oldEOF) _ at h0
    rw [view_reader] at h0
    have h1:=peek_run .oldEOF (ctl .done) (ctl .abort) (ctl .abort) (aux .reader)
      (view (dictionary prev) (variableKey prev.length) [] q pfx [] [] found lookupReader out) [] rfl rfl
    exact ⟨2,by simp [oldClock],join h0 h1⟩
  | cons id ids ih=>
    obtain ⟨a,ha,h0⟩:=old_step prev id q pfx (vectorBits ids) found lookupReader out
    obtain ⟨b,hb,h1⟩:=ih (id::prev)
    have h:=join h0 h1
    have he:ids.reverse++id::prev=(id::ids).reverse++prev:=by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    rw [he] at h
    refine ⟨a+b,?_,h⟩
    unfold oldClock at *
    simp only [List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith
/-- Actual prefix-extension clock is quadratic in the physical vector bytes, including all padded payloads. -/
theorem oldClock_le (ids:List (List Bool)) :oldClock 0 ids≤1000*((vectorBits ids).length+1)^2 :=by
  unfold oldClock
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length]
  simp only [Nat.zero_add]
  nlinarith only [Nat.zero_le ((ids.map List.length).sum^2),Nat.zero_le (ids.length^2),
    Nat.zero_le ((ids.map List.length).sum*ids.length)]
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentPrefix
