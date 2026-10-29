/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectPrimitives
/-! # Exact paid removal of a temporary candidate dictionary head
Two real field calls expose the identical old dictionary tail. Actual drains
clear both parsed fields, the temporary key and candidate; the acquired old key
is restored only by the real preserving-copy program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectRollback
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Complete physical bank during rollback; all other58 fields are retained verbatim. -/
def view (retained:Stack→List Bool) (dict key id parsed valid:List Bool) :Stack→List Bool :=
  fun k=>if k=dictionary then dict else if k=nextKey then key else if k=candidate then id
    else if k=aux .discard then parsed else if k=aux .valid then valid else retained k
/-- One real dict update preserves all other physical words. -/
theorem update_dict (retained:Stack→List Bool) (dict key id parsed valid word:List Bool) :
    Function.update (view retained dict key id parsed valid) (dictionary) word=view retained word key id parsed valid :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One real key update preserves all other physical words. -/
theorem update_key (retained:Stack→List Bool) (dict key id parsed valid word:List Bool) :
    Function.update (view retained dict key id parsed valid) (nextKey) word=view retained dict word id parsed valid :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One real id update preserves all other physical words. -/
theorem update_id (retained:Stack→List Bool) (dict key id parsed valid word:List Bool) :
    Function.update (view retained dict key id parsed valid) (candidate) word=view retained dict key word parsed valid :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One real parsed update preserves all other physical words. -/
theorem update_parsed (retained:Stack→List Bool) (dict key id parsed valid word:List Bool) :
    Function.update (view retained dict key id parsed valid) (aux .discard) word=view retained dict key id word valid :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- One real valid update preserves all other physical words. -/
theorem update_valid (retained:Stack→List Bool) (dict key id parsed valid word:List Bool) :
    Function.update (view retained dict key id parsed valid) (aux .valid) word=view retained dict key id parsed word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Actual rollback visits both complete fields, restores only a physically saved key and leaves the literal old tail. -/
theorem rollback_run (retained:Stack→List Bool) (dict parsedKey value newKey oldKey id:List Bool)
    (hp:retained (aux .parserScratch)=[]) (hc:retained (aux .copyScratch)=[])
    (hk:retained (aux .savedKey)=oldKey) :
    Runs program (9*parsedKey.length+9*value.length+newKey.length+5*oldKey.length+id.length+25)
      (ctl .rollbackTag)
      (view retained (true::frame parsedKey (frame value dict)) newKey id [] [])
      (ctl (.header false)) (view retained dict oldKey [] [] []) :=by
  have h0:=pop_run .rollbackTag (ctl .abort) (ctl .abort) (ctl .rollbackKey) dictionary
    (view retained (true::frame parsedKey (frame value dict)) newKey id [] [])
    (true::frame parsedKey (frame value dict)) rfl rfl
  change Runs program 1 _ _ _
    (Function.update (view retained (true::frame parsedKey (frame value dict)) newKey id [] []) dictionary
      (frame parsedKey (frame value dict))) at h0
  rw [update_dict] at h0
  have h1:=field_call .rollback .rollbackKey .rollbackKeyValid rfl
    (view retained (frame parsedKey (frame value dict)) newKey id [] []) parsedKey (frame value dict)
    rfl rfl hp rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update
      (view retained (frame parsedKey (frame value dict)) newKey id [] []) dictionary (frame value dict))
      (aux .discard) parsedKey) (aux .valid) [true]) at h1
  rw [update_dict,update_parsed,update_valid] at h1
  have h2:=pop_run .rollbackKeyValid (ctl .abort) (ctl .abort) (ctl .drainRollbackKey) (aux .valid)
    (view retained (frame value dict) newKey id parsedKey [true]) [true] rfl rfl
  change Runs program 1 _ _ _
    (Function.update (view retained (frame value dict) newKey id parsedKey [true]) (aux .valid) []) at h2
  rw [update_valid] at h2
  have h3:=drain_loop .drainRollbackKey (ctl .rollbackValue) (aux .discard) rfl
    (view retained (frame value dict) newKey id parsedKey []) parsedKey rfl
  rw [update_parsed] at h3
  have h4:=field_call .rollback .rollbackValue .rollbackValueValid rfl
    (view retained (frame value dict) newKey id [] []) value dict rfl rfl hp rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update
      (view retained (frame value dict) newKey id [] []) dictionary dict) (aux .discard) value) (aux .valid) [true]) at h4
  rw [update_dict,update_parsed,update_valid] at h4
  have h5:=pop_run .rollbackValueValid (ctl .abort) (ctl .abort) (ctl .drainRollbackValue) (aux .valid)
    (view retained dict newKey id value [true]) [true] rfl rfl
  change Runs program 1 _ _ _
    (Function.update (view retained dict newKey id value [true]) (aux .valid) []) at h5
  rw [update_valid] at h5
  have h6:=drain_loop .drainRollbackValue (ctl .clearTempKey) (aux .discard) rfl
    (view retained dict newKey id value []) value rfl
  rw [update_parsed] at h6
  have h7:=drain_loop .clearTempKey (ctl .restoreKey) nextKey rfl
    (view retained dict newKey id [] []) newKey rfl
  rw [update_key] at h7
  have h8:=copy_call .restoreKey .restoreKey .clearCandidate rfl
    (view retained dict [] id [] []) oldKey [] hk rfl hc
  change Runs program _ _ _ _
    (Function.update (view retained dict [] id [] []) nextKey (oldKey++[])) at h8
  rw [List.append_nil,update_key] at h8
  have h9:=drain_loop .clearCandidate (ctl (.header false)) candidate rfl
    (view retained dict oldKey id [] []) id rfl
  rw [update_id] at h9
  have h:=join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9
  have ht:1+(8*parsedKey.length+7)+1+(parsedKey.length+1)+(8*value.length+7)+1+
      (value.length+1)+(newKey.length+1)+(5*oldKey.length+4)+(id.length+1)=
      9*parsedKey.length+9*value.length+newKey.length+5*oldKey.length+id.length+25:=by omega
  simpa only [ht] using h
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectRollback
