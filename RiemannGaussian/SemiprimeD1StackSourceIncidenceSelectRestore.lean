/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectView
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectRollback
/-! # Exact acquired-prefix cache after the actual candidate rollback
No dictionary snapshot or reconstruction occurs. The literal old dictionary
survives both real field parses; the only key restoration is the paid copy of
its actual saved word, and the temporary chosen ID is really drained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectRestore
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectView
open SemiprimeD1StackProcedureTrace
namespace E
export SemiprimeD1StackSourceEnvironmentEncoding (dictionary variableKey marked)
end E
local notation "ctl" => Label.local
/-- The complete retained real cache returns to its old prefix after removing precisely one actual head. -/
theorem restore_run (ids:List (List Bool))
    (id pfx stream square cube fourth catalogue owners factors todo reader bestID bestScore:List Bool) :
    ∃t ≤ 50*((E.variableKey ids.length).length+id.length+1),
      Runs program t (ctl .rollbackTag)
        (clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo reader
          (E.variableKey ids.length) bestID bestScore [])
        (ctl (.header false))
        (clean ids [] pfx stream square cube fourth catalogue owners factors todo reader
          (E.variableKey ids.length) bestID bestScore []) :=by
  let before:=clean (id::ids) id pfx stream square cube fourth catalogue owners factors todo reader
    (E.variableKey ids.length) bestID bestScore []
  let key:=E.variableKey ids.length
  let newKey:=E.variableKey (id::ids).length
  let value:=E.marked id
  have h:=SemiprimeD1StackSourceIncidenceSelectRollback.rollback_run before (E.dictionary ids) key value newKey key id rfl rfl rfl
  have hi:SemiprimeD1StackSourceIncidenceSelectRollback.view before
      (true::SemiprimeSourceHistogramKeyBits.frame key (SemiprimeSourceHistogramKeyBits.frame value (E.dictionary ids)))
      newKey id [] []=before:=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  have ho:SemiprimeD1StackSourceIncidenceSelectRollback.view before (E.dictionary ids) key [] [] []=
      clean ids [] pfx stream square cube fourth catalogue owners factors todo reader key bestID bestScore []:=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [hi,ho] at h
  have hn: newKey.length ≤ key.length+1:=by
    simpa only [newKey,key,List.length_cons,SemiprimeD1StackSourceEnvironmentEncoding.variableKey_succ] using
      SemiprimeD1StackSourceEnvironmentEncoding.successor_length key
  have hv: value.length ≤ id.length+1:=by
    have hh:=SemiprimeD1StackSourceEnvironmentEncoding.normalize_length id
    change (true::SemiprimeD1StackSourceEnvironmentEncoding.normalize id).length ≤ _
    simp only [List.length_cons]
    omega
  have ht:9*key.length+9*value.length+newKey.length+5*key.length+id.length+25 ≤
      50*(key.length+id.length+1):=by omega
  exact ⟨_,ht,h⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectRestore
