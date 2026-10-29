/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentEncoding
/-! # Exact physical temporary-head and catalogue row layouts
These identities describe the bytes consumed by two real Field calls. The old
dictionary survives as the identical unconsumed tail; rollback does not rebuild
it from selected IDs or obtain any dictionary value from a runtime getter.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectEncoding
namespace K
export SemiprimeSourceHistogramKeyBits (frame split)
end K
namespace E
export SemiprimeD1StackSourceEnvironmentEncoding (marked dictionary variableKey)
end E
/-- The real environment extension prepends this exact tagged two-field head. -/
def head (key value tail:List Bool) :List Bool :=true::K.frame key (K.frame value tail)
/-- After the actual true-tag pop, the first physical field exposes the complete marked-value frame. -/
theorem head_key (key value tail:List Bool) :
    (K.split (head key value tail).tail).first=key ∧
      (K.split (head key value tail).tail).rest=K.frame value tail ∧
      (K.split (head key value tail).tail).valid=true :=
  SemiprimeSourceHistogramKeyBits.split_frame key (K.frame value tail)
/-- The second actual field parse leaves exactly the old tail, even when either field is empty. -/
theorem head_cancel (key value tail:List Bool) :
    (K.split (K.split (head key value tail).tail).rest).first=value ∧
      (K.split (K.split (head key value tail).tail).rest).rest=tail ∧
      (K.split (K.split (head key value tail).tail).rest).valid=true :=by
  rw [(head_key key value tail).2.1]
  exact SemiprimeSourceHistogramKeyBits.split_frame value tail
/-- The actual appended temporary dictionary head includes only the current acquired key and marked chosen ID. -/
theorem environment_head (id:List Bool) (ids:List (List Bool)) :
    E.dictionary (id::ids)=head (E.variableKey ids.length) (E.marked id) (E.dictionary ids) :=rfl
/-- Rollback of an actual temporary prefix extension preserves its exact old physical dictionary. -/
theorem environment_cancel (id:List Bool) (ids:List (List Bool)) :
    (K.split (K.split (E.dictionary (id::ids)).tail).rest).rest=E.dictionary ids :=by
  rw [environment_head]
  exact (head_cancel _ _ _).2.1
/-- Real head field byte lengths are charged separately from the retained dictionary tail. -/
theorem head_length (key value tail:List Bool) :
    (head key value tail).length=2*key.length+2*value.length+tail.length+3 :=by
  simp only [head,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Every catalogue record has the same actual tagged ID/colour layout consumed by the candidate scan. -/
theorem catalogue_cons (id colour:List Bool) (rows:List (List Bool×List Bool)) :
    SemiprimeD1StackOwnerLookup.records ((id,colour)::rows) []=
      head id colour (SemiprimeD1StackOwnerLookup.records rows []) :=rfl
/-- The actual false catalogue terminator is a single physical byte; no supplied catalogue length is read. -/
theorem catalogue_nil :SemiprimeD1StackOwnerLookup.records [] []=[false] :=rfl
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectEncoding
