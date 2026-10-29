/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMap
import RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
/-! # Actual generated activation-map records have quadratic paid-byte size
Every key is the actual raw full-adder output and every value one literal
computed bit. High-zero padding is charged additively, independently of key
numeric value, with no supplied map/count/decoder or native clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMapBounds
open SemiprimeD1StackChildGroupFactory
namespace A
export SemiprimeD1StackChildGroupFactoryActivationMap (entries)
export SemiprimeD1StackChildGroupFactoryActivationLoop (Row advance advance_length)
end A
/-- Every actual iteration logs exactly one physical numeric-key/Boolean-value record. -/
theorem entries_length (i:Inputs) (coordinate:Nat) (rows:List A.Row) (key:List Bool):
    (A.entries i coordinate key rows).length=rows.length:=by
  induction rows generalizing key with
  | nil=>rfl
  | cons r rs ih=>simp only [A.entries,List.length_append,List.length_cons,List.length_nil,ih]
/-- Every physically generated map field has an actual visited-marker width bound. -/
theorem entry_lengths (i:Inputs) (coordinate:Nat) (rows:List A.Row) (key:List Bool)
    (p:List Bool×List Bool) (hp:p∈A.entries i coordinate key rows):
    p.1.length≤key.length+2*rows.length ∧ p.2.length=1:=by
  induction rows generalizing key with
  | nil=>simp only [A.entries,List.not_mem_nil] at hp
  | cons r rs ih=>
    simp only [A.entries,List.mem_append,List.mem_singleton] at hp
    rcases hp with hp|hp
    · have ht:=ih (A.advance key) hp
      have ha:=A.advance_length key
      simp only [List.length_cons];constructor <;> omega
    · subst p
      exact ⟨Nat.le_add_right _ _,rfl⟩
private theorem sum_le {T:Type} (xs:List T) (f:T→Nat) (cap:Nat) (h:∀x∈xs,f x≤cap):
    (xs.map f).sum≤xs.length*cap:=by
  induction xs with
  | nil=>simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons x xs ih=>
    have hh:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith
/-- Complete actual map bytes, including the real terminator, have a fixed quadratic estimate. -/
theorem records_length (i:Inputs) (coordinate:Nat) (rows:List A.Row) (key:List Bool):
    (SemiprimeD1StackOwnerLookup.records (A.entries i coordinate key rows) []).length≤
      2*rows.length*(key.length+2*rows.length+1)+3*rows.length+1:=by
  have hs:=sum_le (A.entries i coordinate key rows) (fun p=>p.1.length+p.2.length)
    (key.length+2*rows.length+1) (by
      intro p hp
      have h:=entry_lengths i coordinate rows key p hp
      omega)
  rw [entries_length] at hs
  rw [SemiprimeD1StackOwnerLookupBounds.records_length,entries_length]
  simp only [List.length_nil]
  nlinarith
/-- Actual whole-entry zero-key map is bounded solely by the physically acquired marker count. -/
theorem zero_records_length (i:Inputs) (coordinate:Nat) (rows:List A.Row):
    (SemiprimeD1StackOwnerLookup.records (A.entries i coordinate [] rows) []).length≤10*(rows.length+1)^2:=by
  have h:=records_length i coordinate rows []
  simp only [List.length_nil,Nat.zero_add] at h
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMapBounds
