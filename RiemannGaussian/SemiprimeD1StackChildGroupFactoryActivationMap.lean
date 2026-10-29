/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationSource
import RiemannGaussian.SemiprimeD1StackOwnerLookupOriginal
/-! # Actual generated activation map supplies endpoint flags
The numeric-key proof covers padded physical occurrence keys. The map is
constructed by the actual activation loop, with no supplied mask or permutation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMap
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactory
open SemiprimeD1StackChildGroupFactoryActivationView SemiprimeD1StackChildGroupFactoryActivationLoop
open SemiprimeBitArithmetic (bitValue)
namespace Lookup
export SemiprimeD1StackOwnerLookup (records result)
end Lookup
/-- Original numeric iteration order of physically acquired activation bits. -/
def flags (i:Inputs) (coordinate:Nat) (rows:List Row):List Bool:=rows.map fun row=>active i coordinate row.colours
/-- Newest-first physical key/flag records emitted by the real frame logger. -/
def entries (i:Inputs) (coordinate:Nat):List Bool→List Row→List (List Bool×List Bool)
  | _,[]=>[]
  | key,row::rows=>entries i coordinate (advance key) rows++[(key,[active i coordinate row.colours])]
/-- Exact bytes of the real logged map, preserving an arbitrary earlier map and suffix. -/
theorem finish_map (i:Inputs) (coordinate:Nat) (rows:List Row) (key hist:List Bool)
    (old:List (List Bool×List Bool)) (tail:List Bool):
    (finish i coordinate key hist (Lookup.records old tail) rows).map=
      Lookup.records (entries i coordinate key rows++old) tail:=by
  induction rows generalizing key hist old with
  | nil=>rfl
  | cons row rows ih=>
    have h:=ih (advance key) (active i coordinate row.colours::hist)
      ((key,[active i coordinate row.colours])::old)
    simpa only [finish,entries,List.append_assoc,List.singleton_append,Lookup.records] using h
/-- Every row's actual generated key has its original numeric position. -/
theorem entries_get (i:Inputs) (coordinate:Nat) (rows:List Row) (key:List Bool) (j:Nat) (hj:j<rows.length):
    ∃word,(word,[(flags i coordinate rows).getD j false])∈entries i coordinate key rows ∧
      bitValue word=bitValue key+j:=by
  induction rows generalizing key j with
  | nil=>simp only [List.length_nil] at hj;omega
  | cons row rows ih=>
    cases j with
    | zero=>
      refine ⟨key,?_,by omega⟩
      simp only [flags,List.map_cons,List.getD_cons_zero,entries]
      exact List.mem_append_right _ (List.mem_cons_self)
    | succ j=>
      have hj':j<rows.length:=by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj
      obtain ⟨word,hw,hvalue⟩:=ih (advance key) j hj'
      refine ⟨word,?_,?_⟩
      · simp only [flags,List.map_cons,List.getD_cons_succ,entries]
        exact List.mem_append_left _ hw
      · rw [advance_value] at hvalue
        omega
/-- All keys arise from the actual binary increment sequence; their payload is the actual logged Boolean. -/
theorem entries_member (i:Inputs) (coordinate:Nat) (rows:List Row) (key word value:List Bool)
    (hm:(word,value)∈entries i coordinate key rows):
    ∃j,j<rows.length ∧ bitValue word=bitValue key+j ∧ value=[(flags i coordinate rows).getD j false]:=by
  induction rows generalizing key with
  | nil=>simp only [entries,List.not_mem_nil] at hm
  | cons row rows ih=>
    simp only [entries,List.mem_append,List.mem_singleton] at hm
    rcases hm with hm|hm
    · obtain ⟨j,hj,hvalue,hpayload⟩:=ih (advance key) hm
      refine ⟨j+1,by simp only [List.length_cons];omega,?_,?_⟩
      · rw [advance_value] at hvalue
        omega
      · simpa only [flags,List.map_cons,List.getD_cons_succ] using hpayload
    · cases hm
      refine ⟨0,by simp only [List.length_cons];omega,by omega,?_⟩
      simp only [flags,List.map_cons,List.getD_cons_zero]
/-- Numeric WordEqual on any padded occurrence key computes the corresponding real activation flag. -/
theorem lookup_value (i:Inputs) (coordinate:Nat) (rows:List Row) (key query:List Bool)
    (j:Nat) (hj:j<rows.length) (hq:bitValue query=bitValue key+j):
    (Lookup.result query (entries i coordinate key rows) []).1=[(flags i coordinate rows).getD j false]:=by
  apply SemiprimeD1StackOwnerLookupOriginal.result_value
  · obtain ⟨word,hw,hv⟩:=entries_get i coordinate rows key j hj
    exact ⟨word,hw,hv.trans hq.symm⟩
  · intro word value hm hv
    obtain ⟨k,hk,hvalue,hpayload⟩:=entries_member i coordinate rows key word value hm
    have he:k=j:=by omega
    simpa only [he] using hpayload
/-- The map retained by the actual source prefix is exactly the generated records; no mask advice is assumed. -/
theorem source_map (i:Inputs) (coordinate:Nat) (rows:List Row):
    SemiprimeD1StackChildGroupFactoryActivationSource.result i coordinate rows (aux .activationMap)=
      Lookup.records (entries i coordinate [] rows) []:=by
  change (finish i coordinate [] [] (Lookup.records [] []) rows).map=_
  rw [finish_map]
  simp only [List.append_nil]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMap
