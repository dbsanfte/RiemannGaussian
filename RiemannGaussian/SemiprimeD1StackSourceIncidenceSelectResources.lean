/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectEncoding
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentBounds
/-! # Physical retained-prefix inventories for the actual selector
The bounds concern literal key, marked-ID and selected-vector bytes. They do not
transport any old native query clock or assume a supplied environment budget.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectResources
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace E
export SemiprimeD1StackSourceEnvironmentEncoding (dictionary marked normalize variableKey)
end E
/-- Every retained physical selected-ID byte contributes to the actual copied prefix mass. -/
def mass (ids:List (List Bool)) :Nat :=(ids.map List.length).sum
/-- A menu word-width bound applies to every actual copied selected prefix word. -/
theorem mass_le (ids:List (List Bool)) (W:Nat) (h:∀id∈ids,id.length ≤ W) :mass ids ≤ ids.length*W :=by
  induction ids with
  | nil=>simp only [mass,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons id ids ih=>
    have hh:=h id List.mem_cons_self
    have ht:=ih (fun id hid=>h id (List.mem_cons_of_mem _ hid))
    simp only [mass,List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul] at ⊢ ht
    omega
/-- Every actual compact key increment and normalized marked ID has a charged literal dictionary width. -/
theorem dictionary_length_le (ids:List (List Bool)) :
    (E.dictionary ids).length ≤ 2*mass ids+2*ids.length^2+5*ids.length+1 :=by
  induction ids with
  | nil=>exact Nat.le_refl 1
  | cons id ids ih=>
    have hk:=SemiprimeD1StackSourceEnvironmentEncoding.variableKey_length ids.length
    have hn:=SemiprimeD1StackSourceEnvironmentEncoding.normalize_length id
    rw [SemiprimeD1StackSourceEnvironmentEncoding.dictionary_cons]
    simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,
      SemiprimeD1StackSourceEnvironmentEncoding.marked,List.length_cons,mass,List.map_cons,List.sum_cons] at ⊢
    change (E.dictionary ids).length ≤ 2*(ids.map List.length).sum+2*ids.length^2+5*ids.length+1 at ih
    nlinarith
/-- All candidate and previous-prefix dictionaries remain quadratic in actual variable markers and acquired menu width. -/
theorem dictionary_uniform (ids:List (List Bool)) (S:Nat) (hn:ids.length ≤ S)
    (hw:∀id∈ids,id.length ≤ S) :(E.dictionary ids).length ≤ 10*(S+1)^2 :=by
  have hm:=mass_le ids S hw
  have hmul:=Nat.mul_le_mul_right S hn
  have hp:=Nat.pow_le_pow_left hn 2
  have hd:=dictionary_length_le ids
  nlinarith
/-- The selected vector retains the same actual ID bytes, in newest-first order. -/
theorem vector_uniform (ids:List (List Bool)) (S:Nat) (hn:ids.length ≤ S)
    (hw:∀id∈ids,id.length ≤ S) :(vectorBits ids).length ≤ 5*(S+1)^2 :=by
  have hm:=mass_le ids S hw
  have hmul:=Nat.mul_le_mul_right S hn
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length]
  change (ids.map List.length).sum ≤ ids.length*S at hm
  nlinarith
/-- Temporary dictionary prefix and retained selected-vector prefix may differ by the actual installed candidate. -/
theorem cache_uniform (ids pfx:List (List Bool)) (chosen:List Bool) (S:Nat)
    (hn:ids.length ≤ S) (hpn:pfx.length ≤ S) (hc:chosen.length ≤ S)
    (hw:∀id∈ids,id.length ≤ S) (hpw:∀id∈pfx,id.length ≤ S) :
    SemiprimeD1StackSourceEnvironmentBounds.cacheSize ids chosen [] (vectorBits pfx) ≤ 20*(S+1)^2 :=by
  have hd:=dictionary_uniform ids S hn hw
  have hv:=vector_uniform pfx S hpn hpw
  have hk:=SemiprimeD1StackSourceEnvironmentEncoding.variableKey_length ids.length
  unfold SemiprimeD1StackSourceEnvironmentBounds.cacheSize
  simp only [List.length_nil]
  nlinarith
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectResources
