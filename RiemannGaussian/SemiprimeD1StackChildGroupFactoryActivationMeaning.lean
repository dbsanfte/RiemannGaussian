/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLoop
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentMeaning
import RiemannGaussian.SemiprimeD1ChildActivation
/-! # Acquired complete environment supplies every real activation row
The plan is a proof interpretation of the retained environment/catalogue;
no plan, ID list, decoded colour, flag, or getter is a runtime operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMeaning
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactory
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeD1StackChildGroupFactoryActivationLoop
open SemiprimeBitArithmetic (bitValue)
namespace Env
export SemiprimeD1StackSourceEnvironmentEncoding (prefixRows)
export SemiprimeD1StackSourceEnvironmentMeaning (lookup_prefix markedRead)
end Env
namespace Palette
export SemiprimeD1StackPacketRowsMeaning (fields originalEntries original_lookup fields_original)
end Palette
/-- Actual next unread dictionary bytes are determined by the physical first-match scan. -/
def plan (a:Nat) (ids:List (List Bool)):List Bool→List (List Bool)→List Row
  | _,[]=>[]
  | key,id::rest=>⟨id,(SemiprimeD1StackOwnerLookup.result key (Env.prefixRows ids) []).2,
      Palette.fields 64 a id⟩::plan a ids (advance key) rest
/-- Exact number of real activation rows, independent of original incidence degree. -/
theorem plan_length (a:Nat) (ids:List (List Bool)) (key:List Bool) (remaining:List (List Bool)):
    (plan a ids key remaining).length=remaining.length:=by
  induction remaining generalizing key with
  | nil=>rfl
  | cons id rest ih=>simp only [plan,List.length_cons,ih]
/-- Actual reverse-prefix position at the next original vertex. -/
theorem getD_append_head (before:List (List Bool)) (id:List Bool) (after:List (List Bool)):
    (((before++id::after)[before.length]?).getD [])=id:=by
  simp
/-- Complete source-environment membership discharges every real row-source obligation. -/
theorem plan_valid (a:Nat) (ids:List (List Bool))
    (hm:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (remaining:List (List Bool)) (before:List (List Bool)) (key:List Bool)
    (hp:before++remaining=ids.reverse) (hk:bitValue key=before.length):
    Valid (Env.prefixRows ids) (Palette.originalEntries 64 a) key (plan a ids key remaining):=by
  induction remaining generalizing before key with
  | nil=>trivial
  | cons id rest ih=>
    have hmem:id∈ids:=by
      apply List.mem_reverse.mp
      rw [←hp]
      exact List.mem_append_right _ (List.mem_cons_self)
    have hid:=hm id hmem
    have hc:=SemiprimeSourceCompactWordBank.ids_compact 64 a id hid
    have htrim:(SemiprimeSourceCompactBits.trim id).bits=id:=
      SemiprimeSourceCompactWordIds.compact_value_injective _ _
        (SemiprimeSourceCompactBits.trim_compact id) hc (SemiprimeSourceCompactBits.trim_value id)
    have hlen:=congrArg List.length hp
    have hlt:bitValue key < ids.length:=by
      simp only [List.length_append,List.length_cons,List.length_reverse] at hlen
      omega
    have hexpected:SemiprimeSourceHistogramPrefix.expected ids (bitValue key)=id:=by
      simp only [SemiprimeSourceHistogramPrefix.expected,hk]
      rw [←hp,getD_append_head,htrim]
    have hout:(SemiprimeD1StackOwnerLookup.result key (Env.prefixRows ids) []).1=true::id:=by
      rw [Env.lookup_prefix]
      simp only [Env.markedRead,hlt,ite_true,hexpected]
    have hget:SemiprimeD1StackOwnerLookup.result key (Env.prefixRows ids) []=
        (true::id,(SemiprimeD1StackOwnerLookup.result key (Env.prefixRows ids) []).2):=Prod.ext hout rfl
    have hrow:=Palette.original_lookup 64 a id hid
    have hprefix:(before++[id])++rest=ids.reverse:=by simpa only [List.append_assoc,List.singleton_append] using hp
    have hkey:bitValue (advance key)=(before++[id]).length:=by
      rw [advance_value,hk,List.length_append,List.length_singleton]
    exact ⟨hget,hrow.2.1,hrow.1,ih (before++[id]) (advance key) hprefix hkey⟩
/-- Initial key ZERO and the complete original vertex list need no row/order advice. -/
theorem plan_valid_all (a:Nat) (ids:List (List Bool))
    (hm:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids):
    Valid (Env.prefixRows ids) (Palette.originalEntries 64 a) [] (plan a ids [] ids.reverse):=
  plan_valid a ids hm ids.reverse [] [] rfl rfl
/-- Physical computed colour equality agrees with the exact native selected-row read. -/
theorem active_original (i:Inputs) (a coordinate:Nat) (id:List Bool)
    (hi:id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids):
    active i coordinate (Palette.fields 64 a id)=
      (SemiprimeD1ChildActivation.readOne (SemiprimeSourceHistogramRows.acquire 64 a) a coordinate i.group id).value:=by
  have hv:=(SemiprimeD1PacketRows.original_fields 64 a id hi).2
  unfold SemiprimeD1ChildActivation.readOne
  dsimp only
  rw [hv]
  change active i coordinate (Palette.fields 64 a id)=
    (SemiprimeD1ChildGraph.testColour i.group coordinate (SemiprimeD1PacketRows.parse a
      (SemiprimeSourceHistogramRows.readRow (SemiprimeSourceHistogramRows.acquire 64 a) id).bits).fields).value
  apply Bool.eq_iff_iff.mpr
  rw [SemiprimeD1ChildGraph.testColour_correct]
  simp only [active,SemiprimeD1StackChildGroupFactoryColour.result_word,decide_eq_true_eq]
  rw [←Palette.fields_original 64 a id hi]
  rfl
/-- Actual all-vertex flag order is the original reverse-selected-ID order, including isolated vertices. -/
theorem plan_flags (i:Inputs) (a coordinate:Nat) (ids remaining:List (List Bool)) (key:List Bool):
    (plan a ids key remaining).map (fun row=>active i coordinate row.colours)=
      remaining.map (fun id=>active i coordinate (Palette.fields 64 a id)):=by
  induction remaining generalizing key with
  | nil=>rfl
  | cons id rest ih=>simp only [plan,List.map_cons,ih]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMeaning
