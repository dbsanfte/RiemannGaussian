/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1FactorScopeIncidencesOriginal
/-! # Actual factor ordinal keys and exact original factor-major scope fibres -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1FactorScopePairOriginal
open SemiprimeD1FactorScopePairEncoding SemiprimeD1FactorScopeIncidences
open SemiprimeD1StackFactorScopePairExecution
open SemiprimeD1RootTensorTables (Port factorNode)
open SemiprimePublicAcquiredExecution (factorCount indexedArity vertexEnumeration)
open SemiprimeD1StackOwnerFibreOriginal (enumeration scopeWord)
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Exact unchanged physical factor-key word, including empty factor ordinal zero. -/
def key (factor : Nat) : List Bool :=unary factor
/-- Unary source ordinal is interpreted by the generic numeric filter as2^f−1. -/
theorem key_value_add_one (f : Nat) : bitValue (key f)+1=2^f := by
  induction f with
  | zero=>rfl
  | succ f ih=>
    simp only [key,unary,List.replicate_succ,SemiprimeBitArithmetic.bitValue,
      SemiprimeBitArithmetic.bitNat,ite_true] at ih ⊢
    rw [pow_succ]
    omega
/-- Exact numeric value of the actual old factor counter, without guessing binary f. -/
theorem key_value (f : Nat) : bitValue (key f)=2^f-1 := by have h:=key_value_add_one f;omega
/-- The actual all-ones counter grows by one physical bit. -/
theorem key_succ_value (f : Nat) : bitValue (key (f+1))=1+2*bitValue (key f) := by
  simp only [key,unary,List.replicate_succ,SemiprimeBitArithmetic.bitValue,
    SemiprimeBitArithmetic.bitNat,ite_true]
/-- Numeric comparison of two actual unary ordinal codes is injective. -/
theorem key_injective : Function.Injective (fun f=>bitValue (key f)) := by
  intro f
  induction f with
  | zero=>
    intro g h
    dsimp only at h
    cases g with
    | zero=>rfl
    | succ g=>rw [key_succ_value] at h;change 0=1+2*bitValue (key g) at h;omega
  | succ f ih=>
    intro g h
    dsimp only at h
    cases g with
    | zero=>rw [key_succ_value] at h;change 1+2*bitValue (key f)=0 at h;omega
    | succ g=>
      rw [key_succ_value,key_succ_value] at h
      have hfg:bitValue (key f)=bitValue (key g):=by omega
      exact congrArg Nat.succ (ih hfg)
/-- A physical factor-key match means exactly the same original factor ordinal. -/
theorem key_eq_iff (f g : Nat) : bitValue (key f)=bitValue (key g) ↔ f=g :=
  ⟨fun h=>key_injective h,fun h=>congrArg (fun f=>bitValue (key f)) h⟩
export SemiprimeD1FactorScopeIncidencesOriginal (scope scope_original indexedRecord indexedRows original_rows)
/-- Actual projected key is exactly the old factor UNARY counter, not binary factor.val. -/
theorem indexed_pair (N : Nat) (p : Port N) : pair (indexedRecord N p)=(key p.1.val,scopeWord N p) := by
  change (key p.1.val,scope N p)=(key p.1.val,scopeWord N p)
  rw [scope_original]
/-- Numeric equality on the acquired factor-key stream selects exactly factor membership. -/
theorem values_original_list (N : Nat) (f : Fin (factorCount N)) (ports : List (Port N)) :
    SemiprimeD1StackOwnerFibre.values (key f.val) (ports.map (fun p=>(key p.1.val,scopeWord N p)))=
      (ports.filter (fun p=>decide (p.1=f))).map (scopeWord N) := by
  induction ports with
  | nil=>rfl
  | cons p ps ih=>
    by_cases h:p.1=f
    · simp [SemiprimeD1StackOwnerFibre.values,h,ih]
    · have hv:p.1.val≠f.val:=fun he=>h (Fin.ext he)
      simp [SemiprimeD1StackOwnerFibre.values,key_eq_iff,h,hv,ih]
/-- Filtering the original factor-major dependent incidence enumeration selects
exactly one factor's ascending original local-port list. -/
theorem filter_factor (m : Nat) (arity : Fin m→Nat) (f : Fin m) :
    ((SemiprimeFiniteEnumerations.indexedIncidences m arity).values.filter
      (fun p=>decide (p.1=f)))=(List.finRange (arity f)).map (Sigma.mk f) := by
  have h (es : List (Fin m)) :
      (es.flatMap (fun e=>(List.finRange (arity e)).map (Sigma.mk e))).filter
        (fun p=>decide (p.1=f))=
      (es.filter (fun e=>decide (e=f))).flatMap (fun e=>(List.finRange (arity e)).map (Sigma.mk e)) := by
    induction es with
    | nil=>rfl
    | cons e es ih=>
      by_cases he:e=f
      · subst e
        simp [List.filter_append,List.filter_map,ih,Function.comp_def]
      · simp [List.filter_append,List.filter_map,ih,Function.comp_def,he]
  change ((List.finRange m).flatMap (fun e=>(List.finRange (arity e)).map (Sigma.mk e))).filter _=_
  rw [h]
  have hf : (List.finRange m).filter (fun e=>decide (e=f))=[f] := by
    rw [List.filter_eq]
    have hc : (List.finRange m).count f=1 := by
      exact (List.nodup_finRange m).count_of_mem (List.mem_finRange f)
    rw [hc]
    rfl
  rw [hf]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
/-- Actual N-only projected rows have exactly the old factor keys and scope IDs. -/
theorem pairs_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    (rows bits).map pair=(enumeration (bitValue bits)).values.map (fun p=>(key p.1.val,scopeWord (bitValue bits) p)) := by
  rw [original_rows bits hc hN]
  simp only [indexedRows,List.map_map,Function.comp_def,indexed_pair]
/-- Generic physical filter specializes to ALL original factor-port lists, including
zero-arity factors; no E-wire owner-fibre theorem is used. -/
theorem original_fibre (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    SemiprimeD1StackOwnerFibre.values (key f.val) ((rows bits).map pair)=
      ((factorNode (bitValue bits) hN f).ports).map (scopeWord (bitValue bits)) := by
  rw [pairs_original bits hc hN,values_original_list,SemiprimeD1RootTensorTables.factorNode_ports]
  exact congrArg (List.map (scopeWord (bitValue bits)))
    (filter_factor (factorCount (bitValue bits)) (indexedArity (bitValue bits)) f)
end RiemannGaussian.SemiprimeD1FactorScopePairOriginal
