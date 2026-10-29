/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopePairBounds
import RiemannGaussian.SemiprimeD1StackOwnerFibreOriginal
/-! # Shared original factor-major incidence order of physical scoped-port records
All native list/index constructions in this file are output specifications only.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1FactorScopeIncidences
open SemiprimeD1PortScopeEncoding
open SemiprimeMacroGraph
/-- Mathematical factor ordinal, original vertex and local port slot. -/
abbrev Entry (V : Type) := Nat×V×Nat
/-- Exact factor-major incidence list, including zero-arity holes in its ordinal. -/
def entries {V : Type} (arity : V→Nat) : List V→Nat→List (Entry V)
  | [],_=>[]
  | v::vs,f=>(List.range (arity v)).map (fun j=>(f,v,j))++entries arity vs (f+1)
/-- Index-preserving map fusion, with no runtime list getter. -/
theorem mapIdx_map {A B D : Type} (xs : List A) (g : A→B) (f : Nat→B→D) :
    (xs.map g).mapIdx f=xs.mapIdx (fun i a=>f i (g a)) := by
  induction xs generalizing f with
  | nil=>rfl
  | cons x xs ih=>simp only [List.map_cons,List.mapIdx_cons,ih]
/-- The actual ascending local-slot enumeration has its own zero-based index. -/
theorem mapIdx_range {D : Type} (n : Nat) (f : Nat→Nat→D) :
    (List.range n).mapIdx f=(List.range n).map (fun i=>f i i) := by
  induction n generalizing f with
  | zero=>rfl
  | succ n ih=>simp only [List.range_succ_eq_map,List.mapIdx_cons,mapIdx_map,ih,List.map_cons,List.map_map,Function.comp_def]
/-- Every local physical record is in exact ascending original local-slot order. -/
theorem localPorts_range (words : SemiprimeD1EdgeCatalogueEncoding.Record) (fuel n f slot : Nat) :
    localPorts words fuel n f slot=(List.range fuel).map (fun i=>fields words (n+i) f (slot+i)) := by
  induction fuel generalizing n slot with
  | zero=>rfl
  | succ fuel ih=>
    rw [localPorts,ih,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Nat.add_zero,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    congr 1 <;> omega
/-- All physical source records carry exactly their own factor and global occurrence indices. -/
theorem ports_entries {r t digits : Nat} (vs : List (SubdividedVertex r t digits)) (f n : Nat) :
    ports vs f n=(entries subdividedArity vs f).mapIdx
      (fun i p=>fields (SemiprimeD1EdgeCatalogueEncoding.vertex p.2.1) (n+i) p.1 p.2.2) := by
  induction vs generalizing f n with
  | nil=>rfl
  | cons v vs ih=>
    rw [ports,entries,List.mapIdx_append,mapIdx_map,mapIdx_range,localPorts_range,ih]
    simp only [List.length_map,List.length_range,Nat.zero_add]
    congr 1
    apply congrArg (fun g=>(entries subdividedArity vs (f+1)).mapIdx g)
    funext i p
    congr 1
    omega
/-- Generic source loop equals ascending factor index followed by ascending local slot. -/
theorem entries_ofFn {V : Type} (arity : V→Nat) {m : Nat} (v : Fin m→V) (f : Nat) :
    entries arity (List.ofFn v) f=(List.finRange m).flatMap (fun i=>
      (List.range (arity (v i))).map (fun j=>(f+i.val,v i,j))) := by
  induction m generalizing f with
  | zero=>rfl
  | succ m ih=>
    rw [List.ofFn_succ,entries,List.finRange_succ,List.flatMap_cons,List.flatMap_map,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply congrArg (fun g=>(List.finRange m).flatMap g)
    funext i
    apply List.map_congr_left
    intro j _
    congr 1
    omega
/-- Ordered finite local slots have exactly the natural source-counter values. -/
theorem finRange_values (m : Nat) : (List.finRange m).map Fin.val=List.range m := by
  induction m with
  | zero=>rfl
  | succ m ih=>simp only [List.finRange_succ,List.map_cons,List.map_map,Fin.val_zero,Fin.val_succ,
      List.range_succ_eq_map,←ih,List.map_map,Function.comp_def,Nat.succ_eq_add_one]
/-- The old dependent incidence enumeration has precisely the source factor-major order. -/
theorem entries_indexed {V : Type} [DecidableEq V]
    (en : OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.FiniteEnumeration V) (arity : V→Nat) :
    entries arity en.values 0=
      (SemiprimeFiniteEnumerations.indexedIncidences en.values.length (fun e=>arity (en.equivFin e))).values.map
        (fun p=>(p.1.val,en.equivFin p.1,p.2.val)) := by
  have hv:List.ofFn en.equivFin=en.values:=List.ofFn_get en.values
  conv_lhs=>rw [←hv,entries_ofFn]
  simp only [SemiprimeFiniteEnumerations.indexedIncidences,SemiprimeFiniteEnumerations.sigma,
    SemiprimeFiniteEnumerations.fin,List.map_flatMap,List.map_map,Function.comp_def,Nat.zero_add]
  apply congrArg (fun g=>(List.finRange en.values.length).flatMap g)
  funext i
  conv_lhs=>rw [←finRange_values (arity (en.equivFin i))]
  rw [List.map_map]
  rfl
/-- Full original source-port fields agree with the typed dependent incidence enumeration. -/
theorem ports_indexed {r t digits : Nat}
    (en : OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.FiniteEnumeration (SubdividedVertex r t digits)) :
    ports en.values 0 0=
      (SemiprimeFiniteEnumerations.indexedIncidences en.values.length (fun e=>subdividedArity (en.equivFin e))).values.mapIdx
        (fun i p=>fields (SemiprimeD1EdgeCatalogueEncoding.vertex (en.equivFin p.1)) i p.1.val p.2.val) := by
  rw [ports_entries,entries_indexed,mapIdx_map]
  simp only [Nat.zero_add]
/-- Actual ID words and source rows are joined at their unchanged physical ordinal. -/
theorem zip_indexed {A : Type} (xs : List A) (f : Nat→A→Port) :
    List.zipWith SemiprimeD1FactorScopePairEncoding.joined (xs.mapIdx f)
      (SemiprimeD1OrdinalBankSpec.words xs.length)=
      xs.mapIdx (fun i a=>SemiprimeD1FactorScopePairEncoding.joined (f i a)
        (SemiprimeD1OrdinalBankSpec.idAt xs.length i)) := by
  apply List.ext_getElem
  · simp only [List.length_zipWith,List.length_mapIdx,SemiprimeD1OrdinalBankSpec.length,Nat.min_self]
  · intro i hi hj
    have h:i<xs.length:=by simpa only [List.length_mapIdx] using hj
    have hb:i<(SemiprimeD1OrdinalBankSpec.words xs.length).length:=by simpa only [SemiprimeD1OrdinalBankSpec.length] using h
    simp only [List.getElem_zipWith,List.getElem_mapIdx,SemiprimeD1OrdinalBankSpec.idAt,
      List.getElem?_eq_getElem hb,Option.getD_some]
/-- Indexing an original finite enumeration gives its exact explicit inverse ordinal. -/
theorem indexed_rank {A B : Type} [DecidableEq A]
    (en : OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.FiniteEnumeration A)
    (f : Nat→A→B) :
    en.values.mapIdx f=en.values.map (fun a=>f (en.equivFin.symm a).val a) := by
  apply List.ext_getElem
  · simp only [List.length_mapIdx,List.length_map]
  · intro i hi hj
    have h:i<en.values.length:=by simpa only [List.length_map] using hj
    have hr:(en.equivFin.symm en.values[i]).val=i:=
      congrArg Fin.val (en.equivFin.symm_apply_apply ⟨i,h⟩)
    simp only [List.getElem_mapIdx,List.getElem_map,hr]
/-- Exact same acquired nine-field rows, now expressed in original typed incidence order.
The factor ordinal remains unary and the scope ID remains the acquired M-bit word. -/
theorem scoped_indexed {r t digits : Nat}
    (en : OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.FiniteEnumeration (SubdividedVertex r t digits)) :
    let ie:=SemiprimeFiniteEnumerations.indexedIncidences en.values.length (fun e=>subdividedArity (en.equivFin e))
    List.zipWith SemiprimeD1FactorScopePairEncoding.joined (ports en.values 0 0)
      (SemiprimeD1OrdinalBankSpec.words (SemiprimeD1StackPortCatalogueTransduction.count en.values))=
      ie.values.map (fun p=>SemiprimeD1FactorScopePairEncoding.joined
        (fields (SemiprimeD1EdgeCatalogueEncoding.vertex (en.equivFin p.1)) (ie.equivFin.symm p).val p.1.val p.2.val)
        (SemiprimeD1OrdinalBankSpec.idAt ie.values.length (ie.equivFin.symm p).val)) := by
  dsimp only
  have hm:SemiprimeD1StackPortCatalogueTransduction.count en.values=
      (SemiprimeFiniteEnumerations.indexedIncidences en.values.length (fun e=>subdividedArity (en.equivFin e))).values.length := by
    rw [←ports_length en.values 0 0,ports_indexed,List.length_mapIdx]
  rw [ports_indexed,hm,zip_indexed,indexed_rank]
end RiemannGaussian.SemiprimeD1FactorScopeIncidences
