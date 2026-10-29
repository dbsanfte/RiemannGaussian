/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectMeaning
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesOriginal
/-! # Original physical occurrence stream in the exact selector order
This proof connects the acquired row stream to the original factor/local-slot
metadata. No incidence list, owner function or native index is an operand of the
fixed physical selector.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOccurrences
open SemiprimeD1StackSourceIncidenceSelectMeaning
namespace O
export SemiprimeD1StackSourceOccurrencesOriginal (originalPairsFrom)
end O
/-- Generic ordered-factor row expansion, retaining repetitions and empty rows. -/
theorem pairsFrom_indexed (n F start:Nat) (es:List (Fin F)) (rows:Fin F→List (Fin n))
    (h:es.map Fin.val=List.range' start es.length) :
    O.originalPairsFrom n start (es.map rows)=
      es.flatMap (fun e=>(rows e).map (fun v=>(Keys.numberKey v.val,Keys.numberKey (n+e.val)))) :=by
  induction es generalizing start with
  | nil=>rfl
  | cons e es ih=>
    change e.val::es.map Fin.val=start::List.range' (start+1) es.length at h
    have he: e.val=start:=(List.cons.inj h).1
    have ht:=ih (start+1) (List.cons.inj h).2
    simp only [List.map_cons,O.originalPairsFrom,List.flatMap_cons,he,ht]
/-- The original factor-major metadata stream is exactly the physically acquired row-key stream. -/
theorem original_keys_rows (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    originalKeys n F a arity owner=
      O.originalPairsFrom n 0 ((List.finRange F).map
        (fun e=>(List.finRange (arity e)).map (fun i=>owner ⟨e,i⟩))) :=by
  rw [pairsFrom_indexed n F 0 _ _ (by simp only [List.map_coe_finRange,List.length_finRange,List.range_eq_range'])]
  simp only [originalKeys,SemiprimeSourceHistogramMetadata.acquire,
    SemiprimePaidFiniteEnumerationLists.flat_value,SemiprimeSourceHistogramMetadata.finFast_value,
    SemiprimeSourceHistogramMetadata.ports_value,List.map_flatMap,List.map_map,Function.comp_def]
/-- The same identity on the standard original finite row representation. -/
theorem original_keys_ofFn (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    originalKeys n F a arity owner=
      O.originalPairsFrom n 0 (List.ofFn (fun e:Fin F=>List.ofFn (fun i:Fin (arity e)=>owner ⟨e,i⟩))) :=by
  simpa only [List.ofFn_eq_map] using original_keys_rows n F a arity owner
/-- On every actual network row list, the source keys are exactly the original incidence metadata keys. -/
theorem network_original_keys (net:SemiprimeD1TensorNetwork.Network) (a:Nat) :
    originalKeys net.leftCount net.rows.length a (SemiprimeD1TensorNetwork.arity net.rows)
      (SemiprimeD1TensorNetwork.owner net.rows)=O.originalPairsFrom net.leftCount 0 net.rows :=by
  rw [original_keys_ofFn]
  congr 1
  have hinner:∀e:Fin net.rows.length,
      List.ofFn (fun i:Fin (SemiprimeD1TensorNetwork.arity net.rows e)=>
        SemiprimeD1TensorNetwork.owner net.rows ⟨e,i⟩)=net.rows[e.val] :=by
    intro e
    exact List.ofFn_getElem
  simp only [hinner,List.ofFn_getElem]
/-- Every physically acquired original endpoint lies in the exact owner-plus-factor variable range. -/
theorem original_key_ranges (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (row:List Bool×List Bool)
    (hr:row∈originalKeys n F a arity owner) :
    SemiprimeBitArithmetic.bitValue row.1 < n+F ∧ SemiprimeBitArithmetic.bitValue row.2 < n+F :=by
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hr
  simp only [Keys.numberKey_value]
  have h0:=(owner i).isLt
  have h1:=i.1.isLt
  constructor <;> omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOccurrences
