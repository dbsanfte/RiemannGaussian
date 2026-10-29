/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootCopyContraction
import RiemannGaussian.SemiprimeD1PacketColumnPartition

/-! # Original root owner-copy degrees from actual cached records
Factor grouping may reorder records but preserves every owner occurrence.
No old/new owner-degree equality or incidence bijection is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace RiemannGaussian.SemiprimeD1RootPortCounts
open SemiprimeD1TensorNetwork SemiprimeD1RootTensorTables
open SemiprimeD1PacketColumnPartition
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Flattening the actual finite grouped rows is the literal concatenation. -/
theorem flatten_map {A B : Type*} (xs : List A) (f : A→List B) :
    (xs.map f).flatten=xs.flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,ih]

/-- The actual typed occurrence enumeration reads every row owner in order. -/
theorem incidence_owners {n : ℕ} (rs : Rows n) :
    (incidences rs).map (owner rs)=rs.flatten := by
  change ((List.finRange rs.length).flatMap (fun e => (List.finRange (arity rs e)).map
    (fun j => (⟨e,j⟩ : Incidence rs)))).map (owner rs)=_
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  have hf (e : Fin rs.length) :
      (List.finRange (arity rs e)).map (fun j => owner rs ⟨e,j⟩)=rs[e.val] := by
    change (List.finRange rs[e.val].length).map (fun j => rs[e.val][j.val])=rs[e.val]
    rw [←List.ofFn_eq_map,List.ofFn_getElem]
  simp_rw [hf]
  have hr := List.ofFn_getElem (xs:=rs)
  rw [List.ofFn_eq_map] at hr
  rw [←flatten_map,hr]

/-- Canonical left ports have exactly the actual owner multiplicity in rows. -/
theorem leftPorts_length {n : ℕ} (rs : Rows n) (v : Fin n) :
    (leftPorts rs v).length=rs.flatten.countP (fun w => decide (w=v)) := by
  unfold leftPorts
  rw [List.length_map,←List.countP_eq_length_filter]
  have h := congrArg (List.countP (fun w : Fin n => decide (w=v))) (incidence_owners rs)
  simpa only [List.countP_map,Function.comp_def] using h

/-- Actual factor grouping preserves the complete cached owner list as a
multiset, including parallel incidences and repeated owner coordinates. -/
theorem rows_owner_perm {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity) :
    (SemiprimeD1RootNetwork.rows data).flatten.Perm (data.records.map PortRecord.owner) := by
  have hp := partition_perm data.records (fun p => p.port.1) (fun p => some p.owner)
  have hf (e : Fin F) : partitionMap data.records (fun p => p.port.1) (fun p => some p.owner) e=
      (data.records.filter (fun p => decide (p.port.1=e))).map PortRecord.owner := by
    induction data.records with
    | nil => rfl
    | cons p ps ih =>
      unfold partitionMap at ih
      by_cases h : p.port.1=e <;>
        simp only [partitionMap,List.filterMap_cons,List.filter_cons,h,decide_true,decide_false,
          Bool.false_eq_true,ite_true,ite_false,List.map_cons,ih]
  have hr : data.records.filterMap (fun p => some p.owner)=data.records.map PortRecord.owner := by
    induction data.records with
    | nil => rfl
    | cons p ps ih => simp only [List.filterMap_cons,List.map_cons,ih]
  have hfun : partitionMap data.records (fun p => p.port.1) (fun p => some p.owner)=
      (fun e => (data.records.filter (fun p => decide (p.port.1=e))).map PortRecord.owner) := funext hf
  rw [hfun] at hp
  rw [hr] at hp
  unfold SemiprimeD1RootNetwork.rows
  rw [List.ofFn_eq_map,flatten_map]
  exact hp

/-- No supplied owner-degree answer: canonical network copies and original
cached owner tables have exactly the same number of local ports. -/
theorem original_owner_degree {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity) (v : Fin n) :
    (leftPorts (SemiprimeD1RootNetwork.rows data) v).length=
      (data.records.filter (fun p => decide (p.owner=v))).length := by
  rw [leftPorts_length,←List.countP_eq_length_filter]
  have h := (rows_owner_perm data).countP_eq (fun w => decide (w=v))
  simpa only [List.countP_map,Function.comp_def] using h

end
end RiemannGaussian.SemiprimeD1RootPortCounts
