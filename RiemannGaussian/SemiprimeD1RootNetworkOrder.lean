/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootNetwork
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RootNetworkOrder
/-- Selecting one fibre of a nodup finite list retains its literal block order. -/
private theorem selector {A B : Type} [DecidableEq A] (xs : List A) (f : A→List B)
    (e : A) (hn : xs.Nodup) :
    xs.flatMap (fun a => if a=e then f a else [])=if e∈xs then f e else [] := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hx := List.nodup_cons.mp hn
    by_cases he : a=e
    · subst a
      have hnot : e∉xs := hx.1
      simp [List.flatMap_cons,ih hx.2,hnot]
    · simp [List.flatMap_cons,he,ih hx.2,Ne.symm he]
/-- A factor fibre of the original incidence stream has its original local order. -/
theorem indexed_filter (F : ℕ) (arity : Fin F→ℕ) (e : Fin F) :
 ((SemiprimeFiniteEnumerations.indexedIncidences F arity).values.filter
   (fun p => decide (p.1=e)))=(List.finRange (arity e)).map (Sigma.mk (β := fun e => Fin (arity e)) e) := by
  simp only [SemiprimeFiniteEnumerations.indexedIncidences,SemiprimeFiniteEnumerations.sigma,
    SemiprimeFiniteEnumerations.fin,List.filter_flatMap,List.filter_map]
  have h (a : Fin F) :
      ((List.finRange (arity a)).filter ((fun p : Sigma (fun e => Fin (arity e)) => decide (p.fst=e)) ∘ Sigma.mk (β := fun e => Fin (arity e)) a)).map (Sigma.mk (β := fun e => Fin (arity e)) a)=
      if a=e then (List.finRange (arity a)).map (Sigma.mk (β := fun e => Fin (arity e)) a) else [] := by
    by_cases ha : a=e
    · simp [Function.comp_def,ha]
    · simp [Function.comp_def,ha]
  simp_rw [h]
  rw [selector _ _ _ (List.nodup_finRange F)]
  simp
/-- Canonical right ports preserve factor-local order in every concrete network. -/
theorem rightPorts_order {n : ℕ} (rs : SemiprimeD1TensorNetwork.Rows n)
    (e : Fin rs.length) :
    SemiprimeD1TensorNetwork.rightPorts rs e=
      (List.finRange (SemiprimeD1TensorNetwork.arity rs e)).map
        (fun j => SemiprimeD1TensorNetwork.edgeID rs ⟨e,j⟩) := by
  unfold SemiprimeD1TensorNetwork.rightPorts SemiprimeD1TensorNetwork.incidences
  rw [indexed_filter]
  simp only [List.map_map,Function.comp_def]

/-- The canonical actual factor scope equals its cached owner-row length. -/
theorem rightPorts_length {n : ℕ} (rs : SemiprimeD1TensorNetwork.Rows n)
    (e : Fin rs.length) :
    (SemiprimeD1TensorNetwork.rightPorts rs e).length=SemiprimeD1TensorNetwork.arity rs e := by
  rw [rightPorts_order,List.length_map,List.length_finRange]

/-- Cached-record equality determines literal row order without inspecting any tables. -/
theorem row_of_map {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity)
    (coordinate : (e : Fin F)→Fin (arity e)→Fin n)
    (hr : data.records=(SemiprimeFiniteEnumerations.indexedIncidences F arity).values.map
      (fun p => ⟨p,coordinate p.1 p.2⟩)) (e : Fin F) :
    (SemiprimeD1RootNetwork.rows data)[e.val]'(by
      rw [SemiprimeD1RootNetwork.rows_length];exact e.isLt)=
    (List.finRange (arity e)).map (coordinate e) := by
  simp only [SemiprimeD1RootNetwork.rows,List.getElem_ofFn]
  change (data.records.filter (fun p => decide (p.port.1=e))).map
    SemiprimeD1RootTensorTables.PortRecord.owner=(List.finRange (arity e)).map (coordinate e)
  rw [hr]
  simp only [List.filter_map,List.map_map,Function.comp_def]
  rw [indexed_filter]
  simp only [List.map_map,Function.comp_def]

/-- Actual cached owner rows preserve the original local-port sequence. -/
theorem original_row (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool))
    (e : Fin (SemiprimePublicAcquiredExecution.factorCount N)) :
    (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))[e.val]'(by
      rw [SemiprimeD1RootNetwork.rows_length];exact e.isLt)=
    (List.finRange (SemiprimePublicAcquiredExecution.indexedArity N e)).map
      (SemiprimePublicAcquiredExecution.indexedCoordinate N hN e) := by
  apply row_of_map _ (SemiprimePublicAcquiredExecution.indexedCoordinate N hN)
  exact SemiprimeD1RootTensorTables.acquirePositive_records N hN fixed
/-- Actual root rows have exactly the original acquired factor degree. -/
theorem original_row_length (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool))
    (e : Fin (SemiprimePublicAcquiredExecution.factorCount N)) :
    ((SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))[e.val]'(by
      rw [SemiprimeD1RootNetwork.rows_length];exact e.isLt)).length=
        SemiprimePublicAcquiredExecution.indexedArity N e := by
  rw [original_row N hN fixed e,List.length_map,List.length_finRange]
end RiemannGaussian.SemiprimeD1RootNetworkOrder
