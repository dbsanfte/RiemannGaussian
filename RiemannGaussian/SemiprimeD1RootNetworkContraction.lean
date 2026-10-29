/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootRightAssignments
import RiemannGaussian.SemiprimeD1RootBooleanCount

/-! # Actual acquired root network contraction is the original prefix count
The finite copy contraction is instantiated with actual canonical port fibres
and the original arithmetic checker tables. No count/bijection/value premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace RiemannGaussian.SemiprimeD1RootNetworkContraction
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout SemiprimeD1TensorNetworkFactorization
open SemiprimeD1RootLocalAssignments SemiprimeD1RootRightAssignments SemiprimeD1RootBooleanCount
open SemiprimeD1RootScalar SemiprimeD1RootOwnerTables SemiprimeD1JetInterpretation
open SemiprimeD1TensorTables SemiprimeD1LeafCounter SemiprimePublicAcquiredExecution
open SemiprimeCountRecovery SemiprimeCounterSearch
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
attribute [local irreducible] wireCount factorCount indexedArity indexedEntry indexedCoordinate

/-- Original owner coordinate of each canonical root occurrence. -/
def ownerMap (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    Fin (edgeCount (root N hN fixed))→Fin (wireCount N) :=
  leftGroup (SemiprimeD1RootNetwork.rows (source N hN fixed))

/-- Generic actual cached right product, before any public metadata is inserted. -/
def rightProduct {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity)
    (a : Fin (scope (SemiprimeD1RootNetwork.rows data))→Bool) : ZMod 4 :=
  ((SemiprimeD1RootNetwork.fromCache data).network.right.toList.map
    (fun v => scalarEntry v a)).prod

theorem rightProduct_eq {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity)
    (a : Fin (scope (SemiprimeD1RootNetwork.rows data))→Bool) :
    rightProduct data a=∏e : Fin (SemiprimeD1RootNetwork.rows data).length,
      scalarEntry (rightVertex data e) a := by
  unfold rightProduct
  rw [vector_product]
  rfl

/-- Actual original factor-side literal table product in the root scalar ring. -/
def rightValue (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (a : Fin (scope (SemiprimeD1RootNetwork.rows (source N hN fixed)))→Bool) : ZMod 4 :=
  rightProduct (source N hN fixed) a

/-- Actual root network scalar contraction; every literal vertex appears once. -/
def value (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) : ZMod 4 :=
  ∑a : Fin (edgeCount (root N hN fixed))→Bool,
    ((vertices (root N hN fixed)).map (fun v => scalar (interpret ⟨[],2⟩
      (valueAt v.table (localAssignment a v))))).prod

/-- All actual factor copies on a consistent original owner assignment are the
original public arithmetic checker product, in original factor order. -/
theorem right_consistent (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (bits : Fin (wireCount N)→Bool) :
    rightValue N hN fixed (originalAssignment N hN fixed bits)=
      ∏e : Fin (factorCount N),if (indexedEntry N hN e (fun j => bits (indexedCoordinate N hN e j))).accepted
        then (1:ZMod 4) else 0 := by
  unfold rightValue
  rw [rightProduct_eq]
  let rs := SemiprimeD1RootNetwork.rows (source N hN fixed)
  have hl : rs.length=factorCount N := SemiprimeD1RootNetwork.rows_length (source N hN fixed)
  let eqv := (finCongr hl).symm
  let term := fun j : Fin rs.length =>
    scalarEntry (rightVertex (source N hN fixed) j) (originalAssignment N hN fixed bits)
  change (∏j,term j)=_
  rw [←Equiv.prod_comp eqv term]
  apply Finset.prod_congr rfl
  intro e _
  have he : eqv e=SemiprimeD1RootEntrySemantics.factorIndex N hN fixed e := Fin.ext rfl
  rw [he]
  exact factor_entry N hN fixed bits e

/-- CLOSED actual root contraction modulo four, for every original prefix and
positive integer N. All owner/factor semantics and port relations are derived. -/
theorem value_mod_four (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    value N hN fixed=(acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed):ZMod 4) := by
  have hleft (a : Fin (edgeCount (root N hN fixed))→Bool) :
      ((root N hN fixed).left.toList.map (fun v => scalar (interpret ⟨[],2⟩
        (valueAt v.table (localAssignment a v))))).prod=
      ∏v : Fin (wireCount N),SemiprimeD1RootCopyContraction.copyWeight
        (ownerMap N hN fixed) (fun v b => allowed fixed v b=true) a v := by
    rw [vector_product]
    apply Finset.prod_congr rfl
    intro v _
    exact owner_entry N hN fixed a v
  unfold value
  simp only [vertices,List.map_append,List.prod_append]
  simp_rw [hleft]
  have hs : (∑a : Fin (edgeCount (root N hN fixed))→Bool,
      (∏v : Fin (wireCount N),SemiprimeD1RootCopyContraction.copyWeight
        (ownerMap N hN fixed) (fun v b => allowed fixed v b=true) a v)*rightValue N hN fixed a)=
      ∑a : Fin (edgeCount (root N hN fixed))→Bool,rightValue N hN fixed a*
        ∏v : Fin (wireCount N),SemiprimeD1RootCopyContraction.copyWeight
          (ownerMap N hN fixed) (fun v b => allowed fixed v b=true) a v := by
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  change (∑a : Fin (edgeCount (root N hN fixed))→Bool,
    (∏v : Fin (wireCount N),SemiprimeD1RootCopyContraction.copyWeight
      (ownerMap N hN fixed) (fun v b => allowed fixed v b=true) a v)*rightValue N hN fixed a)=_
  rw [hs]
  have hc := SemiprimeD1RootCopyContraction.contraction (R:=ZMod 4)
    (ownerMap N hN fixed) (fun v b => allowed fixed v b=true) (rightValue N hN fixed)
  refine hc.trans ?_
  have hbc := boolean_count (R:=ZMod 4) (wireCount N) (indexedArity N)
    (fun e input => (indexedEntry N hN e input).accepted) (indexedCoordinate N hN) fixed
  refine Eq.trans ?_ hbc
  apply Finset.sum_congr rfl
  intro bits _
  by_cases ha : ∀v,allowed fixed v (bits v)=true
  · conv_lhs => rw [ite_eq_left ha]
    conv_rhs => rw [ite_eq_left ha]
    exact right_consistent N hN fixed bits
  · conv_lhs => rw [ite_eq_right ha]
    conv_rhs => rw [ite_eq_right ha]


/-- The actual acquired root's complete physical leaf contraction has exactly
the original prefix-count residue, without any supplied contraction oracle. -/
theorem acquired_leaf_mod_four (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    scalar (interpret ⟨[],2⟩ (leaf ⟨[],2⟩ (SemiprimeD1RootNetwork.acquirePositive N hN fixed).network).words)=
      (acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed):ZMod 4) := by
  rw [leaf_value ⟨[],2⟩ (by simp)]
  simp only [map_sum,map_list_prod,List.map_map,Function.comp_def]
  exact value_mod_four N hN fixed

/-- The entire zero-axis root carrier is the literal prefix count residue,
not merely an independently assumed scalar projection. -/
theorem acquired_leaf_carrier (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    interpret ⟨[],2⟩ (leaf ⟨[],2⟩ (SemiprimeD1RootNetwork.acquirePositive N hN fixed).network).words=
      SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims [])
        (acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed):ZMod 4) := by
  calc
    _ = SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims [])
        (scalar (interpret ⟨[],2⟩ (leaf ⟨[],2⟩ (SemiprimeD1RootNetwork.acquirePositive N hN fixed).network).words)) :=
      (constants_scalar _).symm
    _ = _ := congrArg (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims []))
      (acquired_leaf_mod_four N hN fixed)

/-- For an actual semiprime EVERY original prefix residue is its exact natural
count (zero, one or two), including squares and conflicting prefix records. -/
theorem acquired_leaf_exact (N p q : ℕ) (hN : 0<N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N=p*q) (fixed : List (Fin (wireCount N)×Bool)) :
    (SemiprimeD1JetRingBits.coefficient ⟨[],2⟩
      (leaf ⟨[],2⟩ (SemiprimeD1RootNetwork.acquirePositive N hN fixed).network).words 0).val=
      acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed) := by
  rw [←scalar_interpret 2,acquired_leaf_mod_four]
  exact SemiprimeD1SemiprimePrefix.prefix_residue_exact N p q hN hp hq hsem fixed

end
end RiemannGaussian.SemiprimeD1RootNetworkContraction
