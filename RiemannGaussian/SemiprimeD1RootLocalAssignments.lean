/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootOwnerSemantics
import RiemannGaussian.SemiprimeD1TensorNetworkFactorization

/-! # Actual root local assignments on canonical owner fibres
All global/local reads use the acquired original root port lists. Fibre coverage
and source-table values are derived from the original constructor.
-/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace RiemannGaussian.SemiprimeD1RootLocalAssignments
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout SemiprimeD1LeafCounter
open SemiprimeD1TensorTables SemiprimeD1RootEntrySemantics SemiprimeD1RootOwnerSemantics
open SemiprimeD1RootScalar SemiprimeD1RootCopyContraction SemiprimeD1JetInterpretation
open SemiprimeD1RootOwnerTables SemiprimePublicAcquiredExecution
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact actual original root source cache. -/
abbrev source (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :=
  SemiprimeD1RootTensorTables.acquirePositive N hN fixed

/-- Exact actual copied root network, with no semantic fields added. -/
abbrev root (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :=
  (SemiprimeD1RootNetwork.fromCache (source N hN fixed)).network

/-- The actual global/local gather is its literal canonical port read list. -/
theorem valueAt_global_lookup {M : ℕ} (v : Vertex) (a : Fin M→Bool) :
    valueAt v.table (localAssignment a v)=
      (lookup v.table (v.ports.map (fun p => ((List.ofFn a)[p]?).getD false))).words := by
  rw [←evaluateVertex_value]
  change (lookup v.table (gather (List.ofFn a) v.ports).bits).words=_
  rw [gather_value]

/-- Internal canonical-network interface; the original endpoint below derives
its local-entry premise from the actual producer cache. -/
theorem owner_entry_general (net : Network) (hw : WellFormed net)
    (fixed : List (Fin net.leftCount×Bool))
    (hentry : ∀v : Fin net.leftCount,∀bits : List Bool,
      bits.length=(leftPorts net.rows v).length →
      scalar (interpret ⟨[],2⟩ (lookup (net.left[v.val]).table bits).words)=
        (weight fixed v bits : ZMod 4))
    (a : Fin (edgeCount net)→Bool) (v : Fin net.leftCount) :
    scalar (interpret ⟨[],2⟩ (valueAt (net.left[v.val]).table
      (localAssignment a (net.left[v.val]))))=
      copyWeight (leftGroup net.rows) (fun v b => allowed fixed v b=true) a v := by
  let vertex := net.left[v.val]
  let bits := vertex.ports.map (fun p => ((List.ofFn a)[p]?).getD false)
  have hp : vertex.ports=leftPorts net.rows v := hw.1 v
  have hb : bits.length=(leftPorts net.rows v).length := by
    dsimp only [bits]
    rw [List.length_map]
    exact congrArg List.length hp
  calc
    _ = scalar (interpret ⟨[],2⟩ (lookup vertex.table bits).words) := by rw [valueAt_global_lookup]
    _ = (weight fixed v bits : ZMod 4) := hentry v bits hb
    _ = _ := by
      change (weight fixed v (vertex.ports.map (fun p => ((List.ofFn a)[p]?).getD false)):ZMod 4)=_
      rw [hp]
      exact weight_fibre (R:=ZMod 4) (leftGroup net.rows) fixed v _ (leftPorts_lt _ _) (leftGroup_mem _ _) a

/-- Canonical original owner coordinates behind an explicitly typed interface. -/
def ownerCoordinate (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    Fin (edgeCount (root N hN fixed))→Fin (wireCount N) :=
  leftGroup (SemiprimeD1RootNetwork.rows (source N hN fixed))

/-- Complete original root owner entry equals its actual canonical fibre copy
weight. No table value, coverage, degree, prefix admissibility or count advice. -/
theorem owner_entry (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (a : Fin (edgeCount (root N hN fixed))→Bool) (v : Fin (wireCount N)) :
    scalar (interpret ⟨[],2⟩ (valueAt (ownerVertex N hN fixed v).table
      (localAssignment a (ownerVertex N hN fixed v))))=
      copyWeight (ownerCoordinate N hN fixed)
        (fun v b => allowed fixed v b=true) a v := by
  apply owner_entry_general (root N hN fixed)
    (SemiprimeD1RootNetwork.fromCache_wellFormed (source N hN fixed)) fixed
  intro v bits hb
  exact original_owner_scalar N hN fixed v bits hb

end
end RiemannGaussian.SemiprimeD1RootLocalAssignments
