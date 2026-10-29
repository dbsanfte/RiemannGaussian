/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetworkClock
import RiemannGaussian.SemiprimeD1ParentTagOrder

/-! # Original cached network discharges all copied-table degree conditions
No old/child order, activation or local-port count is supplied. These are
properties of the actual original-source constructors and stored parent WF.
-/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildOriginalFields
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1ChildNetwork
open SemiprimeD1TensorNetworkRecursion

/-- The actual parent vertex is a literal read of the full original cache. -/
theorem parent_degree (net : Network) (D : ℕ) (hd : DegreeBound net D)
    (v : Fin (net.leftCount+net.rows.length)) : (parentVertex net v).ports.length ≤ D :=
  hd _ (List.getElem_mem _)

/-- Actual original-source degree facts required by the physical copied-table bound. -/
theorem left_fields (net : Network) (a u : ℕ) (i : Fin a) (g : Fin 64)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) (D : ℕ)
    (hw : WellFormed net) (hd : DegreeBound net D) (hslots : 2*2^a ≤ D)
    (v : Fin (net.leftCount+net.rows.length)) :
    let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64 a u i.val
      old.precision (arity net.rows) (owner net.rows)
    let data := SemiprimeD1ChildPortPullback.fromReplay (owner net.rows) source.packets i g
    let order := SemiprimeD1ChildTableOrder.acquire (owner net.rows) data v
    order.old.length ≤ D ∧ order.child.length ≤ D ∧
      (leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v).length ≤ D ∧
      (parentVertex net v).ports.length ≤ D := by
  dsimp only
  have hp := parent_degree net D hd v
  have ho : (SemiprimeD1ChildOldEntrySemantics.order net 64 a i g v).old.length ≤ D := by
    rw [SemiprimeD1ParentTagOrder.acquired_old_length net hw 64 a i g v]
    exact hp
  have hdchild := SemiprimeD1ChildStateResources.child_degree net hw D a u hd hslots i g old extra p z t beta
  let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64 a u i.val
    old.precision (arity net.rows) (owner net.rows)
  let child := (fromSource net source i g old extra p z t beta).network
  have hwchild := fromSource_wellFormed net source i g old extra p z t beta
  have hc : (leftPorts child.rows v).length ≤ D := by
    rw [←hwchild.1 v]
    exact hdchild _ (left_mem child v)
  have hports : (leftPorts (SemiprimeD1TensorNetworkLayout.childRows
      (SemiprimeD1ChildOldEntrySemantics.data net 64 a i g).graph) v).length ≤ D := hc
  have horder : (SemiprimeD1ChildOldEntrySemantics.order net 64 a i g v).child.length ≤ D := by
    rw [←SemiprimeD1ChildOldEntrySemantics.child_length net 64 a i g v]
    exact hports
  exact ⟨ho,horder,hports,hp⟩

/-- Actual prepared packet masks keep the full original catalogue dimension. -/
theorem header_items_length {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (packet : Fin source.packets.state.packets.length) :
    (SemiprimeD1PacketTensorTables.prepare (owner net.rows) source packet i g).masks.items.length =
      (SemiprimeD1ModeCatalog.catalog (source.packets.state.packets.length*2^(i.val+1))
        (source.precision-1)).length := by
  have h := congrArg List.length (SemiprimeD1PacketTensorTables.prepare_catalogue (owner net.rows) source packet i g)
  simpa only [List.length_map] using h

end RiemannGaussian.SemiprimeD1ChildOriginalFields
