import RiemannGaussian.SemiprimeD1BoundaryLeafLoad
import RiemannGaussian.SemiprimeD1BoundaryPartitionRate
import RiemannGaussian.SemiprimeD1TensorNetworkRecursion

/-! Literal stored-port degree bounds control the acquired endpoint graph. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryNetworkDegree
open SemiprimeD1BoundaryPlan
open SemiprimeD1BoundaryLeafPorts
open SemiprimeD1BoundaryRefinement

theorem degree_le_ports (net : SemiprimeD1TensorNetwork.Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) (v : Nat)
    (hv : v < (SemiprimeD1TensorNetwork.vertices net).length) :
    degree (graph net) v ≤ ((SemiprimeD1TensorNetwork.vertices net)[v]).ports.length := by
  let selected := selectedIndices (graph net).edges (fun x => x.1.1 == v || x.1.2 == v)
  have hlen : selected.length = degree (graph net) v :=
    SemiprimeD1BoundaryLeafLoad.selected_length (graph net).edges
      (fun e => e.1 == v || e.2 == v)
  rw [←hlen]
  apply (selectedIndices_nodup _ _).length_le_of_subset
  intro p hp
  have hpb := selectedIndices_lt _ _ p hp
  have hbound : p < SemiprimeD1TensorNetwork.edgeCount net := by
    simpa only [graph_edges_length] using hpb
  let e : Fin (SemiprimeD1TensorNetwork.edgeCount net) := ⟨p,hbound⟩
  have hpred := (selectedIndices_mem (graph net).edges _ p hpb).mp hp
  have he : (graph net).edges[p]'hpb = ((networkGraph net).left e,(networkGraph net).right e) :=
    networkEndpoints_get net e
  rw [he] at hpred
  apply (edge_mem_vertex_ports net hw v hv e).mpr
  simpa only [Bool.or_eq_true,beq_iff_eq] using hpred

/-- The actual acquired maximum degree inherits the original stored-port cap. -/
theorem maxDegree_le (net : SemiprimeD1TensorNetwork.Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) (d : Nat)
    (hd : SemiprimeD1TensorNetworkRecursion.DegreeBound net d) : maxDegree (graph net) ≤ d := by
  apply SemiprimeD1BoundaryPartitionRate.foldl_max_le _ 0 d (Nat.zero_le _)
  intro x hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  have hvi : v < (SemiprimeD1TensorNetwork.vertices net).length := List.mem_range.mp hv
  exact (degree_le_ports net hw v hvi).trans (hd _ (List.getElem_mem hvi))

end RiemannGaussian.SemiprimeD1BoundaryNetworkDegree
