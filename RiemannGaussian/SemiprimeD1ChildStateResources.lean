/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1NetworkStateResources
import RiemannGaussian.SemiprimeD1OriginalModeAcquisition

/-! # Actual original-source child dimension and degree preservation
No packet count, label assignment or local load is supplied: both contracts are
derived from the parent's literal layout and the actual original acquisition.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1ChildStateResources
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout
open SemiprimeD1NetworkStateResources SemiprimeD1TensorNetworkRecursion
open SemiprimeD1JetAxes
attribute [local irreducible] SemiprimeD1PacketReplayOriginal.acquire

/-- The literal original mode source consumed by the recursive controller. -/
abbrev source (net : Network) (a u i p : ℕ) :=
  SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64 a u i p
    (arity net.rows) (owner net.rows)

/-- Literal canonical original group graph, before table acquisition. -/
abbrev graph (net : Network) (a : ℕ) (i : Fin a) (g : Fin 64) :=
  SemiprimeD1ChildGraph.acquire net.leftCount net.rows.length 64 a
    (arity net.rows) (owner net.rows) i g

/-- Actual child network constructed from one retained source, not reacquired tables. -/
abbrev child (net : Network) (a u : ℕ) (i : Fin a) (g : Fin 64)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :=
  (SemiprimeD1ChildNetwork.fromSource net (source net a u i.val old.precision)
    i g old extra p z t beta).network

/-- The canonical current child rows are exactly the original physical graph. -/
theorem child_rows (net : Network) (a u : ℕ) (i : Fin a) (g : Fin 64)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    (child net a u i g old extra p z t beta).rows=childRows (graph net a i g) := rfl

/-- Both stored degree bounds follow from the actual canonical port lists. -/
theorem canonical_degree (net : Network) (hw : WellFormed net) (D : ℕ)
    (hl : ∀v,(leftPorts net.rows v).length≤D)
    (hr : ∀e,(rightPorts net.rows e).length≤D) : DegreeBound net D := by
  intro v hv
  rcases List.mem_append.mp hv with hv|hv
  · obtain ⟨j,hj,hv⟩:=List.mem_iff_getElem.mp hv
    rw [Vector.getElem_toList] at hv
    subst v
    rw [hw.1 ⟨j,by simpa only [Vector.length_toList] using hj⟩]
    exact hl _
  · obtain ⟨j,hj,hv⟩:=List.mem_iff_getElem.mp hv
    rw [Vector.getElem_toList] at hv
    subst v
    rw [hw.2 ⟨j,by simpa only [Vector.length_toList] using hj⟩]
    exact hr _

/-- Literal child owner degree is the endpoint-list multiplicity, including
parallel occurrences and zero-degree retained vertices. -/
theorem graph_left_degree {V : ℕ} (G : SemiprimeD1ChildGraph.Graph V) (v : Fin V) :
    (leftPorts (childRows G) v).length=
      G.factors.flatten.countP (fun e=>decide (e.vertex=v)) := by
  have h:=congrArg (List.countP (fun x : Fin V=>decide (x=v)))
    (SemiprimeD1RootPortCounts.incidence_owners (childRows G))
  simpa only [leftPorts,List.length_map,←List.countP_eq_length_filter,List.countP_map,
    Function.comp_def,childRows,←List.map_flatten,Fin.ext_iff] using h

/-- Actual packet factor scope retains its acquired endpoint-list arity. -/
theorem graph_right_degree {V : ℕ} (G : SemiprimeD1ChildGraph.Graph V)
    (e : Fin (childRows G).length) :
    (rightPorts (childRows G) e).length=
      SemiprimeD1ChildGraph.arity G ⟨e.val,by simpa only [childRows,List.length_map] using e.isLt⟩ := by
  rw [SemiprimeD1RootNetworkOrder.rightPorts_length]
  simp only [arity,childRows,List.getElem_map,List.length_map,SemiprimeD1ChildGraph.arity]

/-- Every literal child table preserves the global degree cap. Old vertices do
not increase degree; new packet scopes are bounded by twice the actual slot count. -/
theorem child_degree (net : Network) (hw : WellFormed net) (D a u : ℕ)
    (hd : DegreeBound net D) (hslots : 2*2^a≤D) (i : Fin a) (g : Fin 64)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    DegreeBound (child net a u i g old extra p z t beta) D := by
  apply canonical_degree _ (SemiprimeD1ChildNetwork.fromSource_wellFormed ..) D
  · intro v
    change Fin (net.leftCount+net.rows.length) at v
    change (leftPorts (childRows (graph net a i g)) v).length≤D
    rw [graph_left_degree]
    have hc:=original_degree_contract net hw D a hd
    exact SemiprimeD1ChildGraphDegree.child_degree_le net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) D hc.1 hc.2 i g v
  · intro e
    change Fin (childRows (graph net a i g)).length at e
    change (rightPorts (childRows (graph net a i g)) e).length≤D
    rw [graph_right_degree]
    exact (SemiprimeD1ChildGraphBounds.packet_arity net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g _).trans hslots

/-- The number of actual observed packets is paid by3M, from original layout
and the original padding inequalities, not a packet-size answer. -/
theorem packets_le (net : Network) (hw : WellFormed net) (D a : ℕ)
    (hd : DegreeBound net D) (hsmall : 2*(64^(2*a))^2*D≤edgeCount net)
    (hsize : 64^(2*a)*2^a≤edgeCount net) :
    (SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)).state.packets.length≤3*edgeCount net := by
  have hdg:=original_degree_contract net hw D a hd
  have hc:=SemiprimeD1PacketReplayCapacity.threeM_capacity net.leftCount net.rows.length 64 a
    (arity net.rows) (owner net.rows) D hdg.1 hdg.2
    (by simpa only [original_ports,edgeCount,scope] using hsmall) (by simpa only [original_ports,edgeCount,scope] using hsize)
  rw [original_ports] at hc
  change _*2^a≤3*edgeCount net at hc
  have hp : 1≤(2:ℕ)^a:=Nat.one_le_pow _ _ (by decide)
  nlinarith

/-- Whole actual child vertex count grows by at most3M, retaining all isolated
old vertices rather than discarding them in an assumed sparse representation. -/
theorem child_vertex_growth (net : Network) (hw : WellFormed net) (D a u : ℕ)
    (hd : DegreeBound net D) (hsmall : 2*(64^(2*a))^2*D≤edgeCount net)
    (hsize : 64^(2*a)*2^a≤edgeCount net) (i : Fin a) (g : Fin 64)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    vertexCount (child net a u i g old extra p z t beta)≤vertexCount net+3*edgeCount net := by
  rw [child_vertexCount]
  exact Nat.add_le_add_left (packets_le net hw D a hd hsmall hsize) _

end RiemannGaussian.SemiprimeD1ChildStateResources
