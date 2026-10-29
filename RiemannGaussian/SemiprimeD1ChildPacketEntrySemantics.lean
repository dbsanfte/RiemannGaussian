/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPacketAssignment
import RiemannGaussian.SemiprimeD1PacketEntryPolynomial

/-! # Actual cached packet entries use original acquired polynomial/source data
The original node is acquired from the literal parent rows at the actual phase.
Canonical right-port bits are identified with the common original endpoint
assignment. No gather, mask, row, source-value or coefficient answer is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildPacketEntrySemantics
open SemiprimeD1TensorNetwork
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1ChildOldEntrySemantics SemiprimeD1ChildOldEntryAssignment
open SemiprimeD1ChildPacketAssignment

/-- Original node at the actual phase and parent precision. -/
abbrev node (net : Network) (r a u p : ℕ) (q : Fin a) :=
  SemiprimeD1GlobalModeFibres.node net.leftCount net.rows.length r a u p (arity net.rows) (owner net.rows) q

/-- Actual original packet inventory, independent of report precision. -/
abbrev original (net : Network) (r a : ℕ) :=
  SemiprimeD1GlobalModeOwners.original net.leftCount net.rows.length r a (arity net.rows) (owner net.rows)

/-- Common original two-sided assignment, recovered from the actual original ID bank. -/
abbrev endpointBits (net : Network) (r a : ℕ) (bits : Incidence net.rows×Bool→Bool) :=
  SemiprimeD1ChildAssignmentEndpoint.originalEndpointBit net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows) bits

/-- Actual child-factor and original packet counts agree. -/
theorem packet_length (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r) :
    (rows net r a q g).length=(original net r a).state.packets.length := by
  rw [SemiprimeD1TensorNetworkLayout.childRows_length]
  exact SemiprimeD1ChildGraphSemantics.factors_length (owner net.rows) (original net r a) q g

/-- Identity-index packet-to-actual-child-factor transport, derived from literal counts. -/
def dataVertex (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (f : Fin (original net r a).state.packets.length) : Fin (rows net r a q g).length :=
  (finCongr (packet_length net r a q g).symm) f

/-- The physical table callback receives a finite index in its EXACT source-graph type. -/
def packetVertex (net : Network) (r a u p : ℕ) (q : Fin a) (g : Fin r)
    (f : Fin (original net r a).state.packets.length) :
    Fin (SemiprimeD1TensorNetworkLayout.childRows
      (SemiprimeD1ChildNetwork.graph net (node net r a u p q) q g)).length := ⟨f.val,by
  rw [SemiprimeD1TensorNetworkLayout.childRows_length]
  dsimp only [SemiprimeD1ChildNetwork.graph]
  have h:=SemiprimeD1ChildGraphSemantics.factors_length (owner net.rows)
    (node net r a u p q).packets q g
  rw [h]
  exact f.isLt⟩

/-- Both explicit index views have identical actual global port lists. -/
theorem packet_ports (net : Network) (r a u p : ℕ) (q : Fin a) (g : Fin r)
    (f : Fin (original net r a).state.packets.length) :
    rightPorts (SemiprimeD1TensorNetworkLayout.childRows
      (SemiprimeD1ChildNetwork.graph net (node net r a u p q) q g)) (packetVertex net r a u p q g f)=
    rightPorts (rows net r a q g) (dataVertex net r a q g f) := rfl

/-- No packet identifier advice: computed packet lookup returns the original index itself. -/
theorem packetIndex_vertex (net : Network) (r a u p : ℕ) (q : Fin a) (g : Fin r)
    (f : Fin (original net r a).state.packets.length) :
    SemiprimeD1ChildNetwork.packetIndex net (node net r a u p q) q g (packetVertex net r a u p q g f)=f :=
  Fin.ext rfl

/-- Actual prepared header endpoints are precisely this acquired graph bucket. -/
theorem header_endpoints (net : Network) (r a u p : ℕ) (q : Fin a) (g : Fin r)
    (f : Fin (original net r a).state.packets.length) :
    (SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p q) f q g).endpoints=
      ((data net r a q g).graph.factors[f.val]?).getD [] := rfl

/-- The concrete cached packet gather uses the same original endpoint bits as all other groups. -/
theorem gather_rightOne (net : Network) (r a u p : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (bits : Incidence net.rows×Bool→Bool)
    (f : Fin (original net r a).state.packets.length) :
    (SemiprimeD1LeafCounter.gather (List.ofFn (networkAssignment net r a q g bits))
      (SemiprimeD1ChildNetwork.rightOne net (node net r a u p q) q g ctx z t beta
        (packetVertex net r a u p q g f)).1.ports).bits=
      (SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p q) f q g).endpoints.map
        (endpointBits net r a bits) := by
  rw [SemiprimeD1ChildNetwork.rightOne_ports]
  rw [packet_ports,gather_right]
  rw [header_endpoints]
  have hf : f.val<(data net r a q g).graph.factors.length := by
    have h:=packet_length net r a q g
    rw [SemiprimeD1TensorNetworkLayout.childRows_length] at h
    rw [h];exact f.isLt
  rw [List.getElem?_eq_getElem hf]
  rfl

/-- Actual packet-table evaluation, with all gather/shape guards derived. -/
theorem evaluate_rightOne (net : Network) (r a u p : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (bits : Incidence net.rows×Bool→Bool)
    (f : Fin (original net r a).state.packets.length) :
    (SemiprimeD1LeafCounter.evaluateVertex
      (SemiprimeD1ChildNetwork.rightOne net (node net r a u p q) q g ctx z t beta
        (packetVertex net r a u p q g f)).1
      (List.ofFn (networkAssignment net r a q g bits))).words=
      (SemiprimeD1PacketEntryBits.evaluate ctx (SemiprimeD1PacketEntryBits.borrow z) a q t
        (SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p q) f q g).masks
        (SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p q) f q g).endpoints beta
        ((SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p q) f q g).endpoints.map
          (endpointBits net r a bits))).words := by
  have hg:=gather_rightOne net r a u p q g ctx z t beta bits f
  dsimp only [SemiprimeD1LeafCounter.evaluateVertex]
  rw [hg]
  have hb : ((SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p q) f q g).endpoints.map
      (endpointBits net r a bits)).length=
      (rightPorts (SemiprimeD1TensorNetworkLayout.childRows
        (SemiprimeD1ChildNetwork.graph net (node net r a u p q) q g))
        (packetVertex net r a u p q g f)).length := by
    rw [List.length_map,SemiprimeD1ChildNetwork.rightOne_degree]
    rw [packetIndex_vertex]
  have h:=SemiprimeD1ChildNetwork.rightOne_value net (node net r a u p q) q g ctx z t beta
    (packetVertex net r a u p q g f) _ hb
  rw [packetIndex_vertex] at h
  exact h
/-- Actual emitted right cache stores the actual packet table callback result. -/
theorem fromSource_right (net : Network) {r a : ℕ} (source : SemiprimeD1ChildNetwork.Source net a)
    (q : Fin a) (g : Fin r) (old : Context) (extra : List ℕ) (p : ℕ)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (SemiprimeD1ChildNetwork.graph net source q g)).length) :
    (SemiprimeD1ChildNetwork.fromSource net source q g old extra p z t beta).network.right[e.val]=
      (SemiprimeD1ChildNetwork.rightOne net source q g ⟨extra++old.axes,p⟩ z t beta e).1 := by
  simp only [SemiprimeD1ChildNetwork.fromSource,Vector.getElem_map,Vector.getElem_ofFn]

/-- Actual original-node source acquisition supplies this exact cached right table. -/
theorem acquire_right (net : Network) (old : Context) (extra : List ℕ) (p r a u : ℕ)
    (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (f : Fin (original net r a).state.packets.length) :
    (SemiprimeD1ChildNetwork.acquire net old extra p r a u q.val q g z t beta).network.right[
      (packetVertex net r a u old.precision q g f).val]=
      (SemiprimeD1ChildNetwork.rightOne net (node net r a u old.precision q) q g
        ⟨extra++old.axes,p⟩ z t beta (packetVertex net r a u old.precision q g f)).1 :=
  fromSource_right net (node net r a u old.precision q) q g old extra p z t beta _

/-- The original physical packet entry, specified in the actual current quotient;
this is a proof-side term, never an entry-answer or source-value runtime input. -/
noncomputable def packetTerm (net : Network) (r a u p0 : ℕ) (q : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (bits : Incidence net.rows×Bool→Bool)
    (f : Fin (original net r a).state.packets.length) : Carrier ctx :=
  interpret ctx (SemiprimeD1PacketEntryBits.evaluate ctx (SemiprimeD1PacketEntryBits.borrow z) a q t
    (SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p0 q) f q g).masks
    (SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p0 q) f q g).endpoints beta
    ((SemiprimeD1PacketTensorTables.prepare (owner net.rows) (node net r a u p0 q) f q g).endpoints.map
      (endpointBits net r a bits))).words

/-- The actual cached original-node packet entry has the original physical semantics,
under the actual canonical GLOBAL child assignment; no local bit/shape advice remains. -/
theorem evaluate_acquire_right (net : Network) (old : Context) (extra : List ℕ)
    (p r a u : ℕ) [NeZero r] (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (bits : Incidence net.rows×Bool→Bool) (f : Fin (original net r a).state.packets.length) :
    interpret ⟨extra++old.axes,p⟩ (SemiprimeD1LeafCounter.evaluateVertex
      (SemiprimeD1ChildNetwork.acquire net old extra p r a u q.val q g z t beta).network.right[
        (packetVertex net r a u old.precision q g f).val]
      (List.ofFn (networkAssignment net r a q g bits))).words=
      packetTerm net r a u old.precision q g ⟨extra++old.axes,p⟩ z t beta bits f := by
  rw [acquire_right]
  exact congrArg (interpret ⟨extra++old.axes,p⟩)
    (evaluate_rightOne net r a u old.precision q g ⟨extra++old.axes,p⟩ z t beta bits f)
end RiemannGaussian.SemiprimeD1ChildPacketEntrySemantics
