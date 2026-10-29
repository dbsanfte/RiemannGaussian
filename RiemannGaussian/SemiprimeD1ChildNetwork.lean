/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootNetworkOrder
import RiemannGaussian.SemiprimeD1ChildTensorTables
import RiemannGaussian.SemiprimeD1PacketTensorTables
import RiemannGaussian.SemiprimeD1TensorNetworkLayout

/-! # Actual child network assembly from literal parent caches
Every old vertex table is copied through the computed child port order, and
every actual packet factor is materialized by the physical packet evaluator.
Only literal parent tables and actual acquired replay/mode data are consumed;
no local-entry function is stored in the resulting network.
-/
set_option autoImplicit false
set_option maxHeartbeats 90000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildNetwork
open SemiprimeD1JetAxes
open SemiprimeD1TensorNetwork (Network)

/-- Actual unified parent-vertex read, with range derived from both cache lengths. -/
def parentVertex (net : Network) (v : Fin (net.leftCount+net.rows.length)) :
    SemiprimeD1LeafCounter.Vertex :=
  (SemiprimeD1TensorNetwork.vertices net)[v.val]'(by
    simpa only [SemiprimeD1TensorNetwork.vertices,List.length_append,Vector.length_toList] using v.isLt)

/-- Every read parent table inherits canonicality from the actual complete cache. -/
theorem parentVertex_good (ctx : Context) (net : Network)
    (hg : SemiprimeD1TensorNetwork.Good ctx net)
    (v : Fin (net.leftCount+net.rows.length)) :
    SemiprimeD1TensorTables.Good ctx (parentVertex net v).table :=
  hg _ (List.getElem_mem _)

/-- Canonical global port descriptors and an actual paid cached-table copy. -/
def copyTable {d : ℕ} (ports : List ℕ) (table : SemiprimeD1TensorTables.Table d) :
    SemiprimeD1LeafCounter.Vertex × ℕ :=
  let out:=SemiprimeD1TensorTables.build ports.length
    (fun bits => SemiprimeD1TensorTables.lookup table bits)
  (⟨ports,out.table⟩,out.clock+3)

/-- The copy retains exactly its computed global-port descriptors. -/
theorem copyTable_ports {d : ℕ} (ports : List ℕ) (table : SemiprimeD1TensorTables.Table d) :
    (copyTable ports table).1.ports=ports := rfl

/-- Every copied entry is an actual literal source-table read. -/
theorem copyTable_value {d : ℕ} (ports : List ℕ) (table : SemiprimeD1TensorTables.Table d)
    (bits : List Bool) (hb : bits.length=ports.length) :
    (SemiprimeD1TensorTables.lookup (copyTable ports table).1.table bits).words=
      (SemiprimeD1TensorTables.lookup table bits).words :=
  SemiprimeD1TensorTables.build_value _ _ bits hb

/-- Cached copying preserves actual current-context coefficient shape. -/
theorem copyTable_good {d : ℕ} (ctx : Context) (ports : List ℕ)
    (table : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good ctx table) :
    SemiprimeD1TensorTables.Good ctx (copyTable ports table).1.table :=
  SemiprimeD1TensorTables.build_good ctx _ _ (fun bits _ =>
    SemiprimeD1TensorTables.lookup_good ctx table hg bits)

/-- Source type is determined by literal current parent rows. -/
abbrev Source (net : Network) (a : ℕ) :=
  SemiprimeD1OriginalModeAcquisition.Acquired net.leftCount net.rows.length a
    (SemiprimeD1TensorNetwork.arity net.rows)

/-- Pullback type is determined by the same actual parent rows. -/
abbrev Pullback (net : Network) (a : ℕ) :=
  SemiprimeD1ChildPortPullback.Acquired net.leftCount net.rows.length a
    (SemiprimeD1TensorNetwork.arity net.rows)

/-- Acquire one old-vertex table using its actual cached parent table and computed routing. -/
def leftOne {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ)
    (v : Fin (net.leftCount+net.rows.length)) : SemiprimeD1LeafCounter.Vertex × ℕ :=
  let order:=SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v
  let parent:=parentVertex net v
  let aligned:=SemiprimeD1TensorTables.build order.old.length
    (fun bits => SemiprimeD1TensorTables.lookup parent.table bits)
  let child:=SemiprimeD1ChildTensorTables.fromCache
    (SemiprimeD1TensorNetwork.owner net.rows) data v old extra p aligned.table
  let ports:=SemiprimeD1TensorNetwork.leftPorts
    (SemiprimeD1TensorNetworkLayout.childRows data.graph) v
  let copied:=copyTable ports child.table
  (copied.1,order.clock+aligned.clock+child.clock+copied.2+ports.length+v.val+12)

/-- Every assembled old child vertex uses the canonical child global port list. -/
theorem leftOne_ports {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ)
    (v : Fin (net.leftCount+net.rows.length)) :
    (leftOne net data old extra p v).1.ports=
      SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v := rfl

/-- Active old entries are the literal parent lookup in the computed child order,
then the actual constant-coordinate lift; no requested entry answer is supplied. -/
theorem leftOne_active_value {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ)
    (v : Fin (net.leftCount+net.rows.length)) (bits : List Bool)
    (hb : bits.length=(SemiprimeD1TensorNetwork.leftPorts
      (SemiprimeD1TensorNetworkLayout.childRows data.graph) v).length)
    (ha : (data.activation.bits[v.val]?).getD false=true)
    (hc : bits.length=(SemiprimeD1ChildTableOrder.acquire
      (SemiprimeD1TensorNetwork.owner net.rows) data v).child.length) :
    (SemiprimeD1TensorTables.lookup (leftOne net data old extra p v).1.table bits).words=
    (SemiprimeD1ChildTableCopy.lift old extra p
      (SemiprimeD1TensorTables.lookup (parentVertex net v).table
        (SemiprimeD1ChildTableCopy.gather bits (SemiprimeD1ChildTableOrder.acquire
          (SemiprimeD1TensorNetwork.owner net.rows) data v).order).value).words).words := by
  dsimp only [leftOne]
  rw [copyTable_value _ _ bits hb]
  rw [SemiprimeD1ChildTensorTables.fromCache_active_value _ _ _ old extra p _ ha bits hc]
  rw [SemiprimeD1TensorTables.build_value]
  exact (SemiprimeD1ChildTableCopy.gather_length bits _).trans
    (SemiprimeD1ChildTableOrder.order_length _ data v)

/-- Shape follows from actual parent caches and the physical old-table copy. -/
theorem leftOne_good {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ)
    (v : Fin (net.leftCount+net.rows.length))
    (hg : SemiprimeD1TensorNetwork.Good old net) (he : 0<extra.prod) :
    SemiprimeD1TensorTables.Good ⟨extra++old.axes,p⟩ (leftOne net data old extra p v).1.table := by
  apply copyTable_good
  apply SemiprimeD1ChildTensorTables.fromCache_good
  · apply SemiprimeD1TensorTables.build_good
    intro bits _
    exact SemiprimeD1TensorTables.lookup_good old _ (parentVertex_good old net hg v) bits
  · exact he

/-- Actual prepared child graph, without a caller-supplied graph or bucket catalogue. -/
def graph {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r) :=
  SemiprimeD1ChildGraph.fromReplay (SemiprimeD1TensorNetwork.owner net.rows) source.packets i g

/-- Packet identity is the actual child-factor index, with its range derived from replay. -/
def packetIndex {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length) :
    Fin source.packets.state.packets.length := ⟨e.val,by
  have h:=SemiprimeD1TensorNetworkLayout.childRows_length (graph net source i g)
  have h':=SemiprimeD1ChildGraphSemantics.factors_length
    (SemiprimeD1TensorNetwork.owner net.rows) source.packets i g
  exact lt_of_lt_of_eq e.isLt (h.trans h')⟩

/-- Acquire one actual packet-factor table, then copy its canonical global descriptors. -/
def rightOne {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length) :
    SemiprimeD1LeafCounter.Vertex × ℕ :=
  let packet:=packetIndex net source i g e
  let header:=SemiprimeD1PacketTensorTables.prepare
    (SemiprimeD1TensorNetwork.owner net.rows) source packet i g
  let table:=SemiprimeD1PacketTensorTables.acquire header ctx z a i t beta
  let replayGraph:=graph net source i g
  let ports:=SemiprimeD1TensorNetwork.rightPorts
    (SemiprimeD1TensorNetworkLayout.childRows replayGraph) e
  let copied:=copyTable ports table.table
  (copied.1,table.clock+replayGraph.work+copied.2+ports.length+e.val+10)

/-- Packet vertices likewise use canonical actual child port lists. -/
theorem rightOne_ports {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length) :
    (rightOne net source i g ctx z t beta e).1.ports=
      SemiprimeD1TensorNetwork.rightPorts
        (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)) e := rfl

/-- Canonical global factor scopes have exactly the actual physical bucket length. -/
theorem rightOne_degree {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length) :
    (SemiprimeD1TensorNetwork.rightPorts
      (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)) e).length=
    (SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
      source (packetIndex net source i g e) i g).endpoints.length := by
  rw [SemiprimeD1RootNetworkOrder.rightPorts_length]
  have he : e.val<(graph net source i g).factors.length := by
    simpa only [SemiprimeD1TensorNetworkLayout.childRows,List.length_map] using e.isLt
  simp only [SemiprimeD1TensorNetwork.arity,SemiprimeD1TensorNetworkLayout.childRows,List.getElem_map,List.length_map]
  change ((graph net source i g).factors[e.val]).length=
    (((graph net source i g).factors[e.val]?).getD []).length
  rw [List.getElem?_eq_getElem he]
  rfl

/-- An actual assembled packet entry is the physical kernel/mode/affine evaluator result. -/
theorem rightOne_value {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length)
    (bits : List Bool)
    (hb : bits.length=(SemiprimeD1TensorNetwork.rightPorts
      (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)) e).length) :
    (SemiprimeD1TensorTables.lookup (rightOne net source i g ctx z t beta e).1.table bits).words=
    (SemiprimeD1PacketEntryBits.evaluate ctx (SemiprimeD1PacketEntryBits.borrow z) a i t
      (SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
        source (packetIndex net source i g e) i g).masks
      (SemiprimeD1PacketTensorTables.prepare (SemiprimeD1TensorNetwork.owner net.rows)
        source (packetIndex net source i g e) i g).endpoints beta bits).words := by
  dsimp only [rightOne]
  rw [copyTable_value _ _ bits hb]
  apply SemiprimeD1PacketTensorTables.acquire_value
  exact hb.trans (rightOne_degree net source i g e)

/-- Actual packet entry generation and copying need no coefficient-shape oracle. -/
theorem rightOne_good {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length) :
    SemiprimeD1TensorTables.Good ctx (rightOne net source i g ctx z t beta e).1.table := by
  apply copyTable_good
  exact SemiprimeD1PacketTensorTables.acquire_good _ ctx z a i t beta

/-- Whole actual child network and all source/table/control reports. -/
structure Run where
  /-- Entire concrete child rows and both literal vertex caches. -/
  network : Network
  /-- Every actual old-copy and packet-entry table report, retaining source acquisition. -/
  clock : ℕ

/-- Assemble all old and packet vertices from actual retained source data. -/
def fromSource {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) : Run :=
  let data:=SemiprimeD1ChildPortPullback.fromReplay (SemiprimeD1TensorNetwork.owner net.rows)
    source.packets i g
  let replayGraph:=graph net source i g
  let rs:=SemiprimeD1TensorNetworkLayout.childRows replayGraph
  let left:=Vector.ofFn (leftOne net data old extra p)
  let right:=Vector.ofFn (fun e : Fin rs.length =>
    rightOne net source i g ⟨extra++old.axes,p⟩ z t beta e)
  ⟨⟨net.leftCount+net.rows.length,rs,left.map Prod.fst,right.map Prod.fst⟩,
    source.work+data.work+replayGraph.work+z.clock+(left.toList.map Prod.snd).sum+(right.toList.map Prod.snd).sum+
      10*(net.leftCount+net.rows.length+rs.length+data.links.length+1)^3⟩

/-- Child assembly exposes exactly the actual prepared graph's rows. -/
theorem fromSource_rows {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    (fromSource net source i g old extra p z t beta).network.rows=
      SemiprimeD1TensorNetworkLayout.childRows (graph net source i g) := rfl

/-- Every actual child table has its canonical global incidence ports. -/
theorem fromSource_wellFormed {r a : ℕ} (net : Network) (source : Source net a)
    (i : Fin a) (g : Fin r) (old : Context) (extra : List ℕ) (p : ℕ)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) :
    SemiprimeD1TensorNetwork.WellFormed (fromSource net source i g old extra p z t beta).network := by
  constructor
  · intro v
    simp only [fromSource,Vector.getElem_map,Vector.getElem_ofFn,leftOne_ports]
    congr 1
  · intro e
    simp only [fromSource,Vector.getElem_map,Vector.getElem_ofFn,rightOne_ports]
    congr 1

/-- Actual parent shape suffices for every copied and newly computed child table. -/
theorem fromSource_good {r a : ℕ} (net : Network) (source : Source net a)
    (i : Fin a) (g : Fin r) (old : Context) (extra : List ℕ) (p : ℕ)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (hg : SemiprimeD1TensorNetwork.Good old net) (he : 0<extra.prod) :
    SemiprimeD1TensorNetwork.Good ⟨extra++old.axes,p⟩
      (fromSource net source i g old extra p z t beta).network := by
  dsimp only [SemiprimeD1TensorNetwork.Good,SemiprimeD1TensorNetwork.vertices,fromSource]
  intro v hv
  change SemiprimeD1RootNetwork.GoodVertex ⟨extra++old.axes,p⟩ v
  rcases List.mem_append.mp hv with h|h
  · obtain ⟨j,hj,hv⟩:=List.mem_iff_getElem.mp h
    rw [Vector.getElem_toList] at hv
    subst v
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    exact leftOne_good net _ old extra p _ hg he
  · obtain ⟨j,hj,hv⟩:=List.mem_iff_getElem.mp h
    rw [Vector.getElem_toList] at hv
    subst v
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    exact rightOne_good net source i g ⟨extra++old.axes,p⟩ z t beta _

/-- Original selector/replay/mode acquisition remains in the complete child report. -/
theorem fromSource_retains {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    source.work≤(fromSource net source i g old extra p z t beta).clock := by
  dsimp only [fromSource]
  omega
/-- The supplied affine-node acquisition is retained even when the packet family is empty. -/
theorem fromSource_retains_node {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    z.clock≤(fromSource net source i g old extra p z t beta).clock := by
  dsimp only [fromSource]
  omega

/-- Original current-network entry: replay, selector and mode data are acquired internally. -/
def acquire (net : Network) (old : Context) (extra : List ℕ) (p r a u phase : ℕ)
    (i : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) : Run :=
  let source:=SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length r a u phase
    old.precision (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)
  fromSource net source i g old extra p z t beta

/-- Actual original-source child acquisition has canonical ports. -/
theorem acquire_wellFormed (net : Network) (old : Context) (extra : List ℕ) (p r a u phase : ℕ)
    (i : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    SemiprimeD1TensorNetwork.WellFormed (acquire net old extra p r a u phase i g z t beta).network :=
  fromSource_wellFormed net _ i g old extra p z t beta

/-- Actual original-source child acquisition derives coefficient shape from the parent. -/
theorem acquire_good (net : Network) (old : Context) (extra : List ℕ) (p r a u phase : ℕ)
    (i : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (hg : SemiprimeD1TensorNetwork.Good old net) (he : 0<extra.prod) :
    SemiprimeD1TensorNetwork.Good ⟨extra++old.axes,p⟩
      (acquire net old extra p r a u phase i g z t beta).network :=
  fromSource_good net _ i g old extra p z t beta hg he
end RiemannGaussian.SemiprimeD1ChildNetwork
