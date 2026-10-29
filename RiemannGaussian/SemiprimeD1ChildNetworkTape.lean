/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildTensorTablesTape
import RiemannGaussian.SemiprimeD1ChildNetwork

/-! # Actual static child left tables with sequential tape memory
Alignment, activated per-entry lifting, and canonical-port recopy all execute
full paid serialization/lookup. No entry/copy/backend supplier is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1ChildNetworkTape
open SemiprimeD1JetAxes SemiprimeD1TensorTables
open SemiprimeD1TensorNetwork (Network)
open SemiprimeD1ChildNetwork (Pullback parentVertex)

/-- Canonical ordered-port copy with the actual tape backend at every assignment. -/
def copyTable {d : ℕ} (ports : List ℕ) (table : Table d) : SemiprimeD1LeafCounter.Vertex×ℕ :=
  let out:=build ports.length (fun bits => SemiprimeD1TensorTapeLookup.fromTable table bits)
  (⟨ports,out.table⟩,out.clock+3)

/-- Copying retains the literal canonical descriptors. -/
theorem copyTable_ports {d : ℕ} (ports : List ℕ) (table : Table d) :
    (copyTable ports table).1.ports=ports := rfl

/-- The literal copied vertex is unchanged, excluding its new memory-access clock. -/
theorem copyTable_vertex {d : ℕ} (ports : List ℕ) (table : Table d) :
    (copyTable ports table).1=(SemiprimeD1ChildNetwork.copyTable ports table).1 := by
  have h:=SemiprimeD1TensorTapeLeaf.build_table_congr ports.length
    (fun bits => SemiprimeD1TensorTapeLookup.fromTable table bits) (lookup table)
    (fun bits => SemiprimeD1TensorTapeLookup.fromTable_words table bits)
  exact congrArg (fun tab => (⟨ports,tab⟩ : SemiprimeD1LeafCounter.Vertex)) h

/-- Generic dependent-table transport preserves exact literal copied vertices. -/
theorem copyTable_payload {d e : ℕ} (ports : List ℕ) (t : Table d) (u : Table e)
    (h : (⟨d,t⟩ : (k : ℕ) × Table k)=⟨e,u⟩) :
    (copyTable ports t).1=(SemiprimeD1ChildNetwork.copyTable ports u).1 :=
  (copyTable_vertex ports t).trans
    (congrArg (fun x : (k : ℕ) × Table k => (SemiprimeD1ChildNetwork.copyTable ports x.2).1) h)

/-- Actual alignment, per-entry old integer lift and canonical recopy for one old vertex. -/
def leftOne {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ)
    (v : Fin (net.leftCount+net.rows.length)) : SemiprimeD1LeafCounter.Vertex×ℕ :=
  let order:=SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v
  let parent:=parentVertex net v
  let aligned:=build order.old.length (fun bits => SemiprimeD1TensorTapeLookup.fromTable parent.table bits)
  let child:=SemiprimeD1ChildTensorTablesTape.fromCache
    (SemiprimeD1TensorNetwork.owner net.rows) data v old extra p aligned.table
  let ports:=SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v
  let copied:=copyTable ports child.table
  (copied.1,order.clock+aligned.clock+child.clock+copied.2+ports.length+v.val+12)

/-- Every left vertex has exactly the actual canonical child port order. -/
theorem leftOne_ports {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ) (v : Fin (net.leftCount+net.rows.length)) :
    (leftOne net data old extra p v).1.ports=
      SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v := rfl

/-- The complete new left vertex equals the frozen original literal child vertex. -/
theorem leftOne_vertex {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ) (v : Fin (net.leftCount+net.rows.length)) :
    (leftOne net data old extra p v).1=(SemiprimeD1ChildNetwork.leftOne net data old extra p v).1 := by
  let order:=SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v
  let parent:=parentVertex net v
  let aligned:=build order.old.length (fun bits => SemiprimeD1TensorTapeLookup.fromTable parent.table bits)
  let original:=build order.old.length (lookup parent.table)
  let ports:=SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v
  have ha : aligned.table=original.table := SemiprimeD1TensorTapeLeaf.build_table_congr _ _ _
    (fun bits => SemiprimeD1TensorTapeLookup.fromTable_words parent.table bits)
  have hc:=SemiprimeD1ChildTensorTablesTape.fromCache_payload
    (SemiprimeD1TensorNetwork.owner net.rows) data v old extra p aligned.table
  have hc' := hc.trans (congrArg (fun tab => SemiprimeD1ChildTensorTablesTape.payload
    (SemiprimeD1ChildTensorTables.fromCache (SemiprimeD1TensorNetwork.owner net.rows)
      data v old extra p tab)) ha)
  exact copyTable_payload ports _ _ hc'

/-- Canonical child words derive from the actual old data and original per-entry lift. -/
theorem leftOne_good {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ) (v : Fin (net.leftCount+net.rows.length))
    (hg : SemiprimeD1TensorNetwork.Good old net) (he : 0<extra.prod) :
    Good ⟨extra++old.axes,p⟩ (leftOne net data old extra p v).1.table := by
  rw [leftOne_vertex]
  exact SemiprimeD1ChildNetwork.leftOne_good net data old extra p v hg he

/-- Static complete left-table cache with its actual construction report. -/
structure LeftRun (N : ℕ) where
  /-- Every old vertex remains present, including isolated or masked-out vertices. -/
  values : Vector SemiprimeD1LeafCounter.Vertex N
  /-- Sum of every actual repeated alignment, activation, lift and recopy report. -/
  clock : ℕ

/-- Execute and cache all actual leftOne reports once before reading their fields. -/
def acquireLeft {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ) : LeftRun (net.leftCount+net.rows.length) :=
  let all:=Vector.ofFn (leftOne net data old extra p)
  ⟨all.map Prod.fst,(all.toList.map Prod.snd).sum+10*(net.leftCount+net.rows.length+1)⟩

/-- Static new left data are literally the frozen original data in the same order. -/
theorem acquireLeft_values {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ) :
    (acquireLeft net data old extra p).values=
      (Vector.ofFn (SemiprimeD1ChildNetwork.leftOne net data old extra p)).map Prod.fst := by
  apply Vector.ext
  intro i hi
  simp only [acquireLeft,Vector.getElem_map,Vector.getElem_ofFn,leftOne_vertex]

/-- Every actual left report and the static vector traversal allowance are retained. -/
theorem acquireLeft_clock {a : ℕ} (net : Network) (data : Pullback net a)
    (old : Context) (extra : List ℕ) (p : ℕ) :
    (acquireLeft net data old extra p).clock=
      ((Vector.ofFn (leftOne net data old extra p)).toList.map Prod.snd).sum+
        10*(net.leftCount+net.rows.length+1) := rfl

end RiemannGaussian.SemiprimeD1ChildNetworkTape
