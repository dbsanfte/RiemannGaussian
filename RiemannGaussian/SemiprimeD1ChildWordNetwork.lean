/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordPacketTables
import RiemannGaussian.SemiprimeD1ChildNetworkTape

/-! # Actual child networks with word packet entries and tape parent copies
Complete literal caches, not entry functions, are stored in the resulting
network. Every actual source/header/table/copy report remains in its own run.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildWordNetwork
open SemiprimeD1JetAxes
open SemiprimeD1TensorNetwork (Network)
open SemiprimeD1ChildNetwork (Source Pullback graph packetIndex)

/-- Acquire an actual right packet table and recopy via the physical tape reader. -/
def rightOne {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length) :
    SemiprimeD1LeafCounter.Vertex×ℕ :=
  let packet:=packetIndex net source i g e
  let header:=SemiprimeD1PacketTensorTables.prepare
    (SemiprimeD1TensorNetwork.owner net.rows) source packet i g
  let table:=SemiprimeD1JetWordPacketTables.acquire header ctx z a i t beta
  let replayGraph:=graph net source i g
  let ports:=SemiprimeD1TensorNetwork.rightPorts
    (SemiprimeD1TensorNetworkLayout.childRows replayGraph) e
  let copied:=SemiprimeD1ChildNetworkTape.copyTable ports table.table
  (copied.1,table.clock+replayGraph.work+copied.2+ports.length+e.val+10)

/-- Literal right vertex data match the original acquired child, excluding clocks. -/
theorem rightOne_vertex {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (ctx : Context) (hpos:ctx.Positive) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows (graph net source i g)).length) :
    (rightOne net source i g ctx z t beta e).1=
      (SemiprimeD1ChildNetwork.rightOne net source i g ctx z t beta e).1 := by
  dsimp only [rightOne,SemiprimeD1ChildNetwork.rightOne]
  rw [SemiprimeD1JetWordPacketTables.acquire_table _ ctx hpos,
    SemiprimeD1ChildNetworkTape.copyTable_vertex]

/-- New source/word/tape child construction, with all cached reports materialized once. -/
def fromSource {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) : SemiprimeD1ChildNetwork.Run :=
  let data:=SemiprimeD1ChildPortPullback.fromReplay (SemiprimeD1TensorNetwork.owner net.rows)
    source.packets i g
  let replayGraph:=graph net source i g
  let rs:=SemiprimeD1TensorNetworkLayout.childRows replayGraph
  let left:=SemiprimeD1ChildNetworkTape.acquireLeft net data old extra p
  let right:=Vector.ofFn (fun e:Fin rs.length=>
    rightOne net source i g ⟨extra++old.axes,p⟩ z t beta e)
  ⟨⟨net.leftCount+net.rows.length,rs,left.values,right.map Prod.fst⟩,
    source.work+data.work+replayGraph.work+z.clock+left.clock+(right.toList.map Prod.snd).sum+
      10*(net.leftCount+net.rows.length+rs.length+data.links.length+1)^3⟩

/-- Exact child network equality derives every table/port/order correspondence.
No old clock equality or execution is used by the new constructor. -/
theorem fromSource_network {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (hpos:(⟨extra++old.axes,p⟩:Context).Positive) :
    (fromSource net source i g old extra p z t beta).network=
      (SemiprimeD1ChildNetwork.fromSource net source i g old extra p z t beta).network := by
  have hr:(Vector.ofFn (fun e=>rightOne net source i g ⟨extra++old.axes,p⟩ z t beta e)).map Prod.fst=
      (Vector.ofFn (fun e=>SemiprimeD1ChildNetwork.rightOne net source i g
        ⟨extra++old.axes,p⟩ z t beta e)).map Prod.fst:=by
    apply Vector.ext
    intro k hk
    simp only [Vector.getElem_map,Vector.getElem_ofFn,rightOne_vertex _ _ _ _ _ hpos]
  dsimp only [fromSource,SemiprimeD1ChildNetwork.fromSource]
  rw [SemiprimeD1ChildNetworkTape.acquireLeft_values,hr]

/-- New runtime still retains the actual source and acquired affine node reports. -/
theorem fromSource_retains {r a : ℕ} (net : Network) (source : Source net a) (i : Fin a) (g : Fin r)
    (old : Context) (extra : List ℕ) (p : ℕ) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    source.work+z.clock ≤ (fromSource net source i g old extra p z t beta).clock := by
  dsimp only [fromSource]
  omega
end RiemannGaussian.SemiprimeD1ChildWordNetwork
