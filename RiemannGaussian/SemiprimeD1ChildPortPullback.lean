/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildActivationOriginal

/-! # Executed cached original-port pullback for physical group children
The original edge-ID bank is acquired from retained original typed ports and
actual placements. Every child endpoint performs a literal physical ID lookup.
No desired permutation, Word getter, or tensor truth callback is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1ChildPortPullback
open SemiprimeMaterializedWords SemiprimeD1ChildGraph SemiprimeD1PacketInventory

/-- Acquire the original occurrence-ID bank by physically copying each actual ID. -/
def bank {I : Type*} : List (I×Placement)→Run (List (List Bool×I))
  | [] => ⟨[],2⟩
  | (i,p)::ps =>
    let id := SemiprimeSourceCompactBits.copy p.edge
    let tail := bank ps
    ⟨(id.bits,i)::tail.value,id.clock+tail.work+6⟩

/-- Literal bank content from original acquired occurrences, without an ID oracle. -/
theorem bank_value {I : Type*} (ps : List (I×Placement)) :
    (bank ps).value=ps.map (fun p => (p.2.edge,p.1)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [bank,ih,SemiprimeSourceCompactBits.copy_bits,List.map_cons]

/-- Linear physical lookup; arbitrary padding aliases are not conflated. -/
def findPort {I : Type*} (target : List Bool) : List (List Bool×I)→Run (Option I)
  | [] => ⟨none,2⟩
  | (id,i)::rest =>
    let same := equalBytes id target
    if same.value then ⟨some i,same.work+4⟩
    else
      let tail := findPort target rest
      ⟨tail.value,same.work+tail.work+6⟩

/-- Acquire one original-port/side link for every actual child incidence. -/
def pull {I : Type*} {V : ℕ} (ids : List (List Bool×I)) :
    List (Endpoint V)→Run (List (Option (I×Bool)))
  | [] => ⟨[],2⟩
  | e::es =>
    let here := findPort e.edge ids
    let tail := pull ids es
    ⟨(here.value.map (fun i => (i,e.side)))::tail.value,here.work+tail.work+5⟩

/-- Exact child factor-major pullback scan; all searches are actually executed. -/
theorem pull_value {I : Type*} {V : ℕ} (ids : List (List Bool×I)) (es : List (Endpoint V)) :
    (pull ids es).value=es.map (fun e => (findPort e.edge ids).value.map (fun i => (i,e.side))) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [pull,ih,List.map_cons]

/-- Whole prepared group data, retaining source, graph, activation and computed links. -/
structure Acquired (n F a : ℕ) (inputArity : Fin F→ℕ) where
  /-- Once-produced parent source, also needed for isolated old-vertex activation. -/
  source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity
  /-- Actual cached group child graph. -/
  graph : Graph (n+F)
  /-- Actual activation bits for every old vertex. -/
  activation : SemiprimeSourceCompactBits.Report
  /-- Actual physically copied original ID/native-port bank. -/
  ids : List (List Bool×((e : Fin F)×Fin (inputArity e)))
  /-- Actually computed original-port/side links in child factor-major order. -/
  links : List (Option (((e : Fin F)×Fin (inputArity e))×Bool))
  /-- Shared source once, actual graph/mask locals, bank and lookup reports. -/
  work : ℕ

/-- Conservative native list/zip/flatten metadata traversal allowance.
This is not a binary-address machine clock. -/
def metadataAllowance {n F a : ℕ} {inputArity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (graph : Graph (n+F)) : ℕ :=
  10*(source.padding.source.selection.cache.data.metadata.incidences.length+
    source.placements.length+graph.factors.length+graph.endpoints.length+1)

/-- Reuse original source once; independently execute each physical producer once. -/
def fromReplay {n F a r : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (q : Fin a) (g : Fin r) :
    Acquired n F a inputArity :=
  let graph := SemiprimeD1ChildGraph.fromReplay inputOwner source q g
  let activation := SemiprimeD1ChildActivation.fromReplay source q g
  let ids := bank (source.padding.source.selection.cache.data.metadata.incidences.zip source.placements)
  let links := pull ids.value graph.factors.flatten
  ⟨source,graph,activation,ids.value,links.value,
    graph.work+(activation.clock-source.state.clock)+ids.work+links.work+metadataAllowance source graph+20⟩

/-- Original-input prepared child, with no activation or port-permutation advice. -/
def acquire (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    Acquired n F a inputArity :=
  fromReplay inputOwner (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) q g

/-- The shared original source report is counted once, not executed twice by a wrapper. -/
theorem work_decomposition {n F a r : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (q : Fin a) (g : Fin r) :
    (fromReplay inputOwner source q g).work=
      source.state.clock+
      ((SemiprimeD1ChildGraph.fromReplay inputOwner source q g).work-source.state.clock)+
      ((SemiprimeD1ChildActivation.fromReplay source q g).clock-source.state.clock)+
      (bank (source.padding.source.selection.cache.data.metadata.incidences.zip source.placements)).work+
      (pull (fromReplay inputOwner source q g).ids (fromReplay inputOwner source q g).graph.factors.flatten).work+
      metadataAllowance source (fromReplay inputOwner source q g).graph+20 := by
  have hg := SemiprimeD1ChildGraph.fromReplay_retains inputOwner source q g
  unfold fromReplay
  dsimp only
  omega

end RiemannGaussian.SemiprimeD1ChildPortPullback
