/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootTensorTablesBounds
import RiemannGaussian.SemiprimeD1TensorNetwork

/-! # Original eager root caches into concrete network data
The adapter reads cached owner records and literal local tables. It never
reexecutes an arithmetic entry checker. Canonical port relabeling copies whole
local tables through paid literal lookups; its report retains the source once.
Native finite-index/filter/search operations remain a separate bit-cost seam.
-/
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RootNetwork
open SemiprimeD1RootTensorTables

/-- Cached owner rows retain repeated occurrences in original factor order. -/
def rows {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) : SemiprimeD1TensorNetwork.Rows n :=
  List.ofFn (fun e : Fin F =>
    (data.records.filter (fun p => decide (p.port.1=e))).map PortRecord.owner)

/-- The cached row family has exactly the original factor count. -/
theorem rows_length {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) :
    (rows data).length=F := List.length_ofFn

/-- Explicit canonical zero tensor used only for an out-of-range cache read. -/
def defaultNode (I : Type) : Node I := ⟨[],.leaf [[]],0⟩

/-- Canonical ports and a copied cached table, with every literal lookup retained. -/
def copyNode {I : Type} (ports : List ℕ) (source : Node I) : SemiprimeD1LeafCounter.Vertex × ℕ :=
  let out:=SemiprimeD1TensorTables.build ports.length (fun bits => SemiprimeD1TensorTables.lookup source.table bits)
  (⟨ports,out.table⟩,out.clock+3)

/-- Copying changes only the global port descriptors. -/
theorem copyNode_ports {I : Type} (ports : List ℕ) (source : Node I) :
    (copyNode ports source).1.ports=ports := rfl

/-- Every copied entry is an actual lookup in the acquired source table. -/
theorem copyNode_value {I : Type} (ports : List ℕ) (source : Node I)
    (bits : List Bool) (hb : bits.length=ports.length) :
    (SemiprimeD1TensorTables.lookup (copyNode ports source).1.table bits).words=
      (SemiprimeD1TensorTables.lookup source.table bits).words := SemiprimeD1TensorTables.build_value _ _ bits hb

/-- Canonical source coefficients remain canonical through the paid copy. -/
theorem copyNode_good {I : Type} (ctx : SemiprimeD1JetAxes.Context)
    (ports : List ℕ) (source : Node I) (hs : SemiprimeD1TensorTables.Good ctx source.table) :
    SemiprimeD1TensorTables.Good ctx (copyNode ports source).1.table :=
  SemiprimeD1TensorTables.build_good ctx _ _ (fun bits _ => SemiprimeD1TensorTables.lookup_good ctx source.table hs bits)

/-- Copy cost is derived from the actual source table shape and physical lookup clock. -/
theorem copyNode_clock {I : Type} (ctx : SemiprimeD1JetAxes.Context)
    (ports : List ℕ) (source : Node I) (hs : SemiprimeD1TensorTables.Good ctx source.table) :
    (copyNode ports source).2≤
      (ctx.rank*(3*ctx.precision+4)+4*source.ports.length+8)*2^ports.length := by
  have h:=SemiprimeD1TensorTables.build_clock ports.length
    (ctx.rank*(3*ctx.precision+4)+1+4*source.ports.length)
    (fun bits => SemiprimeD1TensorTables.lookup source.table bits)
    (fun bits _ => SemiprimeD1TensorTables.lookup_clock ctx source.table hs bits)
  have he : ctx.rank*(3*ctx.precision+4)+1+4*source.ports.length+7=
      ctx.rank*(3*ctx.precision+4)+4*source.ports.length+8 := by omega
  rw [he] at h
  dsimp only [copyNode]
  omega

/-- Full resulting network and the source/copy/control report. -/
structure Run where
  /-- Concrete finite rows and literal table vectors. -/
  network : SemiprimeD1TensorNetwork.Network
  /-- Retained original cache production and every copied-table report. -/
  clock : ℕ

/-- Assemble canonical global port lists using only cached root metadata/tables. -/
def fromCache {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) : Run :=
  let rs:=rows data
  let left:=Vector.ofFn (fun v : Fin n =>
    copyNode (SemiprimeD1TensorNetwork.leftPorts rs v) (data.owners[v.val]?.getD (defaultNode _)))
  let right:=Vector.ofFn (fun e : Fin rs.length =>
    copyNode (SemiprimeD1TensorNetwork.rightPorts rs e) (data.factors[e.val]?.getD (defaultNode _)))
  ⟨⟨n,rs,left.map Prod.fst,right.map Prod.fst⟩,
    data.clock+(left.toList.map Prod.snd).sum+(right.toList.map Prod.snd).sum+
      10*(data.records.length+F+n+1)^3⟩

/-- The assembled network's rows are the actual cached owner rows. -/
theorem fromCache_rows {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) :
    (fromCache data).network.rows=rows data := rfl

/-- Global ports are canonical by construction, without a layout-answer premise. -/
theorem fromCache_wellFormed {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) :
    SemiprimeD1TensorNetwork.WellFormed (fromCache data).network := by
  constructor
  · intro v
    simp only [fromCache, Vector.getElem_map, Vector.getElem_ofFn, copyNode_ports]
    congr 1
  · intro e
    simp only [fromCache, Vector.getElem_map, Vector.getElem_ofFn, copyNode_ports]
    congr 1

/-- Original source production remains paid before any copied network table. -/
theorem fromCache_retains {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) :
    data.clock≤(fromCache data).clock := by
  dsimp only [fromCache]
  omega

/-- Positive-N entry computes its own original root cache exactly once. -/
def acquirePositive (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) : Run :=
  fromCache (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)

/-- Actual original-N assembly supplies a well-formed literal network. -/
theorem acquirePositive_wellFormed (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) :
    SemiprimeD1TensorNetwork.WellFormed (acquirePositive N hN fixed).network :=
  fromCache_wellFormed _
/-- Canonical fallback and canonical cached entries give canonical finite reads. -/
theorem cache_good {I : Type} (ctx : SemiprimeD1JetAxes.Context)
    (xs : List (Node I)) (fallback : Node I)
    (hf : SemiprimeD1TensorTables.Good ctx fallback.table)
    (hx : ∀x∈xs,SemiprimeD1TensorTables.Good ctx x.table) (i : ℕ) :
    SemiprimeD1TensorTables.Good ctx (xs[i]?.getD fallback).table := by
  induction xs generalizing i with
  | nil => exact hf
  | cons x xs ih =>
    cases i with
    | zero => exact hx x (List.mem_cons_self)
    | succ i => exact ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) i

/-- The default zero vector is a canonical root coefficient. -/
theorem defaultNode_good (I : Type) :
    SemiprimeD1TensorTables.Good SemiprimeD1RootOwnerTables.rootContext (defaultNode I).table := by
  simp [defaultNode,SemiprimeD1TensorTables.Good,SemiprimeD1TensorTables.GoodWords,
    SemiprimeD1RootOwnerTables.rootContext,SemiprimeD1JetAxes.Context.rank,
    SemiprimeSourceCompactBits.Compact]

/-- Canonicality as a predicate of the whole dependent vertex record. -/
def GoodVertex (ctx : SemiprimeD1JetAxes.Context) (v : SemiprimeD1LeafCounter.Vertex) : Prop :=
  SemiprimeD1TensorTables.Good ctx v.table

/-- Every actual copied cache remains canonical; no coefficient-shape advice is used. -/
theorem fromCache_good {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity)
    (hl : ∀x∈data.owners,SemiprimeD1TensorTables.Good SemiprimeD1RootOwnerTables.rootContext x.table)
    (hr : ∀x∈data.factors,SemiprimeD1TensorTables.Good SemiprimeD1RootOwnerTables.rootContext x.table) :
    SemiprimeD1TensorNetwork.Good SemiprimeD1RootOwnerTables.rootContext (fromCache data).network := by
  dsimp only [SemiprimeD1TensorNetwork.Good,SemiprimeD1TensorNetwork.vertices,fromCache]
  intro v hv
  change GoodVertex SemiprimeD1RootOwnerTables.rootContext v
  rcases List.mem_append.mp hv with h | h
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
    rw [Vector.getElem_toList] at he
    subst v
    have hi' : i<n := by simpa only [Vector.length_toList] using hi
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    change GoodVertex SemiprimeD1RootOwnerTables.rootContext
      (copyNode (SemiprimeD1TensorNetwork.leftPorts (rows data) ⟨i,hi'⟩)
        (data.owners[i]?.getD (defaultNode _))).1
    exact copyNode_good _ _ _ (cache_good _ _ _ (defaultNode_good _) hl i)
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
    rw [Vector.getElem_toList] at he
    subst v
    have hi' : i<(rows data).length := by simpa only [Vector.length_toList] using hi
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    change GoodVertex SemiprimeD1RootOwnerTables.rootContext
      (copyNode (SemiprimeD1TensorNetwork.rightPorts (rows data) ⟨i,hi'⟩)
        (data.factors[i]?.getD (defaultNode _))).1
    exact copyNode_good _ _ _ (cache_good _ _ _ (defaultNode_good _) hr i)

/-- Membership in a literal canonical table map needs no execution of its producer. -/
theorem map_good {A I : Type} (xs : List A) (f : A→Node I)
    (hf : ∀a,SemiprimeD1TensorTables.Good SemiprimeD1RootOwnerTables.rootContext (f a).table) :
    ∀x∈xs.map f,SemiprimeD1TensorTables.Good SemiprimeD1RootOwnerTables.rootContext x.table := by
  intro x hx
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
  exact hf a

/-- The actual original-N producer supplies both canonical cache families itself. -/
theorem acquirePositive_good (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) :
    SemiprimeD1TensorNetwork.Good SemiprimeD1RootOwnerTables.rootContext
      (acquirePositive N hN fixed).network := by
  dsimp only [acquirePositive]
  apply fromCache_good
  · rw [SemiprimeD1RootTensorTables.acquirePositive_owners N hN fixed]
    exact map_good _ _ (ownerNode_good N fixed _)
  · rw [SemiprimeD1RootTensorTables.acquirePositive_factors N hN fixed]
    exact map_good _ _ (factorNode_good N hN)
end RiemannGaussian.SemiprimeD1RootNetwork
